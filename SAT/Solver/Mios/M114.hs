{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Solver.Mios.M114
       (
         simplifyDB
       , solve
       )
        where

import Control.Monad ((<=<), forM_, unless, when)
import Data.Bits
import Data.Foldable (foldrM)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.ClauseManager
import SAT.Solver.Mios.WatcherLists
import SAT.Solver.Mios.Solver

--------------------------------------------------------------------------------
-- Operations on 'Clause'
--------------------------------------------------------------------------------

-- | __Fig. 8. (p.12)__ create a new clause and adds it to watcher lists
-- Constructor function for clauses. Returns @False@ if top-level conflict is determined.
-- @outClause@ may be set to Null if the new clause is already satisfied under the current
-- top-level assignment.
--
-- __Post-condition:__ @ps@ is cleared. For learnt clauses, all
-- literals will be false except @lits[0]@ (this by design of the 'analyze' method).
-- For the propagation to work, the second watch must be put on the literal which will
-- first be unbound by backtracking. (Note that none of the learnt-clause specific things
-- needs to done for a user defined contraint type.)
--
-- This is a restricted version of 'newClause' for learnt clause.
{-# INLINABLE newLearntClause #-}
newLearntClause :: Solver -> Vec -> IO Clause
newLearntClause s@Solver{..} ps = do
  -- now ps[0] is the number of living literals
  -- Since this solver must generate only healthy learnt clauses, we need not to check then
  k <- getNth ps 0
  case k of
   0 -> return NullClause
   1 -> do
     l <- getNth ps 1
     enqueue s l NullClause
     return NullClause
   _ -> do
     -- allocate clause:
     c <- newClauseFromVec True ps
     -- Pick a second literal to watch:
     let
       findMax :: Int -> Int -> Int -> IO Int
       findMax ((<= k) -> False) j _ = return j
       findMax i j val = do
         v' <- lit2var <$> getNth ps i
         a <- getNth assigns v'
         b <- getNth level v'
         if (a /= lBottom) && (val < b)
           then findMax (i + 1) i b
           else findMax (i + 1) j val
     -- Let @max_i@ be the index of the literal with highest decision level
     max_i <- findMax 1 1 0
     swapBetween ps 2 max_i
     -- check literals occurences
     -- x <- asList c
     -- unless (length x == length (nub x)) $ error "new clause contains a element doubly"
     -- Bumping:
     claBumpActivity s c -- newly learnt clauses should be considered active
     forM_ [1 .. k] $ varBumpActivity s . lit2var <=< getNth ps -- variables in conflict clauses are bumped
     -- Add clause to watcher lists:
     l0 <- negateLit <$> getNth ps 1
     pushClause (getNthWatchers watches l0) c
     l1 <- negateLit <$> getNth ps 2
     pushClause (getNthWatchers watches l1) c
     return c

-- | __Remove.__ The 'remove' method supplants the destructor by receiving
-- the solver state as a parameter. It should dispose the constraint and
-- remove it from the watcher lists.
{-# INLINABLE remove #-}
remove :: Clause -> Int -> Solver -> IO ()
remove !c@Clause{..} i Solver{..} = do
  let lvec = asVec c
  l1 <- negateLit <$> getNth lvec 0
  removeClause (getNthWatchers watches l1) c
  l2 <- negateLit <$> getNth lvec 1
  removeClause (getNthWatchers watches l2) c
  removeNthClause (if learnt then learnts else constrs) i
  return ()

-- | __Simplify.__ At the top-level, a constraint may be given the opportunity to
-- simplify its representation (returns @False@) or state that the constraint is
-- satisfied under the current assignment and can be removed (returns @True@).
-- A constraint must /not/ be simplifiable to produce unit information or to be
-- conflicting; in that case the propagation has not been correctly defined.
{-# INLINABLE simplify #-}
simplify :: Clause -> Solver -> IO Bool
simplify c@Clause{..} s@Solver{..} = do
  let cvec = asVec c
  n <- sizeOfClause c
  l1 <- negateLit <$> getNth cvec 0
  l2 <- negateLit <$> getNth cvec 1
  let
    lvec = asVec c
    loop :: Int -> Int -> IO Bool
    loop ((< n) -> False) j = do
      when (0 < n - j) $ do
        shrinkClause (n - j) c
        l1' <- negateLit <$> getNth lvec 0
        when (l1 /= l1') $ do
          removeClause (getNthWatchers watches l1) c
          pushClause (getNthWatchers watches l1') c
        l2' <- negateLit <$> getNth lvec 1
        when (l2 /= l2') $ do
          removeClause (getNthWatchers watches l2) c
          pushClause (getNthWatchers watches l2') c
      return False
    loop i j = do
      l <- getNth lvec i
      v <- valueLit s l
      case v of
       1  -> return True
       -1 -> loop (i+1) j
       _ -> when (i /= j) (setNth lvec j l) >> loop (i+1) (j+1)     -- false literals are not copied (only occur for i >= 2)
  loop 0 0

--------------------------------------------------------------------------------
-- Major methods
--------------------------------------------------------------------------------

-- | __Fig. 10. (p.15)__
-- #M22:
--
-- analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel :: int&) -> [void]
--
-- __Description:_-
--   Analzye confilct and produce a reason clause.
--
-- __Pre-conditions:__
--   * 'out_learnt' is assumed to be cleared.
--   * Corrent decision level must be greater than root level.
--
-- __Post-conditions:__
--   * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
--   * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
--     rest of literals. There may be others from the same level though.
--
-- `analyze` is invoked from `search`
-- {-# INLINEABLE analyze #-}
analyze :: Solver -> Clause -> IO Int
analyze s@Solver{..} confl = do
  -- litvec
  clearStack litsLearnt
  pushToStack litsLearnt 0 -- reserve the first place for the unassigned literal
  setAll an_seen 0   -- FIXME: it should be done in a valid place; not here.
  dl <- getInt decisionLevel
  let
    litsVec = asVec litsLearnt
    trailVec = asVec trail
    loopOnClauseChain :: Clause -> Lit -> Int -> Int -> Int -> IO Int
    loopOnClauseChain c p ti bl pathC = do -- p : literal, ti = trail index, bl = backtrack level
      when (learnt c) $ claBumpActivity s c
      sc <- sizeOfClause c
      let
        lvec = asVec c
        loopOnLiterals :: Int -> Int -> Int -> IO (Int, Int)
        loopOnLiterals ((< sc) -> False) b pc = return (b, pc) -- b = btLevel, pc = pathC
        loopOnLiterals j b pc = do
          (q :: Lit) <- getNth lvec j
          let v = lit2var q
          sn <- getNth an_seen v
          l <- getNth level v
          if sn == 0 && 0 < l
            then do
                varBumpActivity s v
                setNth an_seen v 1
                if l == dl
                  then loopOnLiterals (j + 1) b (pc + 1)
                  else pushToStack litsLearnt q >> loopOnLiterals (j + 1) (max b l) pc
            else loopOnLiterals (j + 1) b pc
      (b', pathC') <- loopOnLiterals (if p == bottomLit then 0 else 1) bl pathC
      let
        -- select next clause to look at
        nextUnseenLit :: Int -> IO Int
        nextUnseenLit i = do
          x <- getNth an_seen . lit2var =<< getNth trailVec i
          if x == 0 then nextUnseenLit $ i - 1 else return i
      ti' <- nextUnseenLit ti
      nextP <- getNth trailVec ti'
      let nextV = lit2var nextP
      confl' <- getNthClause reason nextV
      setNth an_seen nextV 0
      if 1 < pathC'
        then loopOnClauseChain confl' nextP (ti' - 1) b' (pathC' - 1)
        else setNth litsVec 0 (negateLit nextP) >> return b'
  ti <- subtract 1 <$> sizeOfStack trail
  result <- loopOnClauseChain confl bottomLit ti 0 0
  -- Simplify phase
  n <- sizeOfStack litsLearnt
  clearStack an_stack           -- analyze_stack.clear();
  clearStack an_toClear         -- out_learnt.copyTo(analyze_toclear);
  pushToStack an_toClear =<< getNth litsVec 0
  let
    merger :: Int -> Int -> IO Int
    merger ((< n) -> False) b = return b
    merger i b = do
      l <- getNth litsVec i
      pushToStack an_toClear l
      -- restrict the search depth (range) to 32
      merger (i + 1) . setBit b . (31 .&.) =<< getNth level (lit2var l)
  levels <-  merger 1 0
  let
    loopOnLits :: Int -> Int -> IO ()
    loopOnLits ((< n) -> False) n' = shrinkStack litsLearnt $ n - n'
    loopOnLits i j = do
      l <- getNth litsVec i
      c1 <- (NullClause ==) <$> getNthClause reason (lit2var l)
      if c1
        then setNth litsVec j l >> loopOnLits (i + 1) (j + 1)
        else do
           c2 <- not <$> litRedundant s l levels
           if c2
             then setNth litsVec j l >> loopOnLits (i + 1) (j + 1)
             else loopOnLits (i + 1) j
  loopOnLits 1 1                -- the first literal is specail
  return result

-- | #M22
-- Check if 'p' can be removed, 'abstract_levels' is used to abort early if the algorithm is
-- visiting literals at levels that cannot be removed later.
--
-- Implementation memo:
--
-- *  @an_toClear@ is initialized by @ps@ in 'analyze' (a copy of 'learnt').
--   This is used only in this function and 'analyze'.
--
{-# INLINEABLE litRedundant #-}
litRedundant :: Solver -> Lit -> Int -> IO Bool
litRedundant Solver{..} p minLevel = do
  -- assert (reason[var(p)]!= NullCaulse);
  clearStack an_stack      -- analyze_stack.clear()
  pushToStack an_stack p   -- analyze_stack.push(p);
  top <- sizeOfStack an_toClear
  let
    loopOnStack :: IO Bool
    loopOnStack = do
      k <- sizeOfStack an_stack  -- int top = analyze_toclear.size();
      if 0 == k
        then return True
        else do -- assert(reason[var(analyze_stack.last())] != GClause_NULL);
            sl <- lastOfStack an_stack
            popFromStack an_stack             -- analyze_stack.pop();
            c <- getNthClause reason (lit2var sl) -- getRoot sl
            nl <- sizeOfClause c
            let
              cvec = asVec c
              loopOnLit :: Int -> IO Bool -- loopOnLit (int i = 1; i < c.size(); i++){
              loopOnLit ((< nl) -> False) = loopOnStack
              loopOnLit i = do
                p' <- getNth cvec i              -- valid range is [0 .. nl - 1]
                let v' = lit2var p'
                l' <- getNth level v'
                c1 <- (1 /=) <$> getNth an_seen v'
                if c1 && (0 /= l')   -- if (!analyze_seen[var(p)] && level[var(p)] != 0){
                  then do
                      c3 <- (NullClause /=) <$> getNthClause reason v'
                      if c3 && testBit minLevel (l' .&. 31) -- if (reason[var(p)] != GClause_NULL && ((1 << (level[var(p)] & 31)) & min_level) != 0){
                        then do
                            setNth an_seen v' 1        -- analyze_seen[var(p)] = 1;
                            pushToStack an_stack p'    -- analyze_stack.push(p);
                            pushToStack an_toClear p'  -- analyze_toclear.push(p);
                            loopOnLit $ i + 1
                        else do
                            -- loopOnLit (int j = top; j < analyze_toclear.size(); j++) analyze_seen[var(analyze_toclear[j])] = 0;
                            top' <- sizeOfStack an_toClear
                            let vec = asVec an_toClear
                            forM_ [top .. top' - 1] $ \j -> do x <- getNth vec j; setNth an_seen (lit2var x) 0
                            -- analyze_toclear.shrink(analyze_toclear.size() - top); note: shrink n == repeat n pop
                            shrinkStack an_toClear $ top' - top
                            return False
                  else loopOnLit $ i + 1
            loopOnLit 1
  loopOnStack

-- | #M22
-- propagate : [void] -> [Clause+]
--
-- __Description:__
--   Porpagates all enqueued facts. If a conflict arises, the cornflicting clause is returned.
--   otherwise CRef_undef.
--
-- __Post-conditions:__
--   * the propagation queue is empty, even if there was a conflict.
--
-- memo:`propagate` is invoked by `search`,`simpleDB` and `solve`
{-# INLINABLE propagate #-}
propagate :: Solver -> IO Clause
propagate s@Solver{..} = do
  let
    queue = asVec trail
    loopOnQueue :: IO Clause
    loopOnQueue = do
      qi <- getInt qHead        -- queue index
      k <- sizeOfStack trail
      if k <= qi                -- trail contains literals to be propagated
        then return NullClause  -- No conflict
        else do
            p <- getNth queue qi
            modifyInt qHead (+ 1)
            let np = negateLit p
            let w = getNthWatchers watches p
            vec <- getClauseVector w
            let
              loopOnWatcher :: Int -> Int-> IO Clause
              loopOnWatcher i n
                | i == n = loopOnQueue
                | otherwise = do
                    c <- getNthClause vec i
                    x <- propagateLit c s np
                    -- This function inserts @c@ into an apropriate watchers here
                    case x of
                      1  {- still in -} -> loopOnWatcher (i + 1) n
                      -1 {- conflict -} -> (setInt qHead =<< sizeOfStack trail) >> return c
                      _  {- it moved -} -> removeNthClause w i >> loopOnWatcher i (n - 1)
            loopOnWatcher 0 =<< numberOfClauses w
  loopOnQueue

-- | __Propagate.__ The 'propagateLit' method is called if the constraint is found
-- in a watcher list during propagation of unit information /p/. The constraint
-- is removed from the list and is required to insert itself into a new or
-- the same watcher list. Any unit information derivable as a consequence of /p/
-- should enqueued. If successful, @True@ is returned; if a conflict is detected,
-- @False@ is returned. The constraint may add itself to the undo list of @var(p)@
-- if it needs to be updated when /p/ becomes unbound.
--
-- | returns @True@ if no conflict occured
-- this is invoked by 'propagate'
{-# INLINABLE propagateLit #-}
propagateLit :: Clause -> Solver -> Lit -> IO Int -- FIXME: LiftedBool
-- | This function checks clause satisfiabiliy eagerly as Minisat 2.2.
-- But @blocker@ is not used (implemented).
propagateLit c@(asVec -> cv) s@Solver{..} !np = do -- this is slow
  -- Make sure the false literal is not at cv[0] but cv[1] AFTER CHECKING THE CLAUSE SATISFIABILITY
  l0 <- getNth cv 0
  lit <-                   -- @lit@ is the literal at lits[0] or 0 for exception.
    if l0 == np            -- the case that the false literal is at 0
    then do                -- then swap watchers only if the 2nd watecher isn't satisfied.
      l1 <- getNth cv 1
      v1 <- valueLit s l1
      if lTrue == v1 then return 0 else swapBetween cv 0 1 >> return l1
    else                   -- then check the watcher's satisfiability and return it if needed
      (\x -> if lTrue == x then 0 else l0) <$> valueLit s l0
  if lit == 0 -- this means the clause is satisfied, so we keep @c@ in the original watcher list
    then return lTrue
    else do
        -- Look for a new literal to watch:
        !n <- sizeOfClause c
        let
          loopOnLits :: Int -> IO Int -- FIXME: LiftedBool
          loopOnLits ((< n) -> False) = do
            -- Clause is unit under assignment:
            noconf <- enqueue s lit c
            if noconf
              then return lTrue  -- By returning lTrue, it remains in the original watcher list
              else return lFalse -- A conflict occures
          loopOnLits i = do
            !(l :: Lit) <- getNth cv i
            !val <- valueLit s l
            if val /= lFalse    -- l is unassigned or satisfied already; a new wather
              then do
                  swapBetween cv 1 i
                  -- @removeClause m c@ will be done by propagate
                  pushClause (getNthWatchers watches (negateLit l)) c
                  return lBottom
              else loopOnLits $ i + 1
        loopOnLits 2

-- | #M22
-- reduceDB: () -> [void]
--
-- __Description:__
--   Remove half of the learnt clauses, minus the clauses locked by the current assigmnent. Locked
--   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
{-# INLINABLE reduceDB #-}
reduceDB :: Solver -> IO ()
reduceDB s@Solver{..} = do
  ci <- getDouble claInc
  nL <- nLearnts s
  let lim = ci / fromIntegral nL
  -- new engine 0.8
  let isRequired c = do
        l <- sizeOfClause c
        if l == 2
          then return True
          else do
              l <- locked c s
              if l
                then return True
                else (lim <=) <$> getDouble (activity c)
  let isRequired' c = do
        l <- sizeOfClause c
        if l == 2 then return True else locked c s
{-
  let isRequired c = do
        l <- sizeOfClause c
        if l == 2
          then putStr "B" >> return True
          else do
              l <- locked c s
              if l
                then putStr "L" >> return True
                else do
                    r <- (lim <=) <$> getDouble (activity c)
                    putStr $ if r then "U" else "_"
                    return r
  let isRequired' c = do
        l <- sizeOfClause c
        if l == 2
          then putStr "B" >> return True
          else do
              l <- locked c s
              if l
                then putStr "L" >> return True
                else putStr "_" >> return False
-}
  vec <- getClauseVector learnts
  let
    half = div nL 2
    loopOn :: Int -> Int -> IO ()
    loopOn i j
      | i >= j = return ()
      | otherwise = do
          c <- getNthClause vec i
          yes <- if i < half then isRequired c else isRequired' c
          if yes then loopOn (i + 1) j else remove c i s >> loopOn i (j - 1)
  sortOnActivity learnts
  loopOn 0 nL

-- | (Big to small) Quick sort on a clause vector based on their activities
sortOnActivity :: ClauseManager -> IO ()
sortOnActivity cm = do
  n <- numberOfClauses cm
  vec <- getClauseVector cm
  let
    keyOf :: Int -> IO Double
    keyOf i = negate <$> (getDouble . activity =<< getNthClause vec i)
    sortOnRange :: Int -> Int -> IO ()
    sortOnRange left right
      | not (left < right) = return ()
      | left + 1 == right = do
          a <- keyOf left
          b <- keyOf right
          unless (a < b) $ swapClauses vec left right
      | otherwise = do
          let p = div (left + right) 2
          pivot <- keyOf p
          swapClauses vec p left -- set a sentinel for r'
          let
            nextL :: Int -> IO Int
            nextL i@((<= right) -> False) = return i
            nextL i = do v <- keyOf i; if v < pivot then nextL (i + 1) else return i
            nextR :: Int -> IO Int
            -- nextR i@((left <=) -> False) = return i
            nextR i = do v <- keyOf i; if pivot < v then nextR (i - 1) else return i
            divide :: Int -> Int -> IO Int
            divide l r = do
              l' <- nextL l
              r' <- nextR r
              if l' < r' then swapClauses vec l' r' >> divide (l' + 1) (r' - 1) else return r'
          m <- divide (left + 1) right
          swapClauses vec left m
          sortOnRange left (m - 1)
          sortOnRange (m + 1) right
  sortOnRange 0 (n - 1)
  -- checkClauseOrder cm

-- | #M22
--
-- simplify : [void] -> [bool]
--
-- __Description:__
--   Simplify the clause database according to the current top-level assigment. Currently, the only
--   thing done here is the removal of satisfied clauses, but more things can be put here.
--
{-# INLINABLE simplifyDB #-}
simplifyDB :: Solver -> IO Bool
simplifyDB s@Solver{..} = do
  p <- propagate s
  if p /= NullClause
    then return False
    else do
        let
          for :: Int -> IO Bool
          for ((< 2) -> False) = return True
          for t = do
            let ptr = if t == 0 then learnts else constrs
            vec <- getClauseVector ptr
            let
              loopOnVector :: Int -> Int -> IO Bool
              loopOnVector i n
                | i == n = return True
                | otherwise = do
                    c <- getNthClause vec i
                    r <- simplify c s
                    if r then remove c i s >> loopOnVector i (n - 1) else loopOnVector (i + 1) n
            loopOnVector 0 =<< numberOfClauses ptr
        for 0

-- | #M22
--
-- search : (nof_conflicts : int) (params : const SearchParams&) -> [lbool]
--
-- __Description:__
--   Search for a model the specified number of conflicts.
--   NOTE: Use negative value for 'nof_conflicts' indicate infinity.
--
-- __Output:__
--   'l_True' if a partial assigment that is consistent with respect to the clause set is found. If
--   all variables are decision variables, that means that the clause set is satisfiable. 'l_False'
--   if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
{-# INLINABLE search #-}
search :: Solver -> Int -> Int -> IO LiftedBool
search s@Solver{..} nOfConflicts nOfLearnts = do
  -- clear model
  let
    loop :: Int -> IO LiftedBool
    loop conflictC = do
      !confl <- propagate s
      d <- getInt decisionLevel
      if confl /= NullClause
        then do
            -- CONFLICT
            r <- getInt rootLevel
            if d == r
              then return LFalse
              else do
                  backtrackLevel <- analyze s confl -- 'analyze' resets litsLearnt by itself
                  (s `cancelUntil`) . max backtrackLevel =<< getInt rootLevel
                  record s =<< isoVec litsLearnt
                  varDecayActivity s
                  claDecayActivity s
                  loop $ conflictC + 1
        else do                 -- NO CONFLICT
            -- Simplify the set of problem clauses:
            when (d == 0) $ simplifyDB s >> return () -- our simplifier cannot return @False@ here
            k1 <- numberOfClauses learnts
            k2 <- nAssigns s
            when (k1 - k2 >= nOfLearnts) $ do
              reduceDB s -- Reduce the set of learnt clauses
            case () of
             _ | k2 == nVars -> do
                   -- Model found:
                   -- (model `growTo`) nv
                   -- nv <- nVars s
                   -- forM_ [1 .. nv] $ \i -> setAt model i =<< (lTrue ==) <$> assigns .! i
                   forM_ [0 .. nVars - 1] $ \i -> setNthBool model i . (lTrue ==) =<< getNth assigns (i + 1)
                   return LTrue
             _ | conflictC >= nOfConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< getInt rootLevel -- force a restart
                   return Bottom
             _ -> do
               -- New variable decision:
               v <- select s -- many have heuristic for polarity here
               -- << #phasesaving
               oldVal <- valueVar s v
               assume s $ var2lit v (0 < oldVal) -- cannot return @False@
               -- >> #phasesaving
               loop conflictC
  loop 0

-- | __Fig. 16. (p.20)__
-- Main solve method.
--
-- __Pre-condition:__ If assumptions are used, 'simplifyDB' must be
-- called right before using this method. If not, a top-level conflict (resulting in a
-- non-usable internal state) cannot be distinguished from a conflict under assumptions.
solve :: (Foldable t) => Solver -> t Lit -> IO Bool
solve s@Solver{..} assumps = do
  nc <- fromIntegral <$> nConstraints s
  -- PUSH INCREMENTAL ASSUMPTIONS:
  let
    injector :: Lit -> Bool -> IO Bool
    injector _ False = return False
    injector a True = do
      b <- assume s a
      if not b
        then cancelUntil s 0 >> return False
        else do
            c <- propagate s
            if c /= NullClause
              then cancelUntil s 0 >> return False
              else return True
  x <- foldrM injector True assumps
  if not x
    then return False
    else do
        setInt rootLevel =<< getInt decisionLevel
        -- SOLVE:
        let
          while :: LiftedBool -> Double -> Double -> IO Bool
          while Bottom nOfConflicts nOfLearnts = do
            status <- search s (floor nOfConflicts) (floor nOfLearnts)
            while status (1.5 * nOfConflicts) (1.1 * nOfLearnts)
          while status _ _ = do
            cancelUntil s 0
            return $ status == LTrue
        while Bottom 100 (nc / 3.0)

-- | __Fig. 11. (p.15)__
-- Record a clause and drive backtracking.
--
-- __Pre-Condition:__ "clause[0]" must contain
-- the asserting literal. In particular, 'clause[]' must not be empty.
{-# INLINE record #-}
record :: Solver -> Vec -> IO ()
record s@Solver{..} v = do
  c <- newLearntClause s v -- will be set to created clause, or NULL if @clause[]@ is unit
  l <- getNth v 1
  enqueue s l c
  unless (c == NullClause) $ pushClause learnts c
