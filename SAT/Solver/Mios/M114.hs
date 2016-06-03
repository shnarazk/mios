-- | This is an implementaion of MiniSat 1.14 in Haskell
{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
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

import Control.Monad ((<=<), forM_, unless, void, when)
import Data.Bits
import Data.Foldable (foldrM)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.ClauseManager
import SAT.Solver.Mios.WatcherLists
import SAT.Solver.Mios.Solver
import SAT.Solver.Mios.Glucose

-- | #114: __RemoveWatch__
{-# INLINABLE removeWatch #-}
removeWatch :: Solver -> Clause -> IO ()
removeWatch Solver{..} c = do
  let lvec = asVec c
  l1 <- negateLit <$> getNth lvec 0
  removeClause (getNthWatchers watches l1) c
  l2 <- negateLit <$> getNth lvec 1
  removeClause (getNthWatchers watches l2) c

--------------------------------------------------------------------------------
-- Operations on 'Clause'
--------------------------------------------------------------------------------

-- | __Fig. 8. (p.12)__ create a new LEARNT clause and adds it to watcher lists
-- This is a strippped-down version of 'newClause' in Solver
{-# INLINABLE newLearntClause #-}
newLearntClause :: Solver -> Vec -> IO ()
newLearntClause s@Solver{..} ps = do
  good <- getBool ok
  when good $ do
    -- ps is a 'SizedVectorInt'; ps[0] is the number of active literals
    -- Since this solver must generate only healthy learnt clauses, we need not to run misc check in 'newClause'
    k <- getNth ps 0
    case k of
     1 -> do
       l <- getNth ps 1
       unsafeEnqueue s l NullClause
     _ -> do
       -- allocate clause:
       c <- newClauseFromVec True ps
       let vec = asVec c
       -- Pick a second literal to watch:
       let
         findMax :: Int -> Int -> Int -> IO Int
         findMax ((< k) -> False) j _ = return j
         findMax i j val = do
           v' <- lit2var <$> getNth vec i
           a <- getNth assigns v'
           b <- getNth level v'
           if (a /= lBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       swapBetween vec 1 =<< findMax 0 0 0 -- Let @max_i@ be the index of the literal with highest decision level
       -- Bump, enqueue, store clause:
       claBumpActivity s c -- newly learnt clauses should be considered active
       -- Add clause to all managers
       pushClause learnts c
       l <- getNth vec 0
       pushClause (getNthWatchers watches (negateLit l)) c
       l1 <- negateLit <$> getNth vec 1
       pushClause (getNthWatchers watches l1) c
       -- Since unsafeEnqueue updates the 1st literal's level, setLBD should be called after unsafeEnqueue
       setLBD s c
       -- update the solver state by @l@
       unsafeEnqueue s l c

-- | __Simplify.__ At the top-level, a constraint may be given the opportunity to
-- simplify its representation (returns @False@) or state that the constraint is
-- satisfied under the current assignment and can be removed (returns @True@).
-- A constraint must /not/ be simplifiable to produce unit information or to be
-- conflicting; in that case the propagation has not been correctly defined.
--
-- MIOS NOTE: the original doesn't update watchers; only checks its satisfiabiliy.
{-# INLINABLE simplify #-}
simplify :: Solver -> Clause -> IO Bool
simplify s c = do
  n <- sizeOfClause c
  let
    lvec = asVec c
    loop ::Int -> IO Bool
    loop ((< n) -> False) = return False
    loop i = do
      v <- valueLit s =<< getNth lvec i
      if v == 1 then return True else loop (i + 1)
  loop 0

--------------------------------------------------------------------------------
-- MIOS NOTE on Minor methods:
--
-- * no (meaningful) 'newVar' in mios
-- * 'assume' is defined in 'Solver'
-- * `cancelUntil` is defined in 'Solver'

--------------------------------------------------------------------------------
-- Major methods

-- | M114: __Fig. 10. (p.15)__
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
  dl <- decisionLevel s
  let
    litsVec = asVec litsLearnt
    trailVec = asVec trail
    loopOnClauseChain :: Clause -> Lit -> Int -> Int -> Int -> IO Int
    loopOnClauseChain c p ti bl pathC = do -- p : literal, ti = trail index, bl = backtrack level
      when (learnt c) $ do
        claBumpActivity s c
        -- update LBD like #Glucose4.0
        d <- getInt (lbd c)
        when (2 < d) $ do
          nblevels <- lbdOf s c
          when (nblevels + 1 < d) $ do -- improve the LBD
            when (d <= 30) $ setBool (protected c) True -- 30 is `lbLBDFrozenClause`
            -- seems to be interesting: keep it fro the next round
            setInt (lbd c) nblevels    -- Update it
      sc <- sizeOfClause c
      let
        lvec = asVec c
        loopOnLiterals :: Int -> Int -> Int -> IO (Int, Int)
        loopOnLiterals ((< sc) -> False) b pc = return (b, pc) -- b = btLevel, pc = pathC
        loopOnLiterals j b pc = do
          (q :: Lit) <- getNth lvec j
          let v = lit2var q
          sn <- getNth an'seen v
          l <- getNth level v
          if sn == 0 && 0 < l
            then do
                varBumpActivity s v
                setNth an'seen v 1
                if dl <= l      -- cancelUntil doesn't clear level of cancelled literals
                  then do
                      -- glucose heuristics
                      r <- getNthClause reason v
                      when (r /= NullClause && learnt r) $ pushToStack lastDL q
                      -- end of glucose heuristics
                      loopOnLiterals (j + 1) b (pc + 1)
                  else pushToStack litsLearnt q >> loopOnLiterals (j + 1) (max b l) pc
            else loopOnLiterals (j + 1) b pc
      (b', pathC') <- loopOnLiterals (if p == bottomLit then 0 else 1) bl pathC
      let
        -- select next clause to look at
        nextPickedUpLit :: Int -> IO Int
        nextPickedUpLit i = do
          x <- getNth an'seen . lit2var =<< getNth trailVec i
          if x == 0 then nextPickedUpLit $ i - 1 else return i
      ti' <- nextPickedUpLit ti
      nextP <- getNth trailVec ti'
      let nextV = lit2var nextP
      confl' <- getNthClause reason nextV
      setNth an'seen nextV 0
      if 1 < pathC'
        then loopOnClauseChain confl' nextP (ti' - 1) b' (pathC' - 1)
        else setNth litsVec 0 (negateLit nextP) >> return b'
  ti <- subtract 1 <$> sizeOfStack trail
  levelToReturn <- loopOnClauseChain confl bottomLit ti 0 0
  -- Simplify phase (implemented only @expensive_ccmin@ path)
  n <- sizeOfStack litsLearnt
  clearStack an'stack           -- analyze_stack.clear();
  clearStack an'toClear         -- out_learnt.copyTo(analyze_toclear);
  pushToStack an'toClear =<< getNth litsVec 0
  let
    merger :: Int -> Int -> IO Int
    merger ((< n) -> False) b = return b
    merger i b = do
      l <- getNth litsVec i
      pushToStack an'toClear l
      -- restrict the search depth (range) to 32
      merger (i + 1) . setBit b . (31 .&.) =<< getNth level (lit2var l)
  levels <- merger 1 0
  let
    loopOnLits :: Int -> Int -> IO ()
    loopOnLits ((< n) -> False) n' = shrinkStack litsLearnt $ n - n'
    loopOnLits i j = do
      l <- getNth litsVec i
      c1 <- (NullClause ==) <$> getNthClause reason (lit2var l)
      if c1
        then setNth litsVec j l >> loopOnLits (i + 1) (j + 1)
        else do
           c2 <- not <$> analyzeRemovable s l levels
           if c2
             then setNth litsVec j l >> loopOnLits (i + 1) (j + 1)
             else loopOnLits (i + 1) j
  loopOnLits 1 1                -- the first literal is specail
  -- glucose heuristics
  nld <- sizeOfStack lastDL
  -- lbd' <- computeLBD s $ asSizedVec litsLearnt -- this is not the right value
  let
    vec = asVec lastDL
    loopOnLastDL :: Int -> IO ()
    loopOnLastDL ((<= nld + 1) -> False) = return ()
    loopOnLastDL i = do
      {-
      v <- lit2var <$> getNth vec i
      d' <- getInt . lbd =<< getNthClause reason v
      when (lbd' < d') $ varBumpActivity s v
      -}
      varBumpActivity s . lit2var =<< getNth vec i
      loopOnLastDL $ i + 1
  loopOnLastDL 1                -- irrational value
  clearStack lastDL
  -- Clear seen
  k <- sizeOfStack an'toClear
  let
    vec' = asVec an'toClear
    cleaner :: Int -> IO ()
    cleaner ((< k) -> False) = return ()
    cleaner i = do
      v <- lit2var <$> getNth vec' i
      setNth an'seen v 0
      cleaner $ i + 1
  cleaner 0
  return levelToReturn

-- | #M114
-- Check if 'p' can be removed, 'abstract_levels' is used to abort early if the algorithm is
-- visiting literals at levels that cannot be removed later.
--
-- Implementation memo:
--
-- *  @an'toClear@ is initialized by @ps@ in 'analyze' (a copy of 'learnt').
--   This is used only in this function and 'analyze'.
--
{-# INLINEABLE analyzeRemovable #-}
analyzeRemovable :: Solver -> Lit -> Int -> IO Bool
analyzeRemovable Solver{..} p minLevel = do
  -- assert (reason[var(p)]!= NullCaulse);
  clearStack an'stack      -- analyze_stack.clear()
  pushToStack an'stack p   -- analyze_stack.push(p);
  top <- sizeOfStack an'toClear
  let
    loopOnStack :: IO Bool
    loopOnStack = do
      k <- sizeOfStack an'stack  -- int top = analyze_toclear.size();
      if 0 == k
        then return True
        else do -- assert(reason[var(analyze_stack.last())] != GClause_NULL);
            sl <- lastOfStack an'stack
            popFromStack an'stack             -- analyze_stack.pop();
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
                c1 <- (1 /=) <$> getNth an'seen v'
                if c1 && (0 /= l')   -- if (!analyze_seen[var(p)] && level[var(p)] != 0){
                  then do
                      c3 <- (NullClause /=) <$> getNthClause reason v'
                      if c3 && testBit minLevel (l' .&. 31) -- if (reason[var(p)] != GClause_NULL && ((1 << (level[var(p)] & 31)) & min_level) != 0){
                        then do
                            setNth an'seen v' 1        -- analyze_seen[var(p)] = 1;
                            pushToStack an'stack p'    -- analyze_stack.push(p);
                            pushToStack an'toClear p'  -- analyze_toclear.push(p);
                            loopOnLit $ i + 1
                        else do
                            -- loopOnLit (int j = top; j < analyze_toclear.size(); j++) analyze_seen[var(analyze_toclear[j])] = 0;
                            top' <- sizeOfStack an'toClear
                            let vec = asVec an'toClear
                            forM_ [top .. top' - 1] $ \j -> do x <- getNth vec j; setNth an'seen (lit2var x) 0
                            -- analyze_toclear.shrink(analyze_toclear.size() - top); note: shrink n == repeat n pop
                            shrinkStack an'toClear $ top' - top
                            return False
                  else loopOnLit $ i + 1
            loopOnLit 1
  loopOnStack

-- | #114
-- analyzeFinal : (confl : Clause *) (skip_first : boot) -> [void]
--
-- __Description:__
--   Specialized analysis proceduce to express the final conflict in terms of assumptions.
--   'root_level' is allowed to point beyond end of trace (useful if called after conflict while
--   making assumptions). If 'skip_first' is TRUE, the first literal of 'confl' is ignored (needed
--   if conflict arose before search even started).
--
analyzeFinal :: Solver -> Clause -> Bool -> IO ()
analyzeFinal Solver{..} confl skipFirst = do
  clearStack conflict
  rl <- getInt rootLevel
  unless (rl == 0) $ do
    n <- sizeOfClause confl
    let
      lvec = asVec confl
      loopOnConfl :: Int -> IO ()
      loopOnConfl ((< n) -> False) = return ()
      loopOnConfl i = do
        (x :: Var) <- lit2var <$> getNth lvec i
        lvl <- getNth level x
        when (0 < lvl) $ setNth an'seen x 1
        loopOnConfl $ i + 1
    loopOnConfl $ if skipFirst then 1 else 0
    tls <- sizeOfStack trailLim
    trs <- sizeOfStack trail
    tlz <- getNth (asVec trailLim) 0
    let
      trailVec = asVec trail
      loopOnTrail :: Int -> IO ()
      loopOnTrail ((tlz <) -> False) = return ()
      loopOnTrail i = do
        (l :: Lit) <- getNth trailVec i
        let (x :: Var) = lit2var l
        saw <- getNth an'seen x
        when (saw == 1) $ do
          (r :: Clause) <- getNthClause reason x
          if r == NullClause
            then pushToStack conflict (negateLit l)
            else do
                k <- sizeOfClause r
                let
                  cvec = asVec r
                  loopOnLits :: Int -> IO ()
                  loopOnLits ((< k) -> False) = return ()
                  loopOnLits j = do
                    (v :: Var) <- lit2var <$> getNth cvec j
                    lv <- getNth level v
                    when (0 < lv) $ setNth an'seen v 1
                    loopOnLits $ i + 1
                loopOnLits 1
        setNth an'seen x 0
        loopOnTrail $ i - 1
    loopOnTrail =<< if tls <= rl then return (trs - 1) else getNth (asVec trailLim) rl

--
-- 'enqueue' is defined in 'Solver' and functions in M114 use 'unsafeEnqueue'
--

-- | M114:
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
  -- myVal <- getNth stats (fromEnum NumOfBackjump)
  let
    myVal = 0
    bumpAllVar :: IO ()         -- not in use
    bumpAllVar = do
      let
        loop :: Int -> IO ()
        loop ((<= nVars) -> False) = return ()
        loop i = do
          c <- getNth pr'seen i
          when (c == myVal) $ varBumpActivity s i
          loop $ i + 1
      loop 1
    trailVec = asVec trail
    while :: Clause -> Bool -> IO Clause
    while confl False = {- bumpAllVar >> -} return confl
    while confl True = do
      (p :: Lit) <- getNth trailVec =<< getInt qHead
      modifyInt qHead (+ 1)
      let (ws :: ClauseManager) = getNthWatchers watches p
      end <- numberOfClauses ws
      cvec <- getClauseVector ws
--      rc <- getNthClause reason $ lit2var p
--      byGlue <- if (rc /= NullClause) && learnt rc then (== 2) <$> getInt (lbd rc) else return False
      let
        checkAllLiteralsIn :: Clause -> IO () -- not in use
        checkAllLiteralsIn c = do
          nc <- sizeOfClause c
          let
            vec = asVec c
            loop :: Int -> IO ()
            loop((< nc) -> False) = return ()
            loop i = do
              (v :: Var) <- lit2var <$> getNth vec i
              setNth pr'seen v myVal
              loop $ i + 1
          loop 0
        forClause :: Clause -> Int -> Int -> IO Clause
        forClause confl i@((< end) -> False) j = do
          shrinkClauseManager ws (i - j)
          while confl =<< ((<) <$> getInt qHead <*> sizeOfStack trail)
        forClause confl i j = do
          (c :: Clause) <- getNthClause cvec i
          -- checkAllLiteralsIn c
          let
            lits = asVec c
            falseLit = negateLit p
          -- Make sure the false literal is data[1]
          ((falseLit ==) <$> getNth lits 0) >>= (`when` swapBetween lits 0 1)
          -- if 0th watch is true, then clause is already satisfied.
          (first :: Lit) <- getNth lits 0
          val <- valueLit s first
          if val == lTrue
            then setNthClause cvec j c >> forClause confl (i + 1) (j + 1)
            else do
                -- Look for new watch
                cs <- sizeOfClause c
                let
                  forLit :: Int -> IO Clause
                  forLit ((< cs) -> False) = do
                    -- Did not find watch; clause is unit under assignment:
                    setNthClause cvec j c
                    result <- enqueue s first c
                    if not result
                      then do
                          ((== 0) <$> decisionLevel s) >>= (`when` setBool ok False)
                          setInt qHead =<< sizeOfStack trail
                          -- Copy the remaining watches:
                          let
                            copy i'@((< end) -> False) j' = forClause c i' j'
                            copy i' j' = (setNthClause cvec j' =<< getNthClause cvec i') >> copy (i' + 1) (j' + 1)
                          copy (i + 1) (j + 1)
                      else forClause confl (i + 1) (j + 1)
                  forLit k = do
                    (l :: Lit) <- getNth lits k
                    lv <- valueLit s l
                    if lv /= lFalse
                      then do
                          swapBetween lits 1 k
                          pushClause (getNthWatchers watches (negateLit l)) c
                          forClause confl (i + 1) j
                      else forLit $ k + 1
                forLit 2
      forClause confl 0 0
  while NullClause =<< ((<) <$> getInt qHead <*> sizeOfStack trail)

-- | #M22
-- reduceDB: () -> [void]
--
-- __Description:__
--   Remove half of the learnt clauses, minus the clauses locked by the current assigmnent. Locked
--   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
{-# INLINABLE reduceDB #-}
reduceDB :: Solver -> IO ()
reduceDB s@Solver{..} = do
  nL <- nLearnts s
  vec <- getClauseVector learnts
  let
    loop :: Int -> IO ()
    loop ((< nL) -> False) = return ()
    loop i = (removeWatch s =<< getNthClause vec i) >> loop (i + 1)
  k <- max (div nL 2) <$> setClauseKeys s learnts -- k is the number of clauses not to be purged
  sortOnActivity learnts
  loop $ k                      -- CAVEAT: `vec` is a zero-based vector
  shrinkClauseManager learnts (nL - k)

-- | sets valid key to all clauses in ClauseManager and returns number of privileged clauses.
-- this uses the same metrix as reduceDB_lt in glucose 4.0:
-- 1. binary clause
-- 2. smaller lbd
-- 3. larger activity defined in MiniSat
-- smaller value is better
{-# INLINABLE setClauseKeys #-}
setClauseKeys :: Solver -> ClauseManager -> IO Int
setClauseKeys s cm = do
  n <- numberOfClauses cm
  vec <- getClauseVector cm
  let
    updateNth :: Int -> Int -> IO Int
    updateNth ((< n) -> False) m = return m
    updateNth i m = do
      c <- getNthClause vec i
      k <- sizeOfClause c
      d <- getInt $ lbd c
      p <- getBool $ protected c
      when p $ setBool (protected c) False
      l <- locked s c
      case () of
        _ | k == 2 -> setDouble (sortKey c) (-4) >> updateNth (i + 1) (m + 1)
        _ | l      -> setDouble (sortKey c) (-3) >> updateNth (i + 1) (m + 1)
        _ | p      -> setDouble (sortKey c) (-2) >> updateNth (i + 1) (m + 1)
--      _ | d <= 2 -> setDouble (sortKey c) (-1) >> updateNth (i + 1) m
--        _ -> setDouble (sortKey c) (fromIntegral d) >> updateNth (i + 1) m
--        _ | p -> do
--          a <- getDouble (activity c)
--          let d' = div d 2
--          setDouble (sortKey c) (fromIntegral d' + 1 / (a + 1.1))
--          updateNth (i + 1) m
        _ -> do
          a <- getDouble (activity c)
          setDouble (sortKey c) (fromIntegral d + 1 / (a + 1.1))
          updateNth (i + 1) m
  updateNth 0 0

-- | (Good to Bad) Quick sort on a clause vector based on their activities
sortOnActivity :: ClauseManager -> IO ()
sortOnActivity cm = do
  n <- numberOfClauses cm
  vec <- getClauseVector cm
  let
    keyOf :: Int -> IO Double
    keyOf i = getDouble . sortKey =<< getNthClause vec i
    sortOnRange :: Int -> Int -> IO ()
    sortOnRange left right
      | left >= right = return ()
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
  good <- getBool ok
  if good
    then do
      p <- propagate s
      if p /= NullClause
        then setBool ok False >> return False
        else do
            -- Clear watcher lists:
            n <- sizeOfStack trail
            let
              vec = asVec trail
              loopOnLit ((< n) -> False) = return ()
              loopOnLit i = do
                l <- getNth vec i
                clearClauseManager . getNthWatchers watches $ l
                clearClauseManager . getNthWatchers watches $ negateLit l
                loopOnLit $ i + 1
            loopOnLit 0
            -- Remove satisfied clauses:
            let
              for :: Int -> IO Bool
              for ((< 2) -> False) = return True
              for t = do
                let ptr = if t == 0 then learnts else clauses
                vec' <- getClauseVector ptr
                n' <- numberOfClauses ptr
                let
                  loopOnVector :: Int -> Int -> IO Bool
                  loopOnVector ((< n') -> False) j = shrinkClauseManager ptr (n' - j) >> return True
                  loopOnVector i j = do
                        c <- getNthClause vec' i
                        l <- locked s c
                        r <- simplify s c
                        if not l && r
                          then removeWatch s c >> loopOnVector (i + 1) j
                          else setNthClause vec' j c >> loopOnVector (i + 1) (j + 1)
                loopOnVector 0 0
            for 0
    else return False

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
      d <- decisionLevel s
      if confl /= NullClause
        then do
            -- CONFLICT
            incrementStat s NumOfBackjump 1
            r <- getInt rootLevel
            if d == r
              then do
                  -- Contradiction found:
                  analyzeFinal s confl False
                  return LFalse
              else do
--                  u <- (== 0) . (flip mod 5000) <$> getNth stats (fromEnum NumOfBackjump)
--                  when u $ do
--                    d <- getDouble varDecay
--                    when (d < 0.95) $ modifyDouble varDecay (+ 0.01)
                  backtrackLevel <- analyze s confl -- 'analyze' resets litsLearnt by itself
                  (s `cancelUntil`) . max backtrackLevel =<< getInt rootLevel
                  newLearntClause s $ asSizedVec litsLearnt
                  k <- sizeOfStack litsLearnt
                  when (k == 1) $ do
                    (v :: Var) <- lit2var <$> getNth (asVec litsLearnt) 0
                    setNth level v 0
                  varDecayActivity s
                  claDecayActivity s
                  loop $ conflictC + 1
        else do                 -- NO CONFLICT
            -- Simplify the set of problem clauses:
            when (d == 0) . void $ simplifyDB s -- our simplifier cannot return @False@ here
            k1 <- numberOfClauses learnts
            k2 <- nAssigns s
            when (k1 - k2 >= nOfLearnts) $ reduceDB s -- Reduce the set of learnt clauses
            case () of
             _ | k2 == nVars -> do
                   -- Model found:
                   forM_ [0 .. nVars - 1] $ \i -> setNthBool model i . (lTrue ==) =<< getNth assigns (i + 1)
                   return LTrue
             _ | conflictC >= nOfConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< getInt rootLevel -- force a restart
                   incrementStat s NumOfRestart 1
                   return Bottom
             _ -> do
               -- New variable decision:
               v <- select s -- many have heuristic for polarity here
               -- << #phasesaving
               oldVal <- valueVar s v
               unsafeAssume s $ var2lit v (0 < oldVal) -- cannot return @False@
               -- >> #phasesaving
               loop conflictC
  good <- getBool ok
  if good then loop 0 else return LFalse

-- | __Fig. 16. (p.20)__
-- Main solve method.
--
-- __Pre-condition:__ If assumptions are used, 'simplifyDB' must be
-- called right before using this method. If not, a top-level conflict (resulting in a
-- non-usable internal state) cannot be distinguished from a conflict under assumptions.
solve :: (Foldable t) => Solver -> t Lit -> IO Bool
solve s@Solver{..} assumps = do
  -- PUSH INCREMENTAL ASSUMPTIONS:
  let
    injector :: Lit -> Bool -> IO Bool
    injector _ False = return False
    injector a True = do
      b <- assume s a
      if not b
        then do                 -- conflict analyze
            (confl :: Clause) <- getNthClause reason (lit2var a)
            analyzeFinal s confl True
            pushToStack conflict (negateLit a)
            cancelUntil s 0
            return False
        else do
            confl <- propagate s
            if confl /= NullClause
              then do
                  analyzeFinal s confl True
                  cancelUntil s 0
                  return False
              else return True
  good <- simplifyDB s
  x <- if good then foldrM injector True assumps else return False
  if not x
    then return False
    else do
        setInt rootLevel =<< decisionLevel s
        -- SOLVE:
        nc <- fromIntegral <$> nClauses s
        let
          while :: Double -> Double -> IO Bool
          while nOfConflicts nOfLearnts = do
            status <- search s (floor nOfConflicts) (floor nOfLearnts)
            if status == Bottom
              then while (1.5 * nOfConflicts) (400 + nOfLearnts)
              else cancelUntil s 0 >> return (status == LTrue)
        while 100 nc

{-# INLINABLE unsafeEnqueue #-}
unsafeEnqueue :: Solver -> Lit -> Clause -> IO ()
unsafeEnqueue s@Solver{..} p from = do
  let v = lit2var p
  setNth assigns v $! if positiveLit p then lTrue else lFalse
  setNth level v =<< decisionLevel s
  setNthClause reason v from     -- NOTE: @from@ might be NULL!
  pushToStack trail p

-- __Pre-condition:__ propagation queue is empty
{-# INLINE unsafeAssume #-}
unsafeAssume :: Solver -> Lit -> IO ()
unsafeAssume s@Solver{..} p = do
  pushToStack trailLim =<< sizeOfStack trail
  unsafeEnqueue s p NullClause

-- | for debug
fromAssigns :: Vec -> IO [Int]
fromAssigns as = zipWith f [1 .. ] . tail <$> asList as
  where
    f n x
      | x == lTrue = n
      | x == lFalse = negate n
      | otherwise = 0

-- | for debug
dumpAssignment :: String -> Vec -> IO String
dumpAssignment mes v = (mes ++) . show <$> fromAssigns v
