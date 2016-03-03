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
{-# LANGUAGE Trustworthy #-}

module SAT.Solver.Mios.Solver
       (
         -- * Solver
         Solver (..)
       , newSolver
       , setInternalState
         -- * public interface of 'Solver' (p.2)
       , addClause
       , simplifyDB
       , solve
         -- * misc accessors for Solver
       , nConstraints
       , nLearnts
       )
        where

import Control.Monad ((<=<), filterM, foldM, forM, forM_, unless, when)
import Data.Bits
import Data.Foldable (foldrM)
import qualified Data.IORef as IORef
import System.Random (mkStdGen, randomIO, setStdGen)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.ClauseManager
import SAT.Solver.Mios.WatcherLists

-- | __Fig. 2.(p.9)__ Internal State of the solver
data Solver = Solver
              {
                -- for public interface
               model         :: FixedVecBool       -- ^ If found, this vector has the model
                -- Contraint database
              , constrs       :: ClauseManager     -- ^ List of problem constraints.
              , learnts       :: ClauseManager     -- ^ List of learnt clauses.
              , claInc        :: DoubleSingleton   -- ^ Clause activity increment amount to bump with.
                -- Variable order
              , activities    :: FixedVecDouble    -- ^ Heuristic measurement of the activity of a variable; var-indexed
              , varInc        :: DoubleSingleton   -- ^ Variable activity increment amount to bump with.
              , order         :: VarHeap           -- ^ Keeps track of the dynamic variable order.
                -- Propagation
              , watches       :: WatcherLists      -- ^ For each literal 'p', a list of constraint wathing 'p'.
                                 -- A constraint will be inspected when 'p' becomes true.
--            , undos         :: FixedVecOf ClauseManager -- ^ For each variable 'x', a list of constraints that need
                                 -- to update when 'x' becomes unbound by backtracking.
              , propQ         :: Queue             -- ^ Propagation queue.
                -- Assignments
              , assigns       :: Vec               -- ^ The current assignments indexed on variables; var-indexed
              , trail         :: Stack             -- ^ List of assignments in chronological order; var-indexed
              , trailLim      :: Stack             -- ^ Separator indices for different decision levels in 'trail'.
              , decisionLevel :: IntSingleton
              , reason        :: ClauseVector      -- ^ For each variable, the constraint that implied its value; var-indexed
              , level         :: Vec               -- ^ For each variable, the decision level it was assigned; var-indexed
              , rootLevel     :: IntSingleton      -- ^ Separates incremental and search assumptions.
              , an_seen       :: Vec               -- ^ scratch var for 'analyze'; var-indexed
              , an_toClear    :: Stack             -- ^ ditto
              , an_stack      :: Stack             -- ^ ditto
              , nVars         :: Int               -- ^ number of variables
                -- working memory
              , litsLearnt    :: Stack             -- ^ used to create a learnt clause
                -- Configuration
              , config        :: MiosConfiguration -- ^ search paramerters
              }

-- | returns the number of current assigments
{-# INLINE nAssigns #-}
nAssigns :: Solver -> IO Int
nAssigns = sizeOfStack . trail

-- | returns the number of constraints (clauses)
{-# INLINE nConstraints #-}
nConstraints  :: Solver -> IO Int
nConstraints = numberOfClauses . constrs

-- | returns the number of learnt clauses
{-# INLINE nLearnts #-}
nLearnts :: Solver -> IO Int
nLearnts = numberOfClauses . learnts

-- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Var'
{-# INLINE valueVar #-}
valueVar :: Solver -> Var -> IO Int
valueVar !s !x = getNth (assigns s) x

-- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Lit'
{-# INLINE valueLit #-}
valueLit :: Solver -> Lit -> IO LBool
valueLit !Solver{..} !p = if positiveLit p then getNth assigns (lit2var p) else negate <$> getNth assigns (lit2var p)

-- | returns an everything-is-initialized solver from the argument
setInternalState :: Solver -> CNFDescription -> IO Solver
setInternalState s (CNFDescription nv nc _) = do
  setStdGen $ mkStdGen 91648253
  m <- newVecBool nv False
  m1 <- newClauseManager nc
  m2 <- newClauseManager nc
  ac <- newVecDouble (nv + 1) 0.0
  w <- newWatcherLists nv (div (2 * nc) nv)
--  u <- newVec 0 -- nv
  -- forM_ [0 .. nv - 1] $ \i -> setVecAt u i =<< newVec 0
  a <- newVecWith (nv + 1) lBottom
  t <- newStack (2 * nv)
  t' <- newStack nv
  r <- newClauseVector (nv + 1)
  l <- newVecWith (nv + 1) (-1)
  o <- newVarHeap nv
  q <- newQueue nv
  n1 <- newVec (nv + 1)
  n2 <- newStack nv
  n3 <- newStack nv
  ll <- newStack nv
  let s' = s
           {
             model = m
           , activities = ac
           , constrs = m1
           , learnts = m2
           , watches = w
--           , undos = u
           , assigns = a
           , trail = t
           , trailLim = t'
           , reason = r
           , level = l
           , order = o
           , propQ = q
           , an_seen = n1
           , an_toClear = n2
           , an_stack = n3
           , nVars  = nv
           , litsLearnt = ll
           }
  return s'

-- | constructor
newSolver :: MiosConfiguration -> IO Solver
newSolver conf = Solver
            <$> newVecBool 0 False  -- model
            <*> newClauseManager 1  -- constrs
            <*> newClauseManager 1  -- learnts
            <*> newDouble 1.0       -- claInc
            <*> newVecDouble 0 0    -- activities
            <*> newDouble 1.0       -- varInc
            <*> newVarHeap 0        -- order
            <*> newWatcherLists 1 1 -- watches
--            <*> newVec 0          -- undos
            <*> newQueue 0          -- porqQ
            <*> newVec 0            -- assigns
            <*> newStack 0          -- trail
            <*> newStack 0          -- trailLim
            <*> newInt 0            -- decisionLevel
            <*> newClauseVector 0   -- reason
            <*> newVec 0            -- level
            <*> newInt 0            -- rootLevel
            <*> newVec 0            -- an_seen
            <*> newStack 0          -- an_toClear
            <*> newStack 0          -- an_stack
            <*> return 0            -- nVars
            <*> newStack 0          -- litsLearnt
            <*> return conf         -- config

-- | public interface of 'Solver' (p.2)
--
-- returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses.
{-# INLINABLE addClause #-}
addClause :: Solver -> Vec -> IO Bool
addClause s@Solver{..} vecLits = do
  result <- clauseNew s vecLits False
  case result of
   (False, _) -> return False   -- Conflict occured
   (True, c)  -> do
     unless (c == NullClause) $ pushClause constrs c
     return True                -- No conflict

-- functions on "Solver"

-- | __Fig. 9 (p.14)__
-- Propagates all enqueued facts. If a conflict arises, the /conflicting/
-- clause is returned, otherwise @NullClause@ (instead of Null).
--
-- `propagate` is invoked by `search`,`simpleDB` and `solve`
{-# INLINABLE propagate #-}
propagate :: Solver -> IO Clause
propagate s@Solver{..} = do
  let
    loopOnQueue :: IO Clause
    loopOnQueue = do
      k <- sizeOfQueue propQ
      if k == 0
        then return NullClause        -- No conflict
        else do
            p <- dequeue propQ
            let w = getNthWatchers watches p
            vec <- getClauseVector w
            let
              loopOnWatcher :: Int -> Int-> IO Clause
              loopOnWatcher i n
                | i == n = loopOnQueue
                | otherwise = do
                    c <- getNthClause vec i
                    x <- propagateLit c s p w -- c will be inserted into apropriate watchers in this function
                    case () of
                      _ | x == lTrue  {- still in -} -> loopOnWatcher (i + 1) n
                      _ | x == lFalse {- conflict -} -> clearQueue propQ >> return c
                      _               {- it moved -} -> removeNthClause w i >> loopOnWatcher i (n - 1)
{-
                if not x -- Constraint is conflicting;return constraint
                  then clearQueue propQ >> shrinkClauseManager w (max 0 (i - 1)) >> return c
                  else loopOnWatcher $ i - 1
-}
            loopOnWatcher 0 =<< numberOfClauses w
  loopOnQueue

-- | __Fig. 9 (p.14)__
-- Puts a new fact on the propagation queue, as well as immediately updating the variable's value
-- in the assignment vector. If a conflict arises, @False@ is returned and the propagation queue is
-- cleared. The parameter 'from' contains a reference to the constraint from which 'p' was
-- propagated (defaults to @Nothing@ if omitted).
{-# INLINABLE enqueue #-}
enqueue :: Solver -> Lit -> Clause -> IO Bool
enqueue s@Solver{..} p from = do
  let signumP = if positiveLit p then lTrue else lFalse
  let v = lit2var p
  val <- valueVar s v
  if val /= lBottom
    then do -- Existing consistent assignment -- don't enqueue
        return $ signum val == signumP
    else do
        -- New fact, store it
        setNth assigns v $! signumP
        d <- getInt decisionLevel
        setNth level v d
        setNthClause reason v from     -- NOTE: @from@ might be NULL!
        pushToStack trail p
        insertQueue propQ p
        return True

-- | __Fig. 10. (p.15)__
-- #M114 Analyze a cnflict and produce a reason clause.
--
-- __Pre-conditions:__ (1) 'outLearnt' is
-- assumed to be cleared. (2) Current decision level must be greater than root level.
--
-- __Post-conditions:__ (1) 'outLearnt[0]' is the asserting literal at level 'outbtLevel'.
--
-- __Effect:__ Will undo part of the trail, but not beyond last decision level.
--
-- (p.13) In the code for 'analyze', we make use of the fact that a breadth-first traversal
-- can be archieved by inspecting the trail backwords. Especially, the variables of the
-- reason set of /p/ is always before /p/ in the trail. Furthermore, in the algorithm we
-- initialize /p/ to 'bottomLit', which will make 'calcReason' return the reason for the conflict.
--
-- `analyze` is invoked from `search`
-- {-# INLINEABLE analyze #-}
analyze :: Solver -> Clause -> IO Int
analyze s@Solver{..} confl = do
  -- litvec
  clearStack litsLearnt
  pushToStack litsLearnt 0 -- reserve the first place for the unassigned literal
  setAll an_seen 0   -- FIXME: it should be done in a valid place; not here.
  ti <- subtract 1 <$> sizeOfStack trail
  dl <- getInt decisionLevel
  let
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
      confl' <- getNthClause reason (lit2var nextP)
      setNth an_seen (lit2var nextP) 0
      if 1 < pathC'
        then loopOnClauseChain confl' nextP (ti' - 1) b' (pathC' - 1)
        else setNth (asVec litsLearnt) 0 (negateLit nextP) >> return b'
  result <- loopOnClauseChain confl bottomLit ti 0 0
  -- Simplify phase
  let litsVec = asVec litsLearnt
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
      setBit i . mod 60 <$> getNth level (lit2var l)
  levels <-  merger 0 0
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

-- | M22: Check if 'p' can be removed, 'min_level' is used to abort early if visiting literals at a level that
-- cannot be removed.
-- Implementation memo:
--
-- * @an_toClear@ is initialized by @ps@ in 'analyze' (a copy of 'learnt').
--   This is used only in this function and `analyze'.
--
litRedundant :: Solver -> Lit -> Int -> IO Bool
litRedundant Solver{..} p minLevel = do
  -- assert (reason[var(p)]!= NullCaulse);
  clearStack an_stack      -- analyze_stack.clear()
  pushToStack an_stack p   -- analyze_stack.push(p);
  top <- sizeOfStack an_toClear
  let
    getRoot :: Lit -> IO Clause
    getRoot l = do
      (r :: Clause) <- getNthClause reason (lit2var l) -- GClause r = reason[var(analyze_stack.last())]
      let cvec = asVec r
      if r == NullClause
        then return NullClause
        else do
            nl <- sizeOfClause r
            if nl == 2
              then do
                  l1 <- getNth cvec 0
                  l2 <- getNth cvec 1
                  tmp <- getRoot $ if l1 /= l then l1 else l2
                  return $ if tmp == NullClause then r else tmp
              else return r
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
              for :: Int -> IO Bool -- for (int i = 1; i < c.size(); i++){
              for ((< nl) -> False) = loopOnStack
              for i = do
                p' <- getNth cvec i              -- valid range is [0 .. nl - 1]
                let v' = lit2var p'
                c1 <- (1 /=) <$> getNth an_seen v'
                c2 <- (0 <) <$> getNth level v'
                if c1 && c2   -- if (!analyze_seen[var(p)] && level[var(p)] != 0){
                  then do
                      c3 <- (NullClause /=) <$> getNthClause reason v'
                      c4 <- testBit minLevel . flip mod 60 <$> getNth level v'
                      if c3 && c4 -- if (reason[var(p)] != GClause_NULL && ((1 << (level[var(p)] & 31)) & min_level) != 0){
                        then do
                            setNth an_seen v' 1        -- analyze_seen[var(p)] = 1;
                            pushToStack an_stack p'    -- analyze_stack.push(p);
                            pushToStack an_toClear p'  -- analyze_toclear.push(p);
                            for $ i + 1
                        else do
                            -- for (int j = top; j < analyze_toclear.size(); j++) analyze_seen[var(analyze_toclear[j])] = 0;
                            top' <- sizeOfStack an_toClear
                            let vec = asVec an_toClear
                            forM_ [top .. top' - 1] $ \j -> do x <- getNth vec j; setNth an_seen (lit2var x) 0
                            -- analyze_toclear.shrink(analyze_toclear.size() - top); note: shrink n == repeat n pop
                            shrinkStack an_toClear $ top' - top
                            return False
                  else for (i + 1)
            for 1
  loopOnStack

-- | __Fig. 11. (p.15)__
-- Record a clause and drive backtracking.
--
-- __Pre-Condition:__ "clause[0]" must contain
-- the asserting literal. In particular, 'clause[]' must not be empty.
{-# INLINE record #-}
record :: Solver -> Vec -> IO ()
record s@Solver{..} v = do
  c <- snd <$> clauseNew s v True -- will be set to created clause, or NULL if @clause[]@ is unit
  l <- getNth v 1
  enqueue s l c
  unless (c == NullClause) $ pushClause learnts c

-- | __Fig. 12 (p.17)__
-- returns @False@ if immediate conflict.
--
-- __Pre-condition:__ propagation queue is empty
{-# INLINE assume #-}
assume :: Solver -> Lit -> IO Bool
assume s@Solver{..} p = do
  pushToStack trailLim =<< sizeOfStack trail
  modifyInt decisionLevel (+ 1)
  enqueue s p NullClause

-- | M22 __Fig. 12 (p.17)__
-- cancels several levels of assumptions.
{-# INLINABLE cancelUntil #-}
cancelUntil :: Solver -> Int -> IO ()
cancelUntil s@Solver{..} lvl = do
  dl <- getInt decisionLevel
  when (lvl < dl) $ do
    let tr = asVec trail
    let tl = asVec trailLim
    lim <- getNth tl lvl
    ts <- sizeOfStack trail
    ls <- sizeOfStack trailLim
    let
      loopOnLevel :: Int -> IO ()
      loopOnLevel ((lim <=) -> False) = return ()
      loopOnLevel c = do
        x <- lit2var <$> getNth tr c
        setNth assigns x lBottom
        -- FIXME: #polarity https://github.com/shnarazk/minisat/blob/master/core/Solver.cc#L212
        undo s x
        -- insertHeap s x              -- insertVerOrder
        loopOnLevel $ c - 1
    loopOnLevel $ ts - 1
    shrinkStack trail (ts - lim)
    shrinkStack trailLim (ls - lvl)
    setInt decisionLevel lvl

-- | __Fig. 13. (p.18)__
-- Assumes and propagates until a conflict is found, from which a conflict clause
-- is learnt and backtracking until search can continue.
--
-- __Pre-condition:__
-- @root_level == decisionLevel@
{-# INLINABLE search #-}
search :: Solver -> Int -> Int -> IO LBool
search s@Solver{..} nOfConflicts nOfLearnts = do
  -- clear model
  let
    loop :: Int -> IO LBool
    loop conflictC = do
      !confl <- propagate s
      -- putStrLn $ "propagate done: " ++ show (confl /= NullClause)
      d <- getInt decisionLevel
      if confl /= NullClause
        then do
            -- CONFLICT
            -- putStrLn . ("conf: " ++) =<< dump "" confl
            r <- getInt rootLevel
            if d == r
              then return lFalse
              else do
                  backtrackLevel <- analyze s confl -- 'analyze' resets litsLearnt by itself
                  (s `cancelUntil`) . max backtrackLevel =<< getInt rootLevel
                  -- putStrLn =<< dump "BACKTRACK after search.analyze :: trail: " trail
                  record s =<< isoVec litsLearnt
                  decayActivities s
                  loop $ conflictC + 1
        else do                 -- NO CONFLICT
            -- Simplify the set of problem clauses:
            when (d == 0) $ simplifyDB s >> return () -- our simplifier cannot return @False@ here
            k1 <- numberOfClauses learnts
            k2 <- nAssigns s
            when (k1 - k2 >= nOfLearnts) $ do
--              n1 <- nLearnts s
              reduceDB s -- Reduce the set of learnt clauses
              {-
              n2 <- nLearnts s
              n3 <- sizeOfStack trail
              dl <- getInt decisionLevel
              case () of
                _ | n2 <= n3 -dl -> putStrLn "purge all"
                _ | n1 /= 0 && n1 == n2 -> return ()
                _ -> print (n1, n2, n3, fromIntegral n2 / fromIntegral n1)
              -}
            case () of
             _ | k2 == nVars -> do
                   -- Model found:
                   -- (model `growTo`) nv
                   -- nv <- nVars s
                   -- forM_ [1 .. nv] $ \i -> setAt model i =<< (lTrue ==) <$> assigns .! i
                   forM_ [0 .. nVars - 1] $ \i -> setNthBool model i . (lTrue ==) =<< getNth assigns (i + 1)
                   -- putStrLn =<< dump "activities:" activities
                   return lTrue
             _ | conflictC >= nOfConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< getInt rootLevel -- force a restart
                   return lBottom
             _ -> do
               -- New variable decision:
               v <- select s -- many have heuristic for polarity here
               -- putStrLn $ "search determines next decision var: " ++ show v
               -- << #phasesaving
               oldVal <- valueVar s v
               assume s $ var2lit v (0 < oldVal) -- cannot return @False@
               -- >> #phasesaving
               loop conflictC
  loop 0

-- | __Fig. 14 (p.19)__ Bumping of clause activity
{-# INLINE varBumpActivity #-}
varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity s@Solver{..} !x = do
  !a <- (+) <$> getNthDouble x activities <*> getDouble varInc
  if 1e100 < a
    then varRescaleActivity s
    else setNthDouble x activities a
  update s x

-- | __Fig. 14 (p.19)__
{-# INLINE varDecayActivity #-}
varDecayActivity :: Solver -> IO ()
varDecayActivity Solver{..} = modifyDouble varInc (/ variableDecayRate config)

-- | __Fig. 14 (p.19)__
{-# INLINE varRescaleActivity #-}
varRescaleActivity :: Solver -> IO ()
varRescaleActivity Solver{..} = do
  forM_ [1 .. nVars] $ \i -> modifyNthDouble i activities (* 1e-100)
  modifyDouble varInc (* 1e-100)

-- | __Fig. 14 (p.19)__
{-# INLINE claBumpActivity #-}
claBumpActivity :: Solver -> Clause -> IO ()
claBumpActivity s@Solver{..} Clause{..} = do
  a <- (+) <$> getDouble activity <*> getDouble claInc
  if 1e100 < a
    then claRescaleActivity s
    else setDouble activity $! a

-- | __Fig. 14 (p.19)__
{-# INLINE claDecayActivity #-}
claDecayActivity :: Solver -> IO ()
claDecayActivity Solver{..} = modifyDouble claInc (/ clauseDecayRate config)

-- | __Fig. 14 (p.19)__
{-# INLINE claRescaleActivity #-}
claRescaleActivity :: Solver -> IO ()
claRescaleActivity Solver{..} = do
  vec <- getClauseVector learnts
  n <- numberOfClauses learnts
  let
    loopOnVector :: Int -> IO ()
    loopOnVector ((< n) -> False) = return ()
    loopOnVector i = do
      c <- getNthClause vec i
      modifyDouble (activity c) (* 1e-100)
      loopOnVector $ i + 1
  loopOnVector 0
  modifyDouble claInc (* 1e-100)

-- | __Fig. 14 (p.19)__
{-# INLINE decayActivities #-}
decayActivities :: Solver -> IO ()
decayActivities s = varDecayActivity s >> claDecayActivity s

-- | __Fig. 15 (p.20)__
-- Remove half of the learnt clauses minus some locked clause. A locked clause
-- is a clause that is reason to a current assignment. Clauses below a certain
-- lower bound activity are also be removed.
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
{-
  -- This code causes core dumps sadly.
  let
    compareActivity NullClause NullClause = EQ
    compareActivity NullClause _ = GT
    compareActivity _ NullClause = LT
    compareActivity c1 c2 = unsafePerformIO $ reverseCompareActivityReally c1 c2
      where
        reverseCompareActivityReally x y = compare <$> getDouble (activity y) <*> getDouble (activity x)
  putStr "sorting..."
  VA.sortBy compareActivity vec
  putStr "done..."
-}
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
          --let check m i = unless (0 <= i && i < n) $ error (m ++ " out of index:" ++ (show (i, (left, right), n)))
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

-- | __Fig. 15. (p.20)__
-- Top-level simplify of constraint database. Will remove any satisfied constraint
-- and simplify remaining constraints under current (partial) assignment. If a
-- top-level conflict is found, @False@ is returned.
--
-- __Pre-condition:__ Decision
-- level must be zero.
--
-- __Post-condition:__ Propagation queue is empty.
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
    for [] = return True
    for (a : rest) = do
      !b <- assume s a
      if not b
        then cancelUntil s 0 >> return False
        else do
            c <- propagate s
            if c /= NullClause
              then cancelUntil s 0 >> return False
              else for rest
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
  -- !x <- for =<< asList assumps
  if not x
    then return False
    else do
        setInt rootLevel =<< getInt decisionLevel
        -- SOLVE:
        let
          while :: LBool -> Double -> Double -> IO Bool
          while status@((lBottom ==) -> False) _ _ = do
            cancelUntil s 0
            return $ status == lTrue
          while _ nOfConflicts nOfLearnts = do
            status <- search s (floor nOfConflicts) (floor nOfLearnts)
            while status (1.5 * nOfConflicts) (1.1 * nOfLearnts)
        while lBottom 100 (nc / 3.0)

---- constraint interface

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
      case () of
       _ | v == lTrue   -> return True
       _ | v == lBottom -> do
             when (i /= j) $ setNth lvec j l      -- false literals are not copied (only occur for i >= 2)
             loop (i+1) (j+1)
       _ -> loop (i+1) j
  loop 0 0

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
propagateLit :: Clause -> Solver -> Lit -> ClauseManager -> IO LBool
propagateLit !c@Clause{..} !s@Solver{..} !p !m = do
  -- Make sure the false literal is lits[1] = 2nd literal = 2nd watcher:
  !l' <- negateLit <$> getNth lits 1
  when (l' == p) $ do
    -- swap lits[0] and lits[1]
    swapBetween lits 1 2
  -- If 0th watch is True, then clause is already satisfied.
  !l1 <- getNth lits 1
  !val <- valueLit s l1
  if val == lTrue
    then return lTrue           -- this means the clause is satisfied, so we must keep it in the original watcher list
    else do
        -- Look for a new literal to watch:
        !n <- sizeOfClause c
        let
          loopOnLits :: Int -> IO LBool
          loopOnLits ((<= n) -> False) = do
            -- Clause is unit under assignment:
            -- pushClause m c
            noconf <- enqueue s l1 c
            if noconf
              then return lTrue  -- unit caluse should be in the original watcher list
              else return lFalse -- A conflict occures
          loopOnLits i = do
            !(l :: Int) <- getNth lits i
            !val <- valueLit s l
            if val /= lFalse    -- l is unassigned or satisfied already
              then do
                  swapBetween lits 2 i -- setNth 2 lits l >> setNth i lits np
                  -- putStrLn "## from propagateLit"
                  -- @removeClause m c@ will be done by propagate
                  pushClause (getNthWatchers watches (negateLit l)) c -- insert clause into watcher list
                  return lBottom -- this means the clause is moved to other watcher list
              else loopOnLits $ i + 1
        loopOnLits 3

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
{-# INLINABLE clauseNew #-}
clauseNew :: Solver -> Vec -> Bool -> IO (Bool, Clause)
clauseNew s@Solver{..} ps learnt = do
  -- now ps[0] is the number of living literals
  exit <- do
    let
      handle :: Int -> Int -> Int -> IO Bool
      handle j l n      -- removes duplicates, but returns @True@ if this clause is satisfied
        | j > n = return False
        | otherwise = do
            y <- getNth ps j
            case () of
             _ | y == l -> do             -- finds a duplicate
                   swapBetween ps j n
                   modifyNth ps (subtract 1) 0
                   handle j l (n - 1)
             _ | - y == l -> setNth ps 0 0 >> return True -- p and negateLit p occurs in ps
             _ -> handle (j + 1) l n
      loopForLearnt :: Int -> IO Bool
      loopForLearnt i = do
        n <- getNth ps 0
        if n < i
          then return False
          else do
              l <- getNth ps i
              sat <- handle (i + 1) l n
              if sat
                then return True
                else loopForLearnt $ i + 1
      loop :: Int -> IO Bool
      loop i = do
        n <- getNth ps 0
        if n < i
          then return False
          else do
              l <- getNth ps i     -- check the i-th literal's satisfiability
              sat <- valueLit s l                                      -- any literal in ps is true
              case () of
               _ | sat == lTrue -> setNth ps 0 0 >> return True
               _ | sat == lFalse -> do
                 swapBetween ps i n
                 modifyNth ps (subtract 1) 0
                 loop i
               _ -> do
                 sat' <- handle (i + 1) l n
                 if sat'
                   then return True
                   else loop $ i + 1
    if learnt then loopForLearnt 1 else loop 1
  k <- getNth ps 0
  case k of
   0 -> return (exit, NullClause)
   1 -> do
     l <- getNth ps 1
     (, NullClause) <$> enqueue s l NullClause
   _ -> do
     -- allocate clause:
     c <- newClauseFromVec learnt ps
     when learnt $ do
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
     return (True, c)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
{-# INLINE locked #-}
locked :: Clause -> Solver -> IO Bool
locked !c@Clause{..} !Solver{..} =  (c ==) <$> (getNthClause reason . lit2var =<< getNth lits 1)

-- | For small-sized problems, heap may not be a good choice.
useHeap :: Int
useHeap = 100 -- 0000
-- | For small-sized problems, randomess may lead to worse results.
useRand :: Int
useRand = 100

-- | Interfate to select a decision var based on variable activity.
instance VarOrder Solver where
  -- | __Fig. 6. (p.10)__
  -- Creates a new SAT variable in the solver.
  newVar _ = return 0
    -- i <- nVars s
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- push undos =<< newVec        -- push'
    -- push reason NullClause       -- push'
    -- push assigns lBottom
    -- push level (-1)
    -- push activities (0.0 :: Double)
    -- newVar order
    -- growQueueSized (i + 1) propQ
    -- return i
  {-# SPECIALIZE INLINE update :: Solver -> Var -> IO () #-}
  update s v = when (useHeap < nVars s) $ increase s v
  {-# SPECIALIZE INLINE undo :: Solver -> Var -> IO () #-}
  undo s v = when (useHeap < nVars s) $ inHeap s v >>= (`unless` insertHeap s v)
  {-# SPECIALIZE INLINE select :: Solver -> IO Var #-}
  select s = do
    let
      nv = nVars s
      asg = assigns s
      -- | returns the most active var (heap-based implementation)
      loop :: IO Var
      loop = do
        n <- numElementsInHeap s
        if n == 0
          then return 0
          else do
              v <- getHeapRoot s
              val <- getNth asg v
              if val == lBottom then return v else loop
      -- | O(n) implementation on vector: loop2 1 0 (-1)
      loop2 :: Int -> Int -> Double -> IO Var
      loop2 ((<= nv) -> False) j _ = return j
      loop2 i j best = do
        x <- getNth asg i
        if x == lBottom
          then do
              actv <- getNthDouble i $ activities s
              if best < actv
                then loop2 (i + 1) i actv
                else loop2 (i + 1) j best
          else loop2 (i + 1) j best
    -- the threshold used in MiniSat 1.14 is 0.02, namely 20/1000
    -- But it is 0 in MiniSat 2.20
    let rd = randomDecisionRate (config s)
    if 0 < rd
      then do
          !r <- flip mod 1001 <$> randomIO :: IO Int
          if r < rd
            then do
                !i <- (+ 1) . flip mod nv <$> randomIO
                x <- getNth asg i
                if x == lBottom then return i else if useHeap < nv then loop else loop2 1 0 (-1)
            else if useHeap < nv then loop else loop2 1 0 (-1)
      else if useHeap < nv then loop else loop2 1 0 (-1)

-------------------------------------------------------------------------------- VarHeap

-- | 'VarHeap' is a heap tree built from two 'Vec'
-- This implementation is identical wtih that in Minisat-1.14
-- Note: the zero-th element of 'heap' is used for holding the number of elements
-- Note: VarHeap itself is not a 'VarOrder', because it requires a pointer to solver
data VarHeap = VarHeap
                {
                  heap :: Vec -- order to var
                , idxs :: Vec -- var to order (index)
                }

newVarHeap :: Int -> IO VarHeap
newVarHeap n = VarHeap <$> newSizedVecIntFromList lst <*> newSizedVecIntFromList lst
  where
    lst = [1 .. n]

{-# INLINE numElementsInHeap #-}
numElementsInHeap :: Solver -> IO Int
numElementsInHeap (order -> heap -> h) = getNth h 0

{-# INLINE inHeap #-}
inHeap :: Solver -> Var -> IO Bool
inHeap (order -> idxs -> at) n = (/= 0) <$> getNth at n

{-# INLINE increase #-}
increase :: Solver -> Int -> IO ()
increase s@(order -> idxs -> at) n = inHeap s n >>= (`when` (percolateUp s =<< getNth at n))

{-# INLINABLE percolateUp #-}
percolateUp :: Solver -> Int -> IO ()
percolateUp Solver{..} start = do
  let VarHeap to at = order
  v <- getNth to start
  ac <- getNthDouble v activities
  let
    loop :: Int -> IO ()
    loop i = do
      let iP = div i 2          -- parent
      if iP == 0
        then setNth to i v >> setNth at v i >> return () -- end
        else do
            v' <- getNth to iP
            acP <- getNthDouble v' activities
            if ac > acP
              then setNth to i v' >> setNth at v' i >> loop iP -- loop
              else setNth to i v >> setNth at v i >> return () -- end
  loop start

{-# INLINABLE percolateDown #-}
percolateDown :: Solver -> Int -> IO ()
percolateDown Solver{..} start = do
  let (VarHeap to at) = order
  n <- getNth to 0
  v <- getNth to start
  ac <- getNthDouble v activities
  let
    loop :: Int -> IO ()
    loop i = do
      let iL = 2 * i            -- left
      if iL <= n
        then do
            let iR = iL + 1     -- right
            l <- getNth to iL
            r <- getNth to iR
            acL <- getNthDouble l activities
            acR <- getNthDouble r activities
            let (ci, child, ac') = if iR <= n && acL < acR then (iR, r, acR) else (iL, l, acL)
            if ac' > ac
              then setNth to i child >> setNth at child i >> loop ci
              else setNth to i v >> setNth at v i >> return () -- end
        else setNth to i v >> setNth at v i >> return ()       -- end
  loop start

{-# INLINE insertHeap #-}
insertHeap :: Solver -> Var -> IO ()
insertHeap s@(order -> VarHeap to at) v = do
  n <- (1 +) <$> getNth to 0
  setNth at v n
  setNth to n v
  setNth to 0 n
  percolateUp s n

-- | renamed from 'getmin'
{-# INLINE getHeapRoot #-}
getHeapRoot :: Solver -> IO Int
getHeapRoot s@(order -> VarHeap to at) = do
  r <- getNth to 1
  l <- getNth to =<< getNth to 0 -- the last element's value
  setNth to 1 l
  setNth at l 1
  setNth at r 0
  modifyNth to (subtract 1) 0 -- pop
  n <- getNth to 0
  when (1 < n) $ percolateDown s 1
  return r
