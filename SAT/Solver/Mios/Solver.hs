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
       , nVars
       , nConstraints
       , nLearnts
       )
        where

import Control.Monad ((<=<), filterM, forM, forM_, unless, when)
import Data.List (nub)
import Data.IORef
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Implementation.FixedVecInt (FixedVecInt, getNthInt, modifyNthInt, newSizedVecIntFromList, setNthInt, sizeOfVecInt, swapIntsBetween)
import SAT.Solver.Mios.Implementation.FixedVecDouble (FixedVecDouble, getNthDouble, modifyNthDouble, newVecDouble, setNthDouble)
import SAT.Solver.Mios.Implementation.FixedVecOf (FixedVecOf)
import SAT.Solver.Mios.Implementation.ListOf (ListOf(..), newList, pushToList)
import SAT.Solver.Mios.Implementation.ListOfInt (ListOfInt, lastOfListOfInt, newListOfInt, popFromListOfInt, pushToListOfInt, sizeOfListOfInt)
import SAT.Solver.Mios.Implementation.QueueOfBoundedInt (QueueOfBoundedInt, clearQueue, dequeue, insertQueue, newQueue, sizeOfQueue)
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.ClauseList
import SAT.Solver.Mios.WatchList

-- | __Fig. 2.(p.9)__ Internal State of the solver
data Solver = Solver
              {
                -- for public interface
                model      :: ListOf Bool       -- ^ If found, this vector has the model
                -- Contraint databale
              , constrs    :: ClauseLink        -- ^ List of problem constraints.
              , learnts    :: ClauseLink        -- ^ List of learnt clauses.
              , claInc     :: IORef Double      -- ^ Clause activity increment amount to bump with.
              , claDecay   :: IORef Double      -- ^ Decay factor for clause activity.
                -- Variable order
              , activities :: FixedVecDouble    -- ^ Heuristic measurement of the activity of a variable.
              , varInc     :: IORef Double      -- ^ Variable activity increment amount to bump with.
              , varDecay   :: IORef Double      -- ^ Decay factor for variable activity.
              , order      :: VarOrderStatic    -- ^ Keeps track of the dynamic variable order.
                -- Propagation
              , watches    :: WatcherList       -- ^ For each literal 'p', a list of constraint wathing 'p'.
                             -- A constraint will be inspected when 'p' becomes true.
              , undos      :: FixedVecOf VecOfClause -- ^ For each variable 'x', a list of constraints that need
                             -- to update when 'x' becomes unbound by backtracking.
              , propQ      :: QueueOfBoundedInt -- ^ Propagation queue.
                -- Assignments
              , assigns    :: FixedVecInt       -- ^ The current assignments indexed on variables.
                              -- __Note:__ the index for 'assigns' is __0__-based, while lit and var start from __1__.
              , trail      :: ListOfInt 	-- ^ List of assignments in chronological order.
              , trailLim   :: ListOfInt         -- ^ Separator indices for different decision levels in 'trail'.
              , decisionLevel :: IORef Int
              , reason     :: FixedVecOf Clause -- ^ For each variable, the constraint that implied its value.
              , level      :: FixedVecInt       -- ^ For each variable, the decision level it was assigned.
              , rootLevel  :: IORef Int         -- ^ Separates incremental and search assumptions.
              , seen       :: UV.IOVector Int   -- ^ scratch vector for 'analyze'
              , currentWatch :: WatchLink       -- ^ used in 'propagate` repeatedely
--              , currentReason :: ListOfInt    -- ^ used in 'analyze' and 'calcReason'
              }

-- | returns the number of 'Var'
nVars :: Solver -> IO Int
nVars = sizeOfVecInt . assigns

-- | returns the number of current assigments
nAssigns :: Solver -> IO Int
nAssigns = sizeOfListOfInt . trail

-- | returns the number of constraints (clauses)
nConstraints  :: Solver -> IO Int
nConstraints = numberOfClauses . constrs

-- | returns the number of learnt clauses
nLearnts :: Solver -> IO Int
nLearnts = numberOfClauses . learnts

-- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Var'
{-# INLINE valueVar #-}
valueVar :: Solver -> Var -> IO Int
valueVar !s !x = getNthInt (x - 1) (assigns s)

-- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Lit'
{-# INLINE valueLit #-}
valueLit !Solver{..} !p
  | p < 0 = negate <$> getNthInt (var p - 1) assigns
  | otherwise = getNthInt (var p - 1) assigns

-- | returns an everything-is-initialized solver from the argument
setInternalState :: Solver -> Int -> IO Solver
setInternalState s nv = do
  ac <- newVecDouble nv 0.0
  w <- newWatcherList $ nv * 2
  u <- newVec 0 -- nv
  -- forM_ [0 .. nv - 1] $ \i -> setVecAt u i =<< newVec 0
  a <- newVecWith nv lBottom
  t <- newListOfInt (2 * nv)
  t' <- newListOfInt nv
  r <- newVecWith nv NullClause
  l <- newVecWith nv (-1)
  q <- newQueue (2 * nv)
  n <- UV.new nv
--  cr <- newListOfInt nv
  let s' = s
           { activities = ac
           , watches = w
           , undos = u
           , assigns = a
           , trail = t
           , trailLim = t'
           , reason = r
           , level = l
           , order = VarOrderStatic s'
           , propQ = q
           , seen = n
--           , currentReason = cr
           }
  return s'

-- | constructor
newSolver :: IO Solver
newSolver = do
  _model      <- newList
  _constrs    <- newClauseLink
  _learnts    <- newClauseLink
  _claInt     <- newIORef 0
  _claDecay   <- newIORef 0
  _activities <- newVecDouble 0 0
  _varInc     <- newIORef 1
  _varDecay   <- newIORef 0
  let _order  = undefined
  _watches    <- newWatcherList 0
  _undos      <- newVec 0
  _propQ      <- newQueue 0
  _assigns    <- newVec 0
  _trail      <- newListOfInt 0
  _trailLim   <- newListOfInt 0
  _decLevel   <- newIORef 0
  _reason     <- newVec 0
  _level      <- newVec 0
  _rootLevel  <- newIORef 0
  _seen       <- UV.new 0
  _currentWatch <- newWatchLink
--   _currentReason <- newListOfInt 0
  let s = Solver
              _model
              _constrs
             _learnts
             _claInt
             _claDecay
             _activities
             _varInc
             _varDecay
             _order
             _watches
             _undos
             _propQ
             _assigns
             _trail
             _trailLim
             _decLevel
             _reason
             _level
             _rootLevel
             _seen
             _currentWatch
--             _currentReason
  return $ s { order = VarOrderStatic s }

-- | public interface of 'Solver' (p.2)
--
-- returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses.
addClause :: Solver -> FixedVecInt -> IO Bool
addClause s@Solver{..} vecLits = do
  result <- clauseNew s vecLits False
  case result of
   (False, _) -> return False   -- Conflict occured
   (True, c)  -> do
     unless (c == NullClause) $ pushClause constrs c
     return True                -- No conflict

-- function on "Solver"

-- | __Fig. 9 (p.14)__
-- Propagates all enqueued facts. If a conflict arises, the /conflicting/
-- clause is returned, otherwise @NullClause@ (instead of Null).
--
-- `propagate` is invoked by `search`,`simpleDB` and `solve`
propagate :: Solver -> IO Clause
propagate s@Solver{..} = do
  let
    loop = do
      k <- sizeOfQueue propQ
      -- checkIt ("propagate.loop starts (" ++ show k ++ ")") s Nothing
      if k == 0
        then return NullClause        -- No conflict
        else do
            -- checkWatches s
            p <- dequeue propQ
            let !w@(fw, sw) = getNthWatchLink (index p) watches
            -- moveTo w tmp
            writeIORef (fst currentWatch) =<< readIORef fw
            writeIORef (snd currentWatch) =<< readIORef sw
            writeIORef fw NullClause
            writeIORef sw NullClause
            let
              for :: Clause -> IO Clause
              for !c = do
                !next <- nextWatcher currentWatch p c
                x <- propagateLit c s p
                if not x
                  then do
                      -- checkIt ("propagate.propagateLit conflict on " ++ show p) s Nothing
                      -- putStrLn =<< dump "conflicted: " c
                      -- Constraint is conflicting; copy remaining watches to 'watches[p]'
                      -- and return constraint:
                      writeIORef (fst currentWatch) next
                      mergeWatcher w p currentWatch
                      clearQueue propQ
                      return c
                  else do
                      if next == NullClause
                        then loop
                        else for next
            c <- readIORef (fst currentWatch)
            -- checkIt "propagate.loop.for starts" s Nothing
            if c == NullClause
              then loop
              else for c
  loop

-- | __Fig. 9 (p.14)__
-- Puts a new fact on the propagation queue, as well as immediately updating the variable's value
-- in the assignment vector. If a conflict arises, @False@ is returned and the propagation queue is
-- cleared. The parameter 'from' contains a reference to the constraint from which 'p' was
-- propagated (defaults to @Nothing@ if omitted).
enqueue :: Solver -> Lit -> Clause -> IO Bool
enqueue s@Solver{..} !p from = do
  let v = var p
  val <- valueVar s v
  if val /= lBottom
    then do -- Existing consistent assignment -- don't enqueue
        return $ signum val == signum p
    else do
        -- New fact, store it
        setNthInt (v - 1) assigns (signum p)
        d <- readIORef decisionLevel
        setNthInt (v - 1) level d
        setNthClause (v - 1) reason from     -- NOTE: @from@ might be NULL!
        pushToListOfInt trail p
        insertQueue propQ p
        -- putStr $ "### " ++ (if from == NullClause then "dec." else "imp.") ++ show p ++ " \t"
        -- dumpStatus s
        return True

-- | __Fig. 10. (p.15)__
-- Analyze a cnflict and produce a reason clause.
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
analyze :: Solver -> Clause -> ListOf Lit -> IO Int
analyze s@Solver{..} confl learnt = do
  UV.set seen 0
  d <- readIORef decisionLevel
  -- learnt `push` 0               -- leave room for the asserting literal
  let
    loop !p confl !counter !btLevel = do
      -- invariant here: @confl /= NullClause@
      -- Because any decision var should be a member of reason of an implication vars.
      -- So it becomes /seen/ in an early stage before the traversing loop
      -- clear pReason
      !pReason <- calcReason confl s p -- pReason holds a negated reason now.
      -- TRACE REASON FOR P:
      let
        for :: [Int] -> Int -> Int -> IO (Int, Int)
        for ![] !counter !btLevel = return (counter, btLevel)
        for !(q:rest) !counter !btLevel = do
          let v = var q - 1
          sv <- UV.unsafeRead seen v
          if sv == 0
            then do
                UV.unsafeWrite seen v 1
                l <- getNthInt v level
                case () of
                 _ | l == d -> for rest (counter + 1) btLevel
                 _ | 0 <  l -> do -- exclude variables from decision level 0
                       pushToList learnt q
                       for rest counter $ max btLevel l
                 _ -> for rest counter btLevel
            else for rest counter btLevel
      -- pl <- asList pReason
      !(counter, btLevel) <- for pReason counter btLevel
      -- SELECT NEXT LITERAL TO LOOK AT:
      let
        doWhile = do
          p <- lastOfListOfInt trail
          let !i = var p - 1
          confl <- getNthClause i reason -- should call it before 'undoOne'
          undoOne s
          sn <- UV.unsafeRead seen i
          if sn == 0 then doWhile else return (p, confl)
      !(p, confl) <- doWhile
      if 1 < counter
        then loop p confl (counter - 1) btLevel
        else {- setAt learnt 0 (negate p) -} pushToList learnt (negate p) >> return btLevel
  loop bottomLit confl 0 0

-- | __Fig. 11. (p.15)__
-- Record a clause and drive backtracking.
--
-- __Pre-Condition:__ "clause[0]" must contain
-- the asserting literal. In particular, 'clause[]' must not be empty.
record :: Solver -> FixedVecInt -> IO ()
record s@Solver{..} v = do
  c <- snd <$> clauseNew s v True -- will be set to created clause, or NULL if @clause[]@ is unit
  l <- getNthInt 1 v
  enqueue s l c
  unless (c == NullClause) $ pushClause learnts c

-- | __Fig. 12. (p.17)__
-- unbinds the last variable on the trail.
undoOne :: Solver -> IO ()
undoOne s@Solver{..} = do
  !p <- lastOfListOfInt trail
  let !x = var p - 1
  setNthInt x assigns lBottom
  setNthClause x reason NullClause
  setNthInt x level (-1)
  undo order (var p)
  popFromListOfInt trail
{-
  let
    loop = do
      k <- sizeOfClauses =<< undos .! x
      when (0 < k) $ do
        a <- undos .! x
        b <- lastE' a
        undoConstraint b s p
        pop' a
        loop
  loop
-}

-- | __Fig. 12 (p.17)__
-- returns @False@ if immediate conflict.
--
-- __Pre-condition:__ propagation queue is empty
assume :: Solver -> Lit -> IO Bool
assume s@Solver{..} p = do
  pushToListOfInt trailLim =<< sizeOfListOfInt trail
  modifyIORef' decisionLevel (+ 1)
  enqueue s p NullClause

-- | __Fig. 12 (p.17)__
-- reverts to the state before last "push".
--
-- __Pre-condition:__ propagation queue is empty.
cancel :: Solver -> IO ()
cancel s@Solver{..} = do
  let
    for c = when (c /= 0) $ undoOne s >> for (c - 1)
  st <- sizeOfListOfInt trail
  tl <- lastOfListOfInt trailLim
  when (0 < st - tl) $ for $ st - tl
  popFromListOfInt trailLim
  modifyIORef' decisionLevel (subtract 1)

-- | __Fig. 12 (p.17)__
-- cancels several levels of assumptions.
cancelUntil :: Solver -> Int -> IO ()
cancelUntil s lvl = do
  let
    loop ((lvl <) -> False) = return ()
    loop d = cancel s >> loop (d - 1)
  loop =<< readIORef (decisionLevel s)

-- | __Fig. 13. (p.18)__
-- Assumes and propagates until a conflict is found, from which a conflict clause
-- is learnt and backtracking until search can continue.
--
-- __Pre-condition:__
-- @root_level == decisionLevel@
search :: Solver -> Int -> Int -> IO LBool
search s@Solver{..} nOfConflicts nOfLearnts = do
  -- clear model
  let
    loop conflictC = do
      -- checkIt "search.loop starts" s Nothing
      !confl <- propagate s
      -- checkIt "search.propagate done" s Nothing
      -- putStrLn $ "propagate done: " ++ show (confl /= NullClause)
      -- checkWatches s
      d <- readIORef decisionLevel
      if confl /= NullClause
        then do
            -- CONFLICT
            -- putStrLn . ("conf: " ++) =<< dump "" confl
            -- checkIt "search is conflict after propagate" s Nothing
            r <- readIORef rootLevel
            if d == r
              then return lFalse
              else do
                  learntClause <- newList
                  backtrackLevel <- analyze s confl learntClause
                  (s `cancelUntil`) . max backtrackLevel =<< readIORef rootLevel
                  -- putStrLn =<< dump "BACKTRACK after search.analyze :: trail: " trail
                  (s `record`) =<< newSizedVecIntFromList =<< asList learntClause
                  decayActivities s
                  -- checkIt "search done backtrack" s Nothing
                  loop $ conflictC + 1
        else do                 -- NO CONFLICT
            -- Simplify the set of problem clauses:
            when (d == 0) $ simplifyDB s >> return () -- our simplifier cannot return @False@ here
            k1 <- numberOfClauses learnts
            k2 <- nAssigns s
            when (k1 - k2 >= nOfLearnts) $ reduceDB s -- Reduce the set of learnt clauses
            k3 <- nVars s
            case () of
             _ | k2 == k3 -> do
                   -- Model found:
                   -- (model `growTo`) k3
                   -- nv <- nVars s
                   -- forM_ [0 .. nv - 1] $ \i -> setAt model i =<< (lTrue ==) <$> assigns .! i
                   writeIORef (ptr model) . map (lTrue ==) =<< asList assigns
                   -- putStrLn =<< dump "activities:" activities
                   return lTrue
             _ | conflictC >= nOfConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< readIORef rootLevel -- force a restart
                   -- checkIt "search terminates to restart" s Nothing
                   return lBottom
             _ -> do
               -- New variable decision:
               p <- select order -- many have heuristic for polarity here
               -- putStrLn $ "search determines next decision var: " ++ show p
               assume s p        -- cannot return @False@
               loop conflictC
  loop 0

-- | __Fig. 14 (p.19)__ Bumping of clause activity
varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity s@Solver{..} !x = do
  a <- (+) <$> getNthDouble (x - 1) activities <*> readIORef varInc
  if 1e100 < a
    then varRescaleActivity s
    else setNthDouble (x - 1) activities a
  update order x

-- | __Fig. 14 (p.19)__
varDecayActivity :: Solver -> IO ()
varDecayActivity s@Solver{..} = do
  d <- readIORef varDecay
  modifyIORef' varInc (* d)

-- | __Fig. 14 (p.19)__
varRescaleActivity :: Solver -> IO ()
varRescaleActivity s@Solver{..} = do
  nv <- subtract 1 <$> nVars s
  forM_ [0 .. nv] $ \i -> modifyNthDouble i activities (* 1e-100)
  modifyIORef' varInc (* 1e-100)

-- | __Fig. 14 (p.19)__
claBumpActivity :: Solver -> Clause -> IO ()
claBumpActivity s@Solver{..} c@Clause{..} = do
  a <- (+) <$> readIORef activity <*> readIORef claInc
  if 1e100 < a
    then claRescaleActivity s
    else writeIORef activity a

-- | __Fig. 14 (p.19)__
claDecayActivity :: Solver -> IO ()
claDecayActivity s@Solver{..} = do
  d <- readIORef claDecay
  modifyIORef' claInc (* d)

-- | __Fig. 14 (p.19)__
claRescaleActivity :: Solver -> IO ()
claRescaleActivity s@Solver{..} = do
  let
    loop NullClause = return ()
    loop c@Clause{..} = do
      modifyIORef' activity (* 1e-100)
      loop =<< nextClause learnts c
  loop =<< nextClause learnts NullClause
  modifyIORef' claInc (* 1e-100)

-- | __Fig. 14 (p.19)__
decayActivities :: Solver -> IO ()
decayActivities s = do
  varDecayActivity s
  claDecayActivity s

-- | __Fig. 15 (p.20)__
-- Remove half of the learnt clauses minus some locked clause. A locked clause
-- is a clause that is reason to a current assignment. Clauses below a certain
-- lower bound activity are also be removed.
reduceDB :: Solver -> IO ()
reduceDB s@Solver{..} = do
  ci <- readIORef claInc
  cd <- readIORef claDecay
  -- staticVarOrder s
  lim <- (cd *) <$> setClauseActivities s
  -- new engine 0.8
  let isRequired c = (||) <$> locked c s <*> ((lim <=). negate <$> readIORef (activity c))
  let
    loop c = do
      c' <- nextClause learnts c
      if c' == NullClause
        then return ()
        else do
            r <- isRequired c'
            if r
              then loop c'
              else remove c' s >> unlinkClause learnts c >> loop c
  loop NullClause

-- | __Fig. 15. (p.20)__
-- Top-level simplify of constraint database. Will remove any satisfied constraint
-- and simplify remaining constraints under current (partial) assignment. If a
-- top-level conflict is found, @False@ is returned.
--
-- __Pre-condition:__ Decision
-- level must be zero.
--
-- __Post-condition:__ Propagation queue is empty.
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
            let
              ptr = if t == 0 then learnts else constrs
              loop :: Clause -> IO Bool
              loop c = do
                c' <- nextClause ptr c
                if c' == NullClause
                  then return True
                  else do
                      r <- simplify c' s
                      if r
                        then remove c' s >> unlinkClause ptr c >> loop c
                        else loop c'
            loop NullClause
        for 0

-- | __Fig. 16. (p.20)__
-- Main solve method.
--
-- __Pre-condition:__ If assumptions are used, 'simplifyDB' must be
-- called right before using this method. If not, a top-level conflict (resulting in a
-- non-usable internal state) cannot be distinguished from a conflict under assumptions.
solve :: Solver -> ListOf Lit -> IO Bool
solve s@Solver{..} assumps = do
  writeIORef varDecay (1 / 0.95)
  writeIORef claDecay (1 / 0.999)
  writeIORef varInc 1
  nv <- fromIntegral <$> nVars s
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
  !x <- for =<< asList assumps
  if not x
    then return False
    else do
        writeIORef rootLevel =<< readIORef decisionLevel
        -- SOLVE:
        let
          while status@((lBottom ==) -> False) _ _ = do
            cancelUntil s 0
            return $ status == lTrue
          while status nOfConflicts nOfLearnts = do
            status <- search s (fromEnum . fromRational $ nOfConflicts) (fromEnum . fromRational $ nOfLearnts)
            while status (1.5 * nOfConflicts) (1.1 * nOfLearnts)
        while lBottom (min 100 (1 + (10000 + nc)/ nv)) (nc / 3)


---- constraint interface

-- | __Remove.__ The 'remove' method supplants the destructor by receiving
-- the solver state as a parameter. It should dispose the constraint and
-- remove it from the watcher lists.
{-# INLINABLE remove #-}
remove :: Clause -> Solver -> IO ()
remove !c@Clause{..} s@Solver{..} = do
  -- checkWatches s
  -- version 0.5 -- removeElem c =<< (watches .!) . index . negate =<< lits .! 0
  l1 <- negate <$> getNthLiteral 0 c
  removeWatcher (getNthWatchLink (index l1) watches) l1 c
  -- version 0.5 -- removeElem c =<< (watches .!) . index . negate =<< lits .! 1
  l2 <- negate <$> getNthLiteral 1 c
  removeWatcher (getNthWatchLink (index l2) watches) l2 c
  -- c should be deleted here
  return ()

-- | __Simplify.__ At the top-level, a constraint may be given the opportunity to
-- simplify its representation (returns @False@) or state that the constraint is
-- satisfied under the current assignment and can be removed (returns @True@).
-- A constraint must /not/ be simplifiable to produce unit information or to be
-- conflicting; in that case the propagation has not been correctly defined.
{-# INLINABLE simplify #-}
simplify :: Clause -> Solver -> IO Bool
simplify c@Clause{..} s@Solver{..} = do
  n <- sizeOfClause c
  l1 <- negate <$> getNthLiteral 0 c
  l2 <- negate <$> getNthLiteral 1 c
  let
    loop ((< n) -> False) j = do
      when (0 < n - j) $ do
        shrinkClause (n - j) c
        l1' <- negate <$> getNthLiteral 0 c
        when (l1 /= l1') $ do
          pushWatcher (getNthWatchLink (index l1') watches) l1' c
        l2' <- negate <$> getNthLiteral 1 c
        when (l2 /= l2') $ do
          pushWatcher (getNthWatchLink (index l2') watches) l2' c
      return False
    loop i j = do
      l <- getNthLiteral i c
      v <- valueLit s l
      case () of
       _ | v == lTrue   -> return True
       _ | v == lBottom -> do
             when (i /= j && j < 2) $ do
               removeWatcher (getNthWatchLink (index (negate l)) watches) (negate l) c
             when (i /= j) $ do
               setNthLiteral j c l	-- false literals are not copied (only occur for i >= 2)
             loop (i+1) (j+1)
       _ | otherwise -> loop (i+1) j
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
propagateLit :: Clause -> Solver -> Lit -> IO Bool
propagateLit !c@Clause{..} !s@Solver{..} !p = do
  let !w = getNthWatchLink (index p) watches
  -- Make sure the false literal is lits[1]:
  !l <- getNthInt 1 lits
  let !np = negate p
  when (l == np) $ do
    -- swap lits[0] and lits[1]
    setNthInt 1 lits =<< getNthInt 2 lits
    setNthInt 2 lits np
    -- then swap watcher[0] and watcher[1], of course!
    !c' <- readIORef nextWatch1
    writeIORef nextWatch1 =<< readIORef nextWatch2
    writeIORef nextWatch2 c'
  -- If 0th watch is True, then clause is already satisfied.
  !val <- valueLit s =<< getNthInt 1 lits
  if val == lTrue
    then do
        pushWatcher w p c -- re-insert clause into watcher list
        return True
    else do
        -- Look for a new literal to watch:
        !n <- sizeOfClause c
        let
          loop ((< n) -> False) = do
            -- Clause is unit under assignment:
            pushWatcher w p c
            !l <- getNthInt 1 lits
            -- when (c == NullClause) $ error "propagateLit undef"
            enqueue s l c
          loop i = do
            !l <- getNthInt (i + 1) lits
            !val <- valueLit s l
            if val /= lFalse
              then do
                   setNthInt 2 lits l 
                   setNthInt (i + 1) lits np
                   pushWatcher (getNthWatchLink (index (negate l)) watches) (negate l) c -- insert clause into watcher list
                   -- checkIt "propagateLit.pushWatcher done:" s $ Just c
                   --  putStrLn $ "propagateLit(" ++ show p ++ "): move " ++ str ++ " to " ++ show (negate l)
                   return True
              else loop $ i + 1
        loop 2

-- | __Undo.__ During backtracking, this method is called if the constaint added itself
-- to the undo list of /var(p)/ in 'propagateLit'.The current variable assignments are
-- guaranteed to be identical to that of the moment before 'propagateLit' was called.
undoConstraint :: Clause -> Solver -> Lit -> IO ()
undoConstraint _ _ _ = return () -- defaults to do nothing

-- | __Calculate Reason.__ Thi method is given a literal /p/ and an empty vector.
-- The constraint is the /reason/ for /p/ being true, that is, during
-- propagation, the current constraint enqueued /p/. The received vector is
-- extended to include a set of assignments (represented as literals)
-- implying /p/ The current variable assignments are guaranteed to be
-- identical to that of the moment before the constraint propagated /p/.
-- The literal /p/ is also allowed to be the special constant 'bottomLit'
-- in which case the reason for the clause being conflicting should be
-- returned through the vector.
--
-- 'calcReason` is invoked from 'analyze'
--
-- The literal /p/ is also allowed to be the special constant 'bottomLit'
-- in which case the reason for the clause being conflicting should be
-- returned through the vector: @outReason@.
--
-- __invaliant__ @c /= NullClause@
--
-- WARNING: this version returns not a reason but a negated reason! So this is 'calcAntiReason'
{-# INLINABLE calcReason #-}
calcReason :: Clause -> Solver -> Lit -> IO [Lit]
calcReason c s@Solver{..} p {- outReason -} = do
  -- putStrLn =<< dump "c in calcReason" c
  -- invariant: (p == bottomLit) || (p == lits[0])
  -- when (c == NullClause) $ error $ "calcReason can't handle NullClause; p = " ++ show p
  n <- sizeOfClause c
  -- putStrLn $ "calcReason :: n = " ++ show n
  when (learnt c) $ claBumpActivity s c
  let
    loop ((< n) -> False) l = return l
    loop i l = do loop (i + 1) . (: l) =<< getNthLiteral i c
--      push' outReason =<< getNthLiteral i c -- invariant: S.value(lits[i]) == lFalse
--      loop $ i + 1
  loop (if p == bottomLit then 0 else 1) []

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
clauseNew :: Solver -> FixedVecInt -> Bool -> IO (Bool, Clause)
clauseNew s@Solver{..} ps learnt = do
  -- now ps[0] is the number of living literals
  exit <- do
    let
      handle j l n      -- removes duplicates, but returns @True@ if this clause is satisfied
        | j > n = return False
        | otherwise = do
            y <- getNthInt j ps
            case () of
             _ | y == l -> do             -- finds a duplicate
                   swapIntsBetween ps j n
                   modifyNthInt 0 ps (subtract 1)
                   handle j l (n - 1)
             _ | - y == l -> setNthInt 0 ps 0 >> return True -- p and negate p occurs in ps
             _ -> handle (j + 1) l n

      loopForLearnt i = do
        n <- getNthInt 0 ps
        if n < i
          then return False
          else do
              l <- getNthInt i ps
              sat <- handle (i + 1) l n
              if sat
                then return True
                else loopForLearnt $ i + 1

      loop i = do
        n <- getNthInt 0 ps
        if n < i
          then return False
          else do
              l <- getNthInt i ps     -- check the i-th literal's satisfiability
              sat <- valueLit s l                                      -- any literal in ps is true
              case () of
               _ | sat == lTrue -> setNthInt 0 ps 0 >> return True
               _ | sat == lFalse -> do
                 swapIntsBetween ps i n
                 modifyNthInt 0 ps (subtract 1)
                 loop i
               _ -> do
                 sat <- handle (i + 1) l n
                 if sat
                   then return True
                   else loop $ i + 1
    if learnt then loopForLearnt 1 else loop 1
  k <- getNthInt 0 ps
  case k of
   0 -> return (exit, NullClause)
   1 -> do
     l <- getNthInt 1 ps
     (, NullClause) <$> enqueue s l NullClause
   otherwise -> do
     -- allocate clause:
     c <- newClauseFromVec learnt ps
     when learnt $ do
       -- Pick a second literal to watch:
       let
         findMax i@((< k) -> False) j val = return j
         findMax i j val = do
           l' <- var <$> getNthLiteral i c
           a <- getNthInt (l' - 1) assigns
           b <- getNthInt (l' - 1) level
           if (a /= lBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       -- Let @max_i@ be the index of the literal with highest decision level
       max_i <- findMax 0 0 0
       tmp <- getNthLiteral 1 c
       setNthLiteral 1 c =<< getNthLiteral max_i c
       setNthLiteral max_i c tmp   -- OLD: setAt (lits c) max_i =<< c .! 1
       -- check literals occurences
       -- x <- asList c
       -- unless (length x == length (nub x)) $ error "new clause contains a element doubly"
       -- Bumping:
       claBumpActivity s c -- newly learnt clauses should be considered active
       n <- subtract 1 <$> sizeOfClause c
       forM_ [0 .. n] $ varBumpActivity s . var <=< flip getNthLiteral c -- variables in conflict clauses are bumped
     -- Add clause to watcher lists:
     l0 <- negate <$> getNthLiteral 0 c
     pushWatcher (getNthWatchLink (index l0) watches) l0 c
     l1 <- negate <$> getNthLiteral 1 c
     pushWatcher (getNthWatchLink (index l1) watches) l1 c
     return (True, c)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
{-# INLINE locked #-}
locked :: Clause -> Solver -> IO Bool
locked !c !Solver{..} =  (c ==) <$> ((flip getNthClause reason) . subtract 1 . var =<< getNthLiteral 0 c)

{-
-- | __Fig. 17. (p.23)__
-- The static variable ordering of "SATZOO". The code is defined only for clauses, not for
-- arbitrary constraints. It must be adapted before it can be used in MINISAT.
-- The main purpose of this function is to update each activity field in learnt clauses.
staticVarOrder :: Solver -> IO ()
staticVarOrder s@Solver{..} = do
  let clauses = learnts
  -- CLEAR ACTIVITY:
  nv <- nVars s
  forM_ [0 .. nv - 1] $ \i -> setAt activities i 0
  -- DO SIMPLE VARIABLE ACTIVITY HEURISTICS:
  nc <- numberOfClauses learnts
  forM_ [0 .. nc - 1] $ \i -> do
    c <- clauses .! i
    m <- sizeOfClause c
    let a = 2 ** fromIntegral (negate m)
    forM_ [0 .. m - 1] $ \j -> do
      k <- subtract 1 . var <$> c .! j
      setAt activities k . (a +) =<< activities .! k
  -- CALCULATE THE INITIAL "HEAD" OF ALL CLAUSES:
  (occurs :: FixedVecOf (VecOf Lit)) <- newVecWith (2 * nv) =<< newVec 0
  (heat :: FixedVecOf (Double, Int)) <- newVecWith nc (0.0 :: Double,0 :: Int)
  forM_ [0 .. nc - 1] $ \i -> do
    c <- clauses .! i
    cs <- subtract 1 <$> sizeOfClause c
    x <- sum <$> forM [0 .. cs] (\j -> do
                                    l <- c .! j
                                    (`push` i) =<< occurs .! index l
                                    -- return (0::Double)
                                    activities .! (var l - 1)
                                )
    setAt heat i (x, i)
  -- BUMP HEAT FOR CLAUSES WHOSE VARIABLES OCCUR IN OTHER HOT CLAUSES:
  iterSize <- (1 +) . sum <$>
              forM [0 .. nc - 1] (\i -> do
                                     c <- clauses .! i
                                     n <- subtract 1 <$> sizeOfClause c
                                     sum <$> forM [0 .. n] (((size =<<) . (occurs .!) . index) <=< (c .!))
                                 )
  let literals = 2 * nv
  -- putStrLn $ "iterations = " ++ show (fromIntegral literals, fromIntegral iterSize)
  let iterations = min (10 :: Int) . fromEnum $ fromRational (100.0 * fromIntegral literals / fromIntegral iterSize)
  let disapation = (1.0 :: Double) / fromIntegral iterations
  forM_ [0 .. iterations - 1] $ \_ ->
    forM_ [0 .. nc - 1] $ \i -> do
      c <- clauses .! i
      nl <- subtract 1 <$> sizeOfClause c
      forM_ [0 ..nl] $ \j -> do
        os <- (occurs .!) =<< index <$> c .! j
        (iv, ii) <- heat .! i
        iv' <- sum . map fst <$> (mapM (heat .!) =<< asList os)
        setAt heat i (iv + iv' * disapation, ii)
  -- SET ACTIVITIES ACCORDING TO HOT CLAUSES:
  -- @sort(heat)@
  sortByFst heat
  forM_ [0 .. nv - 1] $ \i -> setAt activities i 0
  hs <- size heat
  let
    for i@((< hs) -> False) _ = return ()
    for i extra = do
      h <- heat .! i
      c <- clauses .! snd h
      cs <- sizeOfClause c
      let
        for2 j@((< cs) -> False) extra = return extra
        for2 j extra = do
          v' <- subtract 1 . var <$> c .! j
          a <- activities .! v'
          if a == 0
            then setAt activities v' extra >> for2 (j + 1) (extra * 0.995)
            else for2 (j + 1) extra
      extra <- for2 0 extra
      for (i + 1) extra
  for 0 1e200
  -- updateAll order
  -- writeIORef varInc 1
-}

-- | Another basic implementation
-- all method but select is nop code.
instance VarOrder Solver where
  -- | __Fig. 6. (p.10)__
  -- Creates a new SAT variable in the solver.
  newVar s@Solver{..} = do
    index <- nVars s
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- push undos =<< newVec        -- push'
    -- push reason NullClause       -- push'
    -- push assigns lBottom
    -- push level (-1)
    -- push activities (0.0 :: Double)
    newVar order
    -- growQueueSized (index + 1) propQ
    return index
  updateAll Solver{..} = updateAll order
  select solver = error "?" {- do
    -- firstly run 'staticVarOrder' on solver
    -- staticVarOrder solver
    -- then, search and return a bottom-ed var
    nv <- nVars solver
    let
      loop ((< nv) -> False) = error "no unassigned variable left"
      loop i = do
        x <- assigns solver .! i
        if x == lBottom
          then return $ i + 1   -- NOTE: i is not 1-based 'Var' but 0-based var-index
          else loop $ i + 1
    loop 0 -}

-- | returns an average value of activity
setClauseActivities :: Solver -> IO Double
setClauseActivities s@Solver{..} = do
  -- update activity of learnt clauses
  let
    loop m NullClause = return m
    loop m c = do
      nc <- sizeOfClause c
      let
         loop' ((< nc) -> False) !v = return v
         loop' !i !v = do
             x <- getNthLiteral i c
             v' <- getNthDouble (var x - 1) activities
             loop' (i + 1) (v + v')
      !x <- (/ fromIntegral nc) <$> loop' 0 0
      writeIORef (activity c) x
      -- bad result: writeIORef (activity c) (x / fromIntegral nc)
      loop  (max m x) =<< nextClause learnts c
  (/ 2.0) <$> (loop 0 =<< nextClause learnts NullClause)

-- | delegation-based implementation to use 'staticVarOrder'
data VarOrderStatic = VarOrderStatic
                      {
                        solver :: Solver
                      }

-- | using list for 'VarOrder'
instance VarOrder VarOrderStatic where
  newVar x = return bottomVar
  update o v = return ()
  updateAll o = return ()
  undo o v = return ()
  select VarOrderStatic{..} = do
    -- firstly run 'staticVarOrder' on solver
    -- staticVarOrder solver
    -- then, search and return a bottom-ed var
    nv <- nVars solver
    let
      loop ((< nv) -> False) j _ = return $ j + 1
      loop i j best = do
        x <- getNthInt i $ assigns solver
        if x == lBottom
          then do
              a <- getNthDouble i $ activities solver
              if best < a
                 then loop (i + 1) i a
                 else loop (i + 1) j best
          else loop (i + 1) j best
    loop 0 0 (-1)   -- NOTE: i is not 1-based 'Var' but 0-based var-index

dumpStatus :: Solver -> IO ()
dumpStatus Solver{..} = do
  putStrLn . ("level: " ++) . show . filter ((0 <=) . snd) . zip [1..] =<< asList level
--  putStrLn =<< dump "trail: " trail
--  putStrLn =<< dump "trailLim: " trailLim
  -- putStrLn =<< makeGraph <$> asList trail <*> fromReason reason

{-
fromReason :: VecOf Clause -> IO [(Int, [Int])]
fromReason vec = do
  l <- zip [1..] <$> asList vec
  let f (i, c) = (i, ) <$> asList c
  mapM f l

-- | dump the current status of 'watches'
checkWatches :: Solver -> IO ()
checkWatches s@Solver{..} = do
  n <- nVars s
  forM_ [0 .. 2 * n -1] $ \i -> do
    let w = getNthWatchLink i watches
    let l = index2lit i
    putStrLn . ((show l ++ " : ") ++) . show =<< traverseWatcher w l
-}

{-
numRegisteredClauses :: Solver -> IO Int
numRegisteredClauses Solver{..} = do
  n <- size watches
  sum . map length <$> forM [0 .. n -1] (\i -> flip traverseWatcher (index2lit i) =<< watches .! i)

watcherList :: Solver -> Lit -> IO [[Lit]]
watcherList Solver{..} lit = do
  (b, e) <- watches .! index lit
  x <- map sort <$> (flip traverseWatcher lit =<< watches .! index lit)
{-
  unless (null x) $ do
    cs <- sort <$> (asList =<< readIORef b)
    ce <- sort <$> (asList =<< readIORef e)
    unless (head x == cs) $ error $ "inconsistent head watcherList" ++ show (x, cs)
    unless (last x == ce) $ error $ "inconsistent tail watcherList" ++ show (x, ce)
-}
  return x

checkWatchers :: Solver -> Clause -> IO ()
checkWatchers s NullClause = return ()
checkWatchers s c = do
  l1 <- negate <$> c .! 0
  l2 <- negate <$> c .! 1
  b1 <- watcherList s l1
  b2 <- watcherList s l2
  l <- sort <$> asList c
  s <- dump "clause" c
  unless (elem l b1) $ error $ s ++ " = " ++ show l ++ " is not registered the 1st wathers list:" ++ show l1
  unless (elem l b2) $ error $ s ++ " = " ++ show l ++ " is not registered the 2nd wathers list:" ++ show l2

checkIt :: String -> Solver -> Maybe Clause -> IO ()
-- checkIt _ _ _ = return ()
checkIt mes s@Solver{..} Nothing = mapM_ (checkIt mes s . Just) =<< asList learnts
checkIt mes s@Solver{..} (Just c) = do
  let lits = [-87,-75,-28,-7,-3,-2,-1,5,26,46,73]
  l <- asList learnts
  ll <- sort <$> asList c
  when (ll == lits) $ do
    putStr $ (take 40 (mes ++ repeat ' ')) ++ " : "
    putStr =<< dump "The trace " c
    l1 <- c .! 0
    l2 <- c .! 1
    putStr $ " -- 1st literal " ++ show l1 ++ " "
    w1 <- watcherList s (negate l1)
    if elem lits w1
      then putStr ", " -- w1
      else putStr "not found, " -- >> error "not found"
    putStr $ " 2nd literal " ++ show l2 ++ " "
    w2 <- watcherList s (negate l2)
    if elem lits w2
      then putStrLn " -- " -- w2
      else putStrLn "not found -- " --  >> error "not found"
-}
