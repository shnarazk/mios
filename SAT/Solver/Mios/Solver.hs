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
         -- * public interface of 'Solver' (p.2)
       , addClause
       , simplifyDB
       , solve
         -- * methods of 'Solver'
       , propagate
       , enqueue
       , analyze
       , record
       , undoOne
       , assume
       , cancel
       , cancelUntil
       , clauseNew
       )
        where

import GHC.Prim
import Control.Monad
import Data.List (nub, sort)
import Data.IORef
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.WatchList
import SAT.Solver.Mios.SolverRelation

-- | __Fig. 2.(p.9)__ Internal State of the solver
data Solver = Solver
              {
                -- for public interface
                model      :: VecOf Bool   -- ^ If found, this vector has the model
                -- Contraint databale
              , constrs    :: VecOf Clause -- ^ List of problem constraints.
              , learnts    :: VecOf Clause -- ^ List of learnt clauses.
              , claInc     :: IORef Double -- ^ Clause activity increment amount to bump with.
              , claDecay   :: IORef Double -- ^ Decay factor for clause activity.
                -- Variable order
              , activities :: FixedVecOf Double -- ^ Heuristic measurement of the activity of a variable.
              , varInc     :: IORef Double -- ^ Variable activity increment amount to bump with.
              , varDecay   :: IORef Double -- ^ Decay factor for variable activity.
              , order      :: VarOrderStatic -- ^ Keeps track of the dynamic variable order.
                -- Propagation
              , watches    :: FixedVecOf WatchLink -- ^ For each literal 'p', a list of constraint wathing 'p'.
                             -- A constraint will be inspected when 'p' becomes true.
              , undos      :: FixedVecOf (VecOf Clause) -- ^ For each variable 'x', a list of constraints that need
                             -- to update when 'x' becomes unbound by backtracking.
              , propQ      :: FixedQueueOf Lit  -- ^ Propagation queue.
                -- Assignments
              , assigns    :: FixedVecOf LBool  -- ^ The current assignments indexed on variables.
                              -- __Note:__ the index for 'assigns' is __0__-based, while lit and var start from __1__.
              , trail      :: StackOfLit    -- ^ List of assignments in chronological order.
              , trailLim   :: VecOf Int    -- ^ Separator indices for different decision levels in 'trail'.
              , reason     :: FixedVecOf Clause -- ^ For each variable, the constraint that implied its value.
              , level      :: FixedVecOf Int    -- ^ For each variable, the decision level it was assigned.
              , rootLevel  :: IORef Int    -- ^ Separates incremental and search assumptions.
              }

instance SolverState Solver where
 nVars = size . assigns
 nAssigns = size . trail
 nConstraints = size . constrs
 nLearnts = size . learnts
 valueVar s x = assigns s .! (x - 1)
 {-# SPECIALIZE INLINE valueLit :: Solver -> Lit -> IO Int #-}
 valueLit s p
   | p < 0 = negate <$> (assigns s .! (var p - 1))
   | otherwise = assigns s .! (var p - 1)
 decisionLevel = size . trailLim
 setInternalState s nv = do
   ac <- newVecSizedWith nv 0.0
   w <- newVecSized $ nv * 2
   u <- newVecSized nv
   forM_ [0 .. nv - 1] $ \i -> setAt u i =<< newVec
   forM_ [0 .. nv * 2 - 1] $ \i -> do
     a <- newIORef NullClause
     b <- newIORef NullClause
     setAt w i (a, b)
   a <- newVecSizedWith nv lBottom
   t <- newVecSized (2 * nv)
   r <- newVecSizedWith nv NullClause
   l <- newVecSizedWith nv (-1)
   q <- newQueueSized (2 * nv)
   let s' = s
            { activities = ac
            , watches = w
            , undos = u
            , assigns = a
            , trail = t
            , reason = r
            , level = l
            , order = VarOrderStatic s'
            , propQ = q
            }
   return s'

-- | constructor
newSolver :: IO Solver
newSolver = do
  _model      <- newVec
  _constrs    <- newVec
  _learnts    <- newVec
  _claInt     <- newIORef 0
  _claDecay   <- newIORef 0
  _activities <- newVec
  _varInc     <- newIORef 1
  _varDecay   <- newIORef 0
  let _order  = undefined
  _watches    <- newVec
  _undos      <- newVec
  _propQ      <- newQueue
  _assigns    <- newVec
  _trail      <- newVec
  _trailLim   <- newVec
  _reason     <- newVec
  _level      <- newVec
  _rootLevel  <- newIORef 0
  act <- newIORef (-1)
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
             _reason
             _level
             _rootLevel
  return $ s { order = VarOrderStatic s }

-- | public interface of 'Solver' (p.2)
--
-- returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses.
addClause :: Solver -> [Lit] -> IO Bool
addClause s@Solver{..} literals = do
  vecLits <- newFromList literals
  result <- clauseNew s vecLits False
  case result of
   (False, _) -> return False   -- Conflict occured
   (True, c)  -> do
     unless (c == NullClause) $ push constrs c
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
      k <- size propQ
      -- checkIt ("propagate.loop starts (" ++ show k ++ ")") s Nothing
      if k == 0
        then return NullClause        -- No conflict
        else do
            -- checkWatches s
            p <- dequeue propQ
            w@(fw, sw) <- watches .! index p
            b <- newIORef =<< readIORef fw
            e <- newIORef =<< readIORef sw
            let tmp = (b, e)
            -- moveTo w tmp
            writeIORef fw NullClause
            writeIORef sw NullClause
            let
              for :: Clause -> IO Clause
              for !c = do
                !next <- c `seq` nextWatcher tmp p c
                x <- c `seq` propagateLit c s p
                if not x
                  then do
                      -- checkIt ("propagate.propagateLit conflict on " ++ show p) s Nothing
                      -- putStrLn =<< dump "conflicted: " c
                      -- Constraint is conflicting; copy remaining watches to 'watches[p]'
                      -- and return constraint:
                      let
                        revert NullClause = clear propQ >> return c
                        revert !c' = do
                          next <- c' `seq` nextWatcher tmp p c'
                          pushWatcher w p c'
                          -- checkIt "progress.revert.pushWatcher pre" s $ Just next
                          revert next
                      revert next
                  else do
                      -- checkIt ("propagate.pro...it no conf on " ++ show (p, next == NullClause)) s Nothing
                      if next == NullClause
                        then loop
                        else for next
            c <- readIORef b
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
enqueue s@Solver{..} p from = do
  let v = var p
  val <- valueVar s v
  if val /= lBottom
    then do -- Existing consistent assignment -- don't enqueue
        return $ signum val == signum p
    else do
        -- New fact, store it
        setAt assigns (v - 1) (signum p)
        d <- decisionLevel s
        setAt level (v - 1) (d :: Int)
        setAt reason (v - 1) from     -- NOTE: @from@ might be NULL!
        push trail p
        insert propQ p
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
analyze :: Solver -> Clause -> VecOf Lit -> IO Int
analyze s@Solver{..} confl learnt = do
--  putStrLn =<< dump "analyze arg: " confl
  n <- nVars s
  (seen :: FixedVecOf Bool) <- newVecSizedWith n False
  pReason <- newVec
  learnt `push` 0               -- leave room for the asserting literal
  let
    loop p confl counter btLevel = do
      -- invariant here: @confl /= NullClause@
      -- Because any decision var should be a member of reason of an implication vars.
      -- So it becomes /seen/ in an early stage before the traversing loop
      clear pReason
      calcReason confl s p pReason
      -- TRACE REASON FOR P:
      let
        for :: Int -> Int -> Int -> IO (Int, Int)
        for j counter btLevel = do
          k <- size pReason
          if j >= k
            then return (counter, btLevel)
            else do
                q <- pReason .! j
                let v = var q
                sv <- seen .! (v - 1)
                if not sv
                  then do
                      setAt seen (v - 1) True
                      d <- decisionLevel s
                      l <- level .! (v - 1)
                      case () of
                       _ | l == d -> for (j + 1) (counter + 1) btLevel
                       _ | 0 <  l -> do -- exclude variables from decision level 0
                             push learnt $ negate q
                             for (j + 1) counter $ max btLevel l
                       _ -> for (j + 1) counter btLevel
                  else for (j + 1) counter btLevel
      (counter, btLevel) <- for 0 counter btLevel
      -- SELECT NEXT LITERAL TO LOOK AT:
      let
        doWhile p confl = do
          p <- lastE trail
          confl <- reason .! (var p - 1)
          undoOne s
          notSeen <- not <$> seen .! (var p - 1)
          if notSeen
            then doWhile p confl
            else return (p, confl)
      (p, confl) <- doWhile p confl
      if 1 < counter
        then loop p confl (counter - 1) btLevel
        else setAt learnt 0 (negate p) >> return btLevel
  loop bottomLit confl 0 0

-- | __Fig. 11. (p.15)__
-- Record a clause and drive backtracking.
--
-- __Pre-Condition:__ "clause[0]" must contain
-- the asserting literal. In particular, 'clause[]' must not be empty.
record :: Solver -> VecOf Lit -> IO ()
record s@Solver{..} clause = do
  c <- snd <$> clauseNew s clause True -- will be set to created clause, or NULL if @clause[]@ is unit
  l <- clause .! 0
  enqueue s l c
  unless (c == NullClause) $ push learnts c

-- | __Fig. 12. (p.17)__
-- unbinds the last variable on the trail.
undoOne :: Solver -> IO ()
undoOne s@Solver{..} = do
  !p <- lastE trail
  let x = var p - 1
  setAt assigns x lBottom
  setAt reason  x NullClause
  setAt level   x (-1)
  undo order (var p)
  pop trail
  let
    loop = do
      k <- size =<< undos .! x
      when (0 < k) $ do
        a <- undos .! x
        b <- lastE a
        undoConstraint b s p
        pop a
        loop
  loop

-- | __Fig. 12 (p.17)__
-- returns @False@ if immediate conflict.
--
-- __Pre-condition:__ propagation queue is empty
assume :: Solver -> Lit -> IO Bool
assume s@Solver{..} p = do
  push trailLim =<< size trail
  enqueue s p NullClause

-- | __Fig. 12 (p.17)__
-- reverts to the state before last "push".
--
-- __Pre-condition:__ propagation queue is empty.
cancel :: Solver -> IO ()
cancel s@Solver{..} = do
  let
    for c = when (c /= 0) $ undoOne s >> for (c - 1)
  st <- size trail
  tl <- lastE trailLim
  when (0 < st - tl) $ for $ st - tl
  pop trailLim

-- | __Fig. 12 (p.17)__
-- cancels several levels of assumptions.
cancelUntil :: Solver -> Int -> IO ()
cancelUntil s lvl = do
  d <- decisionLevel s
  when (lvl < d) $ do
    cancel s
    (s `cancelUntil`) lvl

-- | __Fig. 13. (p.18)__
-- Assumes and propagates until a conflict is found, from which a conflict clause
-- is learnt and backtracking until search can continue.
--
-- __Pre-condition:__
-- @root_level == decisionLevel@
search :: Solver -> Int -> Int -> IO LBool
search s@Solver{..} nOfConflicts nOfLearnts = do
  clear model
  let
    loop conflictC = do
      -- checkIt "search.loop starts" s Nothing
      !confl <- propagate s
      -- checkIt "search.propagate done" s Nothing
      -- putStrLn $ "propagate done: " ++ show (confl /= NullClause)
      -- checkWatches s
      if confl /= NullClause
        then do
            -- CONFLICT
            -- putStrLn . ("conf: " ++) =<< dump "" confl
            -- checkIt "search is conflict after propagate" s Nothing
            d <- decisionLevel s
            r <- readIORef rootLevel
            if d == r
              then return lFalse
              else do
                  learntClause <- newVec
                  backtrackLevel <- analyze s confl learntClause
                  (s `cancelUntil`) . max backtrackLevel =<< readIORef rootLevel
                  -- putStrLn =<< dump "BACKTRACK after search.analyze :: trail: " trail
                  (s `record`) learntClause
                  decayActivities s
                  -- checkIt "search done backtrack" s Nothing
                  loop $ conflictC + 1
        else do                 -- NO CONFLICT
            d <- decisionLevel s
            -- Simplify the set of problem clauses:
            when (d == 0) $ simplifyDB s >> return () -- our simplifier cannot return @False@ here
            k1 <- size learnts
            k2 <- nAssigns s
            when (k1 - k2 >= nOfLearnts) $ reduceDB s -- Reduce the set of learnt clauses
            k3 <- nVars s
            case () of
             _ | k2 == k3 -> do
                   -- Model found:
                   (model `growTo`) k3
                   nv <- nVars s
                   forM_ [0 .. nv - 1] $ \i -> setAt model i =<< (lTrue ==) <$> assigns .! i
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
varBumpActivity s@Solver{..} x = do
  a <- (+) <$> activities .! (x - 1) <*> readIORef varInc
  if 1e100 < a
    then varRescaleActivity s
    else setAt activities (x - 1) a
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
  forM_ [0 .. nv] $ \i -> setAt activities i =<< (1e-100 *) <$>  activities .! i
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
  nc <- subtract 1 <$> nLearnts s
  forM_ [0 .. nc] $ \i -> do
    a <- activity <$> learnts .! i
    writeIORef a . (1e-100 *) =<< readIORef a
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
  n <- size learnts
  ci <- readIORef claInc
  -- staticVarOrder s
  lim <- setClauseActivities s
  sortVecOn ((negate <$>) . readIORef . activity) learnts -- sortOnActivity(learnts)
  let
    n' = fromIntegral n
    -- lim = ci / n'
    n2 = div n 2
  let
    for i@((< n2) -> False) j = return (i, j)
    for i j = do
      !c <- learnts .! i
      lk <- locked c s
      if not lk
        then remove c s >> for (i + 1) j -- O(n) operation
        else setAt learnts j c >> for (i + 1) (j + 1)
  (i, j) <- for 0 0
  let
    for' i@((< n) -> False) j = return (i, j)
    for' i j = do
      !c <- learnts .! i
      lk <- locked c s
      a <- readIORef $ activity c
      if not lk && a < lim
        then remove c s >> for' (i + 1) j -- O(n) operation
        else setAt learnts j c >> for' (i + 1) (j + 1)
  (_, j') <- for' i j
  shrink (n - j') learnts
  return ()

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
          for t@((< 2) -> False) = return True
          for t = do
            let cs = if t == 0 then learnts else constrs
            k <- size cs
            let
              for2 i@((< k) -> False) j = return j
              for2 i j = do
                !c <- cs .! i
                x <- simplify c s
                if x
                  then remove c s >> for2 (i + 1) j
                  else setAt cs j c >> for2 (i + 1) (j + 1)
            j <- for2 0 0
            k <- size cs
            shrink (k - j) cs
            for (t + 1)
        for 0
        return True

-- | __Fig. 16. (p.20)__
-- Main solve method.
--
-- __Pre-condition:__ If assumptions are used, 'simplifyDB' must be
-- called right before using this method. If not, a top-level conflict (resulting in a
-- non-usable internal state) cannot be distinguished from a conflict under assumptions.
solve :: Solver -> VecOf Lit -> IO Bool
solve s@Solver{..} assumps = do
  writeIORef varDecay (1 / 0.95)
  writeIORef claDecay (1 / 0.999)
  writeIORef varInc 1
  nc <- fromIntegral <$> nConstraints s
  -- PUSH INCREMENTAL ASSUMPTIONS:
  k <- size assumps
  let
    for i@((< k) -> False) = return True
    for i = do
      a <- assumps .! i
      b <- assume s a
      if not b
        then cancelUntil s 0 >> return False
        else do
            c <- propagate s
            if c /= NullClause
              then cancelUntil s 0 >> return False
              else for $ i + 1
  x <- for 0
  if not x
    then return False
    else do
        writeIORef rootLevel =<< decisionLevel s
        -- SOLVE:
        let
          while status@((lBottom ==) -> False) _ _ = do
            cancelUntil s 0
            return $ status == lTrue
          while status nOfConflicts nOfLearnts = do
            status <- search s (fromEnum . fromRational $ nOfConflicts) (fromEnum . fromRational $ nOfLearnts)
            while status (1.5 * nOfConflicts) (1.1 * nOfLearnts)
        while lBottom 100 (nc / 3)

instance BoolConstraint Solver Clause where
  -- | constraint interface
  remove !c@Clause{..} s@Solver{..} = do
    -- checkWatches s
    -- version 0.5 -- removeElem c =<< (watches .!) . index . negate =<< lits .! 0
    l1 <- negate <$> c .! 0
    w1 <- watches .! index l1
    removeWatcher w1 l1 c
    -- version 0.5 -- removeElem c =<< (watches .!) . index . negate =<< lits .! 1
    l2 <- negate <$> c .! 1
    w2 <- watches .! index l2
    removeWatcher w2 l2 c
    -- c should be deleted here
    return ()
  -- | only called at top level with prop. queue
  simplify c@Clause{..} s@Solver{..} = do
    n <- size c
    l1 <- negate <$> c .! 0
    l2 <- negate <$> c .! 1
    let
      loop ((< n) -> False) j = do
        when (0 < n - j) $ do
          shrink (n - j) c
          l1' <- negate <$> c .! 0
          when (l1 /= l1') $ do
            w <- watches .! index l1'
            pushWatcher w l1' c
          l2' <- negate <$> c .! 1
          when (l2 /= l2') $ do
            w <- watches .! index l2'
            pushWatcher w l2' c
        return False
      loop i j = do
        l <- c .! i
        v <- valueLit s l
        case () of
         _ | v == lTrue   -> return True
         _ | v == lBottom -> do
               when (i /= j && j < 2) $ do
                 w <- watches .! index (negate l)
                 removeWatcher w (negate l) c
               when (i /= j) $ do
                 setAt c j l	-- false literals are not copied (only occur for i >= 2)
               loop (i+1) (j+1)
         _ | otherwise -> loop (i+1) j
    loop 0 0
  -- | returns @True@ if no conflict occured
  -- this is invoked by 'propagate'
  {-# SPECIALIZE INLINE propagateLit :: Clause -> Solver -> Lit -> IO Bool #-}
  propagateLit c@Clause{..} s@Solver{..} p = do
    -- checkIt ("propagateLit start on it! (" ++ show p ++ ")") s $ Just c
    w <- watches .! index p
    -- Make sure the false literal is lits[1]:
    l <- c .! 0
    when (l == negate p) $ do
      -- swap lits[0] and lits[1]
      setAt c 0 =<< c .! 1
      setAt c 1 (negate p)
      -- then swap watcher[0] and watcher[1], of course!
      c' <- readIORef nextWatch1
      writeIORef nextWatch1 =<< readIORef nextWatch2
      writeIORef nextWatch2 c'
    -- If 0th watch is True, then clause is already satisfied.
    val <- valueLit s =<< c .! 0
    if val == lTrue
      then do
          pushWatcher w p c -- re-insert clause into watcher list
          return True
      else do
          -- Look for a new literal to watch:
          n <- size c
          let
            loop ((< n) -> False) = do
              -- Clause is unit under assignment:
              pushWatcher w p c
              l <- c .! 0
              -- when (c == NullClause) $ error "propagateLit undef"
              enqueue s l c
            loop i = do
              l <- c .! i
              val <- valueLit s l
              if val /= lFalse
                then do
                    setAt c 1 l
                    setAt c i (negate p)
                    w <- watches .! index (negate l)
                    -- checkIt ("propagateLit.pushWatcher call " ++ show (negate l)) s $ Just c
                    pushWatcher w (negate l) c -- insert clause into watcher list
                    -- checkIt "propagateLit.pushWatcher done:" s $ Just c
                    --  putStrLn $ "propagateLit(" ++ show p ++ "): move " ++ str ++ " to " ++ show (negate l)
                    return True
                else loop $ i + 1
          loop 2
  -- The literal /p/ is also allowed to be the special constant 'bottomLit'
  -- in which case the reason for the clause being conflicting should be
  -- returned through the vector: @outReason@.
  --
  -- __invaliant__ @c /= NullClause@
  calcReason c s@Solver{..} p outReason = do
    -- putStrLn =<< dump "c in calcReason" c
    -- invariant: (p == bottomLit) || (p == lits[0])
    -- when (c == NullClause) $ error $ "calcReason can't handle NullClause; p = " ++ show p
    n <- size c
    -- putStrLn $ "calcReason :: n = " ++ show n
    let
      loop ((< n) -> False) = return ()
      loop i = do
        push outReason . negate =<< c .! i -- invariant: S.value(lits[i]) == lFalse
        loop $ i + 1
    loop $ if p == bottomLit then 0 else 1
    when (learnt c) $ claBumpActivity s c

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
-- clauseNew :: Solver -> VecOf Lit -> Bool -> Clause -> IO Bool
clauseNew :: Solver -> VecOf Lit -> Bool -> IO (Bool, Clause)
clauseNew s@Solver{..} ps learnt = do
  (exit, k, psWithLen) <- do
    ls <- nub <$> asList ps        -- remove all duplicatates from ps
    if not learnt
      then do
      cond1 <- or <$> mapM (\l -> (lTrue ==) <$> valueLit s l) ls -- any literal in ps is true
      let cond2 = any (flip elem ls) (map negate ls) -- both p and negate p occurs in ps
      if cond1 || cond2
        then return (True, 0, undefined)
        else do
        -- remove all false literals from ps
        l' <- filterM (\l -> (lFalse /=) <$> valueLit s l) ls
        clear ps
        forM_ l' $ push ps
        let ln = length l'
        (False, ln, ) <$> newFromList (ln : l')
      else do
      ls <- asList ps
      let ln = length ls
      (False, ln, ) <$> newFromList (ln : ls)
  case k of
   0 -> return (exit, NullClause)
   1 -> do
     l <- ps .! 0
     (, NullClause) <$> enqueue s l NullClause
   otherwise -> do
     -- allocate clause:
     act <- newIORef 0
     n1 <- newIORef NullClause
     n2 <- newIORef NullClause
     let !c = Clause learnt act n1 n2 psWithLen
     when learnt $ do
       -- Pick a second literal to watch:
       let
         findMax i@((< k) -> False) j val = return j
         findMax i j val = do
           l' <- var <$> c .! i
           a <- assigns .! (l' - 1)
           b <- level .! (l' - 1)
           if (a /= lBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       -- Let @max_i@ be the index of the literal with highest decision level
       max_i <- findMax 0 0 0
       tmp <- c .! 1
       setAt c 1 =<< c .! max_i
       setAt c max_i tmp   -- OLD: setAt (lits c) max_i =<< c .! 1
       -- check literals occurences
       -- x <- asList c
       -- unless (length x == length (nub x)) $ error "new clause contains a element doubly"
       -- Bumping:
       claBumpActivity s c -- newly learnt clauses should be considered active
       n <- subtract 1 <$> size c
       forM_ [0 .. n] $ varBumpActivity s . var <=< (c .!) -- variables in conflict clauses are bumped
     -- Add clause to watcher lists:
     l0 <- negate <$> c .! 0
     w0 <- watches .! index l0
     pushWatcher w0 l0 c
     l1 <- negate <$> c .! 1
     w1 <- watches .! index l1
     pushWatcher w1 l1 c
     -- putStrLn =<< dump ("add new clause to " ++ show (l0, l1) ++ ": ") c
     return (True, c)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
locked :: Clause -> Solver -> IO Bool
locked c Solver{..} =  (c ==) <$> ((reason .!) . subtract 1 . var =<< c .! 0)

---- C-ish statement
-- | a monadic iteration trying its condition after the body
doWhile :: IO Bool -> IO a -> IO a
doWhile cond body = do { res <- body; whileCond <- cond; if whileCond then doWhile cond body else return res }

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
  nc <- size clauses
  forM_ [0 .. nc - 1] $ \i -> do
    c <- clauses .! i
    m <- size c
    let a = 2 ** fromIntegral (negate m)
    forM_ [0 .. m - 1] $ \j -> do
      k <- subtract 1 . var <$> c .! j
      setAt activities k . (a +) =<< activities .! k
  -- CALCULATE THE INITIAL "HEAD" OF ALL CLAUSES:
  (occurs :: FixedVecOf (VecOf Lit)) <- newVecSizedWith (2 * nv) =<< emptyVec
  (heat :: FixedVecOf (Double, Int)) <- newVecSizedWith nc (0.0 :: Double,0 :: Int)
  forM_ [0 .. nc - 1] $ \i -> do
    c <- clauses .! i
    cs <- subtract 1 <$> size c
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
                                     n <- subtract 1 <$> size c
                                     sum <$> forM [0 .. n] (((size =<<) . (occurs .!) . index) <=< (c .!))
                                 )
  let literals = 2 * nv
  -- putStrLn $ "iterations = " ++ show (fromIntegral literals, fromIntegral iterSize)
  let iterations = min (10 :: Int) . fromEnum $ fromRational (100.0 * fromIntegral literals / fromIntegral iterSize)
  let disapation = (1.0 :: Double) / fromIntegral iterations
  forM_ [0 .. iterations - 1] $ \_ ->
    forM_ [0 .. nc - 1] $ \i -> do
      c <- clauses .! i
      nl <- subtract 1 <$> size c
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
      cs <- size c
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
        x <- assigns solver .! i
        a <- activities solver .! i
        if x == lBottom
          then
              if best < a
                 then loop (i + 1) i a
                 else loop (i + 1) j best
          else loop (i + 1) j best
    loop 0 0 (-1)   -- NOTE: i is not 1-based 'Var' but 0-based var-index

numVec :: VectorLike v Int => Int -> v -> IO [Int]
numVec base v = zipWith (*) [base ..] <$> asList v

dumpStatus :: Solver -> IO ()
dumpStatus Solver{..} = do
  -- putStrLn . ("level: " ++) . show . filter ((0 <=) . snd) . zip [1..] =<< asList level
  putStrLn =<< dump "trail: " trail
  putStrLn =<< dump "trailLim: " trailLim
  -- putStrLn =<< makeGraph <$> asList trail <*> fromReason reason

fromReason :: VecOf Clause -> IO [(Int, [Int])]
fromReason vec = do
  l <- zip [1..] <$> asList vec
  let f (i, c) = (i, ) <$> asList c
  mapM f l

-- | dump the current status of 'watches'
checkWatches :: Solver -> IO ()
checkWatches Solver{..} = do
  n <- size watches
  forM_ [0 .. n -1] $ \i -> do
    w <- watches .! i
    let l = index2lit i
    putStrLn . ((show l ++ " : ") ++) . show =<< traverseWatcher w l

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
checkIt _ _ _ = return ()
{-
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

-- | returns an average value of activity
setClauseActivities :: Solver -> IO Double
setClauseActivities s@Solver{..} = do
  -- update activity of learnt clauses
  nl <- size learnts
  let
    for ((< nl) -> False) m = return m
    for i m = do
      c <- learnts .! i
      nc <- size c
      x <- (/ fromIntegral nc) . sum <$> mapM ((activities .!) . subtract 1 . var <=< (c .!)) [0 .. nc - 1]
      writeIORef (activity c) x
      -- bad result: writeIORef (activity c) (x / fromIntegral nc)
      for (i + 1) (max m x)
  m <- for 0 0
  return $ m / 2.0

