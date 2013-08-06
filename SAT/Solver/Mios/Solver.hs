{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , RecordWildCards
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | define 'Solver', 'BoolConstraint', and 'Clause'
--
-- For a standard SAT-problem, the interface is used in the following way:
-- Variables are introduced by calling 'newVar'. From these variables,
-- clauses are built and added by 'addClause'. Trivial conflicts, such as
-- two unit clauses @{x}@ and @{!x}@ being added, can be detected by
-- 'addClause', in which case it returns @False@. From this point on, the
-- solver sate is undefined and must not be used further. If no such
-- trivial conflict is detected during the clause insertion phase, 'solve'
-- is called with an empty list of assumptions. It returns @False@ if the
-- problem is /unsatisfiable/, and @True@ if it is /satisfiable/, in which
-- case the model can be read from the public vector 'model'.
--
-- The 'simplifyDB' method cab be used before calling 'solve' to simplify
-- the set of problem constraints (often called the /constraint database/).
-- In our implementation, 'simplifyDB' will first propagate all unit
-- information, then remove all satisfied constraints. As for 'addClause',
-- the simplifier can sometimes detect a conflict, in which case @False@ is
-- returned and the solver state is, again, undefined and must not be used
-- further.
module SAT.Solver.Mios.Solver
       (
         -- * Solver
         SolverState (..)
       , Solver (..)
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
         -- * Constraint Abstract Class
       , BoolConstraint (..)
         -- * Clause
       , Clause (..)
       , clauseNew
       , locked
         -- * Debug
       , dumpClause
       )
        where

import Control.Monad
import Data.List (intercalate, nub, sort)
import Data.IORef
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Implementation.V01

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
              , activities :: VecOf Double -- ^ Heuristic measurement of the activity of a variable.
              , varInc     :: IORef Double -- ^ Variable activity increment amount to bump with.
              , varDecay   :: IORef Double -- ^ Decay factor for variable activity.
              , order      :: VarOrderStatic -- ^ Keeps track of the dynamic variable order.
                -- Propagation
              , watches    :: VecOf (VecOf Clause) -- ^ For each literal 'p', a list of constraint wathing 'p'.
                             -- A constraint will be inspected when 'p' becomes true.
              , undos      :: VecOf (VecOf Clause) -- ^ For each variable 'x', a list of constraints that need
                             -- to update when 'x' becomes unbound by backtracking.
              , propQ      :: QueueOf Lit  -- ^ Propagation queue.
                -- Assignments
              , assigns    :: VecOf LBool  -- ^ The current assignments indexed on variables.
                              -- __Note:__ the index for 'assigns' is __0__-based, while lit and var start from __1__.
              , trail      :: VecOf Lit    -- ^ List of assignments in chronological order.
              , trailLim   :: VecOf Int    -- ^ Separator indices for different decision levels in 'trail'.
              , reason     :: VecOf Clause -- ^ For each variable, the constraint that implied its value.
              , level      :: VecOf Int    -- ^ For each variable, the decision level it was assigned.
              , rootLevel  :: IORef Int    -- ^ Separates incremental and search assumptions.
              }

-- | __Fig. 3.(p.9)__
-- Small helper methods of 'Solver'. for instance, `nLearnts` returns the number
-- of learnt clauses.
class SolverState s where
 -- | returns the number of 'Var'
 nVars         :: s -> IO Int
 -- | returns the number of current assigments
 nAssigns      :: s -> IO Int
 -- | returns the number of constraints (clauses)
 nConstraints  :: s -> IO Int
 -- | returns the number of learnt clauses
 nLearnts      :: s -> IO Int
 -- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Var'
 valueVar         :: s -> Var -> IO Int
 -- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Lit'
 valueLit      :: s -> Lit -> IO Int
 -- | returns decisionLevel
 decisionLevel :: s -> IO Int

instance SolverState Solver where
 nVars = size . assigns
 nAssigns = size . trail
 nConstraints = size . constrs
 nLearnts = size . learnts
 valueVar s x = assigns s .! (x - 1)
 valueLit s p@(signum -> (-1)) = negate <$> (assigns s .! (var p - 1))
 valueLit s p@(signum -> 1)    = assigns s .! (var p - 1)
 decisionLevel = size . trailLim

-- | constructor
newSolver :: IO Solver
newSolver = do
  _model      <- newVec
  _constrs    <- newVec
  _learnts    <- newVec
  _claInt     <- newIORef 0
  _claDecay   <- newIORef 0
  _activities <- newVec
  _varInc     <- newIORef 0
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
addClause :: Solver -> [Lit] -> IO Bool
addClause s@Solver{..} literals = do
  vecLits <- newFromList literals
  result <- clauseNew s vecLits False
  case result of
   (False, _) -> return False   -- Conflict occured
   (True, c)  -> do
     eq <- c <==> nullClause
     unless eq $ push constrs c
     return True                -- No conflict

-- function on "Solver"

-- | __Fig. 9 (p.14)__
-- Propagates all enqueued facts. If a conflict arises, the /conflicting/
-- clause is returned, otherwise @nullClause@ (instead of Null).
--
-- `propagate` is invoked by `search`,`simpleDB` and `solve`
propagate :: Solver -> IO Clause
propagate s@Solver{..} = do
  let
    loop = do
      k <- size propQ
      if k == 0
        then return nullClause -- Nothing
        else do
            p <- dequeue propQ
            tmp <- newVec
            w <- watches .! index p
            moveTo w tmp
            let
              for i = do
                k <- size tmp
                if i < k
                  then do
                      c <- tmp .! i
                      x <- propagateLit c s p
                      if not x
                        then do
                            -- Constraint is conflicting; copy remaining watches to 'watches[p]'
                            -- and return constraint:
                            nt <- subtract 1 <$> size tmp
                            forM_ [i + 1 .. nt] $ \j -> push <$> (watches .! index p) <*> (tmp .! j)
                            clear propQ
                            return =<< tmp .! i
                        else for $ i + 1
                  else loop
            for 0
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
  n <- nVars s
  seen <- (newVecSizedWith n False :: IO (VecOf Bool))
  pReason <- newVec
  learnt `push` 0               -- leave room for the asserting literal
  let
    loop p confl counter btLevel = do
      -- invariant here: @confl /= nullClause@
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
  c <==> nullClause >>= (`unless` push learnts c)

-- | __Fig. 12. (p.17)__
-- unbinds the last variable on the trail.
undoOne :: Solver -> IO ()
undoOne s@Solver{..} = do
  p <- lastE trail
  let x = var p - 1
  setAt assigns x lBottom
  setAt reason  x nullClause
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
-- returns @False@ if immediate confilct.
--
-- __Pre-condition:__ propagation queue is empty
assume :: Solver -> Lit -> IO Bool
assume s@Solver{..} p = do
  push trailLim =<< size trail
  enqueue s p nullClause

-- | __Fig. 12 (p.17)__
-- reverts to the state before last "push".
--
-- __Pre-condition:__ propagation queue is empty.
cancel :: Solver -> IO ()
cancel s@Solver{..} = do
  let
    for c = unless (c == 0) $ do { undoOne s; for $ c - 1 }
  st <- size trail
  tl <- lastE trailLim
  for $ st - tl
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
search :: Solver -> Int -> Int -> (Double, Double) -> IO LBool
search s@Solver{..} nofConflicts nofLearnts (a, b) = do
  let
    varDecay = 1 / a
    claDecay = 1 / b
  clear model
  let
    loop conflictC = do
      !confl <- propagate s
      neq <- not <$> confl <==> nullClause
      if neq
        then do
            -- CONFLICT
            d <- decisionLevel s
            r <- readIORef rootLevel
            if d == r
              then return lFalse
              else do
                  learntClause <- newVec
                  backtrackLevel <- analyze s confl learntClause
                  (s `cancelUntil`) . max backtrackLevel =<< readIORef rootLevel
                  (s `record`) learntClause
                  decayActivities s
                  loop $ conflictC + 1
        else do                 -- NO CONFLICT
            d <- decisionLevel s
            -- Simplify the set of problem clauses:
            when (d == 0) $ do simplifyDB s ; return () -- our simplifier cannot return @False@ here
            k1 <- size learnts
            k2 <- nAssigns s
            when (k1 - k2 >= nofLearnts) $ reduceDB s -- Reduce the set of learnt clauses
            k3 <- nVars s
            case () of
             _ | k2 == k3 -> do
                   -- Model found:
                   (model `growTo`) k3
                   nv <- nVars s
                   forM_ [0 .. nv - 1] $ \i -> setAt model i =<< (lTrue ==) <$> assigns .! i
                   return lTrue
             _ | conflictC >= nofConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< readIORef rootLevel -- force a restart
                   return lBottom
             _ -> do
               -- New variable decision:
               p <- select order -- many have heuristic for polarity here
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
  modifyIORef varInc (* d)

-- | __Fig. 14 (p.19)__
varRescaleActivity :: Solver -> IO ()
varRescaleActivity s@Solver{..} = do
  nv <- subtract 1 <$> nVars s
  forM_ [0 .. nv] $ \i -> setAt activities i =<< (1e-100 *) <$>  activities .! i
  modifyIORef varInc (* 1e-100)

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
  modifyIORef claInc (* d)

-- | __Fig. 14 (p.19)__
claRescaleActivity :: Solver -> IO ()
claRescaleActivity s@Solver{..} = do
  nc <- subtract 1 <$> nLearnts s
  forM_ [0 .. nc] $ \i -> do
    a <- activity <$> learnts .! i
    writeIORef a . (1e-100 *) =<< readIORef a
  modifyIORef claInc (* 1e-100)

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
  n <- fromIntegral <$> size learnts
  ci <- readIORef claInc
  let
    lim = ci / n
  n2 <- (`div` 2) <$> size learnts
  let
    for i@((< n2) -> False) j = return (i, j)
    for i j = do
      c <- learnts .! i
      lk <- locked c s
      if not lk
        then do remove c s; for (i + 1) j
        else do setAt learnts j c; for (i + 1) (j + 1)
  (i, j) <- for 0 0
  n <- size learnts
  let
    for i@((< n) -> False) j = return (i, j)
    for i j = do
      c <- learnts .! i
      lk <- locked c s
      a <- readIORef $ activity c
      if not lk && a < lim
        then do remove c s; for (i + 1) j
        else do setAt learnts j c; for (i + 1) (j + 1)
  (i, j) <- for i j
  shrink (i - j) learnts
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
  n <- p <==> nullClause
  if not n
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
                c <- cs .! i
                x <- simplify c s
                if x
                  then do remove c s; for2 (i + 1) j
                  else do setAt cs j c; for2 (i + 1) (j + 1)
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
  writeIORef varDecay 0.95
  writeIORef claDecay 0.999
  nc <- fromIntegral <$> nConstraints s
  -- PUSH INCREMENTAL ASSUMPTIONS:
  k <- size assumps
  let
    for i@((< k) -> False) = return True
    for i = do
      a <- assumps .! i
      b <- assume s a
      if not b
        then do cancelUntil s 0; return False
        else do
            c <- propagate s
            n <- c <==> nullClause
            if not n
              then do cancelUntil s 0; return False
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
          while status nofConflicts nofLearnts = do
            status <- search s (fromEnum . fromRational $ nofConflicts) (fromEnum . fromRational $ nofLearnts) (0.95, 0.999)
            while status (1.5 * nofConflicts) (1.1 * nofLearnts)
        while lBottom 100 (nc / 3)

-- | - 4.2 Constraints
--
-- __Constructor.__ The 'constructor' may only be called at the top-level.
-- It must create and add the constraint to appropriate watcher lists
-- after enqueuing any unit information derivable under the current
-- top-level assignment. Should a conflict arise, this must be
-- communicated to the caller.
class BoolConstraint c where
  -- | __Remove.__ The 'remove' method supplants the destructor by receiving
  -- the solver state as a parameter. It should dispose the constraint and
  -- remove it from the watcher lists.
  remove :: c -> Solver -> IO ()

  -- | __Propagate.__ The 'propagateLit' method is called if the constraint is found
  -- in a watcher list during propagation of unit information /p/. The constraint
  -- is removed from the list and is required to insert itself into a new or
  -- the same watcher list. Any unit information derivable as a consequence of /p/
  -- should enqueued. If successful, @True@ is returned; if a conflict is detected,
  -- @False@ is returned. The constraint may add itself to the undo list of @var(p)@
  -- if it needs to be updated when /p/ becomes unbound.
  propagateLit :: c -> Solver -> Lit -> IO Bool

  -- | __Simplify.__ At the top-level, a constraint may be given the opportunity to
  -- simplify its representation (returns @False@) or state that the constraint is
  -- satisfied under the current assignment and can be removed (returns @True@).
  -- A constraint must /not/ be simplifiable to produce unit information or to be
  -- conflicting; in that case the propagation has not been correctly defined.
  simplify :: c -> Solver -> IO Bool
  -- defaults to return false
  simplify _ _ = return False

  -- | __Undo.__ During backtracking, this method is called if the cons taint added itself
  -- to the undo list of /var(p)/ in 'propagateLit'.The current variable assignments are
  -- guaranteed to be identical to that of the moment before 'propagateLit' was called.
  undoConstraint :: c -> Solver -> Lit -> IO ()
  -- defaults to do nothing
  undoConstraint _ _ _ = return ()

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
  calcReason :: c -> Solver -> Lit -> VecOf Lit -> IO ()

-- | __Fig. 7.(p.11)__
-- Clause
data Clause = Clause
              {
                learnt   :: Bool         -- ^ whether this is a learnt clause
              , activity :: IORef Double -- ^ activity of this clause
              , lits     :: VecOf Lit       -- ^ which this clause consists of
              }

-- | for debug
dumpClause :: Clause -> IO String
dumpClause !c@Clause{..} = do
  let eq1 = learnt == False
  eq2 <- c <==> nullClause
  if eq1 && eq2
    then return "NullClause"
    else do
        a <- show <$> readIORef activity
        l <- dump "lits" lits
        return $ "Clause{" ++ intercalate "," [show learnt, a :: String, l] ++ "}"

-- | Haskell-style alternative for NULL
nullClause :: Clause
nullClause = Clause False undefined undefined -- these @undefined@ is place holders.

newLearntClause :: IO Clause
newLearntClause = do
    a <- newIORef 0
    e <- emptyVec
    return $ Clause True a e

instance BoolConstraint Clause where
  -- | constraint interface
  remove c@Clause{..} s@Solver{..} = do
    removeElem c =<< (watches .!) . index . negate =<< lits .! 0
    removeElem c =<< (watches .!) . index . negate =<< lits .! 1
    -- c should be deleted here
    return ()
  -- | only called at top level with prop. queue
  simplify c@Clause{..} s@Solver{..} = do
    n <- size lits
    let
      loop ((< n) -> False) j = do
        shrink (n - j) lits
        return False
      loop i j = do
        l <- lits .! i
        v <- valueLit s l
        case v of
         lTrue   -> return True
         lBottom -> do
           setAt lits j l	-- false literals are not copied (only occur for i >= 2)
           loop (i+1) (j+1)
         _ -> loop (i+1) j
    loop 0 0
  -- | returns @True@ if no conflict occured
  -- this is invoked by 'propagate'
  propagateLit c@Clause{..} s@Solver{..} p = do
    -- Make sure the false literal is lits[1]:
    l <- lits .! 0
    cs <- dumpClause c
    when (l == negate p) $ do { l' <- lits .! 1; setAt lits 0 l'; setAt lits 1 (negate p) }
    -- If 0th watch is True, then clause is already satisfied.
    l0 <- lits .! 0
    val <- valueLit s l0
    if val == lTrue
      then do
          watches .! index p >>= (`push` c) -- re-insert clause into watcher list
          return True
      else do
          -- Look for a new literal to watch:
          n <- size lits
          let
            loop ((< n) -> False) = do
              -- Clause is unit under assignment:
              watches .! index p >>= (`push` c)
              l <- lits .! 0
              enqueue s l c
            loop i = do
              l <- lits .! i
              val <- valueLit s l
              if val /= lFalse
                then do
                    setAt lits 1 l
                    setAt lits i (negate p)
                    (`push` c) =<< watches .! index (negate l) -- insert clause into watcher list
                    return True
                else loop $ i + 1
          loop 2
  -- The literal /p/ is also allowed to be the special constant 'bottomLit'
  -- in which case the reason for the clause being conflicting should be
  -- returned through the vector: @outReason@.
  --
  -- __invaliand__ @c /= nullClause@
  calcReason c s@Solver{..} p outReason = do
    -- invariant: (p == bottomLit) || (p == lits[0])
    when (learnt c == learnt nullClause) $ do
      eq <- c <==> nullClause
      when eq $ error $ "calcReason can't handle nullClause; p = " ++ show p
    n <- size (lits c)
    let
      loop ((< n) -> False) = return ()
      loop i = do
        push outReason . negate =<< (lits c) .! i -- invariant: S.value(lits[i]) == lFalse
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
  unless learnt $ do
    ls' <- asList ps
    let ls = nub ls'
    cond1 <- or <$> mapM (\l -> (lTrue ==) <$> valueLit s l) ls -- any literal in ps is true
    let cond2 = any (flip elem ls) (map negate ls) -- both p and negate p occurs in ps
    when (cond1 || cond2) $ error "cond* holds!!"  -- return (True, nullClause)
    -- remove all duplicatates from ps
    -- remove all false literals from ps
    l' <- filterM (\l -> (lFalse /=) <$> valueLit s l) ls
    clear ps
    forM_ l' $ push ps
  k <- size ps
  case k of
   0 -> return (False, nullClause)
   1 -> do
     l <- ps .! 0
     (\x -> (x, nullClause)) <$> enqueue s l nullClause
   otherwise -> do
     -- allocate clause:
     ptr <- newIORef 0
     writeIORef ptr 0
     let c = Clause learnt ptr ps
     when learnt $ do
       -- Pick a second literal to watch:
       let
         findMax i@((< k) -> False) j val = return j
         findMax i j val = do
           l' <- var <$> ps .! i
           a <- assigns .! (l' - 1)
           b <- level .! (l' - 1)
           if (a /= lBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       -- Let @max_i@ be the index of the literal with highest decision level
       max_i <- findMax 0 0 0
       tmp <- lits c .! 1
       setAt (lits c) 1 =<< ps .! max_i
       setAt (lits c) max_i tmp   -- OLD: setAt (lits c) max_i =<< ps .! 1
       -- check literals occurences
       x <- asList (lits c)
       unless (length x == length (nub x)) $ error "new clause contains a element doubly"
       -- Bumping:
       claBumpActivity s c -- newly learnt clauses should be considered active
       n <- subtract 1 <$> size ps
       forM_ [0 .. n] $ varBumpActivity s . var <=< (ps .!) -- variables in conflict clauses are bumped
     -- Add clause to watcher lists:
     l0 <- lits c .! 0
     l1 <- lits c .! 1
     (`push` c) =<< (watches .!) . index . negate =<< lits c .! 0
     (`push` c) =<< (watches .!) . index . negate =<< lits c .! 1
     return (True, c)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
locked :: Clause -> Solver -> IO Bool
locked c@Clause{..} Solver{..} = do
  v <- var <$> lits .! 0
  c' <- reason .! (v - 1)
  c <==> c'

---- C-ish statement
-- | a monadic iteration trying its condition after the body
doWhile :: IO Bool -> IO a -> IO a
doWhile cond body = do { res <- body; whileCond <- cond; if whileCond then doWhile cond body else return res }

-- | __Fig. 17. (p.23)__
-- The static variable ordering of "SATZOO". The code is defined only for clauses, not for
-- arbitrary constraints. It must be adapted before it can be used in MINISAT.
staticVarOrder :: Solver -> IO ()
staticVarOrder s@Solver{..} = do
  let clauses = constrs
  -- CLEAR ACTIVITY:
  nv <- nVars s
  forM_ [0 .. nv - 1] $ \i -> setAt activities i 0
  -- DO SIMPLE VARIABLE ACTIVITY HEURISTICS:
  nc <- size clauses
  forM_ [0 .. nc - 1] $ \i -> do
    c <- lits <$> clauses .! i
    m <- size c
    let a = 2 ** fromIntegral (negate m)
    forM_ [0 .. m - 1] $ \j -> do
      k <- var <$> c .! j
      setAt activities k . (a +) =<< activities .! k
  -- CALCULATE THE INITIAL "HEAD" OF ALL CLAUSES:
  occurs <- newVecSizedWith (2 * nv) =<< emptyVec
  heat   <- newVecSizedWith nc (0.0 :: Double,0 :: Int)
  forM_ [0 .. nc - 1] $ \i -> do
    c <- clauses .! i
    cs <- subtract 1 <$> size (lits c)
    x <- sum <$> forM [0 .. cs] (\j -> do
                                    l <- lits c .! j
                                    (`push` i) =<< (occurs :: VecOf (VecOf Int)) .! index l
                                    -- return (0::Double)
                                    activities .! (var l - 1)
                                )
    setAt (heat :: VecOf (Double, Int)) i (x, i)
  -- BUMP HEAT FOR CLAUSES WHOSE VARIABLES OCCUR IN OTHER HOT CLAUSES:
  iterSize <- sum <$>
              forM [0 .. nc - 1] (\i -> do
                                     c <- lits <$> clauses .! i
                                     n <- subtract 1 <$> size c
                                     sum <$> forM [0 .. n] (((size =<<) . (occurs .!) . index) <=< (c .!))
                                 )
  let literals = 2 * nv
  let iterations = min (10 :: Int) . fromEnum $ fromRational (100.0 * fromIntegral literals / fromIntegral iterSize)
  let disapation = (1.0 :: Double) / fromIntegral iterations
  forM_ [0 .. iterations - 1] $ \_ ->
    forM_ [0 .. nc - 1] $ \i -> do
      c <- lits <$> clauses .! i
      nl <- subtract 1 <$> size c
      forM_ [0 ..nl] $ \j -> do
        os <- (occurs .!) =<< index <$> c .! j
        m <- subtract 1 <$> size os
        forM_ [0 .. m] $ \k -> do
          (iv, ii) <- heat .! i
          z <- os .! k
          y <- fst <$> heat .! z
          setAt heat i (iv + y * disapation, ii)
  -- SET ACTIVITIES ACCORDING TO HOT CLAUSES:
  -- @sort(heat)@
  sortByFst heat
  forM_ [0 .. nv] $ \i -> setAt activities i 0
  hs <- size heat
  let
    for i@((< hs) -> False) _ = return ()
    for i extra = do
      h <- heat .! i
      c <- lits <$> clauses .! snd h
      cs <- size c
      let
        for2 j@((< cs) -> False) extra = return extra
        for2 j extra = do
          v <- var <$> c .! j
          a <- activities .! v
          if a == 0
            then do { setAt activities v extra; for2 (j + 1) (extra * 0.995) }
            else for2 (j + 1) extra
      extra <- for2 0 extra
      for (i + 1) extra
  for 0 1e200
  updateAll order
  writeIORef varInc 1

-- | Another basic implementation
-- all method but select is nop code.
instance VarOrder Solver where
  -- | __Fig. 6. (p.10)__
  -- Creates a new SAT variable in the solver.
  newVar s@Solver{..} = do
    index <- nVars s
    push watches =<< newVec      -- push'
    push watches =<< newVec      -- push'
    push undos =<< newVec        -- push'
    push reason nullClause       -- push'
    push assigns lBottom
    push level (-1)
    push activities (0.0 :: Double)
    newVar order
    return index
  updateAll Solver{..} = updateAll order


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
    staticVarOrder solver
    -- then, search and return a bottom-ed var
    nv <- nVars solver
    let
      loop ((< nv) -> False) = error "no unassigned variable left"
      loop i = do
        x <- assigns solver .! i
        if x == lBottom
          then return $ i + 1   -- NOTE: i is not 1-based 'Var' but 0-based var-index
          else loop $ i + 1
    loop 0

numVec :: Int -> VecOf Int -> IO [Int]
numVec base v = zipWith (*) [base ..] <$> asList v

dumpStatus :: Solver -> IO ()
dumpStatus Solver{..} = do
  putStrLn . ("assign: " ++) . show =<< numVec 1 assigns
  putStrLn . ("level: " ++) . show . filter ((0 <=) . snd) . zip [1..] =<< asList level
  putStrLn =<< dump "trail: " trail
  putStrLn =<< dump "trailLim: " trailLim
  -- mapM_ (\(x, y) -> putStrLn (show x ++ " : " ++ y)) =<< mapM (\(x,y) -> (\z-> (x, z)) <$> dumpClause y) =<< filter (not . isNull . snd) . zip [1 .. ] <$> asList reason
  -- putStrLn =<< makeGraph <$> asList trail <*> fromReason reason

fromReason :: VecOf Clause -> IO [(Int, [Int])]
fromReason vec = do
  l <- zip [1..] <$> asList vec
  let
    asList' :: Clause -> IO [Int]
    --  asList' (isNull -> True) = return []
    asList' Clause{..} = asList lits
    f (i, c) = (i, ) <$> asList' c
  mapM f l
