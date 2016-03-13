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

module SAT.Solver.Mios.Solver
       (
         -- * Solver
         Solver (..)
       , newSolver
         -- * Misc Accessors
       , nAssigns
       , nConstraints
       , nLearnts
       , valueVar
       , valueLit
       , locked
         -- * State Modifiers
       , setInternalState
       , addClause
       , enqueue
       , assume
       , cancelUntil
         -- * Activities
       , claBumpActivity
       , claDecayActivity
       , varBumpActivity
       , varDecayActivity
       )
        where

import Control.Monad ((<=<), forM_, unless, when)
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
                -- Assignments
              , assigns       :: Vec               -- ^ The current assignments indexed on variables; var-indexed
              , trail         :: Stack             -- ^ List of assignments in chronological order; var-indexed
              , trailLim      :: Stack             -- ^ Separator indices for different decision levels in 'trail'.
              , qHead         :: IntSingleton      -- ^ 'trail' is divided at qHead; assignments and queue
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

-- | returns the assignment (:: 'LiftedBool' = @[-1, 0, -1]@) from 'Var'
{-# INLINE valueVar #-}
valueVar :: Solver -> Var -> IO Int
valueVar !s !x = getNth (assigns s) x

-- | returns the assignment (:: 'LiftedBool' = @[-1, 0, -1]@) from 'Lit'
{-# INLINE valueLit #-}
valueLit :: Solver -> Lit -> IO Int -- FIXME: LiftedBool
valueLit !Solver{..} !p = if positiveLit p then getNth assigns (lit2var p) else negate <$> getNth assigns (lit2var p)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
{-# INLINE locked #-}
locked :: Clause -> Solver -> IO Bool
locked !c@Clause{..} !Solver{..} =  (c ==) <$> (getNthClause reason . lit2var =<< getNth lits 1)

-------------------------------------------------------------------------------- State Modifiers

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
  t <- newStack nv
  t' <- newStack nv
  r <- newClauseVector (nv + 1)
  l <- newVecWith (nv + 1) (-1)
  o <- newVarHeap nv
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
            <*> newVec 0            -- assigns
            <*> newStack 0          -- trail
            <*> newStack 0          -- trailLim
            <*> newInt 0            -- qHead
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

-- | returns @False@ if a conflict has occured.
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
              case sat of
               1  -> setNth ps 0 0 >> return True
               -1 -> do
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
        return $ val == signumP
    else do
        -- New fact, store it
        setNth assigns v $! signumP
        d <- getInt decisionLevel
        setNth level v d
        setNthClause reason v from     -- NOTE: @from@ might be NULL!
        pushToStack trail p
        return True

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

-- | #M22: Revert to the states at given level (keeping all assignment at 'level' but not beyond).
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
      loopOnTrail :: Int -> IO ()
      loopOnTrail ((lim <=) -> False) = return ()
      loopOnTrail c = do
        x <- lit2var <$> getNth tr c
        setNth assigns x lBottom
        -- #reason to set reason Null
        -- if we don't clear @reason[x] :: Clause@ here, @reason[x]@ remains as locked.
        -- This means we can't reduce it from clause DB and affects the performance.
        setNthClause reason x NullClause -- 'analyze` uses reason without checking assigns
        -- FIXME: #polarity https://github.com/shnarazk/minisat/blosb/master/core/Solver.cc#L212
        undo s x
        -- insertHeap s x              -- insertVerOrder
        loopOnTrail $ c - 1
    loopOnTrail $ ts - 1
    shrinkStack trail (ts - lim)
    shrinkStack trailLim (ls - lvl)
    setInt qHead =<< sizeOfStack trail
    setInt decisionLevel lvl

-------------------------------------------------------------------------------- VarOrder


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

-------------------------------------------------------------------------------- Activities

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
    else setDouble activity a

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
