{-# LANGUAGE
    BangPatterns
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | This is a part of MIOS; main data
module SAT.Solver.Mios.Solver
       (
         -- * Solver
         Solver (..)
       , newSolver
         -- * Misc Accessors
       , nAssigns
       , nClauses
       , nLearnts
       , decisionLevel
       , valueVar
       , valueLit
       , locked
       , VarHeap
         -- * State Modifiers
       , addClause
       , enqueue
       , assume
       , cancelUntil
       , getModel
         -- * Activities
       , claBumpActivity
       , claDecayActivity
       , claRescaleActivityAfterRestart
       , varBumpActivity
       , varDecayActivity
       , claActivityThreshold
         -- * Stats
       , StatIndex (..)
       , getStat
       , setStat
       , incrementStat
       , getStats
       )
        where

import Control.Monad ((<=<), forM_, unless, when)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.ClauseManager

-- | __Fig. 2.(p.9)__ Internal State of the solver
data Solver = Solver
              {
                -- Public Interface
                model      :: !VecBool           -- ^ If found, this vector has the model
              , conflict   :: !Stack             -- ^ set of literals in the case of conflicts
                -- Clause Database
              , clauses    :: !ClauseExtManager  -- ^ List of problem constraints.
              , learnts    :: !ClauseExtManager  -- ^ List of learnt clauses.
              , watches    :: !WatcherList       -- ^ a list of constraint wathing 'p', literal-indexed
                -- Assignment Management
              , assigns    :: !Vec               -- ^ The current assignments indexed on variables; var-indexed
              , phases     :: !Vec               -- ^ The last assignments indexed on variables; var-indexed
              , trail      :: !Stack             -- ^ List of assignments in chronological order; var-indexed
              , trailLim   :: !Stack             -- ^ Separator indices for different decision levels in 'trail'.
              , qHead      :: !IntSingleton      -- ^ 'trail' is divided at qHead; assignments and queue
              , reason     :: !ClauseVector      -- ^ For each variable, the constraint that implied its value; var-indexed
              , level      :: !Vec               -- ^ For each variable, the decision level it was assigned; var-indexed
                -- Variable Order
              , activities :: !VecDouble         -- ^ Heuristic measurement of the activity of a variable; var-indexed
              , order      :: !VarHeap           -- ^ Keeps track of the dynamic variable order.
                -- Configuration
              , config     :: !MiosConfiguration -- ^ search paramerters
              , nVars      :: !Int               -- ^ number of variables
              , claInc     :: !DoubleSingleton   -- ^ Clause activity increment amount to bump with.
--            , varDecay   :: !DoubleSingleton   -- ^ used to set 'varInc'
              , varInc     :: !DoubleSingleton   -- ^ Variable activity increment amount to bump with.
              , rootLevel  :: !IntSingleton      -- ^ Separates incremental and search assumptions.
                -- Working Memory
              , ok         :: !BoolSingleton     -- ^ return value holder
              , an'seen    :: !Vec               -- ^ scratch var for 'analyze'; var-indexed
              , an'toClear :: !Stack             -- ^ ditto
              , an'stack   :: !Stack             -- ^ ditto
              , pr'seen    :: !Vec               -- ^ used in propagate
--              , lbd'seen   :: !Vec               -- ^ used in lbd computation
--              , lbd'key    :: !IntSingleton      -- ^ used in lbd computation
              , litsLearnt :: !Stack             -- ^ used to create a learnt clause
              , lastDL     :: !Stack             -- ^ last decision level used in analyze
              , stats      :: !Vec               -- ^ statistics information holder
              }

-- | returns an everything-is-initialized solver from the arguments
newSolver :: MiosConfiguration -> CNFDescription -> IO Solver
newSolver conf (CNFDescription nv nc _) = do
  Solver
    -- Public Interface
    <$> newVecBool nv False                           -- model
    <*> newStack nv                                   -- coflict
    -- Clause Database
    <*> newManager nc                                 -- clauses
    <*> newManager nc                                 -- learnts
    <*> newWatcherList nv 2                           -- watches
    -- Assignment Management
    <*> newVecWith (nv + 1) lBottom                   -- assigns
    <*> newVecWith (nv + 1) lBottom                   -- phases
    <*> newStack nv                                   -- trail
    <*> newStack nv                                   -- trailLim
    <*> newInt 0                                      -- qHead
    <*> newClauseVector (nv + 1)                      -- reason
    <*> newVecWith (nv + 1) (-1)                      -- level
    -- Variable Order
    <*> newVecDouble (nv + 1) 0                       -- activities
    <*> newVarHeap nv                                 -- order
    -- Configuration
    <*> return conf                                   -- config
    <*> return nv                                     -- nVars
    <*> newDouble 1.0                                 -- claInc
--  <*> newDouble (variableDecayRate conf)            -- varDecay
    <*> newDouble 1.0                                 -- varInc
    <*> newInt 0                                      -- rootLevel
    -- Working Memory
    <*> newBool True                                  -- ok
    <*> newVec (nv + 1)                               -- an'seen
    <*> newStack nv                                   -- an'toClear
    <*> newStack nv                                   -- an'stack
    <*> newVecWith (nv + 1) (-1)                      -- pr'seen
--    <*> newVec nv                                     -- lbd'seen
--    <*> newInt 0                                      -- lbd'key
    <*> newStack nv                                   -- litsLearnt
    <*> newStack nv                                   -- lastDL
    <*> newVec (1 + fromEnum (maxBound :: StatIndex)) -- stats

--------------------------------------------------------------------------------
-- Accessors

-- | returns the number of current assigments
{-# INLINE nAssigns #-}
nAssigns :: Solver -> IO Int
nAssigns = sizeOfStack . trail

-- | returns the number of constraints (clauses)
{-# INLINE nClauses #-}
nClauses  :: Solver -> IO Int
nClauses = numberOfClauses . clauses

-- | returns the number of learnt clauses
{-# INLINE nLearnts #-}
nLearnts :: Solver -> IO Int
nLearnts = numberOfClauses . learnts

-- | return the model as a list of literal
getModel :: Solver -> IO [Int]
getModel s = zipWith (\n b -> if b then n else negate n) [1 .. ] <$> asList (model s)

-- | returns the current decision level
{-# INLINE decisionLevel #-}
decisionLevel :: Solver -> IO Int
decisionLevel Solver{..} = sizeOfStack trailLim

-- | returns the assignment (:: 'LiftedBool' = @[-1, 0, -1]@) from 'Var'
{-# INLINE valueVar #-}
valueVar :: Solver -> Var -> IO Int
valueVar s !x = getNth (assigns s) x

-- | returns the assignment (:: 'LiftedBool' = @[-1, 0, -1]@) from 'Lit'
{-# INLINE valueLit #-}
valueLit :: Solver -> Lit -> IO Int -- FIXME: LiftedBool
valueLit Solver{..} !p = if positiveLit p then getNth assigns (lit2var p) else negate <$> getNth assigns (lit2var p)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
{-# INLINE locked #-}
locked :: Solver -> Clause -> IO Bool
locked Solver{..} c@Clause{..} =  (c ==) <$> (getNthClause reason . lit2var =<< getNth lits 1)

-------------------------------------------------------------------------------- Statistics

-- | stat index
data StatIndex =
    NumOfBackjump
  | NumOfRestart
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | returns the value of 'StatIndex'
getStat :: Solver -> StatIndex -> IO Int
getStat (stats -> v) (fromEnum -> i) = getNth v i

-- | sets to 'StatIndex'
setStat :: Solver -> StatIndex -> Int -> IO ()
setStat (stats -> v) (fromEnum -> i) x = setNth v i x

-- | increments a stat data corresponding to 'StatIndex'
incrementStat :: Solver -> StatIndex -> Int -> IO ()
incrementStat (stats -> v) (fromEnum -> i) k = modifyNth v (+ k) i

-- | returns the statistics as list
getStats :: Solver -> IO [(StatIndex, Int)]
getStats (stats -> v) = mapM (\i -> (i, ) <$> getNth v (fromEnum i)) [minBound .. maxBound :: StatIndex]

-------------------------------------------------------------------------------- State Modifiers

-- | returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses.
{-# INLINABLE addClause #-}
addClause :: Solver -> Vec -> IO Bool
addClause s@Solver{..} vecLits = do
  result <- clauseNew s vecLits False
  case result of
   (False, _) -> return False   -- Conflict occured
   (True, c)  -> do
     unless (c == NullClause) $ pushClause clauses c
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
clauseNew s@Solver{..} ps isLearnt = do
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
    if isLearnt then loopForLearnt 1 else loop 1
  k <- getNth ps 0
  case k of
   0 -> return (exit, NullClause)
   1 -> do
     l <- getNth ps 1
     (, NullClause) <$> enqueue s l NullClause
   _ -> do
     -- allocate clause:
     c <- newClauseFromVec isLearnt ps
     let vec = asVec c
     when isLearnt $ do
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
       -- Let @max_i@ be the index of the literal with highest decision level
       max_i <- findMax 0 0 0
       swapBetween vec 1 max_i
       -- check literals occurences
       -- x <- asList c
       -- unless (length x == length (nub x)) $ error "new clause contains a element doubly"
       -- Bumping:
       claBumpActivity s c . fromIntegral =<< decisionLevel s -- newly learnt clauses should be considered active
       forM_ [0 .. k -1] $ varBumpActivity s . lit2var <=< getNth vec -- variables in conflict clauses are bumped
     -- Add clause to watcher lists:
     l0 <- negateLit <$> getNth vec 0
     pushClauseWithKey (getNthWatcher watches l0) c 0
     l1 <- negateLit <$> getNth vec 1
     pushClauseWithKey (getNthWatcher watches l1) c 0
     return (True, c)

-- | __Fig. 9 (p.14)__
-- Puts a new fact on the propagation queue, as well as immediately updating the variable's value
-- in the assignment vector. If a conflict arises, @False@ is returned and the propagation queue is
-- cleared. The parameter 'from' contains a reference to the constraint from which 'p' was
-- propagated (defaults to @Nothing@ if omitted).
{-# INLINABLE enqueue #-}
enqueue :: Solver -> Lit -> Clause -> IO Bool
enqueue s@Solver{..} p from = do
{-
  -- bump psedue lbd of @from@
  when (from /= NullClause && learnt from) $ do
    l <- getInt (lbd from)
    k <- (12 +) <$> decisionLevel s
    when (k < l) $ setInt (lbd from) k
-}
  -- putStrLn . ("ssigns " ++) . show . map lit2int =<< asList trail
  -- putStrLn =<< dump ("enqueue " ++ show (lit2int p) ++ " ") from
  let signumP = if positiveLit p then lTrue else lFalse
  let v = lit2var p
  val <- valueVar s v
  if val /= lBottom
    then do -- Existing consistent assignment -- don't enqueue
        return $ val == signumP
    else do
        -- New fact, store it
        setNth assigns v $! signumP
        setNth level v =<< decisionLevel s
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
  enqueue s p NullClause

-- | #M22: Revert to the states at given level (keeping all assignment at 'level' but not beyond).
{-# INLINABLE cancelUntil #-}
cancelUntil :: Solver -> Int -> IO ()
cancelUntil s@Solver{..} lvl = do
  dl <- decisionLevel s
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
        setNth phases x =<< getNth assigns x
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

-------------------------------------------------------------------------------- VarOrder

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
  update = increaseHeap
  {-# SPECIALIZE INLINE undo :: Solver -> Var -> IO () #-}
  undo s v = inHeap s v >>= (`unless` insertHeap s v)
  {-# SPECIALIZE INLINE select :: Solver -> IO Var #-}
  select s = do
    let
      asg = assigns s
      -- | returns the most active var (heap-based implementation)
      loop :: IO Var
      loop = do
        n <- numElementsInHeap s
        if n == 0
          then return 0
          else do
              v <- getHeapRoot s
              x <- getNth asg v
              if x == lBottom then return v else loop
    loop

-------------------------------------------------------------------------------- Activities

varActivityThreshold :: Double
varActivityThreshold = 1e100

claActivityThreshold :: Double
claActivityThreshold = 1e20

-- | __Fig. 14 (p.19)__ Bumping of clause activity
{-# INLINE varBumpActivity #-}
varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity s@Solver{..} !x = do
  !a <- (+) <$> getNthDouble x activities <*> getDouble varInc
  setNthDouble x activities a
  when (varActivityThreshold < a) $ varRescaleActivity s
  update s x                    -- update the position in heap

-- | __Fig. 14 (p.19)__
{-# INLINE varDecayActivity #-}
varDecayActivity :: Solver -> IO ()
varDecayActivity Solver{..} = modifyDouble varInc (/ variableDecayRate config)
-- varDecayActivity Solver{..} = modifyDouble varInc . (flip (/)) =<< getDouble varDecay

-- | __Fig. 14 (p.19)__
{-# INLINE varRescaleActivity #-}
varRescaleActivity :: Solver -> IO ()
varRescaleActivity Solver{..} = do
  forM_ [1 .. nVars] $ \i -> modifyNthDouble i activities (/ varActivityThreshold)
  modifyDouble varInc (/ varActivityThreshold)

-- | __Fig. 14 (p.19)__
{-# INLINE claBumpActivity #-}
claBumpActivity :: Solver -> Clause -> Double -> IO ()
claBumpActivity s Clause{..} k = do
  a <- (+ k) <$> getDouble activity
  setDouble activity a
  -- setBool protected True
  when (claActivityThreshold <= a) $ claRescaleActivity s

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
      modifyDouble (activity c) (/ claActivityThreshold)
      loopOnVector $ i + 1
  loopOnVector 0
  modifyDouble claInc (/ claActivityThreshold)

-- | __Fig. 14 (p.19)__
{-# INLINE claRescaleActivityAfterRestart #-}
claRescaleActivityAfterRestart :: Solver -> IO ()
claRescaleActivityAfterRestart Solver{..} = do
  vec <- getClauseVector learnts
  n <- numberOfClauses learnts
  let
    loopOnVector :: Int -> IO ()
    loopOnVector ((< n) -> False) = return ()
    loopOnVector i = do
      c <- getNthClause vec i
      d <- sizeOfClause c
      if d < 9
        then modifyDouble (activity c) sqrt
        else setDouble (activity c) 0
      setBool (protected c) False
      loopOnVector $ i + 1
  loopOnVector 0

-------------------------------------------------------------------------------- VarHeap

-- | 'VarHeap' is a heap tree built from two 'Vec'
-- This implementation is identical wtih that in Minisat-1.14
-- Note: the zero-th element of @heap@ is used for holding the number of elements
-- Note: VarHeap itself is not a @VarOrder@, because it requires a pointer to solver
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

{-# INLINE increaseHeap #-}
increaseHeap :: Solver -> Int -> IO ()
increaseHeap s@(order -> idxs -> at) n = inHeap s n >>= (`when` (percolateUp s =<< getNth at n))

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
        then setNth to i v >> setNth at v i -- end
        else do
            v' <- getNth to iP
            acP <- getNthDouble v' activities
            if ac > acP
              then setNth to i v' >> setNth at v' i >> loop iP -- loop
              else setNth to i v >> setNth at v i              -- end
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
              else setNth to i v >> setNth at v i -- end
        else setNth to i v >> setNth at v i       -- end
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
