-- | This is a part of MIOS.
{-# LANGUAGE
    BangPatterns
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | This is a part of MIOS; main data
module SAT.Mios.Solver
       (
         -- * Solver
         Solver (..)
       , VarHeap
       , newSolver
       , getModel
         -- * Misc Accessors
       , nAssigns
       , nClauses
       , nLearnts
       , decisionLevel
       , valueVar
       , valueLit
       , locked
         -- * State Modifiers
       , addClause
       , enqueue
       , assume
       , cancelUntil
         -- * Activities
       , claBumpActivity
       , claDecayActivity
--       , claRescaleActivityAfterRestart
--       , claActivityThreshold
       , varBumpActivity
       , varDecayActivity
         -- * Stats
       , StatIndex (..)
       , getStat
       , setStat
       , incrementStat
       , getStats
       )
        where

import Control.Monad (unless, when)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.ClausePool

-- | __Fig. 2.(p.9)__ Internal State of the solver
data Solver = Solver
              {
{-            Public Interface -}
                model      :: !(Vec Int)         -- ^ If found, this vector has the model
              , conflicts  :: !Stack             -- ^ Set of literals in the case of conflicts
{-            Clause Database -}
              , clauses    :: !ClauseExtManager  -- ^ List of problem constraints.
              , learnts    :: !ClauseExtManager  -- ^ List of learnt clauses.
              , watches    :: !WatcherList       -- ^ list of constraint wathing 'p', literal-indexed
{-            Assignment Management -}
              , assigns    :: !(Vec Int)         -- ^ The current assignments indexed on variables
              , phases     :: !(Vec Int)         -- ^ The last assignments indexed on variables
              , trail      :: !Stack             -- ^ List of assignments in chronological order
              , trailLim   :: !Stack             -- ^ Separator indices for different decision levels in 'trail'.
              , qHead      :: !Int'              -- ^ 'trail' is divided at qHead; assignment part and queue part
              , reason     :: !ClauseVector      -- ^ For each variable, the constraint that implied its value
              , level      :: !(Vec Int)         -- ^ For each variable, the decision level it was assigned
{-            Variable Order -}
              , activities :: !(Vec Double)      -- ^ Heuristic measurement of the activity of a variable
              , order      :: !VarHeap           -- ^ Keeps track of the dynamic variable order.
{-            Configuration -}
              , config     :: !MiosConfiguration -- ^ search paramerters
              , nVars      :: !Int               -- ^ number of variables
              , claInc     :: !Double'           -- ^ Clause activity increment amount to bump with.
{-

              -- , varDecay   :: !Double'           -- ^ used to set 'varInc'
-}
              , varInc     :: !Double'           -- ^ Variable activity increment amount to bump with.
              , rootLevel  :: !Int'              -- ^ Separates incremental and search assumptions.
{-            Learnt DB Size Adjustment -}
              , learntSAdj :: Double'            -- ^ used in 'SAT.Mios.Main.search'
              , learntSCnt :: Int'               -- ^ used in 'SAT.Mios.Main.search'
              , maxLearnts :: Double'            -- ^ used in 'SAT.Mios.Main.search'
{-            Working Memory -}
              , ok         :: !Int'              -- ^ /return value/ holder
              , an'seen    :: !(Vec Int)         -- ^ used in 'SAT.Mios.Main.analyze'
              , an'toClear :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze'
              , an'stack   :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze'
              , an'lastDL  :: !Stack             -- ^ last decision level used in 'SAT.Mios.Main.analyze'
              , clsPool    :: ClausePool         -- ^ clause recycler
              , litsLearnt :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze' and 'SAT.Mios.Main.search' to create a learnt clause
              -- , pr'seen    :: !(Vec Int)         -- ^ used in 'SAT.Mios.Main.propagate'
              , stats      :: !(Vec [Int])       -- ^ statistics information holder
              , lbd'seen   :: !(Vec Int)         -- ^ used in lbd computation
              , lbd'key    :: !Int'              -- ^ used in lbd computation
              }

-- | returns an everything-is-initialized solver from the arguments.
newSolver :: MiosConfiguration -> CNFDescription -> IO Solver
newSolver conf (CNFDescription nv dummy_nc _) = do
  Solver
    -- Public Interface
    <$> newVec nv 0                        -- model
    <*> newStack nv                        -- coflict
    -- Clause Database
    <*> newManager dummy_nc                -- clauses
    <*> newManager dummy_nc                -- learnts
    <*> newWatcherList nv 2                -- watches
    -- Assignment Management
    <*> newVec nv LBottom                  -- assigns
    <*> newVec nv LBottom                  -- phases
    <*> newStack nv                        -- trail
    <*> newStack nv                        -- trailLim
    <*> new' 0                             -- qHead
    <*> newClauseVector (nv + 1)           -- reason
    <*> newVec nv (-1)                     -- level
    -- Variable Order
    <*> newVec nv 0                        -- activities
    <*> newVarHeap nv                      -- order
    -- Configuration
    <*> return conf                        -- config
    <*> return nv                          -- nVars
    <*> new' 1.0                           -- claInc
--  <*> new' (variableDecayRate conf)      -- varDecay
    <*> new' 1.0                           -- varInc
    <*> new' 0                             -- rootLevel
    -- Learnt DB Size Adjustment
    <*> new' 100                           -- learntSAdj
    <*> new' 100                           -- learntSCnt
    <*> new' 100                           -- maxLearnts
    -- Working Memory
    <*> new' LiftedT                       -- ok
    <*> newVec nv 0                        -- an'seen
    <*> newStack nv                        -- an'toClear
    <*> newStack nv                        -- an'stack
    <*> newStack nv                        -- an'lastDL
    <*> newClausePool 10                   -- clsPool
--    <*> newVec nv (-1)                     -- pr'seen
    <*> newStack nv                        -- litsLearnt
    <*> newVec (fromEnum EndOfStatIndex) 0 -- stats
    <*> newVec nv 0                        -- lbd'seen
    <*> new' 0                             -- lbd'key

--------------------------------------------------------------------------------
-- Accessors

-- | returns the number of current assigments.
{-# INLINE nAssigns #-}
nAssigns :: Solver -> IO Int
nAssigns = get' . trail

-- | returns the number of constraints (clauses).
{-# INLINE nClauses #-}
nClauses :: Solver -> IO Int
nClauses = get' . clauses

-- | returns the number of learnt clauses.
{-# INLINE nLearnts #-}
nLearnts :: Solver -> IO Int
nLearnts = get' . learnts

-- | returns the model as a list of literal.
getModel :: Solver -> IO [Int]
getModel = (tail <$>) . asList . model

-- | returns the current decision level.
{-# INLINE decisionLevel #-}
decisionLevel :: Solver -> IO Int
decisionLevel = get' . trailLim

-- | returns the assignment (:: 'LiftedBool' = @[-1, 0, -1]@) from 'Var'.
{-# INLINE valueVar #-}
valueVar :: Solver -> Var -> IO Int
valueVar = getNth . assigns

-- | returns the assignment (:: 'LiftedBool' = @[-1, 0, -1]@) from 'Lit'.
{-# INLINE valueLit #-}
valueLit :: Solver -> Lit -> IO Int
valueLit (assigns -> a) p = (\x -> if positiveLit p then x else negate x) <$> getNth a (lit2var p)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
{-# INLINE locked #-}
locked :: Solver -> Clause -> IO Bool
locked s c = (c ==) <$> (getNth (reason s) . lit2var =<< getNth (lits c) 1)

-------------------------------------------------------------------------------- Statistics

-- | returns the value of 'StatIndex'.
{-# INLINE getStat #-}
getStat :: Solver -> StatIndex -> IO Int
getStat (stats -> v) (fromEnum -> i) = getNth v i

-- | sets to 'StatIndex'.
{-# INLINE setStat #-}
setStat :: Solver -> StatIndex -> Int -> IO ()
setStat (stats -> v) (fromEnum -> i) x = setNth v i x

-- | increments a stat data corresponding to 'StatIndex'.
{-# INLINE incrementStat #-}
incrementStat :: Solver -> StatIndex -> Int -> IO ()
incrementStat (stats -> v) (fromEnum -> i) k = modifyNth v (+ k) i

-- | returns the statistics as a list.
{-# INLINABLE getStats #-}
getStats :: Solver -> IO [(StatIndex, Int)]
getStats (stats -> v) = mapM (\i -> (i, ) <$> getNth v (fromEnum i)) [minBound .. maxBound :: StatIndex]

-------------------------------------------------------------------------------- State Modifiers

-- | returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses.
{-# INLINABLE addClause #-}
addClause :: Solver -> Stack -> IO Bool
addClause s@Solver{..} vecLits = do
  result <- clauseNew s vecLits False
  case result of
   Left b  -> return b   -- No new clause was returned becaues a confilct occured or the clause is a literal
   Right c -> pushTo clauses c >> return True

-- | __Fig. 8. (p.12)__ create a new clause and adds it to watcher lists.
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
-- * @Left False@ if the clause is in a confilct
-- * @Left True@ if the clause is satisfied
-- * @Right clause@ if the clause is enqueued successfully
{-# INLINABLE clauseNew #-}
clauseNew :: Solver -> Stack -> Bool -> IO (Either Bool Clause)
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
             _ | - y == l -> reset ps >> return True -- p and negateLit p occurs in ps
             _ -> handle (j + 1) l n
      loopForLearnt :: Int -> IO Bool
      loopForLearnt i = do
        n <- get' ps
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
        n <- get' ps
        if n < i
          then return False
          else do
              l <- getNth ps i     -- check the i-th literal's satisfiability
              sat <- valueLit s l  -- any literal in ps is true
              case sat of
               1  -> reset ps >> return True
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
  k <- get' ps
  case k of
   0 -> return (Left exit)
   1 -> do
     l <- getNth ps 1
     Left <$> enqueue s l NullClause
   _ -> do
    -- allocate clause:
     c <- newClauseFromStack isLearnt ps
     let lstack = lits c
     when isLearnt $ do
       -- Pick a second literal to watch:
       let
         findMax :: Int -> Int -> Int -> IO Int
         findMax ((<= k) -> False) j _ = return j
         findMax i j val = do
           v' <- lit2var <$> getNth lstack i
           varBumpActivity s v' -- this is a just good chance to bump activities of literals in this clause
           a <- getNth assigns v'
           b <- getNth level v'
           if (a /= LBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       -- Let @max_i@ be the index of the literal with highest decision level
       max_i <- findMax 1 1 0
       swapBetween lstack 2 max_i
       -- check literals occurences
       -- x <- asList c
       -- unless (length x == length (nub x)) $ error "new clause contains a element doubly"
       -- Bumping:
       claBumpActivity s c -- newly learnt clauses should be considered active
     -- Add clause to watcher lists:
     l1 <- getNth lstack 1
     l2 <- getNth lstack 2
     if k == 2
       then do pushClauseWithKey' (getNthWatcher watches (negateLit l1)) c 0
               pushClauseWithKey' (getNthWatcher watches (negateLit l2)) c 0
       else do pushClauseWithKey (getNthWatcher watches (negateLit l1)) c 0
               pushClauseWithKey (getNthWatcher watches (negateLit l2)) c 0
     return (Right c)

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
    l <- get' (lbd from)
    k <- (12 +) <$> decisionLevel s
    when (k < l) $ set' (lbd from) k
-}
  let signumP = lit2lbool p
  let v = lit2var p
  val <- valueVar s v
  if val /= LBottom
    then do -- Existing consistent assignment -- don't enqueue
        return $ val == signumP
    else do
        -- New fact, store it
        setNth assigns v signumP
        setNth level v =<< decisionLevel s
        setNth reason v from     -- NOTE: @from@ might be NULL!
        pushTo trail p
        return True

-- | __Fig. 12 (p.17)__
-- returns @False@ if immediate conflict.
--
-- __Pre-condition:__ propagation queue is empty
{-# INLINE assume #-}
assume :: Solver -> Lit -> IO Bool
assume s p = do
  pushTo (trailLim s) =<< get' (trail s)
  enqueue s p NullClause

-- | #M22: Revert to the states at given level (keeping all assignment at 'level' but not beyond).
{-# INLINABLE cancelUntil #-}
cancelUntil :: Solver -> Int -> IO ()
cancelUntil s@Solver{..} lvl = do
  dl <- decisionLevel s
  when (lvl < dl) $ do
    lim <- getNth trailLim (lvl + 1)
    ts <- get' trail
    ls <- get' trailLim
    let
      loopOnTrail :: Int -> IO ()
      loopOnTrail ((lim <) -> False) = return ()
      loopOnTrail c = do
        x <- lit2var <$> getNth trail c
        setNth phases x =<< getNth assigns x
        setNth assigns x LBottom
        -- #reason to set reason Null
        -- if we don't clear @reason[x] :: Clause@ here, @reason[x]@ remains as locked.
        -- This means we can't reduce it from clause DB and affects the performance.
        setNth reason x NullClause -- 'analyze` uses reason without checking assigns
        -- FIXME: #polarity https://github.com/shnarazk/minisat/blosb/master/core/Solver.cc#L212
        undo s x
        -- insertHeap s x              -- insertVerOrder
        loopOnTrail $ c - 1
    loopOnTrail ts
    shrinkBy trail (ts - lim)
    shrinkBy trailLim (ls - lvl)
    set' qHead =<< get' trail

-------------------------------------------------------------------------------- VarOrder

-- | Interfate to select a decision var based on variable activity.
instance VarOrder Solver where
{-
  -- | __Fig. 6. (p.10)__
  -- Creates a new SAT variable in the solver.
  newVar _ = return 0
    -- i <- nVars s
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- push undos =<< newVec        -- push'
    -- push reason NullClause       -- push'
    -- push assigns LBottom
    -- push level (-1)
    -- push activities (0.0 :: Double)
    -- newVar order
    -- growQueueSized (i + 1) propQ
    -- return i
-}
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
              if x == LBottom then return v else loop
    loop

-------------------------------------------------------------------------------- Activities

varActivityThreshold :: Double
varActivityThreshold = 1e100

-- | __Fig. 14 (p.19)__ Bumping of clause activity
{-# INLINE varBumpActivity #-}
varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity s@Solver{..} x = do
  !a <- (+) <$> getNth activities x <*> get' varInc
  setNth activities x a
  when (varActivityThreshold < a) $ varRescaleActivity s
  update s x                    -- update the position in heap

-- | __Fig. 14 (p.19)__
{-# INLINABLE varDecayActivity #-}
varDecayActivity :: Solver -> IO ()
varDecayActivity Solver{..} = modify' varInc (/ variableDecayRate config)
-- varDecayActivity Solver{..} = modifyDouble varInc . (flip (/)) =<< getDouble varDecay

-- | __Fig. 14 (p.19)__
{-# INLINABLE varRescaleActivity #-}
varRescaleActivity :: Solver -> IO ()
varRescaleActivity Solver{..} = do
  let
    loop ((<= nVars) -> False) = return ()
    loop i = modifyNth activities (/ varActivityThreshold) i >> loop (i + 1)
  loop 1
  modify' varInc (/ varActivityThreshold)

-- | value for rescaling clause activity.
claActivityThreshold :: Double
claActivityThreshold = 1e20

-- | __Fig. 14 (p.19)__
{-# INLINE claBumpActivity #-}
claBumpActivity :: Solver -> Clause -> IO ()
claBumpActivity s@Solver{..} Clause{..} = do
  a <- (+) <$> get' activity <*> get' claInc
  set' activity a
  when (claActivityThreshold <= a) $ claRescaleActivity s

-- | __Fig. 14 (p.19)__
{-# INLINE claDecayActivity #-}
claDecayActivity :: Solver -> IO ()
claDecayActivity Solver{..} = modify' claInc (/ clauseDecayRate config)

-- | __Fig. 14 (p.19)__
{-# INLINABLE claRescaleActivity #-}
claRescaleActivity :: Solver -> IO ()
claRescaleActivity Solver{..} = do
  vec <- getClauseVector learnts
  n <- get' learnts
  let
    loopOnVector :: Int -> IO ()
    loopOnVector ((< n) -> False) = return ()
    loopOnVector i = do
      c <- getNth vec i
      modify' (activity c) (/ claActivityThreshold)
      loopOnVector $ i + 1
  loopOnVector 0
  modify' claInc (/ claActivityThreshold)

-- | __Fig. 14 (p.19)__
{-# INLINABLE claRescaleActivityAfterRestart #-}
claRescaleActivityAfterRestart :: Solver -> IO ()
claRescaleActivityAfterRestart Solver{..} = do
  vec <- getClauseVector learnts
  n <- get' learnts
  let
    loopOnVector :: Int -> IO ()
    loopOnVector ((< n) -> False) = return ()
    loopOnVector i = do
      c <- getNth vec i
      d <- get' c
      if d < 9
        then modify' (activity c) sqrt
        else set' (activity c) 0
      -- set' (protected c) False
      loopOnVector $ i + 1
  loopOnVector 0

-------------------------------------------------------------------------------- VarHeap

-- | A heap tree built from two 'Vec'.
-- This implementation is identical wtih that in Minisat-1.14.
-- Note: the zero-th element of @heap@ is used for holding the number of elements.
-- Note: VarHeap itself is not a @VarOrder@, because it requires a pointer to solver.
data VarHeap = VarHeap
                {
                  heap :: !Stack  -- order to var
                , idxs :: !Stack  -- var to order (index)
                }

newVarHeap :: Int -> IO VarHeap
newVarHeap n = do
  v1 <- newVec n 0
  v2 <- newVec n 0
  let
    loop :: Int -> IO ()
    loop ((<= n) -> False) = set' v1 n >> set' v2 n
    loop i = setNth v1 i i >> setNth v2 i i >> loop (i + 1)
  loop 1
  return $ VarHeap v1 v2

{-# INLINE numElementsInHeap #-}
numElementsInHeap :: Solver -> IO Int
numElementsInHeap = get' . heap . order

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
  ac <- getNth activities v
  let
    loop :: Int -> IO ()
    loop i = do
      let iP = div i 2          -- parent
      if iP == 0
        then setNth to i v >> setNth at v i -- end
        else do
            v' <- getNth to iP
            acP <- getNth activities v'
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
  ac <- getNth activities v
  let
    loop :: Int -> IO ()
    loop i = do
      let iL = 2 * i            -- left
      if iL <= n
        then do
            let iR = iL + 1     -- right
            l <- getNth to iL
            r <- getNth to iR
            acL <- getNth activities l
            acR <- getNth activities r
            let (ci, child, ac') = if iR <= n && acL < acR then (iR, r, acR) else (iL, l, acL)
            if ac' > ac
              then setNth to i child >> setNth at child i >> loop ci
              else setNth to i v >> setNth at v i -- end
        else setNth to i v >> setNth at v i       -- end
  loop start

{-# INLINABLE insertHeap #-}
insertHeap :: Solver -> Var -> IO ()
insertHeap s@(order -> VarHeap to at) v = do
  n <- (1 +) <$> getNth to 0
  setNth at v n
  setNth to n v
  set' to n
  percolateUp s n

-- | returns the value on the root (renamed from @getmin@).
{-# INLINABLE getHeapRoot #-}
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
