-- | (This is a part of MIOS.)
-- Solver, the main data structure
{-# LANGUAGE
    MultiWayIf
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Mios.Solver
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
         -- * State Modifiers
       , setAssign
       , enqueue
       , assume
       , cancelUntil
         -- * Stats
       , StatIndex (..)
       , getStat
       , setStat
       , incrementStat
       , getStats
       )
        where

import Control.Monad (unless, when)
import Data.List (intercalate)
import Numeric (showFFloat)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.ClausePool

-- | __Fig. 2.(p.9)__ Internal State of the solver
data Solver = Solver
              {
                -------- Database
                clauses    :: !ClauseExtManager  -- ^ List of problem constraints.
              , learnts    :: !ClauseExtManager  -- ^ List of learnt clauses.
              , watches    :: !WatcherList       -- ^ list of constraint wathing 'p', literal-indexed
                -------- Assignment Management
              , assigns    :: !(Vec Int)         -- ^ The current assignments indexed on variables
              , phases     :: !(Vec Int)         -- ^ The last assignments indexed on variables
              , trail      :: !Stack             -- ^ List of assignments in chronological order
              , trailLim   :: !Stack             -- ^ Separator indices for different decision levels in 'trail'.
              , qHead      :: !Int'              -- ^ 'trail' is divided at qHead; assignment part and queue part
              , reason     :: !ClauseVector      -- ^ For each variable, the constraint that implied its value
              , level      :: !(Vec Int)         -- ^ For each variable, the decision level it was assigned
              , ndd        :: !(Vec Int)         -- ^ For each variable, the number of depending decisions
              , conflicts  :: !Stack             -- ^ Set of literals in the case of conflicts
                -------- Variable Order
              , activities :: !(Vec Double)      -- ^ Heuristic measurement of the activity of a variable
              , order      :: !VarHeap           -- ^ Keeps track of the dynamic variable order.
                -------- Configuration
              , config     :: !MiosConfiguration -- ^ search paramerters
              , nVars      :: !Int               -- ^ number of variables
              , claInc     :: !Double'           -- ^ Clause activity increment amount to bump with.
              , varInc     :: !Double'           -- ^ Variable activity increment amount to bump with.
              , rootLevel  :: !Int'              -- ^ Separates incremental and search assumptions.
                -------- DB Size Adjustment
              , learntSAdj :: Double'            -- ^ used in 'SAT.Mios.Main.search'
              , learntSCnt :: Int'               -- ^ used in 'SAT.Mios.Main.search'
              , maxLearnts :: Double'            -- ^ used in 'SAT.Mios.Main.search'
                -------- Working Memory
              , ok         :: !Int'              -- ^ internal flag
              , an'seen    :: !(Vec Int)         -- ^ used in 'SAT.Mios.Main.analyze'
              , an'toClear :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze'
              , an'stack   :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze'
              , an'lastDL  :: !Stack             -- ^ last decision level used in 'SAT.Mios.Main.analyze'
              , clsPool    :: ClausePool         -- ^ clause recycler
              , litsLearnt :: !Stack             -- ^ used in 'SAT.Mios.Main.analyze' and 'SAT.Mios.Main.search' to create a learnt clause
              , stats      :: !(Vec Int)         -- ^ statistics information holder
              , lbd'seen   :: !(Vec Int)         -- ^ used in lbd computation
              , lbd'key    :: !Int'              -- ^ used in lbd computation
                -------- restart heuristics #62, clause evaluation criteria #74
              , emaAFast    :: !EMA              -- ^ Number of Assignments Fast
              , emaASlow    :: !EMA              -- ^ Number of Assignments Slow
              , emaBDLvl    :: !EMA              -- ^ Backjumped and Restart Dicision Level
              , emaCDLvl    :: !EMA              -- ^ Conflicting Level
              , emaDFast    :: !EMA              -- ^ (Literal Block) Distance Fast
              , emaDSlow    :: !EMA              -- ^ (Literal Block) Distance Slow
              , nextRestart :: !Int'             -- ^ next restart in number of conflict
              , restartExp  :: !Double'          -- ^ incremented by blocking
              , emaRstBias  :: !EMA              -- ^ average phase of restart
              }

-- | returns an everything-is-initialized solver from the arguments.
newSolver :: MiosConfiguration -> CNFDescription -> IO Solver
newSolver conf (CNFDescription nv dummy_nc _) =
  Solver
    -- Clause Database
    <$> newManager dummy_nc                -- clauses
    <*> newManager 2000                    -- learnts
    <*> newWatcherList nv 1                -- watches
    -- Assignment Management
    <*> newVec nv LBottom                  -- assigns
    <*> newVec nv LBottom                  -- phases
    <*> newStack nv                        -- trail
    <*> newStack nv                        -- trailLim
    <*> new' 0                             -- qHead
    <*> newClauseVector (nv + 1)           -- reason
    <*> newVec nv (-1)                     -- level
    <*> newVec (2 * (nv + 1)) 0            -- ndd
    <*> newStack nv                        -- conflicts
    -- Variable Order
    <*> newVec nv 0                        -- activities
    <*> newVarHeap nv                      -- order
    -- Configuration
    <*> return conf                        -- config
    <*> return nv                          -- nVars
    <*> new' 1.0                           -- claInc
    <*> new' 1.0                           -- varInc
    <*> new' 0                             -- rootLevel
    -- Learnt DB Size Adjustment
    <*> new' 100                           -- learntSAdj
    <*> new' 100                           -- learntSCnt
    <*> new' 2000                          -- maxLearnts
    -- Working Memory
    <*> new' LiftedT                       -- ok
    <*> newVec nv 0                        -- an'seen
    <*> newStack nv                        -- an'toClear
    <*> newStack nv                        -- an'stack
    <*> newStack nv                        -- an'lastDL
    <*> newClausePool 10                   -- clsPool
    <*> newStack nv                        -- litsLearnt
    <*> newVec (fromEnum EndOfStatIndex) 0 -- stats
    <*> newVec nv 0                        -- lbd'seen
    <*> new' 0                             -- lbd'key
    -- restart heuristics #62
    <*> newEMA False ef                    -- emaAFast
    <*> newEMA True es                     -- emaASlow
    <*> newEMA True 2                      -- emaBDLvl
    <*> newEMA True 2                      -- emaCDLvl
    <*> newEMA False ef                    -- emaDFast
    <*> newEMA True es                     -- emaDSlow
    <*> new' 100                           -- nextRestart
    <*> new' 0.0                           -- restartExp
    <*> newEMA False 100                   -- emaRstBias
  where
    (ef, es) = emaCoeffs conf

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

-- | assigns a value to the /n/-th variable
setAssign :: Solver -> Int -> LiftedBool -> IO ()
setAssign Solver{..} v x = setNth assigns v x

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
    then return $ val == signumP     -- Existing consistent assignment -- don't enqueue
    else do setNth assigns v signumP -- New fact, store it
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
        undoVO s x
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
  {-# SPECIALIZE INLINE updateVO :: Solver -> Var -> IO () #-}
  updateVO = increaseHeap
  {-# SPECIALIZE INLINE undoVO :: Solver -> Var -> IO () #-}
  undoVO s v = inHeap s v >>= (`unless` insertHeap s v)
  {-# SPECIALIZE INLINE selectVO :: Solver -> IO Var #-}
  selectVO s = do
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
inHeap Solver{..} n = case idxs order of at -> (/= 0) <$> getNth at n

{-# INLINE increaseHeap #-}
increaseHeap :: Solver -> Int -> IO ()
increaseHeap s@Solver{..} n = case idxs order of
                                at -> inHeap s n >>= (`when` (percolateUp s =<< getNth at n))

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
