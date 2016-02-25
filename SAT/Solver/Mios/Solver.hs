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

import Control.Monad ((<=<), filterM, forM, forM_, unless, when)
import qualified Data.IORef as IORef
import Data.List (sortOn)
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed.Mutable as UV
-- import qualified Data.Vector.Algorithms.Intro as VA
-- import System.IO.Unsafe (unsafePerformIO)
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
                model        :: ListOf Bool            -- ^ If found, this vector has the model
                -- Contraint database
              , constrs      :: ClauseManager          -- ^ List of problem constraints.
              , learnts      :: ClauseManager          -- ^ List of learnt clauses.
              , claInc       :: DoubleSingleton        -- ^ Clause activity increment amount to bump with.
                -- Variable order
              , activities   :: FixedVecDouble         -- ^ Heuristic measurement of the activity of a variable; var-indexed
              , varInc       :: DoubleSingleton        -- ^ Variable activity increment amount to bump with.
              , order        :: VarHeap                -- ^ Keeps track of the dynamic variable order.
                -- Propagation
              , watches      :: WatcherLists           -- ^ For each literal 'p', a list of constraint wathing 'p'.
                                -- A constraint will be inspected when 'p' becomes true.
              , undos        :: FixedVecOf ClauseManager -- ^ For each variable 'x', a list of constraints that need
                                -- to update when 'x' becomes unbound by backtracking.
              , propQ        :: QueueOfBoundedInt      -- ^ Propagation queue.
                -- Assignments
              , assigns      :: FixedVecInt            -- ^ The current assignments indexed on variables; var-indexed
              , trail        :: ListOfInt              -- ^ List of assignments in chronological order; var-indexed
              , trailLim     :: ListOfInt              -- ^ Separator indices for different decision levels in 'trail'.
              , decisionLevel :: IntSingleton
              , reason       :: FixedVecOf Clause      -- ^ For each variable, the constraint that implied its value; var-indexed
              , level        :: FixedVecInt            -- ^ For each variable, the decision level it was assigned; var-indexed
              , rootLevel    :: IntSingleton           -- ^ Separates incremental and search assumptions.
              , seen         :: UV.IOVector Int        -- ^ scratch vector for 'analyze'; var-indexed
              , nVars        :: Int                    -- ^ number of variables
                -- Configuration
              , config       :: MiosConfiguration      -- ^ search paramerters
              }

-- | returns the number of current assigments
{-# INLINE nAssigns #-}
nAssigns :: Solver -> IO Int
nAssigns = sizeOfListOfInt . trail

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
valueVar !s !x = getNthInt x (assigns s)

-- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Lit'
{-# INLINE valueLit #-}
valueLit :: Solver -> Lit -> IO LBool
valueLit !Solver{..} !p = if p < 0 then negate <$> getNthInt (var p) assigns else getNthInt (var p) assigns

-- | returns an everything-is-initialized solver from the argument
setInternalState :: Int -> Int -> Solver -> IO Solver
setInternalState nv nc s = do
  setStdGen $ mkStdGen 91648253
  m1 <- newClauseManager nc
  m2 <- newClauseManager nc
  ac <- newVecDouble (nv + 1) 0.0
  w <- newWatcherLists (nv * 2) (div (2 * nc) nv)
  u <- newVec 0 -- nv
  -- forM_ [0 .. nv - 1] $ \i -> setVecAt u i =<< newVec 0
  a <- newVecWith (nv + 1) lBottom
  t <- newListOfInt (2 * nv)
  t' <- newListOfInt nv
  r <- newVecWith (nv + 1) NullClause
  l <- newVecWith (nv + 1) (-1)
  o <- newVarHeap nv
  q <- newQueue (2 * nv)
  n <- UV.new (nv + 1)
  let s' = s
           {
             activities = ac
           , constrs = m1
           , learnts = m2
           , watches = w
           , undos = u
           , assigns = a
           , trail = t
           , trailLim = t'
           , reason = r
           , level = l
           , order = o
           , propQ = q
           , seen = n
           , nVars  = nv
           }
  return s'

-- | constructor
newSolver :: MiosConfiguration -> IO Solver
newSolver conf = Solver
            <$> newList          -- model
            <*> newClauseManager 1 -- constrs
            <*> newClauseManager 1 -- learnts
            <*> newDouble 1.0    -- claInc
            <*> newVecDouble 0 0 -- activities
            <*> newDouble 1.0    -- varInc
            <*> newVarHeap 0     -- order
            <*> newWatcherLists 1 1 -- watches
            <*> newVec 0         -- undos
            <*> newQueue 0       -- porqQ
            <*> newVec 0         -- assigns
            <*> newListOfInt 0   -- trail
            <*> newListOfInt 0   -- trailLim
            <*> newInt 0         -- decisionLevel
            <*> newVec 0         -- reason
            <*> newVec 0         -- level
            <*> newInt 0         -- rootLevel
            <*> UV.new 0         -- seen
            <*> return 0         -- nVars
            <*> return conf      -- config

-- | public interface of 'Solver' (p.2)
--
-- returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses.
{-# INLINABLE addClause #-}
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
            let w = getNthWatchers watches (index p)
            n <- numberOfClauses w
            vec <- getClauseVector w
            let
              loopOnWatcher :: Int -> Int-> IO Clause
              loopOnWatcher i n
                | i == n = loopOnQueue
                | otherwise = do
                    c <- getNthClause vec i
                    x <- propagateLit c s p w -- c will be inserted into apropriate watchers in this function
                    case () of
                      _ | x == lTrue   {- still in -} -> loopOnWatcher (i + 1) n
                      _ | x == lFalse  {- conflict -} -> clearQueue propQ >> return c
                      _ | x == lBottom {- it moved -} -> removeNthClause w i >> loopOnWatcher i (n - 1)
{-
                if not x -- Constraint is conflicting;return constraint
                  then clearQueue propQ >> shrinkClauseManager w (max 0 (i - 1)) >> return c
                  else loopOnWatcher $ i - 1
-}
            loopOnWatcher 0 n
  loopOnQueue

-- | __Fig. 9 (p.14)__
-- Puts a new fact on the propagation queue, as well as immediately updating the variable's value
-- in the assignment vector. If a conflict arises, @False@ is returned and the propagation queue is
-- cleared. The parameter 'from' contains a reference to the constraint from which 'p' was
-- propagated (defaults to @Nothing@ if omitted).
{-# INLINABLE enqueue #-}
enqueue :: Solver -> Lit -> Clause -> IO Bool
enqueue !s@Solver{..} !p !from = do
  let v = var p
  val <- valueVar s v
  if val /= lBottom
    then do -- Existing consistent assignment -- don't enqueue
        return $ signum val == signum p
    else do
        -- New fact, store it
        setNthInt v assigns $! signum p
        d <- getInt decisionLevel
        setNthInt v level d
        setVecAt reason v from     -- NOTE: @from@ might be NULL!
        pushToListOfInt trail p
        insertQueue propQ p
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
{-# INLINEABLE analyze #-}
analyze :: Solver -> Clause -> ListOf Lit -> IO Int
analyze s@Solver{..} confl learnt = do
  UV.set seen 0
  d <- getInt decisionLevel
  -- learnt `push` 0               -- leave room for the asserting literal
  let
    loop :: Lit -> Clause -> Int -> Int -> IO Int
    loop !p confl !counter !btLevel = do
      -- invariant here: @confl /= NullClause@
      -- Because any decision var should be a member of reason of an implication vars.
      -- So it becomes /seen/ in an early stage before the traversing loop
      -- clear pReason
      !pReason <- calcReason confl s p -- pReason holds a negated reason now.
      -- TRACE REASON FOR P:
      let
        for :: [Int] -> Int -> Int -> IO (Int, Int)
        for [] c b = return (c, b)
        for !(q:rest) counter btLevel = do
          let v = var q
          sv <- UV.unsafeRead seen v
          if sv == 0
            then do
                UV.unsafeWrite seen v 1
                l <- getNthInt v level
                case () of
                 _ | l == d -> for rest (counter + 1) btLevel
                 _ | 0 <  l -> do -- exclude variables from decision level 0
                       pushToList learnt q
                       for rest counter $! max btLevel l
                 _ -> for rest counter btLevel
            else for rest counter btLevel
      -- pl <- asList pReason
      !(counter, btLevel) <- for pReason counter btLevel
      -- SELECT NEXT LITERAL TO LOOK AT:
      let
        doWhile :: IO (Lit, Clause)
        doWhile = do
          p <- lastOfListOfInt trail
          let !i = var p
          confl <- getVecAt reason i -- should call it before 'undoOne'
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
{-# INLINE record #-}
record :: Solver -> FixedVecInt -> IO ()
record s@Solver{..} v = do
  c <- snd <$> clauseNew s v True -- will be set to created clause, or NULL if @clause[]@ is unit
  l <- getNthInt 1 v
  enqueue s l c
  unless (c == NullClause) $ pushClause learnts c

-- | __Fig. 12. (p.17)__
-- unbinds the last variable on the trail.
{-# INLINE undoOne #-}
undoOne :: Solver -> IO ()
undoOne s@Solver{..} = do
  !v <- var <$> lastOfListOfInt trail
  setNthInt v assigns lBottom
  setVecAt reason v NullClause
  setNthInt v level (-1)
  undo s v
  popFromListOfInt trail
{-
  // 'undos' is not used in the paper
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
{-# INLINE assume #-}
assume :: Solver -> Lit -> IO Bool
assume s@Solver{..} p = do
  pushToListOfInt trailLim =<< sizeOfListOfInt trail
  modifyInt decisionLevel (+ 1)
  enqueue s p NullClause

-- | __Fig. 12 (p.17)__
-- reverts to the state before last "push".
--
-- __Pre-condition:__ propagation queue is empty.
{-# INLINABLE cancel #-}
cancel :: Solver -> IO ()
cancel s@Solver{..} = do
  let
    for :: Int -> IO ()
    for c = when (c /= 0) $ undoOne s >> for (c - 1)
  st <- sizeOfListOfInt trail
  tl <- lastOfListOfInt trailLim
  when (0 < st - tl) $ for $ st - tl
  popFromListOfInt trailLim
  modifyInt decisionLevel (subtract 1)

-- | __Fig. 12 (p.17)__
-- cancels several levels of assumptions.
{-# INLINABLE cancelUntil #-}
cancelUntil :: Solver -> Int -> IO ()
cancelUntil s lvl = do
  let
    loop :: Int -> IO ()
    loop ((lvl <) -> False) = return ()
    loop d = cancel s >> loop (d - 1)
  loop =<< getInt (decisionLevel s)

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
      -- checkIt "search.loop starts" s Nothing
      !confl <- propagate s
      -- checkIt "search.propagate done" s Nothing
      -- putStrLn $ "propagate done: " ++ show (confl /= NullClause)
      -- checkWatches s
      d <- getInt decisionLevel
      if confl /= NullClause
        then do
            -- CONFLICT
            -- putStrLn . ("conf: " ++) =<< dump "" confl
            -- checkIt "search is conflict after propagate" s Nothing
            r <- getInt rootLevel
            if d == r
              then return lFalse
              else do
                  learntClause <- newList
                  backtrackLevel <- analyze s confl learntClause
                  (s `cancelUntil`) . max backtrackLevel =<< getInt rootLevel
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
            when (k1 - k2 >= nOfLearnts) $ do
--              n1 <- nLearnts s
              reduceDB s -- Reduce the set of learnt clauses
              {-
              n2 <- nLearnts s
              n3 <- sizeOfListOfInt trail
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
                   IORef.writeIORef (ptr model) . map (lTrue ==) . tail =<< asList assigns
                   -- putStrLn =<< dump "activities:" activities
                   return lTrue
             _ | conflictC >= nOfConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< getInt rootLevel -- force a restart
                   -- checkIt "search terminates to restart" s Nothing
                   return lBottom
             _ -> do
               -- New variable decision:
               p <- select s -- many have heuristic for polarity here
               -- putStrLn $ "search determines next decision var: " ++ show p
               -- << #phasesaving
               oldVal <- valueVar s p                        -- p means 'Var' here
               assume s $ if oldVal < 0 then negate p else p -- 2nd arg is a 'Literal'
               -- assume s p        -- cannot return @False@
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
          unless (a < b) $ MV.unsafeSwap vec left right
      | otherwise = do
          --let check m i = unless (0 <= i && i < n) $ error (m ++ " out of index:" ++ (show (i, (left, right), n)))
          let p = div (left + right) 2
          pivot <- keyOf p
          MV.unsafeSwap vec p left -- set a sentinel for r'
          let
            nextL :: Int -> IO Int
            nextL i@((<= right) -> False) = return i
            nextL i = do v <- keyOf i; if v < pivot then nextL (i + 1) else return i
            nextR :: Int -> IO Int
            nextR i@((left <=) -> False) = return i
            nextR i = do v <- keyOf i; if pivot < v then nextR (i - 1) else return i
            divide :: Int -> Int -> IO Int
            divide l r = do
              l' <- nextL l
              r' <- nextR r
              if l' < r' then MV.unsafeSwap vec l' r' >> divide (l' + 1) (r' - 1) else return r'
          m <- divide (left + 1) right
          MV.unsafeSwap vec left m
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
solve :: Solver -> ListOf Lit -> IO Bool
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
  !x <- for =<< asList assumps
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
  l1 <- negate <$> getNthLiteral 0 c
  removeClause (getNthWatchers watches (index l1)) c
  l2 <- negate <$> getNthLiteral 1 c
  removeClause (getNthWatchers watches (index l2)) c
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
  n <- sizeOfClause c
  l1 <- negate <$> getNthLiteral 0 c
  l2 <- negate <$> getNthLiteral 1 c
  let
    loop :: Int -> Int -> IO Bool
    loop ((< n) -> False) j = do
      when (0 < n - j) $ do
        shrinkClause (n - j) c
        l1' <- negate <$> getNthLiteral 0 c
        when (l1 /= l1') $ do
          removeClause (getNthWatchers watches (index l1)) c
          pushClause (getNthWatchers watches (index l1')) c
        l2' <- negate <$> getNthLiteral 1 c
        when (l2 /= l2') $ do
          removeClause (getNthWatchers watches (index l2)) c
          pushClause (getNthWatchers watches (index l2')) c
      return False
    loop i j = do
      l <- getNthLiteral i c
      v <- valueLit s l
      case () of
       _ | v == lTrue   -> return True
       _ | v == lBottom -> do
             when (i /= j) $ setNthLiteral j c l      -- false literals are not copied (only occur for i >= 2)
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
  !l' <- negate <$> getNthInt 1 lits
  when (l' == p) $ do
    -- swap lits[0] and lits[1]
    swapIntsBetween lits 1 2
  -- If 0th watch is True, then clause is already satisfied.
  !l1 <- getNthInt 1 lits
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
            !(l :: Int) <- getNthInt i lits
            !val <- valueLit s l
            if val /= lFalse    -- l is unassigned or satisfied already
              then do
                  swapIntsBetween lits 2 i -- setNthInt 2 lits l >> setNthInt i lits np
                  -- putStrLn "## from propagateLit"
                  -- @removeClause m c@ will be done by propagate
                  pushClause (getNthWatchers watches (index (negate l))) c -- insert clause into watcher list
                  return lBottom -- this means the clause is moved to other watcher list
              else loopOnLits $ i + 1
        loopOnLits 3

-- | __Undo.__ During backtracking, this method is called if the constaint added itself
-- to the undo list of /var(p)/ in 'propagateLit'.The current variable assignments are
-- guaranteed to be identical to that of the moment before 'propagateLit' was called.
-- undoConstraint :: Clause -> Solver -> Lit -> IO ()
-- undoConstraint _ _ _ = return () -- defaults to do nothing

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
{-# INLINABLE clauseNew #-}
clauseNew :: Solver -> FixedVecInt -> Bool -> IO (Bool, Clause)
clauseNew s@Solver{..} ps learnt = do
  -- now ps[0] is the number of living literals
  exit <- do
    let
      handle :: Int -> Int -> Int -> IO Bool
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
      loopForLearnt :: Int -> IO Bool
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
      loop :: Int -> IO Bool
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
                 sat' <- handle (i + 1) l n
                 if sat'
                   then return True
                   else loop $ i + 1
    if learnt then loopForLearnt 1 else loop 1
  k <- getNthInt 0 ps
  case k of
   0 -> return (exit, NullClause)
   1 -> do
     l <- getNthInt 1 ps
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
           v' <- var <$> getNthInt i ps
           a <- getNthInt v' assigns
           b <- getNthInt v' level
           if (a /= lBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       -- Let @max_i@ be the index of the literal with highest decision level
       max_i <- findMax 1 1 0
       swapIntsBetween ps 2 max_i
       -- check literals occurences
       -- x <- asList c
       -- unless (length x == length (nub x)) $ error "new clause contains a element doubly"
       -- Bumping:
       claBumpActivity s c -- newly learnt clauses should be considered active
       forM_ [1 .. k] $ varBumpActivity s . var <=< flip getNthInt ps -- variables in conflict clauses are bumped
     -- Add clause to watcher lists:
     l0 <- negate <$> getNthInt 1 ps
     pushClause (getNthWatchers watches (index l0)) c
     l1 <- negate <$> getNthInt 2 ps
     pushClause (getNthWatchers watches (index l1)) c
     return (True, c)

-- | __Fig. 7. (p.11)__
-- returns @True@ if the clause is locked (used as a reason). __Learnt clauses only__
{-# INLINE locked #-}
locked :: Clause -> Solver -> IO Bool
locked !c@Clause{..} !Solver{..} =  (c ==) <$> (getVecAt reason . var =<< getNthInt 1 lits)

-- | For small-sized problems, heap may not be a good choice.
useHeap :: Int
useHeap = 1000000
-- | For small-sized problems, randomess may lead to worse results.
useRand :: Int
useRand = 1000

-- | Interfate to select a decision var based on variable activity.
instance VarOrder Solver where
  -- | __Fig. 6. (p.10)__
  -- Creates a new SAT variable in the solver.
  newVar _ = return 0
    -- index <- nVars s
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- Version 0.4:: push watches =<< newVec      -- push'
    -- push undos =<< newVec        -- push'
    -- push reason NullClause       -- push'
    -- push assigns lBottom
    -- push level (-1)
    -- push activities (0.0 :: Double)
    -- newVar order
    -- growQueueSized (index + 1) propQ
    -- return index
  {-# SPECIALIZE INLINE update :: Solver -> Var -> IO () #-}
  update s v = when (useHeap < nVars s) $ increase s v
  {-# SPECIALIZE INLINE undo :: Solver -> Var -> IO () #-}
  undo s v = when (useHeap < nVars s) $ inHeap s v >>= (`unless` insert s v)
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
              val <- getNthInt v asg
              if val == lBottom then return v else loop
      -- | O(n) implementation on vector: loop2 1 0 (-1)
      loop2 :: Int -> Int -> Double -> IO Var
      loop2 ((<= nv) -> False) j _ = return j
      loop2 i j best = do
        x <- getNthInt i asg
        if x == lBottom
          then do
              actv <- getNthDouble i $ activities s
              if best < actv
                then loop2 (i + 1) i actv
                else loop2 (i + 1) j best
          else loop2 (i + 1) j best
    if useRand < nv
      then do
          !r <- flip mod 1001 <$> randomIO :: IO Int
          if r < randomDecisionRate (config s) -- the threshold used in MiniSat 1.14 is 0.02, namely 20/1000
            then do
                !i <- (+ 1) . flip mod nv <$> randomIO
                x <- getNthInt i asg
                if x == lBottom then return i else if useHeap < nv then loop else loop2 1 0 (-1)
            else if useHeap < nv then loop else loop2 1 0 (-1)
      else if useHeap < nv then loop else loop2 1 0 (-1)

-------------------------------------------------------------------------------- VarHeap

-- | 'VarHeap' is a heap tree built from two 'FixedVecInt'
-- This implementation is identical wtih that in Minisat-1.14
-- Note: the zero-th element of 'heap' is used for holding the number of elements
-- Note: VarHeap itself is not a 'VarOrder', because it requires a pointer to solver
data VarHeap = VarHeap
                {
                  heap :: FixedVecInt -- order to var
                , idxs :: FixedVecInt -- var to order (index)
                }

newVarHeap :: Int -> IO VarHeap
newVarHeap n = VarHeap <$> newSizedVecIntFromList lst <*> newSizedVecIntFromList lst
  where
    lst = [1 .. n]

{-# INLINE numElementsInHeap #-}
numElementsInHeap :: Solver -> IO Int
numElementsInHeap (order -> heap -> h) = getNthInt 0 h

{-# INLINE inHeap #-}
inHeap :: Solver -> Int -> IO Bool
inHeap (order -> idxs -> at) n = (/= 0) <$> getNthInt n at

{-# INLINE increase #-}
increase :: Solver -> Int -> IO ()
increase s@(order -> idxs -> at) n = inHeap s n >>= (`when` (percolateUp s =<< getNthInt n at))

{-# INLINABLE percolateUp #-}
percolateUp :: Solver -> Int -> IO ()
percolateUp Solver{..} start = do
  let VarHeap to at = order
  v <- getNthInt start to
  ac <- getNthDouble v activities
  let
    loop :: Int -> IO ()
    loop i = do
      let iP = div i 2          -- parent
      if iP == 0
        then setNthInt i to v >> setNthInt v at i >> return () -- end
        else do
            v' <- getNthInt iP to
            acP <- getNthDouble v' activities
            if ac > acP
              then setNthInt i to v' >> setNthInt v' at i >> loop iP -- loop
              else setNthInt i to v >> setNthInt v at i >> return () -- end
  loop start

{-# INLINABLE percolateDown #-}
percolateDown :: Solver -> Int -> IO ()
percolateDown Solver{..} start = do
  let (VarHeap to at) = order
  n <- getNthInt 0 to
  v <- getNthInt start to
  ac <- getNthDouble v activities
  let
    loop :: Int -> IO ()
    loop i = do
      let iL = 2 * i            -- left
      if iL <= n
        then do
            let iR = iL + 1     -- right
            l <- getNthInt iL to
            r <- getNthInt iR to
            acL <- getNthDouble l activities
            acR <- getNthDouble r activities
            let (ci, child, ac') = if iR <= n && acL < acR then (iR, r, acR) else (iL, l, acL)
            if ac' > ac
              then setNthInt i to child >> setNthInt child at i >> loop ci
              else setNthInt i to v >> setNthInt v at i >> return () -- end
        else setNthInt i to v >> setNthInt v at i >> return ()       -- end
  loop start

{-# INLINE insert #-}
insert :: Solver -> Var -> IO ()
insert s@(order -> VarHeap to at) v = do
  n <- (1 +) <$> getNthInt 0 to
  setNthInt v at n
  setNthInt n to v
  setNthInt 0 to n
  percolateUp s n

-- | renamed from 'getmin'
{-# INLINE getHeapRoot #-}
getHeapRoot :: Solver -> IO Int
getHeapRoot s@(order -> VarHeap to at) = do
  r <- getNthInt 1 to
  l <- flip getNthInt to =<< getNthInt 0 to -- the last element's value
  setNthInt 1 to l
  setNthInt l at 1
  setNthInt r at 0
  modifyNthInt 0 to $ subtract 1 -- pop
  n <- getNthInt 0 to
  when (1 < n) $ percolateDown s 1
  return r

-------------------------------------------------------------------------------- debug code

{-
dumpStatus :: Solver -> IO ()
dumpStatus Solver{..} = do
  putStrLn . ("level: " ++) . show . filter ((0 <=) . snd) . zip [1..] =<< asList level
  putStrLn =<< dump "trail: " trail
  putStrLn =<< dump "trailLim: " trailLim
  putStrLn =<< makeGraph <$> asList trail <*> fromReason reason

fromReason :: VecOf Clause -> IO [(Int, [Int])]
fromReason vec = do
  l <- zip [1..] <$> asList vec
  let f (i, c) = (i, ) <$> asList c
  mapM f l

watcherList :: Solver -> Lit -> IO [[Lit]]
watcherList Solver{..} lit = do
  (b, e) <- watches .! index lit
  x <- map sort <$> (flip traverseWatcher lit =<< watches .! index lit)
{-
  unless (null x) $ do
    cs <- sort <$> (asList =<< getDouble b)
    ce <- sort <$> (asList =<< getDouble e)
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
