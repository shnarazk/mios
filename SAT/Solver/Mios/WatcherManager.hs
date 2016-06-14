{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , UndecidableInstances
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Universal data structure for Clauses
-- | Both of watchlists and @learnt@ are implemented by this.
module SAT.Solver.Mios.WatcherManager
       (
         WatcherManager
       , newManager
       , numberOfClauses
       , clearManager
       , shrinkManager
       , getClauseVector
       , getBlockerVector
       , pushClause
       , removeClause
         -- * Debug
       , checkClauseOrder
         -- * WatcherList (vector of WatcherManager) 
       , WatcherList
       , newWatcherList
       , getNthWatchers
       , numberOfRegisteredClauses
       )
       where

import Control.Monad (forM, forM_, unless, when)
import qualified Data.IORef as IORef
import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types
import qualified SAT.Solver.Mios.Clause as C

-- | The Clause Container
data WatcherManager = WatcherManager
  {
    _nActives      :: IntSingleton               -- number of active clause
  , _clauseVector  :: IORef.IORef C.ClauseVector -- clause list
  , _blockerVector :: IORef.IORef Vec            -- blocker as minisat-2.2
  }

newManager :: Int -> IO WatcherManager
newManager initialSize = do
  i <- newInt 0
  v <- C.newClauseVector initialSize
  b <- newVec (MV.length v)
  WatcherManager i <$> IORef.newIORef v <*> IORef.newIORef b

{-# INLINE numberOfClauses #-}
numberOfClauses :: WatcherManager -> IO Int
numberOfClauses WatcherManager{..} = getInt _nActives

{-# INLINE clearManager #-}
clearManager :: WatcherManager -> IO ()
clearManager WatcherManager{..} = setInt _nActives 0

{-# INLINE shrinkManager #-}
shrinkManager :: WatcherManager -> Int -> IO ()
shrinkManager WatcherManager{..} k = modifyInt _nActives (subtract k)

{-# INLINE getClauseVector #-}
getClauseVector :: WatcherManager -> IO C.ClauseVector
getClauseVector WatcherManager{..} = IORef.readIORef _clauseVector

{-# INLINE getBlockerVector #-}
getBlockerVector :: WatcherManager -> IO Vec
getBlockerVector WatcherManager{..} = IORef.readIORef _blockerVector

-- | O(1) inserter
{-# INLINE pushClause #-}
pushClause :: WatcherManager -> C.Clause -> Lit -> IO ()
pushClause !WatcherManager{..} !c k = do
  -- checkConsistency m c
  !n <- getInt _nActives
  !v <- IORef.readIORef _clauseVector
  !b <- IORef.readIORef _blockerVector
  if MV.length v - 1 <= n
    then do
        let len = max 8 $ MV.length v
        v' <- MV.unsafeGrow v len
        b' <- vecGrow b len
        -- forM_ [n  .. MV.length v' - 1] $ \i -> MV.unsafeWrite v' i C.NullClause
        MV.unsafeWrite v' n c
        setNth b' n k
        IORef.writeIORef _clauseVector v'
        IORef.writeIORef _blockerVector b'
    else MV.unsafeWrite v n c >> setNth b n k
  modifyInt _nActives (1 +)

-- | O(n) but lightweight remove-and-compact function
-- __Pre-conditions:__ the clause manager is empty or the clause is stored in it.
{-# INLINE removeClause #-}
removeClause :: WatcherManager -> C.Clause -> IO ()
removeClause WatcherManager{..} c = do
  -- putStrLn =<< dump "@removeClause| remove " c
  -- putStrLn =<< dump "@removeClause| from " m
  !n <- subtract 1 <$> getInt _nActives
  -- unless (0 <= n) $ error $ "removeClause catches " ++ show n
  !v <- IORef.readIORef _clauseVector
  !b <- IORef.readIORef _blockerVector
  let
    seekIndex :: Int -> IO Int
    seekIndex k = do
      c' <- MV.unsafeRead v k
      if c' == c then return k else seekIndex $ k + 1
  unless (n == -1) $ do
    !i <- seekIndex 0
    MV.unsafeWrite v i =<< MV.unsafeRead v n
    setNth b i =<< getNth b n
    setInt _nActives n

instance VectorFamily WatcherManager C.Clause where
  dump mes WatcherManager{..} = do
    n <- getInt _nActives
    if n == 0
      then return $ mes ++ "empty clausemanager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)

-- | for debug
checkConsistency :: WatcherManager -> C.Clause -> IO ()
checkConsistency WatcherManager{..} c = do
  nc <- getInt _nActives
  vec <- IORef.readIORef _clauseVector
  let
    loop :: Int -> IO ()
    loop i = do
      when (i < nc) $ do
        c' <- MV.unsafeRead vec i
        when (c' == c) $ error "insert a clause to a ClauseMananger twice"
        loop $ i + 1
  loop 0

-- | for debug
checkClauseOrder :: WatcherManager -> IO ()
checkClauseOrder cm = do
  putStr "checking..."
  nc <- numberOfClauses cm
  vec <- getClauseVector cm
  let
    nthActivity :: Int -> IO Double
    nthActivity i = getDouble . C.activity =<< MV.unsafeRead vec i
    report :: Int -> Int -> IO ()
    report i j = (putStr . (++ ", ") . show =<< nthActivity i) >> when (i < j) (report (i + 1) j)
    loop :: Int -> Double -> IO ()
    loop i v = do
      when (i < nc) $ do
        c <- MV.unsafeRead vec i
        a <- getDouble (C.activity c)
        when (c == C.NullClause) $ error "null is included"
        when (v < a) $ report 0 i >> error ("unsorted clause vector: " ++ show (nc, i))
        loop (i + 1) a
  loop 0 =<< nthActivity 0
  putStrLn "done"

-------------------------------------------------------------------------------- WatcherManagers

type WatcherList = V.Vector WatcherManager

-- | /n/ is the number of 'Var', /m/ is default size of each watcher list
-- | For /n/ vars, we need [0 .. 2 + 2 * n - 1] slots, namely /2 * (n + 1)/-length vector
newWatcherList :: Int -> Int -> IO WatcherList
newWatcherList n m = V.fromList <$> (forM [0 .. int2lit (negate n) + 1] $ \_ -> newManager m)

-- | returns the watcher List :: "ClauseManager" for "Literal" /l/
{-# INLINE getNthWatchers #-}
getNthWatchers :: WatcherList -> Lit-> WatcherManager
getNthWatchers = V.unsafeIndex

instance VectorFamily WatcherList C.Clause where
  dump mes wl = (mes ++) . L.concat <$> (forM [1 .. V.length wl - 1] $ \i -> dump ("\n" ++ show (lit2int i) ++ "' watchers:") (getNthWatchers wl i))

numberOfRegisteredClauses :: WatcherList -> IO Int
numberOfRegisteredClauses ws = sum <$> V.mapM numberOfClauses ws

{-
-- | for debug
checkConsistency :: WatcherManagers -> IO ()
checkConsistency wl = do
  forM_ [2 .. V.length wl - 1] $ \i -> do
    let cm = getNthWatchers wl i
    vec <- getClauseVector cm
    n <- numberOfClauses cm
    forM_ [0 .. n - 1] $ \k -> do
      c <- getNthClause vec k
      when (c == C.NullClause) $ error "checkConsistency failed"
  l <- forM [2 .. V.length wl - 1] (numberOfClauses . getNthWatchers wl)
  putStrLn $ "checkConsistency passed: " ++ show l
-}
