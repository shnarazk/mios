{-# LANGUAGE
    BangPatterns
  , DuplicateRecordFields
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , UndecidableInstances
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Clause Managers
module SAT.Solver.Mios.ClauseManager
       (
         -- * higher level interface for ClauseVector
         ClauseManager (..)
         -- * vector of clauses
       , SimpleManager
       , pushClause
         -- * vector of caluses and their blocking literals
       , WatcherManager
       , pushWatcher
       , getBlockerVector
         -- * WatcherList (vector of WatcherManager)
       , WatcherList
       , newWatcherList
       , getNthWatchers
       , numberOfRegisteredClauses
       )
       where

import Control.Monad (forM, unless, when)
import qualified Data.IORef as IORef
import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types
import qualified SAT.Solver.Mios.Clause as C

class ClauseManager a where
  newManager      :: Int -> IO a
  numberOfClauses :: a -> IO Int
  clearManager    :: a -> IO ()
  shrinkManager   :: a -> Int -> IO ()
  getClauseVector :: a -> IO C.ClauseVector
  removeClause    :: a -> C.Clause -> IO ()
  removeNthClause :: a -> Int -> IO ()

-- | The Clause Container
data SimpleManager = SimpleManager
  {
    _nActives     :: IntSingleton               -- number of active clause
  , _clauseVector :: IORef.IORef C.ClauseVector -- clause list
  }

instance ClauseManager SimpleManager where
  {-# SPECIALIZE INLINE newManager :: Int -> IO SimpleManager #-}
  newManager initialSize = do
    i <- newInt 0
    v <- C.newClauseVector initialSize
    SimpleManager i <$> IORef.newIORef v
  {-# SPECIALIZE INLINE numberOfClauses :: SimpleManager -> IO Int #-}
  numberOfClauses SimpleManager{..} = getInt _nActives
  {-# SPECIALIZE INLINE clearManager :: SimpleManager -> IO () #-}
  clearManager SimpleManager{..} = setInt _nActives 0
  {-# SPECIALIZE INLINE shrinkManager :: SimpleManager -> Int -> IO () #-}
  shrinkManager SimpleManager{..} k = modifyInt _nActives (subtract k)
  {-# SPECIALIZE INLINE getClauseVector :: SimpleManager -> IO C.ClauseVector #-}
  getClauseVector SimpleManager{..} = IORef.readIORef _clauseVector
  -- | O(1) remove-and-compact function
  {-# SPECIALIZE INLINE removeNthClause :: SimpleManager -> Int -> IO () #-}
  removeNthClause SimpleManager{..} i = do
    !n <- subtract 1 <$> getInt _nActives
    !v <- IORef.readIORef _clauseVector
    MV.unsafeWrite v i =<< MV.unsafeRead v n
    setInt _nActives n
  -- | O(n) but lightweight remove-and-compact function
  -- __Pre-conditions:__ the clause manager is empty or the clause is stored in it.
  {-# SPECIALIZE INLINE removeClause :: SimpleManager -> C.Clause -> IO () #-}
  removeClause SimpleManager{..} c = do
    -- putStrLn =<< dump "@removeClause| remove " c
    -- putStrLn =<< dump "@removeClause| from " m
    !n <- subtract 1 <$> getInt _nActives
    -- unless (0 <= n) $ error $ "removeClause catches " ++ show n
    !v <- IORef.readIORef _clauseVector
    let
      seekIndex :: Int -> IO Int
      seekIndex k = do
        c' <- MV.unsafeRead v k
        if c' == c then return k else seekIndex $ k + 1
    unless (n == -1) $ do
      !i <- seekIndex 0
      MV.unsafeWrite v i =<< MV.unsafeRead v n
      setInt _nActives n

-- | O(1) inserter
{-# INLINE pushClause #-}
pushClause :: SimpleManager -> C.Clause -> IO ()
pushClause !SimpleManager{..} !c = do
  !n <- getInt _nActives
  !v <- IORef.readIORef _clauseVector
  if MV.length v - 1 <= n
    then do
        v' <- MV.unsafeGrow v (max 8 (MV.length v))
        -- forM_ [n  .. MV.length v' - 1] $ \i -> MV.unsafeWrite v' i C.NullClause
        MV.unsafeWrite v' n c
        IORef.writeIORef _clauseVector v'
    else MV.unsafeWrite v n c
  modifyInt _nActives (1 +)

instance VectorFamily SimpleManager C.Clause where
  dump mes SimpleManager{..} = do
    n <- getInt _nActives
    if n == 0
      then return $ mes ++ "empty clausemanager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)

--------------------------------------------------------------------------------

-- | Clause + Blocking Literal
data WatcherManager = WatcherManager
  {
    _nActives      :: IntSingleton               -- number of active clause
  , _clauseVector  :: IORef.IORef C.ClauseVector -- clause list
  , _blockerVector :: IORef.IORef Vec            -- blocker as minisat-2.2
  }

instance ClauseManager WatcherManager where
  {-# SPECIALIZE INLINE newManager :: Int -> IO WatcherManager #-}
  newManager initialSize = do
    i <- newInt 0
    v <- C.newClauseVector initialSize
    b <- newVec (MV.length v)
    WatcherManager i <$> IORef.newIORef v <*> IORef.newIORef b
  {-# SPECIALIZE INLINE numberOfClauses :: WatcherManager -> IO Int #-}
  numberOfClauses WatcherManager{..} = getInt _nActives
  {-# SPECIALIZE INLINE clearManager :: WatcherManager -> IO () #-}
  clearManager WatcherManager{..} = setInt _nActives 0
  {-# SPECIALIZE INLINE shrinkManager :: WatcherManager -> Int -> IO () #-}
  shrinkManager WatcherManager{..} k = modifyInt _nActives (subtract k)
  {-# SPECIALIZE INLINE getClauseVector :: WatcherManager -> IO C.ClauseVector #-}
  getClauseVector WatcherManager{..} = IORef.readIORef _clauseVector
  -- | O(n) but lightweight remove-and-compact function
  -- __Pre-conditions:__ the clause manager is empty or the clause is stored in it.
  {-# SPECIALIZE INLINE removeClause :: WatcherManager -> C.Clause -> IO () #-}
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
  removeNthClause = error "removeNthClause is not implemented on WatcherManager"

{-# INLINE getBlockerVector #-}
getBlockerVector :: WatcherManager -> IO Vec
getBlockerVector WatcherManager{..} = IORef.readIORef _blockerVector

-- | O(1) inserter
{-# INLINE pushWatcher #-}
pushWatcher :: WatcherManager -> C.Clause -> Lit -> IO ()
pushWatcher !WatcherManager{..} !c k = do
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

instance VectorFamily WatcherManager C.Clause where
  dump mes WatcherManager{..} = do
    n <- getInt _nActives
    if n == 0
      then return $ mes ++ "empty clausemanager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)

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

-------------------------------------------------------------------------------- debugging stuff

checkConsistency :: ClauseManager a => a -> C.Clause -> IO ()
checkConsistency manager c = do
  nc <- numberOfClauses manager
  vec <- getClauseVector manager
  let
    loop :: Int -> IO ()
    loop i = do
      when (i < nc) $ do
        c' <- MV.unsafeRead vec i
        when (c' == c) $ error "insert a clause to a ClauseMananger twice"
        loop $ i + 1
  loop 0

checkClauseOrder :: ClauseManager a => a -> IO ()
checkClauseOrder manager = do
  putStr "checking..."
  nc <- numberOfClauses manager
  vec <- getClauseVector manager
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
