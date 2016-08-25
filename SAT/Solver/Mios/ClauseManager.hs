{-# LANGUAGE
    BangPatterns
  , DuplicateRecordFields
  , FlexibleInstances
  , MultiParamTypeClasses
  , RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | A shrinkable vector of 'C.Clause'
module SAT.Solver.Mios.ClauseManager
       (
         -- * higher level interface for ClauseVector
         ClauseManager (..)
--       -- * vector of clauses
--       , SimpleManager
         -- * Manager with an extra Int (used as sort key or blocking literal)
       , ClauseExtManager
       , pushClauseWithKey
       , getKeyVector
       , markClause
--       , purifyManager
         -- * WatcherList
       , WatcherList
       , newWatcherList
       , getNthWatcher
       , garbageCollect
--       , numberOfRegisteredClauses
       )
       where

import Control.Monad (forM, unless, when)
import qualified Data.IORef as IORef
import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types
import qualified SAT.Solver.Mios.Clause as C

-- | resizable clause vector
class ClauseManager a where
  newManager      :: Int -> IO a
  numberOfClauses :: a -> IO Int
  clearManager    :: a -> IO ()
  shrinkManager   :: a -> Int -> IO ()
  getClauseVector :: a -> IO C.ClauseVector
  pushClause      :: a -> C.Clause -> IO ()
--  removeClause    :: a -> C.Clause -> IO ()
--  removeNthClause :: a -> Int -> IO ()

{-
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
  -- | O(1) inserter
  {-# SPECIALIZE INLINE pushClause :: SimpleManager -> C.Clause -> IO () #-}
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

instance VectorFamily SimpleManager C.Clause where
  dump mes SimpleManager{..} = do
    n <- getInt _nActives
    if n == 0
      then return $ mes ++ "empty clausemanager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)
-}

--------------------------------------------------------------------------------

-- | Clause + Blocking Literal
data ClauseExtManager = ClauseExtManager
  {
    _nActives     :: !IntSingleton               -- number of active clause
  , _purged       :: !BoolSingleton              -- whether it needs gc
  , _clauseVector :: IORef.IORef C.ClauseVector -- clause list
  , _keyVector    :: IORef.IORef Vec            -- Int list
  }

instance ClauseManager ClauseExtManager where
  {-# SPECIALIZE INLINE newManager :: Int -> IO ClauseExtManager #-}
  newManager initialSize = do
    i <- newInt 0
    v <- C.newClauseVector initialSize
    b <- newVec (MV.length v)
    ClauseExtManager i <$> newBool False <*> IORef.newIORef v <*> IORef.newIORef b
  {-# SPECIALIZE INLINE numberOfClauses :: ClauseExtManager -> IO Int #-}
  numberOfClauses ClauseExtManager{..} = getInt _nActives
  {-# SPECIALIZE INLINE clearManager :: ClauseExtManager -> IO () #-}
  clearManager ClauseExtManager{..} = setInt _nActives 0
  {-# SPECIALIZE INLINE shrinkManager :: ClauseExtManager -> Int -> IO () #-}
  shrinkManager ClauseExtManager{..} k = modifyInt _nActives (subtract k)
  {-# SPECIALIZE INLINE getClauseVector :: ClauseExtManager -> IO C.ClauseVector #-}
  getClauseVector ClauseExtManager{..} = IORef.readIORef _clauseVector
  -- | O(1) insertion function
  {-# SPECIALIZE INLINE pushClause :: ClauseExtManager -> C.Clause -> IO () #-}
  pushClause !ClauseExtManager{..} !c = do
    -- checkConsistency m c
    !n <- getInt _nActives
    !v <- IORef.readIORef _clauseVector
    !b <- IORef.readIORef _keyVector
    if MV.length v - 1 <= n
      then do
          let len = max 8 $ MV.length v
          v' <- MV.unsafeGrow v len
          b' <- vecGrow b len
          MV.unsafeWrite v' n c
          setNth b' n 0
          IORef.writeIORef _clauseVector v'
          IORef.writeIORef _keyVector b'
      else MV.unsafeWrite v n c >> setNth b n 0
    modifyInt _nActives (1 +)
{-
  -- | O(n) but lightweight remove-and-compact function
  -- __Pre-conditions:__ the clause manager is empty or the clause is stored in it.
  {-# SPECIALIZE INLINE removeClause :: ClauseExtManager -> C.Clause -> IO () #-}
  removeClause ClauseExtManager{..} c = do
    !n <- subtract 1 <$> getInt _nActives
    !v <- IORef.readIORef _clauseVector
    !b <- IORef.readIORef _keyVector
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
  removeNthClause = error "removeNthClause is not implemented on ClauseExtManager"
-}

-- | sets the expire flag to a clause
{-# INLINE markClause #-}
markClause :: ClauseExtManager -> C.Clause -> IO ()
markClause ClauseExtManager{..} c = do
  !n <- getInt _nActives
  !v <- IORef.readIORef _clauseVector
  let
    seekIndex :: Int -> IO ()
    seekIndex k = do
      c' <- MV.unsafeRead v k
      if c' == c then MV.unsafeWrite v k C.NullClause else seekIndex $ k + 1
  unless (n == 0) $ do
    seekIndex 0
    setBool _purged True

{-# INLINE purifyManager #-}
purifyManager :: ClauseExtManager -> IO ()
purifyManager ClauseExtManager{..} = do
  diry <- getBool _purged
  when diry $ do
    n <- getInt _nActives
    vec <- IORef.readIORef _clauseVector
    keys <- IORef.readIORef _keyVector
    let
      loop :: Int -> Int -> IO Int
      loop ((< n) -> False) n' = return n'
      loop i j = do
        c <- C.getNthClause vec i
        if c /= C.NullClause
          then do
              unless (i == j) $ do
                C.setNthClause vec j c
                setNth keys j =<< getNth keys i
              loop (i + 1) (j + 1)
          else loop (i + 1) j
    setInt _nActives =<< loop 0 0
    setBool _purged False

-- | returns the associated Int vector
{-# INLINE getKeyVector #-}
getKeyVector :: ClauseExtManager -> IO Vec
getKeyVector ClauseExtManager{..} = IORef.readIORef _keyVector

-- | O(1) inserter
{-# INLINE pushClauseWithKey #-}
pushClauseWithKey :: ClauseExtManager -> C.Clause -> Lit -> IO ()
pushClauseWithKey !ClauseExtManager{..} !c k = do
  -- checkConsistency m c
  !n <- getInt _nActives
  !v <- IORef.readIORef _clauseVector
  !b <- IORef.readIORef _keyVector
  if MV.length v - 1 <= n
    then do
        let len = max 8 $ MV.length v
        v' <- MV.unsafeGrow v len
        b' <- vecGrow b len
        MV.unsafeWrite v' n c
        setNth b' n k
        IORef.writeIORef _clauseVector v'
        IORef.writeIORef _keyVector b'
    else MV.unsafeWrite v n c >> setNth b n k
  modifyInt _nActives (1 +)

instance VectorFamily ClauseExtManager C.Clause where
  dump mes ClauseExtManager{..} = do
    n <- getInt _nActives
    if n == 0
      then return $ mes ++ "empty ClauseExtManager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)

-------------------------------------------------------------------------------- WatcherList

-- | Vector of 'ClauseExtManager'
type WatcherList = V.Vector ClauseExtManager

-- | /n/ is the number of 'Var', /m/ is default size of each watcher list
-- | For /n/ vars, we need [0 .. 2 + 2 * n - 1] slots, namely /2 * (n + 1)/-length vector
newWatcherList :: Int -> Int -> IO WatcherList
newWatcherList n m = V.fromList <$> forM [0 .. int2lit (negate n) + 1] (\_ -> newManager m)

-- | returns the watcher List :: "ClauseManager" for "Literal" /l/
{-# INLINE getNthWatcher #-}
getNthWatcher :: WatcherList -> Lit-> ClauseExtManager
getNthWatcher = V.unsafeIndex

instance VectorFamily WatcherList C.Clause where
  dump mes wl = (mes ++) . L.concat <$> forM [1 .. V.length wl - 1] (\i -> dump ("\n" ++ show (lit2int i) ++ "' watchers:") (getNthWatcher wl i))

-- | purges all expirable clauses in 'WatcherList'
{-# INLINE garbageCollect #-}
garbageCollect :: WatcherList -> IO ()
garbageCollect wm = V.mapM_ purifyManager wm

numberOfRegisteredClauses :: WatcherList -> IO Int
numberOfRegisteredClauses ws = sum <$> V.mapM numberOfClauses ws

{-
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
-}
