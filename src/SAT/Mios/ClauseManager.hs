-- | (This is a part of MIOS.)
-- A shrinkable vector of 'C.Clause'
{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  , RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Mios.ClauseManager
       (
         -- * higher level interface for ClauseVector
         ClauseManager (..)
         -- * Simple Clause Manager
       , ClauseSimpleManager
         -- * Manager with an extra Int (used as sort key or blocking literal)
       , ClauseExtManager
       , pushClauseWithKey
       , getKeyVector
       , markClause
--       , allocateKeyVectorSize
         -- * WatcherList
       , WatcherList
       , newWatcherList
       , getNthWatcher
       )
       where

import Control.Monad (unless, when)
import qualified Data.IORef as IORef
import qualified Data.Primitive.ByteArray as BA
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import SAT.Mios.Types
import qualified SAT.Mios.Clause as C

-- | Resizable vector of 'C.Clause'.
class ClauseManager a where
  newManager      :: Int -> IO a
  getClauseVector :: a -> IO C.ClauseVector
--  removeClause    :: a -> C.Clause -> IO ()
--  removeNthClause :: a -> Int -> IO ()

--------------------------------------------------------------------------------

-- | Clause + Blocking Literal
data ClauseSimpleManager = ClauseSimpleManager
  {
    _numActives :: !Int'                         -- number of active clause
  , _clsVector  :: IORef.IORef C.ClauseVector    -- clause list
  }

-- | 'ClauseSimpleManager' is a 'SingleStorage` on the number of clauses in it.
instance SingleStorage ClauseSimpleManager Int where
  {-# SPECIALIZE INLINE get' :: ClauseSimpleManager -> IO Int #-}
  get' m = get' (_numActives m)
  {-# SPECIALIZE INLINE set' :: ClauseSimpleManager -> Int -> IO () #-}
  set' m = set' (_numActives m)

-- | 'ClauseSimpleManager' is a 'StackFamily` on clauses.
instance StackFamily ClauseSimpleManager C.Clause where
  {-# SPECIALIZE INLINE shrinkBy :: ClauseSimpleManager -> Int -> IO () #-}
  shrinkBy m k = modify' (_numActives m) (subtract k)
  pushTo ClauseSimpleManager{..} c = do
    -- checkConsistency m c
    !n <- get' _numActives
    !v <- IORef.readIORef _clsVector
    if MV.length v - 1 <= n
      then do
          let len = max 8 $ MV.length v
          v' <- MV.unsafeGrow v len
          MV.unsafeWrite v' n c
          IORef.writeIORef _clsVector v'
      else MV.unsafeWrite v n c
    modify' _numActives (1 +)
  popFrom m = modify' (_numActives m) (subtract 1)
  lastOf ClauseSimpleManager{..} = do
    n <- get' _numActives
    v <- IORef.readIORef _clsVector
    MV.unsafeRead v (n - 1)

-- | 'ClauseSimpleManager' is a 'ClauseManager'
instance ClauseManager ClauseSimpleManager where
  -- | returns a new instance.
  {-# SPECIALIZE INLINE newManager :: Int -> IO ClauseSimpleManager #-}
  newManager initialSize = do
    i <- new' 0
    v <- C.newClauseVector initialSize
    ClauseSimpleManager i <$> IORef.newIORef v
  -- | returns the internal 'C.ClauseVector'.
  {-# SPECIALIZE INLINE getClauseVector :: ClauseSimpleManager -> IO C.ClauseVector #-}
  getClauseVector !m = IORef.readIORef (_clsVector m)

--------------------------------------------------------------------------------

-- | Clause + Blocking Literal
data ClauseExtManager = ClauseExtManager
  {
    _nActives     :: !Int'                         -- number of active clause
  , _purged       :: !Bool'                        -- whether it needs gc
  , _clauseVector :: IORef.IORef C.ClauseVector    -- clause list
  , _keyVector    :: IORef.IORef (Vec Int)         -- Int list
  }

-- | 'ClauseExtManager' is a 'SingleStorage` on the number of clauses in it.
instance SingleStorage ClauseExtManager Int where
  {-# SPECIALIZE INLINE get' :: ClauseExtManager -> IO Int #-}
  get' m = get' (_nActives m)
  {-# SPECIALIZE INLINE set' :: ClauseExtManager -> Int -> IO () #-}
  set' m = set' (_nActives m)

-- | 'ClauseExtManager' is a 'StackFamily` on clauses.
instance StackFamily ClauseExtManager C.Clause where
  {-# SPECIALIZE INLINE shrinkBy :: ClauseExtManager -> Int -> IO () #-}
  shrinkBy m k = modify' (_nActives m) (subtract k)
  pushTo ClauseExtManager{..} c = do
    -- checkConsistency m c
    !n <- get' _nActives
    !v <- IORef.readIORef _clauseVector
    !b <- IORef.readIORef _keyVector
    if MV.length v - 1 <= n
      then do
          let len = max 8 $ div (MV.length v) 2
          v' <- MV.unsafeGrow v len
          b' <- growBy b len
          MV.unsafeWrite v' n c
          setNth b' n 0
          IORef.writeIORef _clauseVector v'
          IORef.writeIORef _keyVector b'
      else MV.unsafeWrite v n c >> setNth b n 0
    modify' _nActives (1 +)
  popFrom m = modify' (_nActives m) (subtract 1)
  lastOf ClauseExtManager{..} = do
    n <- get' _nActives
    v <- IORef.readIORef _clauseVector
    MV.unsafeRead v (n - 1)

-- | 'ClauseExtManager' is a 'ClauseManager'
instance ClauseManager ClauseExtManager where
  -- | returns a new instance.
  {-# SPECIALIZE INLINE newManager :: Int -> IO ClauseExtManager #-}
  newManager initialSize = do
    i <- new' 0
    v <- C.newClauseVector initialSize
    b <- newVec (MV.length v) 0
    ClauseExtManager i <$> new' False <*> IORef.newIORef v <*> IORef.newIORef b
  -- | returns the internal 'C.ClauseVector'.
  {-# SPECIALIZE INLINE getClauseVector :: ClauseExtManager -> IO C.ClauseVector #-}
  getClauseVector !m = IORef.readIORef (_clauseVector m)
{-
  -- | O(1) insertion function
  pushClause !ClauseExtManager{..} !c = do
    -- checkConsistency m c
    !n <- get' _nActives
    !v <- IORef.readIORef _clauseVector
    !b <- IORef.readIORef _keyVector
    if MV.length v - 1 <= n
      then do
          let len = max 8 $ MV.length v
          v' <- MV.unsafeGrow v len
          b' <- growBy b len
          MV.unsafeWrite v' n c
          setNth b' n 0
          IORef.writeIORef _clauseVector v'
          IORef.writeIORef _keyVector b'
      else MV.unsafeWrite v n c >> setNth b n 0
    modify' _nActives (1 +)
-}
{-
  -- | O(n) but lightweight remove-and-compact function
  -- __Pre-conditions:__ the clause manager is empty or the clause is stored in it.
  {-# SPECIALIZE INLINE removeClause :: ClauseExtManager -> C.Clause -> IO () #-}
  removeClause ClauseExtManager{..} c = do
    !n <- subtract 1 <$> get' _nActives
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
      set' _nActives n
  removeNthClause = error "removeNthClause is not implemented on ClauseExtManager"
-}

-- | sets the expire flag to a clause.
{-# INLINABLE markClause #-}
markClause :: ClauseExtManager -> C.Clause -> IO ()
markClause ClauseExtManager{..} c = do
  !n <- get' _nActives
  !v <- IORef.readIORef _clauseVector
  let
    seekIndex :: Int -> IO ()
    seekIndex k = do
      -- assert (k < n)
      c' <- MV.unsafeRead v k
      if c' == c then MV.unsafeWrite v k C.NullClause else seekIndex $ k + 1
  unless (n == 0) $ do
    seekIndex 0
    set' _purged True

{-# INLINABLE purifyManager #-}
purifyManager :: ClauseExtManager -> IO ()
purifyManager ClauseExtManager{..} = do
  diry <- get' _purged
  when diry $ do
    n <- get' _nActives
    vec <- IORef.readIORef _clauseVector
    keys <- IORef.readIORef _keyVector
    let
      loop :: Int -> Int -> IO Int
      loop ((< n) -> False) n' = return n'
      loop i j = do
        c <- getNth vec i
        if c /= C.NullClause
          then do
              unless (i == j) $ do
                setNth vec j c
                setNth keys j =<< getNth keys i
              loop (i + 1) (j + 1)
          else loop (i + 1) j
    set' _nActives =<< loop 0 0
    set' _purged False

-- | returns the associated Int vector, which holds /blocking literals/.
{-# INLINE getKeyVector #-}
getKeyVector :: ClauseExtManager -> IO (Vec Int)
getKeyVector ClauseExtManager{..} = IORef.readIORef _keyVector

-- | O(1) inserter
{-# INLINABLE pushClauseWithKey #-}
pushClauseWithKey :: ClauseExtManager -> C.Clause -> Lit -> IO ()
pushClauseWithKey ClauseExtManager{..} !c k = do
  -- checkConsistency m c
  !n <- get' _nActives
  !v <- IORef.readIORef _clauseVector
  !b <- IORef.readIORef _keyVector
  if MV.length v - 1 <= n
    then do
        let len = max 8 $ div (MV.length v) 2
        v' <- MV.unsafeGrow v len
        b' <- growBy b len
        MV.unsafeWrite v' n c
        setNth b' n k
        IORef.writeIORef _clauseVector v'
        IORef.writeIORef _keyVector b'
    else MV.unsafeWrite v n c >> setNth b n k
  modify' _nActives (1 +)

-- | 'ClauseExtManager' is a collection of 'C.Clause'
instance VecFamily ClauseExtManager C.Clause where
  getNth = error "no getNth method for ClauseExtManager"
  setNth = error "no setNth method for ClauseExtManager"
  {-# SPECIALIZE INLINE reset :: ClauseExtManager -> IO () #-}
  reset m = set' (_nActives m) 0
{-
  dump mes ClauseExtManager{..} = do
    n <- get' _nActives
    if n == 0
      then return $ mes ++ "empty ClauseExtManager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)
-}

-------------------------------------------------------------------------------- WatcherList

-- | Immutable Vector of 'ClauseExtManager'
type WatcherList = V.Vector ClauseExtManager

-- | /n/ is the number of 'Var', /m/ is default size of each watcher list.
-- | For /n/ vars, we need [0 .. 2 + 2 * n - 1] slots, namely /2 * (n + 1)/-length vector
-- FIXME: sometimes n > 1M
newWatcherList :: Int -> Int -> IO WatcherList
newWatcherList n m = do let n' = int2lit (negate n) + 2
                        v <- MV.unsafeNew n'
                        mapM_  (\i -> MV.unsafeWrite v i =<< newManager m) [0 .. n' - 1]
                        V.unsafeFreeze v

-- | returns the watcher List for "Literal" /l/.
{-# INLINE getNthWatcher #-}
getNthWatcher :: WatcherList -> Lit -> ClauseExtManager
getNthWatcher = V.unsafeIndex

-- | 'WatcherList' is an 'Lit'-indexed collection of 'C.Clause'.
instance VecFamily WatcherList C.Clause where
  getNth = error "no getNth method for WatcherList" -- getNthWatcher is a pure function
  setNth = error "no setNth method for WatcherList"
  {-# SPECIALIZE INLINE reset :: WatcherList -> IO () #-}
  reset = V.mapM_ purifyManager
--  dump _ _ = (mes ++) . concat <$> mapM (\i -> dump ("\n" ++ show (lit2int i) ++ "' watchers:") (getNthWatcher wl i)) [1 .. V.length wl - 1]

--------------------------------------------------------------------------------

-- | returns the associated Int vector, which holds /blocking literals/.
{-# INLINE setKeyVector #-}
setKeyVector :: ClauseExtManager -> Vec Int -> IO ()
setKeyVector ClauseExtManager{..} v = IORef.writeIORef _keyVector v

{-# INLINABLE allocateKeyVectorSize #-}
allocateKeyVectorSize :: ClauseExtManager -> Int -> IO (Vec Int)
allocateKeyVectorSize  ClauseExtManager{..} n' = do
  v <- IORef.readIORef _keyVector
  if realLength v < n'          -- never shrink it
    then do v' <- newVec n' 0
            IORef.writeIORef _keyVector v'
            return v'
    else return v
