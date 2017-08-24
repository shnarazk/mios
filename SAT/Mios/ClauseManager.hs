{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  , RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | A shrinkable vector of 'C.Clause'
module SAT.Mios.ClauseManager
       (
         -- * higher level interface for ClauseVector
         ClauseManager (..)
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
       )
       where

import Control.Monad (unless, when)
import qualified Data.IORef as IORef
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
data ClauseExtManager = ClauseExtManager
  {
    _nActives     :: !Int'                         -- number of active clause
  , _purged       :: !Bool'                        -- whether it needs gc
  , _clauseVector :: IORef.IORef C.ClauseVector    -- clause list
  , _keyVector    :: IORef.IORef (Vec [Int])       -- Int list
  }

-- | 'ClauseExtManager' is a 'SingleStorage` on the numeber of clauses in it.
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
          let len = max 8 $ MV.length v
          v' <- MV.unsafeGrow v len
          b' <- growBy b len
          MV.unsafeWrite v' n c
          setNth b' n 0
          IORef.writeIORef _clauseVector v'
          IORef.writeIORef _keyVector b'
      else MV.unsafeWrite v n c >> setNth b n 0
    modify' _nActives (1 +)

-- | 'ClauseExtManager' is a 'ClauseManager'
instance ClauseManager ClauseExtManager where
  -- | returns a new instance.
  {-# SPECIALIZE INLINE newManager :: Int -> IO ClauseExtManager #-}
  newManager initialSize = do
    i <- new' 0
    v <- newVec initialSize C.NullClause
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
  removeNthClause = errorWithoutStackTrace "removeNthClause is not implemented on ClauseExtManager"
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
getKeyVector :: ClauseExtManager -> IO (Vec [Int])
getKeyVector ClauseExtManager{..} = IORef.readIORef _keyVector

-- | O(1) inserter
{-# INLINABLE pushClauseWithKey #-}
pushClauseWithKey :: ClauseExtManager -> C.Clause -> Lit -> IO ()
pushClauseWithKey !ClauseExtManager{..} !c k = do
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
        setNth b' n k
        IORef.writeIORef _clauseVector v'
        IORef.writeIORef _keyVector b'
    else MV.unsafeWrite v n c >> setNth b n k
  modify' _nActives (1 +)

-- | 'ClauseExtManager' is a collection of 'C.Clause'
instance VecFamily ClauseExtManager (C.Clause, Int) where
  getNth = errorWithoutStackTrace "no getNth method for ClauseExtManager"
  setNth = errorWithoutStackTrace "no setNth method for ClauseExtManager"
  asList cm = do
    n <- get' cm
    l <- zip <$> (asList =<< getClauseVector cm) <*> (asList =<< getKeyVector cm)
    return (take n l)
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

-- | Immutable Vector of 'ClauseExtManager'; an 'Lit'-indexed collection of 'ClauseManager'.
-- Note: 0-th field is not used in mios; is used as multiple conflicting clauses is BCP+
type WatcherList = V.Vector ClauseExtManager

-- | /n/ is the number of 'Var', /m/ is default size of each watcher list.
-- | For /n/ vars, we need [0 .. 2 + 2 * n - 1] slots, namely /2 * (n + 1)/-length vector
newWatcherList :: Int -> Int -> IO WatcherList
newWatcherList n m = V.fromList <$> mapM (\_ -> newManager m) [0 .. int2lit (negate n)]

-- | returns the watcher List for "Literal" /l/.
{-# INLINE getNthWatcher #-}
getNthWatcher :: WatcherList -> Lit -> ClauseExtManager
getNthWatcher = V.unsafeIndex

instance VecFamily WatcherList ClauseExtManager where
  getNth = errorWithoutStackTrace "no getNth method for WatcherList" -- getNthWatcher is a pure function
  setNth = errorWithoutStackTrace "no setNth method for WatcherList"
  asList w = return $ V.toList w
  {-# SPECIALIZE INLINE reset :: WatcherList -> IO () #-}
  reset = V.mapM_ purifyManager
--  dump _ _ = (mes ++) . concat <$> mapM (\i -> dump ("\n" ++ show (lit2int i) ++ "' watchers:") (getNthWatcher wl i)) [1 .. V.length wl - 1]
