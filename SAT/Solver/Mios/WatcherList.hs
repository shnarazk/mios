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
module SAT.Solver.Mios.WatcherList
       (
         -- * Vector of Clause
         ClauseVector
       , newClauseVector
       , getNthClause
       , setNthClause
       , swapClauses
         -- * higher level interface for ClauseVector
       , ClauseManager (..)
       , newClauseManager
       , numberOfClauses
       , clearClauseManager
       , shrinkClauseManager
       , getClauseVector
       , getBlockerVector
       , pushClause
       , removeClause
         -- * Debug
       , checkClauseOrder
       )
       where

import Control.Monad (forM_, unless, when)
import qualified Data.IORef as IORef
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types
import qualified SAT.Solver.Mios.Clause as C

type ClauseVector = MV.IOVector C.Clause

instance VectorFamily ClauseVector C.Clause where
  asList cv = V.toList <$> V.freeze cv
  dump mes cv = do
    l <- asList cv
    sts <- mapM (dump ",") (l :: [C.Clause])
    return $ mes ++ tail (concat sts)

newClauseVector  :: Int -> IO ClauseVector
newClauseVector n = do
  v <- MV.new (max 4 n)
  MV.set v C.NullClause
  return v

{-# INLINE getNthClause #-}
getNthClause :: ClauseVector -> Int -> IO C.Clause
getNthClause = MV.unsafeRead

{-# INLINE setNthClause #-}
setNthClause :: ClauseVector -> Int -> C.Clause -> IO ()
setNthClause = MV.unsafeWrite

{-# INLINE swapClauses #-}
swapClauses :: ClauseVector -> Int -> Int -> IO ()
swapClauses = MV.unsafeSwap

-- | The Clause Container
data WatcherList = WatcherList
  {
    _nActives      :: IntSingleton             -- number of active clause
  , _clauseVector  :: IORef.IORef ClauseVector -- clause list
  , _blockerVector :: IORef.IORef Vec          -- blocker as minisat-2.2
  }

newWatcherList :: Int -> IO WatcherList
newWatcherList initialSize = do
  i <- newInt 0
  v <- newClauseVector initialSize
  b <- newVec (MV.length v)
  WatcherList i <$> IORef.newIORef v <*> IORef.newIORef b

{-# INLINE numberOfClauses #-}
numberOfClauses :: WatcherList -> IO Int
numberOfClauses WatcherList{..} = getInt _nActives

{-# INLINE clearWatcherList #-}
clearWatcherList :: WatcherList -> IO ()
clearWatcherList WatcherList{..} = setInt _nActives 0

{-# INLINE shrinkWatcherList #-}
shrinkWatcherList :: WatcherList -> Int -> IO ()
shrinkWatcherList WatcherList{..} k = modifyInt _nActives (subtract k)

{-# INLINE getClauseVector #-}
getClauseVector :: WatcherList -> IO ClauseVector
getClauseVector WatcherList{..} = IORef.readIORef _clauseVector

{-# INLINE getBlockerVector #-}
getBlockerVector :: WatcherList -> IO Vec
getBlockerVector WatcherList{..} = IORef.readIORef _blockerVector

-- | O(1) inserter
{-# INLINE pushClause #-}
pushClause :: WatcherList -> C.Clause -> Lit -> IO ()
pushClause !WatcherList{..} !c k = do
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

-- | O(1) remove-and-compact function
{-# INLINE removeNthClause #-}
removeNthClause :: WatcherList -> Int -> IO ()
removeNthClause WatcherList{..} i = do
  !n <- subtract 1 <$> getInt _nActives
  !v <- IORef.readIORef _clauseVector
  !b <- IORef.readIORef _blockerVector
  MV.unsafeWrite v i =<< MV.unsafeRead v n
  setNth b i =<< getNth b i
  setInt _nActives n

-- | O(n) but lightweight remove-and-compact function
-- __Pre-conditions:__ the clause manager is empty or the clause is stored in it.
{-# INLINE removeClause #-}
removeClause :: WatcherList -> C.Clause -> IO ()
removeClause WatcherList{..} c = do
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

instance VectorFamily WatcherList C.Clause where
  dump mes WatcherList{..} = do
    n <- getInt _nActives
    if n == 0
      then return $ mes ++ "empty clausemanager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)

-- | for debug
checkConsistency :: WatcherList -> C.Clause -> IO ()
checkConsistency WatcherList{..} c = do
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
checkClauseOrder :: WatcherList -> IO ()
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

-- | exported interface
type ClauseManager  = WatcherList
newClauseManager    = newWatcherList
clearClauseManager  = clearWatcherList
shrinkClauseManager = shrinkWatcherList
