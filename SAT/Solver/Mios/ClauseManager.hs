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
module SAT.Solver.Mios.ClauseManager
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
       , pushClause
       , removeClause
       , removeNthClause
         -- * Debug
       , checkClauseOrder
       )
       where

import Control.Monad (forM_, unless, when)
import qualified Data.IORef as IORef
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types (ContainerLike (..))
import qualified SAT.Solver.Mios.Clause as C
import SAT.Solver.Mios.Data.Singleton

type ClauseVector = MV.IOVector C.Clause

instance ContainerLike ClauseVector C.Clause where
  asList cv = V.toList <$> V.freeze cv
  dump mes cv = do
    l <- take 10 <$> asList cv
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
data ClauseManager = ClauseManager
  {
    _nActives     :: IntSingleton -- number of active clause
  , _clauseVector :: IORef.IORef ClauseVector -- clause list
  }

newClauseManager :: Int -> IO ClauseManager
newClauseManager initialSize = do
  i <- newInt 0
  v <- newClauseVector initialSize
  ClauseManager i <$> IORef.newIORef v

{-# INLINE numberOfClauses #-}
numberOfClauses :: ClauseManager -> IO Int
numberOfClauses ClauseManager{..} = getInt _nActives

clearClauseManager :: ClauseManager -> IO ()
clearClauseManager ClauseManager{..} = setInt _nActives 0

{-# INLINE shrinkClauseManager #-}
shrinkClauseManager :: ClauseManager -> Int -> IO ()
shrinkClauseManager ClauseManager{..} = setInt _nActives

{-# INLINE getClauseVector #-}
getClauseVector :: ClauseManager -> IO ClauseVector
getClauseVector ClauseManager{..} = IORef.readIORef _clauseVector

-- | O(1) inserter
{-# INLINE pushClause #-}
pushClause :: ClauseManager -> C.Clause -> IO ()
pushClause !ClauseManager{..} !c = do
  -- checkConsistency m c
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
{-# INLINE removeNthClause #-}
removeNthClause :: ClauseManager -> Int -> IO ()
removeNthClause ClauseManager{..} i = do
  !n <- subtract 1 <$> getInt _nActives
  !v <- IORef.readIORef _clauseVector
  MV.unsafeWrite v i =<< MV.unsafeRead v n
  setInt _nActives n

-- | O(n) but lightweight remove-and-compact function
{-# INLINE removeClause #-}
removeClause :: ClauseManager -> C.Clause -> IO ()
removeClause ClauseManager{..} c = do
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
  !i <- seekIndex 0
  MV.unsafeWrite v i =<< MV.unsafeRead v n
  setInt _nActives n

instance ContainerLike ClauseManager C.Clause where
  dump mes ClauseManager{..} = do
    n <- getInt _nActives
    if n == 0
      then return $ mes ++ "empty clausemanager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)

checkConsistency :: ClauseManager -> C.Clause -> IO ()
checkConsistency ClauseManager{..} c = do
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
checkClauseOrder :: ClauseManager -> IO ()
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
