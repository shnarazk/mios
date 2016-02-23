{-# LANGUAGE
    FlexibleInstances
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
       , getNthClause
       , setNthClause
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
       )
       where

import Control.Monad (unless)
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

{-# INLINE getNthClause #-}
getNthClause :: ClauseVector -> Int -> IO C.Clause
getNthClause = MV.unsafeRead

{-# INLINE setNthClause #-}
setNthClause :: ClauseVector -> Int -> C.Clause -> IO ()
setNthClause = MV.unsafeWrite

-- | The Clause Container
data ClauseManager = ClauseManager
  {
    _nActives     :: IntSingleton -- number of active clause
  , _clauseVector :: IORef.IORef ClauseVector -- clause list
  }

newClauseManager :: Int -> IO ClauseManager
newClauseManager initialSize = do
  i <- newInt 0
  v <- MV.new initialSize
  MV.set v C.NullClause
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
pushClause :: ClauseManager -> C.Clause -> IO ()
pushClause ClauseManager{..} c = do
  n <- getInt _nActives
  v <- IORef.readIORef _clauseVector
  v' <- if MV.length v <= n
       then do
        v' <- MV.grow v 200
        IORef.writeIORef _clauseVector v'
        return v'
       else return v
  MV.unsafeWrite v' n c
  modifyInt _nActives (1 +)

-- | O(1) remove-and-compact function
{-# INLINE removeNthClause #-}
removeNthClause :: ClauseManager -> Int -> IO ()
removeNthClause ClauseManager{..} i = do
  n <- subtract 1 <$> getInt _nActives
  v <- IORef.readIORef _clauseVector
  MV.unsafeWrite v i =<< MV.unsafeRead v n
  setInt _nActives n

-- | O(n) but lightweight remove-and-compact function
{-# INLINE removeClause #-}
removeClause :: ClauseManager -> C.Clause -> IO ()
removeClause ClauseManager{..} c = do
  -- putStrLn =<< dump "@removeClause| remove " c
  -- putStrLn =<< dump "@removeClause| from " m
  n <- subtract 1 <$> getInt _nActives
  -- unless (0 <= n) $ error $ "removeClause catches " ++ show n
  v <- IORef.readIORef _clauseVector
  let
    seekIndex :: Int -> IO Int
    seekIndex k = do
      c' <- MV.unsafeRead v k
      if c' == c then return k else seekIndex $ k + 1
  i <- seekIndex 0
  MV.unsafeWrite v i =<< MV.unsafeRead v n
  setInt _nActives n

instance ContainerLike ClauseManager C.Clause where
  dump mes ClauseManager{..} = do
    n <- IORef.readIORef _nActives
    if n == 0
      then return $ mes ++ "empty clausemanager"
      else do
          l <- take n <$> (asList =<< IORef.readIORef _clauseVector)
          sts <- mapM (dump ",") (l :: [C.Clause])
          return $ mes ++ "[" ++ show n ++ "]" ++ tail (concat sts)
