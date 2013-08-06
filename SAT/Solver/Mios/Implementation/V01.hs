{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TypeFamilies
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | This is the implementation pack __version 0.1__ for mios: #check-consistency
--
-- * __Vec__ :: @IORef [a]@ -- data type that contains a mutable list of elements
--
-- * __VerOrder__ :: @IORef [Var]@
--
module SAT.Solver.Mios.Implementation.V01 where

import Control.Monad
import Data.IORef
import Data.List
import System.Mem.StableName
import SAT.Solver.Mios.Types

-- | sets to the version name: @"mios v0.1 #check-consistency"@
idString :: String
idString = "mios v0.1 #check-consistency"

-- | __version 0.1__
--
-- Costs of all operations are /O/(/n/)
data VecOf a = VecOf
              {
                ptr :: IORef [a] -- ^ reference pointer to the data
              }

-- | provides 'clear' and 'size'
instance ContainerLike (VecOf a) where
  clear VecOf{..} = writeIORef ptr []
  size VecOf{..} = length <$> readIORef ptr

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (VecOf a) a where
  -- * Constructors
  emptyVec = VecOf <$> newIORef []
  newVec = VecOf <$> newIORef []
  newVecSized n = VecOf <$> newIORef (replicate n undefined)
  newVecSizedWith n x = VecOf <$> newIORef (replicate n x)
  -- * Size operations
  shrink n VecOf{..} = do
    writeIORef ptr . take n =<< readIORef ptr
  growTo _ _ = return ()
  growToWith _ _ = return ()
  -- * Stack operations
  pop VecOf{..} = do
    l <- readIORef ptr
    unless (null l) $ writeIORef ptr $ init l
  push VecOf{..} x = do
    l <- readIORef ptr
    writeIORef ptr $ l ++ [x]
  lastE VecOf{..} = do
    l <- readIORef ptr
    return $ last l
  removeElem x VecOf{..} = do
    l <- readIORef ptr
    writeIORef ptr =<< deleteWOEq x l
  -- * Vector operations
  (.!) VecOf{..} n = (!! n) <$> readIORef ptr
  setAt VecOf{..} n x = do
    l <- readIORef ptr
    writeIORef ptr $ take n l ++ (x : drop (n + 1) l)
  -- * Duplication
  copyTo v1 v2 = do
    l1 <- readIORef (ptr v1)
    writeIORef (ptr v2) l1
  moveTo v1 v2 = do
    l1 <- readIORef (ptr v1)
    writeIORef (ptr v2) l1
    writeIORef (ptr v1) []
  -- * Conversion
  newFromList l = VecOf <$> newIORef l
  asList VecOf{..} = readIORef ptr
  checkConsistency str VecOf{..} func = do
    res <- and <$> (mapM func =<< readIORef ptr)
    unless res $ error str
  dump str VecOf{..} = (str ++) . show <$> readIORef ptr

-- | A normal implementation of 'removeElem' would use
-- @delete :: Eq a => a -> [a] -> [a]@. But this means
-- the element type of 'VecOf' has 'Eq' type constraint. It make difficult
-- to handle mutable types. Thus I use an equality checker based on
-- pointer equivalency.
deleteWOEq :: a -> [a] -> IO [a]
deleteWOEq _ [] = return []
deleteWOEq x (y:l) = do
  e <- x <==> y
  if e
    then deleteWOEq x l
    else (y :) <$> deleteWOEq x l

-- | unit test function
--
-- >>> checkImplementation
-- [3,1,2,1]
-- [5,4,1,2,1]
-- 1
--
checkImplementation = do
  v <- newVec :: IO (VecOf Int)
  mapM_ (push v) [1 :: Int, 2, 1, 3]
  print =<< readIORef (ptr v)
  mapM_ (push v) [4 :: Int, 3, 5]
  removeElem 3 v
  print =<< readIORef (ptr v)
  v2 <- newVec :: IO (VecOf (VecOf Int))
  push v2 v
  print =<< size v2
  return ()

-- | sort elements in /big-to-small/ order
sortByFst :: VecOf (Double, Int) -> IO ()
sortByFst VecOf{..} = writeIORef ptr . reverse . sortOn fst =<< readIORef ptr

-- | __version 0.1__
--
-- Costs of all operations are /O/(/n/)
data QueueOf a = QueueOf
              {
                qPtr :: IORef [a] -- ^ reference pointer to the data
              }

-- | provides 'clear' and 'size'
instance ContainerLike (QueueOf a) where
  clear QueueOf{..} = writeIORef qPtr []
  size QueueOf{..} = length <$> readIORef qPtr

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (QueueOf a) a where
  -- * Constructors
  emptyVec = QueueOf <$> newIORef []
  newVec = QueueOf <$> newIORef []
  newVecSized n = QueueOf <$> newIORef (replicate n undefined)
  newVecSizedWith n x = QueueOf <$> newIORef (replicate n x)
  -- * Size operations
  shrink n QueueOf{..} = do
    writeIORef qPtr . take n =<< readIORef qPtr
  growTo _ _ = return ()
  growToWith _ _ = return ()
  -- * Stack operations
  pop QueueOf{..} = do
    l <- readIORef qPtr
    unless (null l) $ writeIORef qPtr $ init l
  push QueueOf{..} x = do
    l <- readIORef qPtr
    writeIORef qPtr $ l ++ [x]
  lastE QueueOf{..} = do
    l <- readIORef qPtr
    return $ last l
  removeElem x QueueOf{..} = do
    l <- readIORef qPtr
    writeIORef qPtr =<< deleteWOEq x l
  -- * Vector operations
  (.!) QueueOf{..} n = (!! n) <$> readIORef qPtr
  setAt QueueOf{..} n x = do
    l <- readIORef qPtr
    writeIORef qPtr $ take (n -1) l ++ (x : drop n l)
  -- * Duplication
  copyTo v1 v2 = do
    l1 <- readIORef (qPtr v1)
    writeIORef (qPtr v2) l1
  moveTo v1 v2 = do
    l1 <- readIORef (qPtr v1)
    writeIORef (qPtr v2) l1
    writeIORef (qPtr v1) []
  -- * Conversion
  newFromList l = QueueOf <$> newIORef l
  asList QueueOf{..} = readIORef qPtr
  dump str QueueOf{..} = (str ++) . show <$> readIORef qPtr

-- | 'Lit' Container
-- this is a derived type, thus no need to instanciation for 'ContainerLike'
-- type VecLit = UV.IOVector Lit
instance QueueLike (QueueOf a) a where
  newQueue = QueueOf <$> newIORef []
  insert QueueOf{..} x = do
    l <- readIORef qPtr
    writeIORef qPtr $ l ++ [x]
  dequeue QueueOf{..} = do
    l <- readIORef qPtr
    if null l
      then error "empty queue"
      else do
          let x = head l
          writeIORef qPtr $ tail l
          return x
