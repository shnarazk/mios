{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , TypeFamilies
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | This is the implementation pack __version 0.6 #activityEstimation
--
-- * __ListOf a__  @:: IORef [a]@ -- data type that contains a mutable list of elements
--
module SAT.Solver.Mios.Data.ListOf
       (
         ListOf (..)
       , newList
       , newListFromList
       , sizeOfVec
       , pushToList
       , popFromList
       , lastOfList
       , setToList
       )
       where

import Data.IORef
import SAT.Solver.Mios.Types (ContainerLike(..))

-- | __version 0.1__ : pointing a list by IORef
--
newtype ListOf a = ListOf
                  {
                    ptr :: IORef [a] -- ^ reference pointer to the data
                  }

{-# INLINE sizeOfVec #-}
sizeOfVec :: ListOf a -> IO Int
sizeOfVec (ListOf ptr) = length <$> readIORef ptr

-- | provides 'clear' and 'size'
instance ContainerLike (ListOf a) a where
  {-# SPECIALIZE INLINE asList :: ListOf Int -> IO [Int] #-}
  {-# SPECIALIZE INLINE asList :: ListOf Bool -> IO [Bool] #-}
  asList (ListOf ptr) = readIORef ptr
  dump str (ListOf ptr) = (str ++) . show <$> readIORef ptr

{-# INLINABLE newList #-}
newList :: IO (ListOf a)
newList = ListOf <$> newIORef []

{-# INLINABLE newListFromList #-}
newListFromList :: [a] -> IO (ListOf a)
newListFromList !l = ListOf <$> newIORef l

{-# INLINE pushToList #-}
pushToList :: ListOf Int -> Int -> IO ()
pushToList (ListOf ptr) !x = modifyIORef' ptr (x :)

{-# INLINE popFromList #-}
popFromList :: ListOf Int -> IO ()
popFromList (ListOf ptr) = modifyIORef' ptr tail

{-# INLINE lastOfList #-}
lastOfList :: ListOf Int -> IO Int
lastOfList (ListOf ptr) = head <$> readIORef ptr

{-# INLINE setToList #-}
setToList :: ListOf Int -> [Int] -> IO ()
setToList (ListOf ptr) = writeIORef ptr
