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

-- | This is the implementation pack __version 0.8 #diveIntoCore
--
-- * __ListOfInt__  @:: Data.Vector.Unboxed.IOVector INT@ -- vector for a bounded number of Ints
--
module SAT.Solver.Mios.Implementation.ListOfInt
       (
         ListOfInt (..)
       , newListOfInt
       , clearListOfInt
       , sizeOfListOfInt
       , pushToListOfInt
       , popFromListOfInt
       , lastOfListOfInt
       )
       where

import qualified Data.Vector.Unboxed.Mutable as UV

-- | __version 0.1__ : pointing a list by IORef
--
newtype ListOfInt = ListOfInt
                  {
                    ivec :: UV.IOVector Int
                  }

{-# INLINE sizeOfListOfInt #-}
sizeOfListOfInt :: ListOfInt -> IO Int
sizeOfListOfInt !(ListOfInt ivec) = UV.unsafeRead ivec 0

{-# INLINE clearListOfInt #-}
clearListOfInt :: ListOfInt -> IO ()
clearListOfInt !(ListOfInt ivec) = UV.unsafeWrite ivec 0 0

{-# INLINABLE newListOfInt #-}
newListOfInt :: Int -> IO ListOfInt
newListOfInt n = do
  v <- UV.new $ n + 1
  UV.set v 0
  return $ ListOfInt v

{-# INLINE pushToListOfInt #-}
pushToListOfInt :: ListOfInt -> Int -> IO ()
pushToListOfInt !(ListOfInt ivec) !x = do
  i <- (+ 1) <$> UV.unsafeRead ivec 0
  UV.unsafeWrite ivec i x
  UV.unsafeWrite ivec 0 i

{-# INLINE popFromListOfInt #-}
popFromListOfInt :: ListOfInt -> IO ()
popFromListOfInt !(ListOfInt ivec) = UV.unsafeModify ivec (subtract 1) 0

{-# INLINE lastOfListOfInt #-}
lastOfListOfInt :: ListOfInt -> IO Int
lastOfListOfInt !(ListOfInt ivec) = UV.unsafeRead ivec =<< UV.unsafeRead ivec 0
