-- | Mutable Unboxed Vector
--
-- * __VecBool@::UV.IOVector Bool@ -- data type that contains a mutable list of elements
--
{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE TypeFamilies, DataKinds #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Mios.Data.Vec
       (
         Vec
       , MiosVector (..)
         -- * for Vec Int
       , newSizedVecIntFromList
       , newSizedVecIntFromUVector
       )
       where

import Control.Monad (forM)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV

-- | Mutable unboxed Vector

type Vec a = UV.IOVector a

class MiosVector v a | v -> a, a -> v where
  newVec :: Int -> a -> IO v
  getNth ::v -> Int -> IO a
  setNth :: v -> Int -> a -> IO ()
  modifyNth :: v -> (a -> a) -> Int -> IO ()
  swapBetween :: v -> Int -> Int -> IO ()
  setAll :: v -> a -> IO ()
  vecGrow :: v -> Int -> IO v

instance MiosVector (Vec Int) Int where
  {-# SPECIALIZE INLINE newVec :: Int -> Int -> IO (Vec Int) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: Vec Int -> Int -> IO Int #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: Vec Int -> Int -> Int -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: Vec Int -> (Int -> Int) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: Vec Int -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: Vec Int -> Int -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE vecGrow :: Vec Int -> Int -> IO (Vec Int) #-}
  vecGrow = UV.unsafeGrow

instance MiosVector (Vec Bool) Bool where
  {-# SPECIALIZE INLINE newVec :: Int -> Bool -> IO (Vec Bool) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: Vec Bool -> Int -> IO Bool #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: Vec Bool -> Int -> Bool -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: Vec Bool -> (Bool -> Bool) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: Vec Bool -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: Vec Bool -> Bool -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE vecGrow :: (Vec Bool) -> Int -> IO (Vec Bool) #-}
  vecGrow = UV.unsafeGrow

instance MiosVector (Vec Double) Double where
  {-# SPECIALIZE INLINE newVec :: Int -> Double -> IO (Vec Double) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: Vec Double -> Int -> IO Double #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: Vec Double -> Int -> Double -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: Vec Double -> (Double -> Double) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: Vec Double -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: Vec Double -> Double -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE vecGrow :: (Vec Double) -> Int -> IO (Vec Double) #-}
  vecGrow = UV.unsafeGrow

--------------------------------------------------------------------------------

-- | returns a new 'Vec' from a @[Int]@
{-# INLINE newSizedVecIntFromList #-}
newSizedVecIntFromList :: [Int] -> IO (Vec Int)
newSizedVecIntFromList !l = U.unsafeThaw $ U.fromList (length l : l)

-- | returns a new 'Vec' from a Unboxed Int Vector
{-# INLINE newSizedVecIntFromUVector #-}
newSizedVecIntFromUVector :: U.Vector Int -> IO (Vec Int)
newSizedVecIntFromUVector = U.unsafeThaw
