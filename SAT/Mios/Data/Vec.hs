-- | The fundamental data structure: Fixed Mutable Unboxed Int Vector
{-# LANGUAGE
    BangPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Mios.Data.Vec
       (
         Vec
       , sizeOfVector
       , getNth
       , setNth
       , swapBetween
       , modifyNth
       , setAll
       , newVec
       , newVecWith
       , newSizedVecIntFromList
       , newSizedVecIntFromUVector
       , vecGrow
       )
       where

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV

-- | Costs of all operations are /O/(/1/)
type Vec = UV.IOVector Int

-- | returns the size of 'Vec'
{-# INLINE sizeOfVector #-}
sizeOfVector :: Vec -> IO Int
sizeOfVector v = return $! UV.length v

-- | returns a new 'Vec'
{-# INLINE newVec #-}
newVec :: Int -> IO Vec
newVec = UV.new

-- | returns a new 'Vec' filled with an Int
{-# INLINE newVecWith #-}
newVecWith :: Int -> Int -> IO Vec
newVecWith n x = do
  v <- UV.new n
  UV.set v x
  return v

-- | gets the nth value
{-# INLINE getNth #-}
getNth :: Vec -> Int -> IO Int
getNth = UV.unsafeRead

-- | sets the nth value
{-# INLINE setNth #-}
setNth :: Vec -> Int -> Int -> IO ()
setNth = UV.unsafeWrite

-- | modify the nth value
{-# INLINE modifyNth #-}
modifyNth :: Vec -> (Int -> Int) -> Int -> IO ()
modifyNth = UV.unsafeModify

-- | sets all elements
{-# INLINE setAll #-}
setAll :: Vec -> Int -> IO ()
setAll = UV.set

-- | swaps two elements
{-# INLINE swapBetween #-}
swapBetween:: Vec -> Int -> Int -> IO ()
swapBetween = UV.unsafeSwap

-- | returns a new 'Vec' from a @[Int]@
{-# INLINE newSizedVecIntFromList #-}
newSizedVecIntFromList :: [Int] -> IO Vec
newSizedVecIntFromList !l = U.unsafeThaw $ U.fromList (length l : l)

-- | returns a new 'Vec' from a Unboxed Int Vector
{-# INLINE newSizedVecIntFromUVector #-}
newSizedVecIntFromUVector :: U.Vector Int -> IO Vec
newSizedVecIntFromUVector = U.unsafeThaw

-- | calls @unasfeGrow@
{-# INLINE vecGrow #-}
vecGrow :: Vec -> Int -> IO Vec
vecGrow = UV.unsafeGrow
