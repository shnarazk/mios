{-# LANGUAGE
    BangPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | The fundamental data structure: Fixed Unboxed Int Vector
module SAT.Solver.Mios.Data.Vec
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

{-# INLINE sizeOfVector #-}
sizeOfVector :: Vec -> IO Int
sizeOfVector v = return $! UV.length v

{-# INLINE newVec #-}
newVec :: Int -> IO Vec
newVec = UV.new

{-# INLINE newVecWith #-}
newVecWith :: Int -> Int -> IO Vec
newVecWith n x = do
  v <- UV.new n
  UV.set v x
  return v

{-# INLINE getNth #-}
getNth :: Vec -> Int -> IO Int
getNth = UV.unsafeRead

{-# INLINE setNth #-}
setNth :: Vec -> Int -> Int -> IO ()
setNth = UV.unsafeWrite

{-# INLINE modifyNth #-}
modifyNth :: Vec -> (Int -> Int) -> Int -> IO ()
modifyNth = UV.unsafeModify

{-# INLINE setAll #-}
setAll :: Vec -> Int -> IO ()
setAll = UV.set

{-# INLINE swapBetween #-}
swapBetween:: Vec -> Int -> Int -> IO ()
swapBetween = UV.unsafeSwap

{-# INLINE newSizedVecIntFromList #-}
newSizedVecIntFromList :: [Int] -> IO Vec
newSizedVecIntFromList !l = U.unsafeThaw $ U.fromList (length l : l)

{-# INLINE newSizedVecIntFromUVector #-}
newSizedVecIntFromUVector :: U.Vector Int -> IO Vec
newSizedVecIntFromUVector = U.unsafeThaw

vecGrow :: Vec -> Int -> IO Vec
vecGrow = UV.unsafeGrow
