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
       , subVec
       )
       where

import Control.Monad (forM, forM_)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV

-- | __version 1.1__
--
-- Costs of all operations are /O/(/1/)
type Vec = UV.IOVector Int

{-# INLINE sizeOfVector #-}
sizeOfVector :: Vec -> IO Int
sizeOfVector v = return $! UV.length v

-- | constructors, resize, stack, vector, and duplication operations
--instance VectorLike Vec Int where
--  -- * Constructors
--  newVec n = UV.new n
--  newVecWith n x = do
--    v <- UV.new n
--    UV.set v x
--    return v
  -- * Vector operations
--  {-# SPECIALIZE INLINE getAt :: Int -> Vec -> IO Int #-}
--  getAt !n v = UV.unsafeRead v n
--  {-# SPECIALIZE INLINE setAt :: Int -> Vec -> Int -> IO () #-}
--  setAt !n v !x = UV.unsafeWrite v n x
  -- * Conversion
--  newFromList l = do
--    v <- UV.new $ length l
--    forM_ (zip [0 .. length l - 1] l) $ \(i, j) -> UV.unsafeWrite v i j
--    return v

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
newSizedVecIntFromList !l = do
  let n = length l
  v <- UV.new $ n + 1
  UV.unsafeWrite v 0 n
  -- FIXME: why you don't use 'copy'?
  forM_ (zip [1 .. n] l) $ \(i, j) -> UV.unsafeWrite v i j
  return v

{-# INLINE newSizedVecIntFromUVector #-}
newSizedVecIntFromUVector :: U.Vector Int -> IO Vec
newSizedVecIntFromUVector vec = U.unsafeThaw vec

{-# INLINE subVec #-}
subVec :: Int -> Vec -> IO Vec
subVec n v = do
  v' <- UV.new n
  forM_ [0 .. n - 1] $ \i -> UV.unsafeWrite v' i =<< UV.unsafeRead v i
  return v'
