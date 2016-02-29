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
module SAT.Solver.Mios.Data.FixedVecInt
       (
         FixedVecInt
       , sizeOfVecInt
       , getNthInt
       , setNthInt
       , swapIntsBetween
       , modifyNthInt
       , newSizedVecIntFromList
       , newSizedVecIntFromUVector
       )
       where

import Control.Monad (forM, forM_)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..))

-- | __version 0.3__
--
-- Costs of all operations are /O/(/1/)
type FixedVecInt = UV.IOVector Int

{-# INLINE sizeOfVecInt #-}
sizeOfVecInt :: FixedVecInt -> IO Int
sizeOfVecInt v = return $! UV.length v

-- | provides 'clear' and 'size'
instance ContainerLike FixedVecInt Int where
  clear = error "FixedVecInt.clear"
  {-# SPECIALIZE INLINE asList :: FixedVecInt -> IO [Int] #-}
  asList v = forM [0 .. UV.length v - 1] $ UV.unsafeRead v
  dump str v = (str ++) . show <$> asList v
  asVector v = v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike FixedVecInt Int where
  -- * Constructors
  newVec n = UV.new n
  newVecWith n x = do
    v <- UV.new n
    UV.set v x
    return v
  -- * Vector operations
  {-# SPECIALIZE INLINE getAt :: Int -> FixedVecInt -> IO Int #-}
  getAt !n v = UV.unsafeRead v n
  {-# SPECIALIZE INLINE setAt :: Int -> FixedVecInt -> Int -> IO () #-}
  setAt !n v !x = UV.unsafeWrite v n x
  -- * Conversion
  newFromList l = do
    v <- UV.new $ length l
    forM_ (zip [0 .. length l - 1] l) $ \(i, j) -> UV.unsafeWrite v i j
    return v

{-# INLINE getNthInt #-}
getNthInt :: Int -> FixedVecInt -> IO Int
getNthInt !n !v = UV.unsafeRead v n

{-# INLINE setNthInt #-}
setNthInt :: Int -> FixedVecInt -> Int -> IO ()
setNthInt !n !v !x = UV.unsafeWrite v n x

{-# INLINE modifyNthInt #-}
modifyNthInt :: Int -> FixedVecInt -> (Int -> Int) -> IO ()
modifyNthInt !n !v !f = UV.unsafeModify v f n

{-# INLINE swapIntsBetween #-}
swapIntsBetween:: FixedVecInt -> Int -> Int -> IO ()
swapIntsBetween = UV.unsafeSwap

{-# INLINE newSizedVecIntFromList #-}
newSizedVecIntFromList :: [Int] -> IO FixedVecInt
newSizedVecIntFromList !l = do
  let n = length l
  v <- UV.new $ n + 1
  UV.unsafeWrite v 0 n
  -- FIXME: why you don't use 'copy'?
  forM_ (zip [1 .. n] l) $ \(i, j) -> UV.unsafeWrite v i j
  return v

{-# INLINE newSizedVecIntFromUVector #-}
newSizedVecIntFromUVector :: U.Vector Int -> IO FixedVecInt
newSizedVecIntFromUVector vec = U.unsafeThaw vec
