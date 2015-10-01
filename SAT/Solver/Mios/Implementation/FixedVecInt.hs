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
-- * __FixedVecInt @:: MV.IOVector Int@
--
module SAT.Solver.Mios.Implementation.FixedVecInt
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
import Data.List hiding (insert)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..))

-- | __version 0.3__
--
-- Costs of all operations are /O/(/1/)
newtype FixedVecInt = FixedVecInt
                      {
                        litVec :: UV.IOVector Int
                      }

{-# INLINE sizeOfVecInt #-}
sizeOfVecInt :: FixedVecInt -> IO Int
sizeOfVecInt FixedVecInt{..} = return $ UV.length litVec

-- | provides 'clear' and 'size'
instance ContainerLike FixedVecInt Int where
  clear FixedVecInt{..} = error "FixedVecInt.clear"
  {-# SPECIALIZE INLINE asList :: FixedVecInt -> IO [Int] #-}
  asList FixedVecInt{..} = forM [0 .. UV.length litVec - 1] $ UV.unsafeRead litVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike FixedVecInt Int where
  -- * Constructors
  newVec n = FixedVecInt <$> UV.new n
  newVecWith n x = do
    v <- UV.new n
    UV.set v x
    return $ FixedVecInt v
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedVecInt -> Int -> IO Int #-}
  (.!) FixedVecInt{..} !n = UV.unsafeRead litVec n
  {-# SPECIALIZE INLINE setAt :: FixedVecInt -> Int -> Int -> IO () #-}
  setAt FixedVecInt{..} !n !x = UV.unsafeWrite litVec n x
  -- * Conversion
  newFromList l = do
    v <- UV.new $ length l
    forM_ (zip [0 .. length l - 1] l) $ \(i, j) -> UV.unsafeWrite v i j
    return $ FixedVecInt v

{-# INLINE getNthInt #-}
getNthInt :: Int -> FixedVecInt -> IO Int
getNthInt !n !(FixedVecInt litVec) = UV.unsafeRead litVec n

{-# INLINE setNthInt #-}
setNthInt :: Int -> FixedVecInt -> Int -> IO ()
setNthInt !n !(FixedVecInt litVec) !x = UV.unsafeWrite litVec n x

{-# INLINE modifyNthInt #-}
modifyNthInt :: Int -> FixedVecInt -> (Int -> Int) -> IO ()
modifyNthInt !n !(FixedVecInt litVec) !f = UV.unsafeModify litVec f n

{-# INLINE swapIntsBetween #-}
swapIntsBetween:: FixedVecInt -> Int -> Int -> IO ()
swapIntsBetween !(FixedVecInt litVec) !i !j = UV.unsafeSwap litVec i j

{-# INLINE newSizedVecIntFromList #-}
newSizedVecIntFromList :: [Int] -> IO FixedVecInt
newSizedVecIntFromList !l = do
  let n = length l
  v <- UV.new $ n + 1
  UV.unsafeWrite v 0 n
  forM_ (zip [1 .. n] l) $ \(i, j) -> UV.unsafeWrite v i j
  return $ FixedVecInt v

{-# INLINE newSizedVecIntFromUVector #-}
newSizedVecIntFromUVector :: U.Vector Int -> IO FixedVecInt
newSizedVecIntFromUVector vec = FixedVecInt <$> U.unsafeThaw vec
