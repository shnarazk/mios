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
-- * __FixedVec a__ @:: MV.IOVector a@ -- data type that contains a mutable list of elements
--
-- * __VerOrder__ @:: IORef [Var]@
--
-- * __FixedQueueOf Lit__ @:: UV.IOVector Int@
--
module SAT.Solver.Mios.Implementation.FixedUVecOf
       (
         FixedUVecOf (..)
       , FixedVecInt
       , newSizedVecIntFromList
       , newSizedVecIntFromUVector
       , swapIntsBetween
       , FixedVecDouble
       , newVecDouble
       )
       where

import Control.Monad (forM, forM_)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..))

-- | __version 0.4__
--
-- Costs of all operations are /O/(/1/)
newtype FixedUVecOf a = FixedUVecOf
                          {
                            uVec :: UV.IOVector a
                          }

-- | provides 'clear' and 'size'
instance UV.Unbox a => ContainerLike (FixedUVecOf a) a where
  clear FixedUVecOf{..} = error "FixedVec.clear"
  asList FixedUVecOf{..} = forM [0 .. UV.length uVec - 1] $ UV.unsafeRead uVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance UV.Unbox a => VectorLike (FixedUVecOf a) a where
  -- * Constructors
  newVec n = FixedUVecOf <$> UV.new n
  newVecWith n x = do
    v <- UV.new n
    UV.set v x
    return $ FixedUVecOf v
  -- * Vector operations
  {-# SPECIALIZE INLINE getAt :: Int -> FixedUVecOf Int -> IO Int #-}
  {-# SPECIALIZE INLINE getAt :: Int -> FixedUVecOf Double -> IO Double #-}
  getAt !n (FixedUVecOf uVec) = UV.unsafeRead uVec n
  {-# SPECIALIZE INLINE setAt :: Int -> FixedUVecOf Int -> Int -> IO () #-}
  {-# SPECIALIZE INLINE setAt :: Int -> FixedUVecOf Double -> Double -> IO () #-}
  setAt !n (FixedUVecOf uVec) !x = UV.unsafeWrite uVec n x
  {-# SPECIALIZE INLINE modifyAt :: Int -> FixedUVecOf Int -> (Int -> Int) -> IO () #-}
  {-# SPECIALIZE INLINE modifyAt :: Int -> FixedUVecOf Double -> (Double -> Double) -> IO () #-}
  modifyAt !n (FixedUVecOf uVec) f = UV.unsafeModify uVec f n
  -- * Conversion
  newFromList _ = error "FixedUVecOf.newFromList"

type FixedVecInt = FixedUVecOf Int

newSizedVecIntFromList :: [Int] -> IO FixedVecInt
newSizedVecIntFromList !l = do
  let n = length l
  v <- UV.new $ n + 1
  UV.unsafeWrite v 0 n
  forM_ (zip [1 .. n] l) $ \(i, j) -> UV.unsafeWrite v i j
  return $ FixedUVecOf v

{-# INLINE newSizedVecIntFromUVector #-}
newSizedVecIntFromUVector :: U.Vector Int -> IO FixedVecInt
newSizedVecIntFromUVector vec = FixedUVecOf <$> U.unsafeThaw vec

{-# INLINE swapIntsBetween #-}
swapIntsBetween :: FixedVecInt -> Int -> Int -> IO ()
swapIntsBetween (FixedUVecOf uVec) !i !j = UV.unsafeSwap uVec i j

--------------------------------------------------------------------------------
type FixedVecDouble = FixedUVecOf Double

newVecDouble :: Int -> Double -> IO FixedVecDouble
newVecDouble n x = do
  v <- UV.new n
  UV.set v x
  return $ FixedUVecOf v
