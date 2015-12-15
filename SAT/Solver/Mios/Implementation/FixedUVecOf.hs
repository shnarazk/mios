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
         FixedUVecOf
       )
       where

import Control.Monad (forM)
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
  newVecWith n x = FixedUVecOf <$> UV.replicate n x
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedUVecOf Int -> Int -> IO Int #-}
  {-# SPECIALIZE INLINE (.!) :: FixedUVecOf Double -> Int -> IO Double #-}
  (.!) FixedUVecOf{..} !n = UV.unsafeRead uVec n
  {-# SPECIALIZE INLINE setAt :: FixedUVecOf Int -> Int -> Int -> IO () #-}
  {-# SPECIALIZE INLINE setAt :: FixedUVecOf Double -> Int -> Double -> IO () #-}
  setAt FixedUVecOf{..} !n !x = UV.unsafeWrite uVec n x
  -- * Conversion
  newFromList (l) = error "FixedUVecOf.newFromList"
