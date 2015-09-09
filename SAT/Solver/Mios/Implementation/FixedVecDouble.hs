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
-- * __FixedVecDouble@::UV.IOVector Double@ -- data type that contains a mutable list of elements
--
module SAT.Solver.Mios.Implementation.FixedVecDouble
       (
         FixedVecDouble
       )
       where

import Control.Monad (forM, forM_)
import Data.List ()
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..))

-- | __version 0.3__
--
-- Costs of all operations are /O/(/1/)
newtype FixedVecDouble = FixedVecDouble
                          {
                            doubleVec :: UV.IOVector Double
                          }

-- | provides 'clear' and 'size'
instance ContainerLike FixedVecDouble Double where
  clear FixedVecDouble{..} = error "FixedVecDouble.clear"
  size FixedVecDouble{..} = return $ UV.length doubleVec
  asList FixedVecDouble{..} = forM [0 .. UV.length doubleVec - 1] $ UV.unsafeRead doubleVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike FixedVecDouble Double where
  -- * Constructors
  emptyVec = FixedVecDouble <$> UV.new 0
  newVec = FixedVecDouble <$> UV.new 0
  newVecSized n = FixedVecDouble <$> UV.new n
  newVecSizedWith n 0 = FixedVecDouble <$> UV.new n
  newVecSizedWith n x = do
    v <- UV.new n
    forM_ [0 .. n -1] $ \i -> UV.write v i x
    return $ FixedVecDouble v
  -- * Size operations
  shrink n FixedVecDouble{..} = error "FixedVecDouble.shrink"
  growTo _ _ = error "FixedVecDouble.growTo"
  growToWith _ _ = error "FixedVecDouble.growToWith"
  -- * Stack operations
  pop FixedVecDouble{..} = error "FixedVecDouble.pop"
  push FixedVecDouble{..} x = error "FixedVecDouble.push"
  lastE FixedVecDouble{..} = error "FixedVecDouble.lastE"
  removeElem x FixedVecDouble{..} = error "FixedVecDouble.removeElem"
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedVecDouble -> Int -> IO Double #-}
  (.!) FixedVecDouble{..} n = UV.unsafeRead doubleVec n
  {-# SPECIALIZE INLINE setAt :: FixedVecDouble -> Int -> Double -> IO () #-}
  setAt FixedVecDouble{..} n x = UV.unsafeWrite doubleVec n x
  -- * Duplication
  copyTo v1 v2 = error "FixedVecDouble.copyTo"
  moveTo v1 v2 = error "FixedVecDouble.moveTo"
  -- * Conversion
  newFromList l = do
    v <- UV.new $ length l
    forM_ (zip [0 .. length l - 1] l) $ \(i, j) -> UV.write v i j
    return $ FixedVecDouble v
  checkConsistency str FixedVecDouble{..} func = error "FixedVecDouble.checkConsistency"
