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
       , swapVecInt
       )
       where

import Control.Monad (forM, forM_)
import Data.List hiding (insert)
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..))

-- | __version 0.3__
--
-- Costs of all operations are /O/(/1/)
newtype FixedVecInt = FixedVecInt
                      {
                        litVec :: UV.IOVector Int
                      }

-- | provides 'clear' and 'size'
instance ContainerLike FixedVecInt Int where
  clear FixedVecInt{..} = error "FixedVecInt.clear"
  size FixedVecInt{..} = return $ UV.length litVec
  asList FixedVecInt{..} = forM [0 .. UV.length litVec - 1] $ UV.unsafeRead litVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike FixedVecInt Int where
  -- * Constructors
  emptyVec = FixedVecInt <$> UV.new 0
  newVec = FixedVecInt <$> UV.new 0
  newVecSized n = FixedVecInt <$> UV.new n
  newVecSizedWith n 0 = FixedVecInt <$> UV.new n
  newVecSizedWith n x = do
    v <- UV.new n
    forM_ [0 .. n -1] $ \i -> UV.write v i x
    return $ FixedVecInt v
  -- * Size operations
  shrink n FixedVecInt{..} = error "FixedVecInt.shrink"
  growTo _ _ = error "FixedVecInt.growTo"
  growToWith _ _ = error "FixedVecInt.growToWith"
  -- * Stack operations
  pop FixedVecInt{..} = error "FixedVecInt.pop"
  push FixedVecInt{..} x = error "FixedVecInt.push"
  lastE FixedVecInt{..} = error "FixedVecInt.lastE"
  removeElem x FixedVecInt{..} = error "FixedVecInt.removeElem"
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedVecInt -> Int -> IO Int #-}
  (.!) FixedVecInt{..} !n = UV.unsafeRead litVec n
  {-# SPECIALIZE INLINE setAt :: FixedVecInt -> Int -> Int -> IO () #-}
  setAt FixedVecInt{..} !n !x = UV.unsafeWrite litVec n x
  -- * Duplication
  copyTo v1 v2 = error "FixedVecInt.copyTo"
  moveTo v1 v2 = error "FixedVecInt.moveTo"
  -- * Conversion
  newFromList l = do
    v <- UV.new $ length l
    forM_ (zip [0 .. length l - 1] l) $ \(i, j) -> UV.write v i j
    return $ FixedVecInt v
  checkConsistency str FixedVecInt{..} func = error "FixedVecInt.checkConsistency"

swapVecInt :: FixedVecInt -> Int -> Int -> IO ()
swapVecInt FixedVecInt{..} i j = UV.unsafeSwap litVec i j
