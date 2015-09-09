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
module SAT.Solver.Mios.Implementation.FixedVecOf
       (
         FixedVecOf
       , sortByFst
       )
       where

import Control.Monad (forM, forM_)
import Data.List (sortOn)
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..))

-- | __version 0.4__
--
-- Costs of all operations are /O/(/1/)
newtype FixedVecOf a = FixedVecOf
                          {
                            fVec :: MV.IOVector a
                          }

-- | provides 'clear' and 'size'
instance ContainerLike (FixedVecOf a) a where
  clear FixedVecOf{..} = error "FixedVec.clear"
  size FixedVecOf{..} = return $ MV.length fVec
  asList FixedVecOf{..} = forM [0 .. MV.length fVec - 1] $ MV.unsafeRead fVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (FixedVecOf a) a where
  -- * Constructors
  emptyVec = FixedVecOf <$> MV.new 0
  newVec = FixedVecOf <$> MV.new 0
  newVecSized n = FixedVecOf <$> MV.new n
  newVecSizedWith n x = FixedVecOf <$> MV.replicate n x
  -- * Size operations
  shrink n FixedVecOf{..} = error "FixedVecOf.shrink"
  growTo _ _ = error "FixedVecOf.growTo"
  growToWith _ _ = error "FixedVecOf.growToWith"
  -- * Stack operations
  pop FixedVecOf{..} = error "FixedVecOf.pop"
  push FixedVecOf{..} x = error "FixedVecOf.push"
  lastE FixedVecOf{..} = error "FixedVecOf.lastE"
  removeElem x FixedVecOf{..} = error "FixedVecOf.removeElem"
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedVecOf Int -> Int -> IO Int #-}
  {-# SPECIALIZE INLINE (.!) :: FixedVecOf Double -> Int -> IO Double #-}
  (.!) FixedVecOf{..} n = MV.unsafeRead fVec n
  {-# SPECIALIZE INLINE setAt :: FixedVecOf Int -> Int -> Int -> IO () #-}
  {-# SPECIALIZE INLINE setAt :: FixedVecOf Double -> Int -> Double -> IO () #-}
  setAt FixedVecOf{..} n x = MV.unsafeWrite fVec n x
  -- * Duplication
  copyTo v1 v2 = error "FixedVecOf.copyTo"
  moveTo v1 v2 = error "FixedVecOf.moveTo"
  -- * Conversion
  newFromList (l) = error "FixedVecOf.newFromList"
  checkConsistency str FixedVecOf{..} func = error "FixedVecOf.checkConsistency"

-- | sort elements in /big-to-small/ order
sortByFst :: FixedVecOf (Double, Int) -> IO ()
sortByFst v@FixedVecOf{..} = do
  vals <- reverse . sortOn fst <$> asList v
  forM_ (zip [0 ..] vals) $ \(i, x) -> MV.write fVec i x
