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
module SAT.Solver.Mios.Data.FixedVecOf
       (
         FixedVecOf(..)
       , getVecAt
       , setVecAt
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
  asList FixedVecOf{..} = forM [0 .. MV.length fVec - 1] $ MV.unsafeRead fVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (FixedVecOf a) a where
  -- * Constructors
  newVec n = FixedVecOf <$> MV.new n
  newVecWith n x = FixedVecOf <$> MV.replicate n x
  -- * Vector operations
  {-# SPECIALIZE INLINE setAt :: Int -> FixedVecOf Int -> Int -> IO () #-}
  {-# SPECIALIZE INLINE setAt :: Int -> FixedVecOf Double -> Double -> IO () #-}
  setAt n FixedVecOf{..} x = MV.unsafeWrite fVec n x
  -- * Conversion
  newFromList _ = error "FixedVecOf.newFromList"

{-# INLINE setVecAt #-}
setVecAt :: FixedVecOf a -> Int -> a -> IO ()
setVecAt FixedVecOf{..} n = MV.unsafeWrite fVec n

{-# INLINE getVecAt #-}
getVecAt :: FixedVecOf a -> Int -> IO a
getVecAt FixedVecOf{..} = MV.unsafeRead fVec

-- | sort elements in /big-to-small/ order
sortByFst :: FixedVecOf (Double, Int) -> IO ()
sortByFst v@FixedVecOf{..} = do
  vals <- reverse . sortOn fst <$> asList v
  forM_ (zip [0 ..] vals) $ \(i, x) -> MV.unsafeWrite fVec i x
