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
       , newVecDouble
       , getNthDouble
       , setNthDouble
       , modifyNthDouble
       )
       where

import Control.Monad (forM)
import Data.List ()
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..))

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
  asList FixedVecDouble{..} = forM [0 .. UV.length doubleVec - 1] $ UV.unsafeRead doubleVec
  dump str v = (str ++) . show <$> asList v

newVecDouble :: Int -> Double -> IO FixedVecDouble
newVecDouble n 0 = FixedVecDouble <$> UV.new n
newVecDouble n x = do
  v <- UV.new n
  UV.set v x
  return $ FixedVecDouble v

{-# INLINE getNthDouble #-}
getNthDouble :: Int -> FixedVecDouble -> IO Double
getNthDouble !n !(FixedVecDouble doubleVec) = UV.unsafeRead doubleVec n

{-# INLINE setNthDouble #-}
setNthDouble :: Int -> FixedVecDouble -> Double -> IO ()
setNthDouble !n !(FixedVecDouble doubleVec) !x = UV.unsafeWrite doubleVec n x

{-# INLINE modifyNthDouble #-}
modifyNthDouble :: Int -> FixedVecDouble -> (Double -> Double) -> IO ()
modifyNthDouble !n !(FixedVecDouble doubleVec) !f = UV.unsafeModify doubleVec f n
