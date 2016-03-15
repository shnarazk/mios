{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , TypeFamilies
  , UndecidableInstances
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Solver.Mios.Data.FixedVecDouble
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
import SAT.Solver.Mios.Types (VectorFamily(..))

newtype FixedVecDouble = FixedVecDouble
                          {
                            doubleVec :: UV.IOVector Double
                          }

instance VectorFamily FixedVecDouble Double where
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
getNthDouble !n (FixedVecDouble doubleVec) = UV.unsafeRead doubleVec n

{-# INLINE setNthDouble #-}
setNthDouble :: Int -> FixedVecDouble -> Double -> IO ()
setNthDouble !n (FixedVecDouble doubleVec) !x = UV.unsafeWrite doubleVec n x

{-# INLINE modifyNthDouble #-}
modifyNthDouble :: Int -> FixedVecDouble -> (Double -> Double) -> IO ()
modifyNthDouble !n (FixedVecDouble doubleVec) !f = UV.unsafeModify doubleVec f n
