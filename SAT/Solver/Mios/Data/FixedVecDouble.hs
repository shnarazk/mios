{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
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

type FixedVecDouble = UV.IOVector Double

instance VectorFamily FixedVecDouble Double where
  clear _ = error "FixedVecDouble.clear"
  asList v = forM [0 .. UV.length v - 1] $ UV.unsafeRead v
  dump str v = (str ++) . show <$> asList v

newVecDouble :: Int -> Double -> IO FixedVecDouble
newVecDouble n 0 = UV.new n
newVecDouble n x = do
  v <- UV.new n
  UV.set v x
  return v

{-# INLINE getNthDouble #-}
getNthDouble :: Int -> FixedVecDouble -> IO Double
getNthDouble !n v = UV.unsafeRead v n

{-# INLINE setNthDouble #-}
setNthDouble :: Int -> FixedVecDouble -> Double -> IO ()
setNthDouble !n v !x = UV.unsafeWrite v n x

{-# INLINE modifyNthDouble #-}
modifyNthDouble :: Int -> FixedVecDouble -> (Double -> Double) -> IO ()
modifyNthDouble !n v !f = UV.unsafeModify v f n
