{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Trustworthy #-}

-- | This is the implementation pack __version 0.6 #activityEstimation
--
-- * __FixedVecBool@::UV.IOVector Bool@ -- data type that contains a mutable list of elements
--
module SAT.Solver.Mios.Data.FixedVecBool
       (
         FixedVecBool
       , newVecBool
       , getNthBool
       , setNthBool
       , modifyNthBool
       )
       where

import Control.Monad (forM)
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (VectorFamily(..))

type FixedVecBool = UV.IOVector Bool

-- | provides 'clear' and 'size'
instance VectorFamily FixedVecBool Bool where
  clear _ = error "FixedVecBool.clear"
  asList v = forM [0 .. UV.length v - 1] $ UV.unsafeRead v
  dump str v = (str ++) . show <$> asList v

newVecBool :: Int -> Bool -> IO FixedVecBool
newVecBool n x = do
  v <- UV.new n
  UV.set v x
  return v

{-# INLINE getNthBool #-}
getNthBool :: FixedVecBool -> Int -> IO Bool
getNthBool = UV.unsafeRead

{-# INLINE setNthBool #-}
setNthBool :: FixedVecBool -> Int -> Bool -> IO ()
setNthBool = UV.unsafeWrite

{-# INLINE modifyNthBool #-}
modifyNthBool :: FixedVecBool -> (Bool -> Bool) -> Int -> IO ()
modifyNthBool = UV.unsafeModify
