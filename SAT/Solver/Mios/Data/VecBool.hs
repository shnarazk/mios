-- | Mutable Unboxed Boolean Vector
--
-- * __VecBool@::UV.IOVector Bool@ -- data type that contains a mutable list of elements
--
{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Solver.Mios.Data.VecBool
       (
         VecBool
       , newVecBool
       , getNthBool
       , setNthBool
       , modifyNthBool
       )
       where

import Control.Monad (forM)
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (VectorFamily(..))

-- | Mutable unboxed Bool Vector
type VecBool = UV.IOVector Bool

-- | provides 'clear' and 'size'
instance VectorFamily VecBool Bool where
  clear _ = error "VecBool.clear"
  asList v = forM [0 .. UV.length v - 1] $ UV.unsafeRead v
  dump str v = (str ++) . show <$> asList v

-- | returns a new 'VecBool'
newVecBool :: Int -> Bool -> IO VecBool
newVecBool n x = do
  v <- UV.new n
  UV.set v x
  return v

-- | returns the nth value in 'VecBool'
{-# INLINE getNthBool #-}
getNthBool :: VecBool -> Int -> IO Bool
getNthBool = UV.unsafeRead

-- | sets the nth value
{-# INLINE setNthBool #-}
setNthBool :: VecBool -> Int -> Bool -> IO ()
setNthBool = UV.unsafeWrite

-- | sets the nth value
{-# INLINE modifyNthBool #-}
modifyNthBool :: VecBool -> (Bool -> Bool) -> Int -> IO ()
modifyNthBool = UV.unsafeModify
