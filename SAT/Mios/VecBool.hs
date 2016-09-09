{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Abstraction Layer for Mutable Unboxed Vectors (NOT-IN-USE)
module SAT.Mios.VecBool where

import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Mios.Types

instance VectorFamily (Vec Bool) Bool where
  asList (Vec v) = mapM (getNth v) [1 .. UV.length v]
  dump str _ = return $ str ++ "Vec dump"

instance VecFamily (UVector Bool) Bool where
  {-# SPECIALIZE INLINE newVec :: Int -> Bool -> IO (UVector Bool) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: UVector Bool -> Int -> IO Bool #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Bool -> Int -> Bool -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Bool -> (Bool -> Bool) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Bool -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: UVector Bool -> Bool -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growVec :: UVector Bool -> Int -> IO (UVector Bool) #-}
  growVec = UV.unsafeGrow

instance VecFamily (Vec Bool) Bool where
  newVec n x = Vec <$> newVec (n + 1) x
  {-# SPECIALIZE INLINE getNth :: Vec Bool -> Int -> IO Bool #-}
  getNth (Vec v) = UV.unsafeRead v
  {-# SPECIALIZE INLINE setNth :: Vec Bool -> Int -> Bool -> IO () #-}
  setNth (Vec v) = UV.unsafeWrite v
  {-# SPECIALIZE INLINE modifyNth :: Vec Bool -> (Bool -> Bool) -> Int -> IO () #-}
  modifyNth (Vec v) = UV.unsafeModify v
  {-# SPECIALIZE INLINE swapBetween :: Vec Bool -> Int -> Int -> IO () #-}
  swapBetween (Vec v) = UV.unsafeSwap v
  {-# SPECIALIZE INLINE setAll :: Vec Bool -> Bool -> IO () #-}
  setAll (Vec v) = UV.set v
  {-# SPECIALIZE INLINE growVec :: Vec Bool -> Int -> IO (Vec Bool) #-}
  growVec (Vec v) n = Vec <$> UV.unsafeGrow v n
