{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE TypeFamilies, DataKinds #-}
{-# LANGUAGE Trustworthy #-}

-- | Mutable Unboxed Vector
module SAT.Mios.Data.Vec
       (
         UVector
       , Vec (..)
       , VecKind (..)
       , MiosVector (..)
         -- * for Vec Int
--       , newSizedVecFromUVector
         -- * Stack
       , newStack
       , newStackFromList
       , clearStack
       , sizeOfStack
       , pushToStack
       , popFromStack
       , lastOfStack
       , shrinkStack
       , asSizedVec
       )
       where

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV

-- | Mutable unboxed Vector

type UVector a = UV.IOVector a

class MiosVector v a | v -> a where
  newVec :: Int -> a -> IO v
  getNth ::v -> Int -> IO a
  setNth :: v -> Int -> a -> IO ()
  modifyNth :: v -> (a -> a) -> Int -> IO ()
  swapBetween :: v -> Int -> Int -> IO ()
  setAll :: v -> a -> IO ()
  vecGrow :: v -> Int -> IO v

instance MiosVector (UVector Int) Int where
  {-# SPECIALIZE INLINE newVec :: Int -> Int -> IO (UVector Int) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: UVector Int -> Int -> IO Int #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Int -> Int -> Int -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Int -> (Int -> Int) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Int -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: UVector Int -> Int -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE vecGrow :: UVector Int -> Int -> IO (UVector Int) #-}
  vecGrow = UV.unsafeGrow

instance MiosVector (UVector Bool) Bool where
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
  {-# SPECIALIZE INLINE vecGrow :: (UVector Bool) -> Int -> IO (UVector Bool) #-}
  vecGrow = UV.unsafeGrow

instance MiosVector (UVector Double) Double where
  {-# SPECIALIZE INLINE newVec :: Int -> Double -> IO (UVector Double) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: UVector Double -> Int -> IO Double #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Double -> Int -> Double -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Double -> (Double -> Double) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Double -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: UVector Double -> Double -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE vecGrow :: (UVector Double) -> Int -> IO (UVector Double) #-}
  vecGrow = UV.unsafeGrow

--------------------------------------------------------------------------------

-- | returns a new 'UVector' from a @[Int]@
{-# INLINE newStackFromList #-}
newStackFromList :: [Int] -> IO (Vec Int 'AsStack)
newStackFromList !l = Vec <$> U.unsafeThaw (U.fromList (length l : l))

-- | returns a new 'UVector' from a @[Int]@
{-# INLINE newSizedVecFromList #-}
newSizedVecFromList :: [Int] -> IO (UVector Int)
newSizedVecFromList !l = U.unsafeThaw $ U.fromList (length l : l)


-- | returns a new 'UVector' from a Unboxed Int UVector
{-# INLINE newSizedVecFromUVector #-}
newSizedVecFromUVector :: U.Vector Int -> IO (UVector Int)
newSizedVecFromUVector = U.unsafeThaw

--------------------------------------------------------------------------------

data VecKind = ZeroBased | OneBased | AsStack | WithSize

newtype Vec a (b :: VecKind) = Vec (UVector a)

instance MiosVector (Vec Int 'ZeroBased) Int where
  newVec n x = Vec <$> newVec n x
  getNth (Vec v) = UV.unsafeRead v
  setNth (Vec v) = UV.unsafeWrite v
  modifyNth (Vec v) = UV.unsafeModify v
  swapBetween (Vec v) = UV.unsafeSwap v
  setAll (Vec v) = UV.set v
  vecGrow (Vec v) n = Vec <$> UV.unsafeGrow v n

instance MiosVector (Vec Double 'ZeroBased) Double where
  newVec n x = Vec <$> newVec n x
  getNth (Vec v) = UV.unsafeRead v
  setNth (Vec v) = UV.unsafeWrite v
  modifyNth (Vec v) = UV.unsafeModify v
  swapBetween (Vec v) = UV.unsafeSwap v
  setAll (Vec v) = UV.set v
  vecGrow (Vec v) n = Vec <$> UV.unsafeGrow v n

instance MiosVector (Vec Int 'OneBased) Int where
  newVec n x = Vec <$> newVec n x
  getNth (Vec v) = UV.unsafeRead v
  setNth (Vec v) = UV.unsafeWrite v
  modifyNth (Vec v) = UV.unsafeModify v
  swapBetween (Vec v) = UV.unsafeSwap v
  setAll (Vec v) = UV.set v
  vecGrow (Vec v) n = Vec <$> UV.unsafeGrow v n

instance MiosVector (Vec Bool 'OneBased) Bool where
  newVec n x = Vec <$> newVec n x
  getNth (Vec v) = UV.unsafeRead v
  setNth (Vec v) = UV.unsafeWrite v
  modifyNth (Vec v) = UV.unsafeModify v
  swapBetween (Vec v) = UV.unsafeSwap v
  setAll (Vec v) = UV.set v
  vecGrow (Vec v) n = Vec <$> UV.unsafeGrow v n

instance MiosVector (Vec Double 'OneBased) Double where
  newVec n x = Vec <$> newVec n x
  getNth (Vec v) = UV.unsafeRead v
  setNth (Vec v) = UV.unsafeWrite v
  modifyNth (Vec v) = UV.unsafeModify v
  swapBetween (Vec v) = UV.unsafeSwap v
  setAll (Vec v) = UV.set v
  vecGrow (Vec v) n = Vec <$> UV.unsafeGrow v n

instance MiosVector (Vec Int 'AsStack) Int where
  newVec n x = Vec <$> newVec n x
  getNth (Vec v) = UV.unsafeRead v
  setNth (Vec v) = UV.unsafeWrite v
  modifyNth (Vec v) = UV.unsafeModify v
  swapBetween (Vec v) = UV.unsafeSwap v
  setAll (Vec v) = UV.set v
  vecGrow (Vec v) n = Vec <$> UV.unsafeGrow v n

instance MiosVector (Vec Int 'WithSize) Int where
  newVec n x = Vec <$> newVec n x
  getNth (Vec v) = UV.unsafeRead v
  setNth (Vec v) = UV.unsafeWrite v
  modifyNth (Vec v) = UV.unsafeModify v
  swapBetween (Vec v) = UV.unsafeSwap v
  setAll (Vec v) = UV.set v
  vecGrow (Vec v) n = Vec <$> UV.unsafeGrow v n

-------------------------------------------------------------------------------- Stack

-- | returns the number of elements
{-# INLINE sizeOfStack #-}
sizeOfStack :: Vec Int 'AsStack -> IO Int
sizeOfStack (Vec v) = UV.unsafeRead v 0

-- | clear stack
{-# INLINE clearStack #-}
clearStack :: Vec Int 'AsStack -> IO ()
clearStack (Vec v) = UV.unsafeWrite v 0 0

-- | returns a new stack which size is @size@
{-# INLINABLE newStack #-}
newStack :: Int -> IO (Vec Int 'AsStack)
newStack n = do
  v <- UV.new $ n + 1
  UV.set v 0
  return $ Vec v

-- | pushs an int to 'Stack'
{-# INLINE pushToStack #-}
pushToStack :: Vec Int 'AsStack -> Int -> IO ()
pushToStack (Vec v) x = do
  i <- (+ 1) <$> UV.unsafeRead v 0
  UV.unsafeWrite v i x
  UV.unsafeWrite v 0 i

-- | drops the first element from 'Stack'
{-# INLINE popFromStack #-}
popFromStack :: Vec Int 'AsStack -> IO ()
popFromStack (Vec v) = UV.unsafeModify v (subtract 1) 0

-- | peeks the last element in 'Stack'
{-# INLINE lastOfStack #-}
lastOfStack :: Vec Int 'AsStack -> IO Int
lastOfStack (Vec v) = UV.unsafeRead v =<< UV.unsafeRead v 0

-- | Shrink the stack. The given arg means the number of discards.
-- therefore, shrink s n == for [1 .. n] $ \_ -> pop s
{-# INLINE shrinkStack #-}
shrinkStack :: Vec Int 'AsStack -> Int -> IO ()
shrinkStack (Vec v) k = UV.unsafeModify v (subtract k) 0

-- | converts Stack to sized Vec; this is the method to get the internal vector
{-# INLINE asSizedVec #-}
asSizedVec :: Vec Int 'AsStack -> Vec Int 'WithSize
asSizedVec (Vec v) = Vec v
