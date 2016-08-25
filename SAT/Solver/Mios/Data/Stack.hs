{-# LANGUAGE
    MultiParamTypeClasses
  #-}
{-# LANGUAGE Trustworthy #-}

-- | stack of Int, by adding the length field as the zero-th element to a 'Vec'
module SAT.Solver.Mios.Data.Stack
       (
         Stack
       , newStack
       , clearStack
       , sizeOfStack
       , pushToStack
       , popFromStack
       , lastOfStack
       , shrinkStack
       , asSizedVec
--       , isoVec
       )
       where

import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types

-- | Unboxed mutable stack for Int.
newtype Stack = Stack (UV.IOVector Int)

instance VectorFamily Stack Int where
  dump str v = (str ++) . show <$> asList v
  {-# SPECIALIZE INLINE asVec :: Stack -> Vec #-}
  asVec (Stack v) = UV.unsafeTail v
  asList (Stack v) = do
    (n : l) <- asList v
    return $ take n l

-- | returns the number of elements
{-# INLINE sizeOfStack #-}
sizeOfStack :: Stack -> IO Int
sizeOfStack (Stack v) = UV.unsafeRead v 0

-- | clear stack
{-# INLINE clearStack #-}
clearStack :: Stack -> IO ()
clearStack (Stack v) = UV.unsafeWrite v 0 0

-- | returns a new stack which size is @size@
{-# INLINABLE newStack #-}
newStack :: Int -> IO Stack
newStack n = do
  v <- UV.new $ n + 1
  UV.set v 0
  return $ Stack v

-- | pushs an int to 'Stack'
{-# INLINE pushToStack #-}
pushToStack :: Stack -> Int -> IO ()
pushToStack (Stack v) x = do
  i <- (+ 1) <$> UV.unsafeRead v 0
  UV.unsafeWrite v i x
  UV.unsafeWrite v 0 i

-- | drops the first element from 'Stack'
{-# INLINE popFromStack #-}
popFromStack :: Stack -> IO ()
popFromStack (Stack v) = UV.unsafeModify v (subtract 1) 0

-- | peeks the last element in 'Stack'
{-# INLINE lastOfStack #-}
lastOfStack :: Stack -> IO Int
lastOfStack (Stack v) = UV.unsafeRead v =<< UV.unsafeRead v 0

-- | Shrink the stack. The given arg means the number of discards.
-- therefore, shrink s n == for [1 .. n] $ \_ -> pop s
{-# INLINE shrinkStack #-}
shrinkStack :: Stack -> Int -> IO ()
shrinkStack (Stack v) k = UV.unsafeModify v (subtract k) 0

-- | converts Stack to sized Vec; this is the method to get the internal vector
{-# INLINE asSizedVec #-}
asSizedVec :: Stack -> Vec
asSizedVec (Stack v) = v

{-
-- | isomorphic conversion to 'Vec'
--
-- Note: 'asVec' drops the 1st element and no copy (unsafe operation); 'isoVec' really copies the real elements
{-# INLINE isoVec #-}
isoVec :: Stack -> IO Vec
isoVec (Stack v) = UV.clone . flip UV.take v . (1 +) =<< UV.unsafeRead v 0
-}
