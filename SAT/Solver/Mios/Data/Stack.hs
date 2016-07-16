-- | This is stack of Int, not a list!
{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Trustworthy #-}

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
       , isoVec
       )
       where

import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types

-- | Unboxed mutable stack for Int.
newtype Stack = Stack
                  {
                    ivec :: UV.IOVector Int
                  }

instance VectorFamily Stack Int where
  dump str v = (str ++) . show <$> asList v
  {-# SPECIALIZE INLINE asVec :: Stack -> Vec #-}
  asVec (Stack ivec) = UV.unsafeTail ivec
  asList x = do
    (n : l) <- asList (ivec x)
    return $ take n l

-- | returns the number of elements
{-# INLINE sizeOfStack #-}
sizeOfStack :: Stack -> IO Int
sizeOfStack (Stack ivec) = UV.unsafeRead ivec 0

-- | clear stack
{-# INLINE clearStack #-}
clearStack :: Stack -> IO ()
clearStack (Stack ivec) = UV.unsafeWrite ivec 0 0

-- | returns a new stack which size is @size@
{-# INLINABLE newStack #-}
newStack :: Int -> IO Stack
newStack n = do
  v <- UV.new $ n + 1
  UV.set v 0
  return $ Stack v

-- | pushs an int to stack
{-# INLINE pushToStack #-}
pushToStack :: Stack -> Int -> IO ()
pushToStack (Stack ivec) !x = do
  !i <- (+ 1) <$> UV.unsafeRead ivec 0
  UV.unsafeWrite ivec i x
  UV.unsafeWrite ivec 0 i

-- | pops an int from stack
{-# INLINE popFromStack #-}
popFromStack :: Stack -> IO ()
popFromStack (Stack ivec) = UV.unsafeModify ivec (subtract 1) 0

-- | peeks the last element in stack
{-# INLINE lastOfStack #-}
lastOfStack :: Stack -> IO Int
lastOfStack (Stack ivec) = UV.unsafeRead ivec =<< UV.unsafeRead ivec 0

-- | Shrink the stack. The given arg means the number of discards.
-- therefore, shrink s n == for [1 .. n] $ \_ -> pop s
{-# INLINE shrinkStack #-}
shrinkStack :: Stack -> Int -> IO ()
shrinkStack (Stack ivec) k = UV.unsafeModify ivec (subtract k) 0

-- | converts Stack to sized Vec; this is the method to get the internal vector
{-# INLINE asSizedVec #-}
asSizedVec :: Stack -> Vec
asSizedVec (Stack v) = v

-- | isomorphic conversion to 'Vec'
-- Note: 'asVec' drops the 1st element and no copy; 'isoVec' copies the active segment
{-# INLINE isoVec #-}
isoVec :: Stack -> IO Vec
isoVec (Stack ivec) = UV.clone . flip UV.take ivec . (1 +) =<< UV.unsafeRead ivec 0
