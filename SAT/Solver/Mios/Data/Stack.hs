-- | This is stack of Int, not a list!
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

-- | This is the implementation pack __version 0.8 #diveIntoCore
--
-- * __ListOfInt__  @:: Data.Vector.Unboxed.IOVector INT@ -- vector for a bounded number of Ints
--
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
       , isoVec
       )
       where

import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types

-- | __version 0.1__ : pointing a list by IORef
--
newtype Stack = Stack
                  {
                    ivec :: UV.IOVector Int
                  }

instance VectorFamily Stack Int where
  dump str v = do
    (n:l) <- asList v
    return $ str ++ show (take n l)
  {-# SPECIALIZE INLINE asVec :: Stack -> Vec #-}
  asVec Stack{..} = UV.unsafeTail ivec

{-# INLINE sizeOfStack #-}
sizeOfStack :: Stack -> IO Int
sizeOfStack (Stack ivec) = UV.unsafeRead ivec 0

{-# INLINE clearStack #-}
clearStack :: Stack -> IO ()
clearStack (Stack ivec) = UV.unsafeWrite ivec 0 0

{-# INLINABLE newStack #-}
newStack :: Int -> IO Stack
newStack n = do
  v <- UV.new $ n + 1
  UV.set v 0
  return $ Stack v

{-# INLINE pushToStack #-}
pushToStack :: Stack -> Int -> IO ()
pushToStack (Stack ivec) !x = do
  !i <- (+ 1) <$> UV.unsafeRead ivec 0
  UV.unsafeWrite ivec i x
  UV.unsafeWrite ivec 0 i

{-# INLINE popFromStack #-}
popFromStack :: Stack -> IO ()
popFromStack (Stack ivec) = UV.unsafeModify ivec (subtract 1) 0

{-# INLINE lastOfStack #-}
lastOfStack :: Stack -> IO Int
lastOfStack (Stack ivec) = UV.unsafeRead ivec =<< UV.unsafeRead ivec 0

-- | Shrink the stack. The given arg means the number of discards.
-- therefore, shrink s n == for [1 .. n] $ \_ -> pop s
{-# INLINE shrinkStack #-}
shrinkStack :: Stack -> Int -> IO ()
shrinkStack (Stack ivec) k = UV.unsafeModify ivec (subtract k) 0

-- | isomorphic conversion to 'Vec'
-- Note: 'asVec' drops the 1st element and no copy; 'isoVec' copies the active segment
{-# INLINE isoVec #-}
isoVec :: Stack -> IO Vec
isoVec (Stack ivec) = UV.clone . flip UV.take ivec . (1 +) =<< UV.unsafeRead ivec 0
