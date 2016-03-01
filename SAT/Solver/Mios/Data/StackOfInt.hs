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
module SAT.Solver.Mios.Data.StackOfInt
       (
         StackOfInt (..)
       , newStackOfInt
       , clearStackOfInt
       , sizeOfStackOfInt
       , pushToStackOfInt
       , popFromStackOfInt
       , lastOfStackOfInt
       , shrinkStackOfInt
       )
       where

import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types

-- | __version 0.1__ : pointing a list by IORef
--
newtype StackOfInt = StackOfInt
                  {
                    ivec :: UV.IOVector Int
                  }

instance VectorFamily StackOfInt Int where
  dump str v = do
    (n:l) <- asList v
    return $ str ++ show (take n l)
  {-# SPECIALIZE INLINE asVec :: StackOfInt -> Vec #-}
  asVec StackOfInt{..} = ivec

{-# INLINE sizeOfStackOfInt #-}
sizeOfStackOfInt :: StackOfInt -> IO Int
sizeOfStackOfInt (StackOfInt ivec) = UV.unsafeRead ivec 0

{-# INLINE clearStackOfInt #-}
clearStackOfInt :: StackOfInt -> IO ()
clearStackOfInt (StackOfInt ivec) = UV.unsafeWrite ivec 0 0

{-# INLINABLE newStackOfInt #-}
newStackOfInt :: Int -> IO StackOfInt
newStackOfInt n = do
  v <- UV.new $ n + 1
  UV.set v 0
  return $ StackOfInt v

{-# INLINE pushToStackOfInt #-}
pushToStackOfInt :: StackOfInt -> Int -> IO ()
pushToStackOfInt (StackOfInt ivec) !x = do
  !i <- (+ 1) <$> UV.unsafeRead ivec 0
  UV.unsafeWrite ivec i x
  UV.unsafeWrite ivec 0 i

{-# INLINE popFromStackOfInt #-}
popFromStackOfInt :: StackOfInt -> IO ()
popFromStackOfInt (StackOfInt ivec) = UV.unsafeModify ivec (subtract 1) 0

{-# INLINE lastOfStackOfInt #-}
lastOfStackOfInt :: StackOfInt -> IO Int
lastOfStackOfInt (StackOfInt ivec) = UV.unsafeRead ivec =<< UV.unsafeRead ivec 0

-- | Shrink the stack. The given arg means the number of discards.
-- therefore, shrink s n == for [1 .. n] $ \_ -> pop s
{-# INLINE shrinkStackOfInt #-}
shrinkStackOfInt :: StackOfInt -> Int -> IO ()
shrinkStackOfInt (StackOfInt ivec) k = UV.unsafeModify ivec (subtract k) 0
