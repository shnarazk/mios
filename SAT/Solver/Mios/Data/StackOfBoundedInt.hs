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

-- | This is the implementation pack __version 0.6 #activityEstimation
--
-- * __StackOfLit__@:: UV.IOVector Int@
--
module SAT.Solver.Mios.Data.StackOfBoundedInt
       (
         StackOfBoundedInt
       , sizeOfStack
       , popStack
       , pushStack
       , lastElementInStack
       )
       where

import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..), index)

newtype StackOfBoundedInt = StackOfBoundedInt
                  {
                    stackL :: UV.IOVector Int
                  }

sizeOfStack :: StackOfBoundedInt -> IO Int
sizeOfStack StackOfBoundedInt{..} = UV.unsafeRead stackL 0

instance ContainerLike StackOfBoundedInt Int where
  clear StackOfBoundedInt{..} = UV.set stackL 0
  asList = traverseStack
  dump str s@StackOfBoundedInt{..} = do
    n <- UV.unsafeRead stackL 0
    e <- UV.unsafeRead stackL 1
    l <- asList s
    return $ str ++ "Stack" ++ show (n, e) ++ ":" ++ show l

traverseStack :: StackOfBoundedInt -> IO [Int]
traverseStack StackOfBoundedInt{..} = do
  let
    loop l 0 = return $ reverse l
    loop l x = loop (x:l) =<< UV.unsafeRead stackL (index x + 2)
  loop [] =<< UV.unsafeRead stackL 1

instance VectorLike StackOfBoundedInt Int where
  newVec n = StackOfBoundedInt <$> UV.new (2 + n)
  newVecWith n x = error "StackOfBoundedInt.newVecWith" -- FixedLitVec <$> UV.new n

-- * Stack operations
{-# INLINE popStack #-}
popStack :: StackOfBoundedInt -> IO ()
popStack StackOfBoundedInt{..} = do
  n <- UV.unsafeRead stackL 0
  if n == 0
    then error "StackOfBoundedInt.pop zero"
    else do
        l <- UV.unsafeRead stackL 1
        l' <- UV.unsafeRead stackL $ index l + 2
        UV.unsafeWrite stackL 1 l'
        UV.unsafeWrite stackL 0 $ n - 1
        return ()

{-# INLINE pushStack #-}
pushStack :: StackOfBoundedInt -> Int -> IO ()
pushStack !StackOfBoundedInt{..} !x = do
  n <- UV.unsafeRead stackL 0
  if n == 0
    then do
        UV.unsafeWrite stackL 1 x
        UV.unsafeWrite stackL 0 1
    else do
        l <- UV.unsafeRead stackL 1
        UV.unsafeWrite stackL (index x + 2) l
        UV.unsafeWrite stackL 1 x
        UV.unsafeWrite stackL 0 $ n + 1

{-# INLINE lastElementInStack #-}
lastElementInStack :: StackOfBoundedInt -> IO Int
lastElementInStack !(StackOfBoundedInt s) = UV.unsafeRead s 1
