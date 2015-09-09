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
module SAT.Solver.Mios.Implementation.StackOfLit
       (
         StackOfLit
       )
       where

import Control.Monad (forM_)
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..), index)

newtype StackOfLit = StackOfLit
                  {
                    stackL :: UV.IOVector Int
                  }

instance ContainerLike StackOfLit Int where
  clear StackOfLit{..} = forM_ [0 .. UV.length stackL - 1] $ flip (UV.write stackL) 0
  size StackOfLit{..} = UV.unsafeRead stackL 0
  asList = traverseStack
  dump str s@StackOfLit{..} = do
    n <- UV.unsafeRead stackL 0
    e <- UV.unsafeRead stackL 1
    l <- asList s
    return $ str ++ "Stack" ++ show (n, e) ++ ":" ++ show l

traverseStack :: StackOfLit -> IO [Int]
traverseStack StackOfLit{..} = do
  let
    loop l 0 = return $ reverse l
    loop l x = loop (x:l) =<< UV.unsafeRead stackL (index x + 2)
  loop [] =<< UV.unsafeRead stackL 1

instance VectorLike StackOfLit Int where
  emptyVec = StackOfLit <$> UV.new 0
  newVec = StackOfLit <$> UV.new 0
  newVecSized n = StackOfLit <$> UV.new (2 + n)
  newVecSizedWith n x = error "StackOfLit.newVecSizedWith" -- FixedLitVec <$> UV.new n
  -- * Size operations
  shrink _ _ = error "StackOfLit.shrink"
  growTo _ _ = error "StackOfLit.growTo"
  growToWith _ _ = error "StackOfLit.growToWith"
  -- * Stack operations
  pop StackOfLit{..} = do
    n <- UV.unsafeRead stackL 0
    if n == 0
      then error "StackOfLit.pop zero"
      else do
          l <- UV.unsafeRead stackL 1
          l' <- UV.unsafeRead stackL $ index l + 2
          UV.unsafeWrite stackL 1 l'
          UV.unsafeWrite stackL 0 $ n - 1
          return ()
  push StackOfLit{..} x = do
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
  lastE StackOfLit{..} = UV.unsafeRead stackL 1
  removeElem _ _ = error "StackOfLit.removeElem"
