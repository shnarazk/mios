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
-- * __FixedQueueOf Lit__ @:: UV.IOVector Int@
--
module SAT.Solver.Mios.Implementation.FixedQueueOf
       (
         FixedQueueOf
       )
       where

import Control.Monad (forM_)
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Solver.Mios.Types (ContainerLike(..), QueueLike(..), Lit, index)

-- | __version 0.5__
--
-- a shrinked version of 'MutableRings' (a single-linked memory chunk)
--
-- __Layout__
--
-- This is 2*n+3 length vector for n variables.
--
-- * ring[0] is the queue length
--
-- * ring[1] is the first assgined literal
--
-- * ring[2] is the last (latest) assigned literal
--
-- * ring[index(n)+2] == the literal assigned after Literl /n/
--
-- __Definition__ (an empty case is eliminated)
--
-- * insert x = @do x' <- ring .! 2; setAt ring (index x' + 2) x; setAt ring 2 x@
--
-- * dequeue = @do x <- ring .! 1; x' <- ring .! (index x + 2); setAt ring 1 x'; return x@
--
-- * initialization = @setAt ring 0 0; setAt ring 1 0; setAt ring 2 0@
--
newtype FixedQueueOf a = FixedQueueOf
              {
                ring :: UV.IOVector a -- ^ emulate a linked data structure on mutable vector
              }

-- | provides 'clear' and 'size'
instance ContainerLike (FixedQueueOf Lit) Lit where
  clear FixedQueueOf{..} = forM_ [0 .. UV.length ring - 1] $ flip (UV.unsafeWrite ring) 0
  size FixedQueueOf{..} = UV.unsafeRead ring 0
  asList = traverseQueue
  dump str q@FixedQueueOf{..} = do
    n <- UV.unsafeRead ring 0
    s <- UV.unsafeRead ring 1
    e <- UV.unsafeRead ring 2
    l <- asList q
    return $ str ++ "Q" ++ show (n, s, e) ++ ":" ++ show l

-- | 'Lit' Container
-- this is a derived type, thus no need to instanciation for 'ContainerLike'
instance QueueLike (FixedQueueOf Lit) Int where
  newQueue = do
     q <- UV.new 3
     UV.unsafeWrite q 0 0
     UV.unsafeWrite q 1 0
     UV.unsafeWrite q 2 0
     return $ FixedQueueOf q
  newQueueSized n = do
     q <- UV.new $ 3 + n
     UV.unsafeWrite q 0 0
     UV.unsafeWrite q 1 0
     UV.unsafeWrite q 2 0
     return $ FixedQueueOf q
  insert q@FixedQueueOf{..} x = do
    n <- UV.unsafeRead ring 0
    check <- (0 /=) <$> UV.unsafeRead ring (index x + 3)
    case () of
     _ | check -> return ()
     _ | 0 == n -> do
           UV.unsafeWrite ring 1 x
           UV.unsafeWrite ring 2 x
           UV.unsafeWrite ring (index x + 3) 0
           UV.unsafeWrite ring 0 1
     _ | 1 <= n -> do
           i <- (3 +) .index <$> UV.unsafeRead ring 2 -- the slot for the current last element
           UV.unsafeWrite ring i x                    -- points 'x` now
           UV.unsafeWrite ring 2 x                    -- and the pointer points 'x'
           UV.unsafeWrite ring (index x + 3) 0
           UV.unsafeWrite ring 0 $ n + 1
  dequeue q@FixedQueueOf{..} = do
    n <- UV.unsafeRead ring 0
    case () of
     _ | 0 == n -> error "tried to dequeue from zero length queue"
     _ | 1 == n -> do
           x <- UV.unsafeRead ring 1
           UV.unsafeWrite ring (index x + 3) 0
           UV.unsafeWrite ring 0 0
           UV.unsafeWrite ring 1 0
           UV.unsafeWrite ring 2 0
           return x
     _ | otherwise -> do
           x <- UV.unsafeRead ring 1
           i <- UV.unsafeRead ring $ index x + 3
           UV.unsafeWrite ring (index x + 3) 0    -- clear the dequeued field
           UV.unsafeWrite ring 1 i                -- and the pointer points the element
           UV.unsafeWrite ring 0 $ n - 1
           return x

traverseQueue :: FixedQueueOf Int -> IO [Int]
traverseQueue FixedQueueOf{..} = do
  let
    loop l 0 = return $ reverse l
    loop l x = loop (x:l) =<< UV.unsafeRead ring (index x + 3)
  loop [] =<< UV.unsafeRead ring 1
