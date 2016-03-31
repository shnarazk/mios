-- | This is stack of Int, not in use since 1.1
{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , UndecidableInstances
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Simple Queue
module SAT.Solver.Mios.Data.Queue
       (
         Queue
       , newQueue
       , clearQueue
       , sizeOfQueue
       , insertQueue
       , dequeue
       )
       where

import qualified Data.Vector.Unboxed.Mutable as UV

type Queue = UV.IOVector Int

{-# INLINABLE newQueue #-}
newQueue :: Int -> IO Queue
newQueue n = do
  v <- UV.new $ n + 4           -- 2 for header 1 for a padding
  UV.set v 0
  UV.unsafeWrite v 0 1
  UV.unsafeWrite v 1 2
  return v

{-# INLINE sizeOfQueue #-}
sizeOfQueue :: Queue -> IO Int
sizeOfQueue iq = do
  w <- UV.unsafeRead iq 0
  r <- UV.unsafeRead iq 1
  if r <= w + 1
    then return $ w - r + 1
    else return $ UV.length iq -2 + w - r + 1

{-# INLINE clearQueue #-}
clearQueue :: Queue -> IO ()
clearQueue iq = do
  UV.unsafeWrite iq 0 1
  UV.unsafeWrite iq 1 2

{-# INLINE insertQueue #-}
insertQueue :: Queue -> Int -> IO ()
insertQueue iq !x = do
  wh <- (1 +) <$> UV.unsafeRead iq 0 -- write head
  if wh < UV.length iq
    then UV.unsafeWrite iq wh x >> UV.unsafeWrite iq 0 wh
    else UV.unsafeWrite iq 2 x >> UV.unsafeWrite iq 0 2

{-# INLINE dequeue #-}
dequeue :: Queue -> IO Int
dequeue iq = do
  rh <- UV.unsafeRead iq 1       -- read head
  let rh' = rh + 1
  if rh' < UV.length iq
    then UV.unsafeWrite iq 1 rh'
    else UV.unsafeWrite iq 1 2
  UV.unsafeRead iq rh
