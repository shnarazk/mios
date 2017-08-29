{-# LANGUAGE
    BangPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Mios.ClausePool
       (
         ClausePool
       , newClausePool
       , getPool
       )
       where

import qualified Data.Vector as V
import qualified SAT.Mios.ClauseManager as CM

-- | another immutable Vector of 'ClauseExtManager'
type ClausePool = V.Vector CM.ClauseExtManager

newClausePool :: Int -> Int -> IO ClausePool
newClausePool n m = V.fromList <$> mapM (\_ -> CM.newManager m) [0 .. n]

{-# INLINE size2index #-}
size2index :: Int -> Int
size2index n = if n < 16 then if n < 8  then 0
                                        else 1
                         else if n < 32 then 2
                                        else 3

-- | returns 'CM.ClauseManager' for caluses which have suitable sizes.
{-# INLINE getPool #-}
getPool :: ClausePool -> Int -> CM.ClauseExtManager
getPool p n = V.unsafeIndex p $ size2index n

