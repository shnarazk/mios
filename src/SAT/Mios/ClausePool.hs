-- | (This is a part of MIOS.)
-- Recycling clauses
{-# LANGUAGE
    ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Mios.ClausePool
       (
         ClausePool
       , newClausePool
       , makeClauseFromStack
       , putBackToPool
       )
       where

import Control.Monad (when)
import qualified Data.Vector as V
import SAT.Mios.Vec
import SAT.Mios.Clause
import qualified SAT.Mios.ClauseManager as CM

-- | an immutable Vector of 'ClauseSimpleManager'
type ClausePool = V.Vector CM.ClauseSimpleManager

-- | biclause should be stored into index:0, so the real limit is 64.
storeLimit :: Int
storeLimit = 62

-- | returns a new 'ClausePool'
newClausePool ::Int -> IO ClausePool
newClausePool n = V.fromList <$> mapM (\_ -> CM.newManager n) [0 .. storeLimit]

-- | returns 'CM.ClauseManager' for caluses which have suitable sizes.
{-# INLINE getManager #-}
getManager :: ClausePool -> Int -> CM.ClauseSimpleManager
getManager p n = V.unsafeIndex p n

-- | If a nice candidate as a learnt is stored, return it.
-- Otherwise allocate a new clause in heap then return it.
{-# INLINABLE makeClauseFromStack #-}
makeClauseFromStack :: ClausePool -> Stack -> IO Clause
makeClauseFromStack pool v = do
  let pickup :: Int -> IO Clause
      pickup ((<= storeLimit) -> False) = return NullClause
      pickup i = do
        let mgr = getManager pool i
        nn <- get' mgr
        if 0 < nn
          then do c <- lastOf mgr; popFrom mgr; return c
          else pickup $ i + 1
  n <- get' v
  c <- pickup (n - 2)           -- mapping the number of literals for the smallest clauses to zero
  if c == NullClause
    then newClauseFromStack True v
    else do let lstack = lits c
                loop :: Int -> IO ()
                loop ((<= n) -> False) = set' (activity c) 0.0 -- setActivity c 1
                loop i = (setNth lstack i =<< getNth v i) >> loop (i + 1)
            loop 0
            return c    -- the caller (newLearntClause) should set rank and protected by himself

-- | Note: only not-too-large and learnt clauses are recycled.
{-# INLINE putBackToPool #-}
putBackToPool :: ClausePool -> Clause -> IO ()
putBackToPool pool c = do
  n <- subtract 2 <$> get' c    -- the number of literals in a clause >= 2
  l <- getRank c
  when (0 /= l && n <= storeLimit) $ pushTo (getManager pool n) c
