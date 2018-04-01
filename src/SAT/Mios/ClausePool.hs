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

numExtraFields :: Int
numExtraFields = 3 -- size + rank + activity

-- | returns a new 'ClausePool'
newClausePool ::Int -> Clause -> IO ClausePool
newClausePool n null = V.fromList <$> mapM (\_ -> CM.newManager n null) [0 .. storeLimit]

-- | returns 'CM.ClauseManager' for caluses which have suitable sizes.
{-# INLINE getManager #-}
getManager :: ClausePool -> Int -> CM.ClauseSimpleManager
getManager p n = V.unsafeIndex p n

-- | If a nice candidate as a learnt is stored, return it.
-- Otherwise allocate a new clause in heap then return it.
{-# INLINABLE makeClauseFromStack #-}
makeClauseFromStack :: ClausePool -> Stack -> IO Clause
makeClauseFromStack pool v = do
  let pickup :: Int -> IO (Maybe Clause)
      pickup ((<= storeLimit) -> False) = return Nothing
      pickup i = do let mgr = getManager pool i
                    nn <- get' mgr
                    if 0 < nn
                      then do c <- lastOf mgr; popFrom mgr; return (Just c)
                      else pickup $ i + 1
  n <- get' v
  c' <- pickup (n - numExtraFields)
  if c' /= Nothing
    then newClauseFromStack True v
    else do let (Just c@(Clause lstack)) = c'
                loop :: Int -> IO ()
                loop ((<= n) -> False) = setActivity c 1
                loop i = (setNth lstack i =<< getNth v i) >> loop (i + 1)
            loop 0
            -- the caller (newLearntClause) should set these slots: rank, protected
            return c

-- | Note: only not-too-large and learnt clauses are recycled.
{-# INLINE putBackToPool #-}
putBackToPool :: ClausePool -> Clause -> IO ()
putBackToPool pool c@(Clause lits) = do
  l <- getRank c
  when (0 /= l) $ do let n = realLengthOfStack lits - numExtraFields
                     when (n <= storeLimit) $ pushTo (getManager pool n) c
