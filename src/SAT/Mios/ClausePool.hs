{-# LANGUAGE
    BangPatterns
  , ViewPatterns
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

newClausePool ::Int -> IO ClausePool
newClausePool n = V.fromList <$> mapM (\_ -> CM.newManager n) [0 .. storeLimit]

-- | returns 'CM.ClauseManager' for caluses which have suitable sizes.
{-# INLINE getManager #-}
getManager :: ClausePool -> Int -> CM.ClauseSimpleManager
getManager p n = V.unsafeIndex p n

{-# INLINABLE makeClauseFromStack #-}
makeClauseFromStack :: ClausePool -> Stack -> IO Clause
makeClauseFromStack pool v = do
  let pickup :: Int -> IO Clause
      pickup ((<= storeLimit) -> False) = return NullClause
      pickup i = do
        let mgr = getManager pool i
        nn <- get' $ getManager pool i
        if 0 < nn
          then do c <- lastOf mgr
                  popFrom mgr
                  return c
          else pickup $ i + 1
  n <- get' v
  c <- pickup (n - 2)
  if c == NullClause
    then newClauseFromStack True v
    else do let lstack = lits c
                loop :: Int -> IO Clause
                loop ((<= n) -> False) = return c
                loop i = (setNth lstack i =<< getNth v i) >> loop (i + 1)
            loop 0
            -- the caller (newLearntClause) should set these slots
            -- set' (activity c) 0.0
            -- set' (protected c) False
            -- return c

-- | Note: only not-too-large and learnt clauses are recycled.
{-# INLINE putBackToPool #-}
putBackToPool :: ClausePool -> Clause -> IO ()
putBackToPool pool c =
  when (learnt c) $ do let n = realLengthOfStack (lits c) - 3
                       when (n <= storeLimit) $ pushTo (getManager pool n) c
