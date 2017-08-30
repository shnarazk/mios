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

-- | another immutable Vector of 'ClauseExtManager'
type ClausePool = V.Vector CM.ClauseExtManager

-- | biclause should be stored into index:0, so the real limit is 64.
storeLimit :: Int
storeLimit = 62

newClausePool ::Int -> IO ClausePool
newClausePool n = V.fromList <$> mapM (\_ -> CM.newManager n) [0 .. storeLimit]

{-# INLINE size2index #-}
size2index :: Int -> Int
size2index n = if n < 16 then if n < 4  then 0
                                        else 1
                         else if n < 32 then 2
                                        else 3

-- | returns 'CM.ClauseManager' for caluses which have suitable sizes.
{-# INLINE getManager #-}
getManager :: ClausePool -> Int -> CM.ClauseExtManager
getManager p n = V.unsafeIndex p n

makeClauseFromStack :: ClausePool -> Stack -> IO Clause
makeClauseFromStack pool v = do
  n <- get' v
  if storeLimit < n
    then newClauseFromStack True v
    else do let mgr = getManager pool $ n - 2
            nn <- get' mgr
            if nn == 0
              then newClauseFromStack True v
              else do c <- lastOf mgr
                      popFrom mgr
                      let lstack = lits c
                          loop ((<= n) -> False) = return ()
                          loop i = (setNth lstack i =<< getNth v i) >> loop (i + 1)
                      loop 0
                      set' (activity c) 0.0
                      set' (protected c) False
                      return c

-- | Note: only not-too-large and learnt clauses are recycled.
{-# INLINE putBackToPool #-}
putBackToPool :: ClausePool -> Clause -> IO ()
putBackToPool pool c =
  when (learnt c) $ do n <- subtract 2 <$> get' c
                       when (n <= storeLimit) $ pushTo (getManager pool n) c
