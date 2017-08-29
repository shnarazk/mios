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
       , dumpToPool
       )
       where

import Control.Monad (when)
import qualified Data.Vector as V
import SAT.Mios.Vec
import SAT.Mios.Clause
import qualified SAT.Mios.ClauseManager as CM

-- | another immutable Vector of 'ClauseExtManager'
type ClausePool = V.Vector CM.ClauseExtManager

newClausePool ::Int -> IO ClausePool
newClausePool n = V.fromList <$> mapM (\_ -> CM.newManager n) [0 .. 3]

{-# INLINE size2index #-}
size2index :: Int -> Int
size2index n = if n < 16 then if n < 4  then 0
                                        else 1
                         else if n < 32 then 2
                                        else 3

-- | returns 'CM.ClauseManager' for caluses which have suitable sizes.
{-# INLINE getManager #-}
getManager :: ClausePool -> Int -> CM.ClauseExtManager
getManager p n = V.unsafeIndex p $ size2index n

makeClauseFromStack :: ClausePool -> Stack -> IO Clause
makeClauseFromStack pool v = do
  n <- get' v                   -- FIXME: we need the allocated length here
  let mgr = getManager pool n
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

-- | Note: only learnt clauses are stocked.
{-# INLINE dumpToPool #-}
dumpToPool :: ClausePool -> Clause -> IO ()
dumpToPool pool c =
  when (learnt c) $ do n <- get' c  -- FIXME
                       when (4 <= n) $pushTo (getManager pool (div n 2)) c
