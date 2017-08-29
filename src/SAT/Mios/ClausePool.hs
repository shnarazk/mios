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

import qualified Data.Vector as V
import SAT.Mios.Vec
import SAT.Mios.Clause
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
{-# INLINE getManager #-}
getManager :: ClausePool -> Int -> CM.ClauseExtManager
getManager p n = V.unsafeIndex p $ size2index n

makeClauseFromStack :: ClausePool -> Stack -> IO Clause
makeClauseFromStack pool v = do
  n <- get' v
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
dumpToPool :: ClausePool -> Clause -> IO ()
dumpToPool pool c = if learnt c
                    then do n <- get' c; pushTo (getManager pool n) c
                    else return ()
