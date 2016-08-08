{-# LANGUAGE
    BangPatterns
  , RecordWildCards
  , ScopedTypeVariables
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | Clause Rank evalaution
module SAT.Solver.Mios.Ranking
       (
         -- * Rank of Clause
         ranking
--       , setRank
--       , updateRank
--         -- * Literal Block Distance
--       , lbdOf
--         -- * Value for sorting
--       , sortingKey
       )
        where

import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.Solver

-- | returns size of clause with offset
{-# INLINE rankBySize #-}
rankBySize :: Solver -> Clause -> IO Int
rankBySize _ = sizeOfClause

-- | returns size of clause with offset
{-# INLINE rankBySizeOffset #-}
rankBySizeOffset :: Solver -> Clause -> IO Int
rankBySizeOffset _ c = do
  n <- sizeOfClause c
  return $ if n < 12 then n else 12 + n

rankBySizeOffset' :: Solver -> Clause -> IO Int
rankBySizeOffset' s _ = (12 +) <$> decisionLevel s

{-# INLINE ranking #-}
ranking :: Solver -> Clause -> IO Int
ranking = rankBySize

{-# INLINE ranking' #-}
ranking' :: Solver -> Clause -> IO Int
ranking' = rankBySize

{-
-------------------------------------------------------------------------------- Clause.rank
-- | set 'Clause' rank, that keep goodness of the clause
{-# INLINE setRank #-}
setRank :: Solver -> Clause -> IO ()
setRank s c = setInt (rank c) =<< ranking s c

-- | update 'Clause' rank based on @f@ that is applied to the old and new values of @rank@
{-# INLINE updateRank #-}
updateRank :: Solver -> Clause -> (Int -> Int -> Int) -> IO ()
updateRank _ NullClause _ = error "Ranking.updateRank was called on NullClause"
updateRank _ (learnt -> False) _ = return ()
updateRank s c@Clause{..} f = do
  w <- getInt rank
  w' <- ranking' s c
  setInt rank (f w w')

sortingKey :: Clause -> IO Int
sortingKey = undefined
-}

{-
-------------------------------------------------------------------------------- LBD
-- | returns the LBD vaule of 'Clause'
{-# INLINE rankByLBD #-}
rankByLBD :: Solver -> Clause -> IO Int
rankByLBD s (lits -> vec) = lbdOf s vec

-- | returns the LBD vaule of 'SizedVec'
lbdOf :: Solver -> Vec -> IO Int
lbdOf Solver{..} vec = do
  key <- (1 +) <$> getInt lbd'key
  setInt lbd'key key
  nv <- getNth vec 0
  let
    loop :: Int -> Int -> IO Int
    loop ((<= nv) -> False) n = return n
    loop !i !n = do
      l <- getNth level . lit2var =<< getNth vec i
      seen <- if l == 0 then return True else (key ==) <$> getNth lbd'seen l
      if seen
        then loop (i + 1) n
        else setNth lbd'seen l key >> loop (i + 1) (n + 1)
  loop 1 0
-}

-------------------------------------------------------------------------------- Glucose garbage
-- | 0 based
--
-- >>> nextReduction 0
-- 20000
-- >>> nextReduction 1
-- 40000 + 200 = 20000 + 20000 + 200
-- >>> nextReduction 2
-- 6000 + 600 = 20000 + 20200 + 20000 + 400
-- >>> nextReduction 3
-- 80000 + 1200 = 20000 + 20200 + 20400 + 20000 + 600
--
nextReduction :: Int -> Int -> Int
-- nextReduction _ n = 30000 + 10000 * n
nextReduction b n = b + 300 * n
