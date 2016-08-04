-- | Clause Rank evalaution
{-# LANGUAGE
    BangPatterns
  , RecordWildCards
  , ScopedTypeVariables
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Solver.Mios.Ranking
       (
         -- * Rank of Clause 
         setRank
       , updateRank
         -- * Literal Block Distance
       , lbdOf
         -- * Value for sorting
       , sortingKey
       )
        where

import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.Solver

-- | returns size of clause with offset
rankBySize :: Solver -> Clause -> IO Double
rankBySize Solver{..} c = do
  n <- sizeOfClause c
  return . fromIntegral $ if n < 12 then n else 12 + n

-- | returns the LBD vaule of 'Clause'
rankByLBD :: Solver -> Clause -> IO Double
rankByLBD s (lits -> vec) = fromIntegral <$> lbdOf s vec

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

ranking :: Solver -> Clause -> IO Double
ranking = rankBySize

-- | set 'Clause' rank, that keep goodness of the clause
{-# INLINE setRank #-}
setRank :: Solver -> Clause -> IO ()
setRank s c = setDouble (rank c) =<< ranking s c

-- | update 'Clause' rank based on @f@ that is applied to the old and new values of @rank@
{-# INLINE updateRank #-}
updateRank :: Solver -> Clause -> (Double -> Double -> Double) -> IO ()
updateRank _ NullClause _ = error "Ranking.updateRank was called NullClause"
updateRank _ (learnt -> False) _ = return ()
updateRank s c@Clause{..} f = do
  w <- getDouble rank
  w' <- ranking s c
  setDouble rank (f w w')

sortingKey :: Clause -> IO Int
sortingKey = undefined

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
