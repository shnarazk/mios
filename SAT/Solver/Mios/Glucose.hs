-- | This is an implementaion of MiniSat 1.14 in Haskell
{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , MagicHash
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Solver.Mios.Glucose
       (
         lbdOf
       , updateLBD
       , nextReduction
       )
        where

import Control.Monad (when)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.Solver

lbdOf :: Solver -> Vec -> IO Int
lbdOf s@Solver{..} vec = do
  seen <- newVec . (1 +) =<< decisionLevel s
  nv <- sizeOfVector vec
  let
    loop ((< nv) -> False) n = return n
    loop k n = do
      l <- getNth level . lit2var =<< getNth vec k
      x <- getNth seen l
      if x == 0
        then setNth seen l 1 >> loop (k + 1) (n + 1)
        else loop (k + 1) n
  loop 0 0

-- | update the lbd field of /c/
{-# INLINE updateLBD #-}
updateLBD :: Solver -> Clause -> IO ()
updateLBD s NullClause = error "LBD71"
updateLBD s c@Clause{..} = do
  k <- sizeOfClause c
--  o <- getInt lbd
  n <- lbdOf s lits
  case () of
    _ | n == 1 -> setInt lbd (k - 1)
    -- _ | n < o -> setInt lbd n
    _ -> return ()

-- | 0 based
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
nextReduction b n = b {- * (n + 1) -} + 300 * n {- * (n + 1) -}
