-- | This is a part of MIOS
{-# LANGUAGE
    BangPatterns
  , RecordWildCards
  , ScopedTypeVariables
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Solver.Mios.Glucose
       (
         computeLBD
       , lbdOf
       , setLBD
       , updateLBD
       , nextReduction
       )
        where

import Control.Monad (when)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.Solver

computeLBD :: Solver -> Vec -> IO Int
computeLBD Solver{..} vec = do
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

{-# INLINE lbdOf #-}
lbdOf :: Solver -> Clause -> IO Int
lbdOf s (lits -> v) = computeLBD s v

{-# INLINE setLBD #-}
setLBD :: Solver -> Clause -> IO ()
setLBD s c = setInt (lbd c) =<< lbdOf s c

-- | update the lbd field of /c/
{-# INLINE updateLBD #-}
updateLBD :: Solver -> Clause -> IO ()
updateLBD _ NullClause = error "LBD71"
updateLBD _ (learnt -> False) = return ()
updateLBD s c@Clause{..} = setInt lbd =<< lbdOf s c

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
