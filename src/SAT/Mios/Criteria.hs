-- | (This is a part of MIOS.)
-- Advanced heuristics library for 'SAT.Mios.Main'
{-# LANGUAGE
    MultiWayIf
  , RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Mios.Criteria
       (
         -- * Literal Block Distance
         lbdOf
         -- * Restart
       , checkRestartCondition
       )
        where

import Control.Monad (when)
import SAT.Mios.Types
import SAT.Mios.Solver

-------------------------------------------------------------------------------- LBD

-- | returns a POSIVITE value
{-# INLINABLE lbdOf #-}
lbdOf :: Solver -> Stack -> IO Int
lbdOf Solver{..} vec = do
  k <- (\k -> if 1000000 < k then 1 else k + 1) <$> get' lbd'key
  set' lbd'key k                -- store the last used value
  nv <- getNth vec 0
  let loop :: Int -> Int -> IO Int
      loop ((<= nv) -> False) n = return $ max 1 n
      loop i n = do l <- getNth level . lit2var =<< getNth vec i
                    x <- getNth lbd'seen l
                    if x /= k && l /= 0
                      then setNth lbd'seen l k >> loop (i + 1) (n + 1)
                      else loop (i + 1) n
  loop 1 0

{-
{-# INLINE setLBD #-}
setLBD :: Solver -> Clause -> IO ()
setLBD _ NullClause = error "LBD44"
setLBD s c = set' (rank c) =<< lbdOf s (lits c)

-- | update the lbd field of /c/
{-# INLINE updateLBD #-}
updateLBD :: Solver -> Clause -> IO ()
updateLBD s NullClause = error "LBD71"
updateLBD s c@Clause{..} = do
  k <- get' c
--  o <- getInt lbd
  n <- lbdOf s lits
  case () of
    _ | n == 1 -> set' rank (k - 1)
    -- _ | n < o -> setInt lbd n
    _ -> return ()
-}

-------------------------------------------------------------------------------- restart

ema1, ema2, ema3, ema4 :: Double
ema1 = 2 ** (-5)                -- coefficient for fast average of LBD
ema2 = 2 ** (-14)               -- coefficient for slow average of LBD
ema3 = 2 ** (-5)                -- coefficient for fast average of | assignment |
ema4 = 2 ** (-12)               -- coefficient for slow average of | assignment |

ema0 :: Int
ema0 = 2 ^ (14 :: Int)          -- = floor $ 1 / ema2

-- | #62
checkRestartCondition :: Solver -> Int -> IO Bool
checkRestartCondition s@Solver{..} (fromIntegral -> lbd) = do
  k <- getStat s NumOfRestart
  let step = 100
  next <- get' nextRestart
  count <- getStat s NumOfBackjump
  nas <- fromIntegral <$> nAssigns s
  let revise a f x  = do f' <- ((a * x) +) . ((1 - a) *) <$> get' f
                         set' f f'
                         return f'
      gef = 1.1 :: Double       -- geometric expansion factor
  df <- revise ema1 emaDFast lbd
  ds <- revise ema2 emaDSlow lbd
  af <- revise ema3 emaAFast nas
  as <- revise ema4 emaASlow nas
  mode <- get' restartMode
  if | count < next   -> return False
     | mode == 1      -> do
         when (ema0 < count && df < 2.0 * ds) $ set' restartMode 2 -- enter the second mode
         incrementStat s NumOfRestart 1
         incrementStat s NumOfGeometricRestart 1
         k' <- getStat s NumOfGeometricRestart
         set' nextRestart (count + floor (fromIntegral step * gef ** fromIntegral k'))
         when (3 == dumpStat config) $ dumpSolver DumpCSV s
         return True
     | 1.25 * as < af -> do
         incrementStat s NumOfBlockRestart 1
         set' nextRestart (count + floor (fromIntegral step + gef ** fromIntegral k))
         when (3 == dumpStat config) $ dumpSolver DumpCSV s
         return False
     | 1.25 * ds < df -> do
         incrementStat s NumOfRestart 1
         set' nextRestart (count + step)
         when (3 == dumpStat config) $ dumpSolver DumpCSV s
         return True
     | otherwise      -> return False

{-# INLINABLE luby #-}
luby :: Double -> Int -> Double
luby y x_ = loop 1 0
  where
    loop :: Int -> Int -> Double
    loop sz sq
      | sz < x_ + 1 = loop (2 * sz + 1) (sq + 1)
      | otherwise   = loop2 x_ sz sq
    loop2 :: Int -> Int -> Int -> Double
    loop2 x sz sq
      | sz - 1 == x = y ** fromIntegral sq
      | otherwise   = let s = div (sz - 1) 2 in loop2 (mod x s) s (sq - 1)
