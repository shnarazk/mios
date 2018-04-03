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
         -- * Activities
         claBumpActivity
       , claDecayActivity
       , varBumpActivity
       , varDecayActivity
         -- * Clause
       , addClause
         -- * Literal Block Distance
       , lbdOf
         -- * Restart
       , checkRestartCondition
         -- * Reporting
       , dumpStats
       )
        where

import Control.Monad (when)
import Data.List (intercalate)
import Numeric (showFFloat)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.Solver

-------------------------------------------------------------------------------- Activities

varActivityThreshold :: Double
varActivityThreshold = 1e100

-- | __Fig. 14 (p.19)__ Bumping of clause activity
{-# INLINE varBumpActivity #-}
varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity s@Solver{..} x = do
  a <- (+) <$> getNth activities x <*> get' varInc
  setNth activities x a
  when (varActivityThreshold < a) $ varRescaleActivity s
  updateVO s x                    -- update the position in heap

-- | __Fig. 14 (p.19)__
{-# INLINABLE varDecayActivity #-}
varDecayActivity :: Solver -> IO ()
varDecayActivity Solver{..} = modify' varInc (/ variableDecayRate config)

-- | __Fig. 14 (p.19)__
{-# INLINABLE varRescaleActivity #-}
varRescaleActivity :: Solver -> IO ()
varRescaleActivity Solver{..} = do
  let
    loop ((<= nVars) -> False) = return ()
    loop i = modifyNth activities (/ varActivityThreshold) i >> loop (i + 1)
  loop 1
  modify' varInc (/ varActivityThreshold)

-- | value for rescaling clause activity.
claActivityThreshold :: Double
claActivityThreshold = 1e20

-- | __Fig. 14 (p.19)__
{-# INLINE claBumpActivity #-}
claBumpActivity :: Solver -> Clause -> IO ()
claBumpActivity s@Solver{..} Clause{..} = do
  a <- (+) <$> get' activity <*> get' claInc
  set' activity a
  when (claActivityThreshold <= a) $ claRescaleActivity s

-- | __Fig. 14 (p.19)__
{-# INLINE claDecayActivity #-}
claDecayActivity :: Solver -> IO ()
claDecayActivity Solver{..} = modify' claInc (/ clauseDecayRate config)

-- | __Fig. 14 (p.19)__
{-# INLINABLE claRescaleActivity #-}
claRescaleActivity :: Solver -> IO ()
claRescaleActivity Solver{..} = do
  vec <- getClauseVector learnts
  n <- get' learnts
  let
    loopOnVector :: Int -> IO ()
    loopOnVector ((< n) -> False) = return ()
    loopOnVector i = do
      c <- getNth vec i
      modify' (activity c) (/ claActivityThreshold)
      loopOnVector $ i + 1
  loopOnVector 0
  modify' claInc (/ claActivityThreshold)

{-
-- | __Fig. 14 (p.19)__
{-# INLINABLE claRescaleActivityAfterRestart #-}
claRescaleActivityAfterRestart :: Solver -> IO ()
claRescaleActivityAfterRestart Solver{..} = do
  vec <- getClauseVector learnts
  n <- get' learnts
  let
    loopOnVector :: Int -> IO ()
    loopOnVector ((< n) -> False) = return ()
    loopOnVector i = do
      c <- getNth vec i
      d <- get' c
      if d < 9
        then modify' (activity c) sqrt
        else set' (activity c) 0
      -- set' (protected c) False
      loopOnVector $ i + 1
  loopOnVector 0
-}

-------------------------------------------------------------------------------- ClauseNew

-- | __Fig. 8. (p.12)__ create a new clause and adds it to watcher lists.
-- Constructor function for clauses. Returns @False@ if top-level conflict is determined.
-- @outClause@ may be set to Null if the new clause is already satisfied under the current
-- top-level assignment.
--
-- __Post-condition:__ @ps@ is cleared. For learnt clauses, all
-- literals will be false except @lits[0]@ (this by design of the 'analyze' method).
-- For the propagation to work, the second watch must be put on the literal which will
-- first be unbound by backtracking. (Note that none of the learnt-clause specific things
-- needs to done for a user defined contraint type.)
--
-- * @Left False@ if the clause is in a confilct
-- * @Left True@ if the clause is satisfied
-- * @Right clause@ if the clause is enqueued successfully
{-# INLINABLE clauseNew #-}
clauseNew :: Solver -> Stack -> Bool -> IO (Either Bool Clause)
clauseNew s@Solver{..} ps isLearnt = do
  -- now ps[0] is the number of living literals
  exit <- do
    let
      handle :: Int -> Int -> Int -> IO Bool
      handle j l n      -- removes duplicates, but returns @True@ if this clause is satisfied
        | j > n = return False
        | otherwise = do
            y <- getNth ps j
            if | y == l    -> do                      -- finds a duplicate
                   swapBetween ps j n
                   modifyNth ps (subtract 1) 0
                   handle j l (n - 1)
               | - y == l  -> reset ps >> return True -- p and negateLit p occurs in ps
               | otherwise -> handle (j + 1) l n
      loopForLearnt :: Int -> IO Bool
      loopForLearnt i = do
        n <- get' ps
        if n < i
          then return False
          else do
              l <- getNth ps i
              sat <- handle (i + 1) l n
              if sat
                then return True
                else loopForLearnt $ i + 1
      loop :: Int -> IO Bool
      loop i = do
        n <- get' ps
        if n < i
          then return False
          else do
              l <- getNth ps i     -- check the i-th literal's satisfiability
              sat <- valueLit s l  -- any literal in ps is true
              case sat of
               1  -> reset ps >> return True
               -1 -> do
                 swapBetween ps i n
                 modifyNth ps (subtract 1) 0
                 loop i
               _ -> do
                 sat' <- handle (i + 1) l n
                 if sat'
                   then return True
                   else loop $ i + 1
    if isLearnt then loopForLearnt 1 else loop 1
  k <- get' ps
  case k of
   0 -> return (Left exit)
   1 -> do
     l <- getNth ps 1
     Left <$> enqueue s l NullClause
   _ -> do
    -- allocate clause:
     c <- newClauseFromStack isLearnt ps
     let lstack = lits c
     when isLearnt $ do
       -- Pick a second literal to watch:
       let
         findMax :: Int -> Int -> Int -> IO Int
         findMax ((<= k) -> False) j _ = return j
         findMax i j val = do
           v' <- lit2var <$> getNth lstack i
           varBumpActivity s v' -- this is a just good chance to bump activities of literals in this clause
           a <- getNth assigns v'
           b <- getNth level v'
           if (a /= LBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       -- Let @max_i@ be the index of the literal with highest decision level
       max_i <- findMax 1 1 0
       swapBetween lstack 2 max_i
       -- check literals occurences
       -- x <- asList c
       -- unless (length x == length (nub x)) $ error "new clause contains a element doubly"
       -- Bumping:
       claBumpActivity s c -- newly learnt clauses should be considered active
     -- Add clause to watcher lists:
     l1 <- getNth lstack 1
     l2 <- getNth lstack 2
     pushClauseWithKey (getNthWatcher watches (negateLit l1)) c 0
     pushClauseWithKey (getNthWatcher watches (negateLit l2)) c 0
     return (Right c)

-- | returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses.
{-# INLINABLE addClause #-}
addClause :: Solver -> Stack -> IO Bool
addClause s@Solver{..} vecLits = do
  sortStack vecLits
  result <- clauseNew s vecLits False
  case result of
   Left b  -> return b   -- No new clause was returned becaues a confilct occured or the clause is a literal
   Right c -> pushTo clauses c >> return True

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
         when (3 == dumpSolverStatMode config) $ dumpStats DumpCSV s
         return True
     | 1.25 * as < af -> do
         incrementStat s NumOfBlockRestart 1
         set' nextRestart (count + floor (fromIntegral step + gef ** fromIntegral k))
         when (3 == dumpSolverStatMode config) $ dumpStats DumpCSV s
         return False
     | 1.25 * ds < df -> do
         incrementStat s NumOfRestart 1
         set' nextRestart (count + step)
         when (3 == dumpSolverStatMode config) $ dumpStats DumpCSV s
         return True
     | otherwise      -> return False

{-
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
-}

-------------------------------------------------------------------------------- dump

emaLabels :: [(String, Solver -> Double')]
emaLabels = [ ("emaAFast", emaAFast)
            , ("emaASlow", emaASlow)
--            , ("emaBDLvl", emaBDLvl)
--            , ("emaCDLvl", emaCDLvl)
            , ("emaDFast", emaDFast)
            , ("emaDSlow", emaDSlow)
            ]

{-# INLINABLE dumpStats #-}
-- | print statatistic data to stdio. This should be called after each restart.
dumpStats :: DumpMode -> Solver -> IO ()

dumpStats NoDump _ = return ()

dumpStats DumpCSVHeader s@Solver{..} = do
  sts <- init <$> getStats s
  putStrLn . intercalate "," $ map (show . fst) sts ++ map fst emaLabels

dumpStats DumpCSV s@Solver{..} = do
  -- update the stat data before dump
  va <- get' trailLim
  setStat s NumOfVariable . (nVars -) =<< if va == 0 then get' trail else getNth trailLim 1
  setStat s NumOfAssigned =<< nAssigns s
  setStat s NumOfClause =<< get' clauses
  setStat s NumOfLearnt =<< get' learnts
  sts <- init <$> getStats s
  let fs :: (Solver -> Double') -> IO String
      fs e = do x <- get' (e s)
                return $ showFFloat (Just 3) x ""
  vals <- mapM (fs . snd) emaLabels
  putStrLn . intercalate "," $ map (show . snd) sts ++ vals

-- | FIXME: use Util/Stat
dumpStats DumpJSON _ = return ()                -- mode 2: JSON
