-- | (This is a part of MIOS.)
-- Advanced heuristics library for 'SAT.Mios.Main'
{-# LANGUAGE
    BangPatterns
  , MultiWayIf
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
         -- * Clause Metrics
       , lbdOf
       , updateNDD
       , nddOf
         -- * Restart
       , checkRestartCondition
         -- * Reporting
       , dumpStats
       )
        where

import Control.Monad (void, when)
import Data.Bits
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
varBumpActivity s@Solver{..} v = do
  x <- getNth activities v
  y <- fromIntegral <$> getStat s NumOfBackjump
  let a = (x + y) / 2
  setNth activities v a
  when (varActivityThreshold < a) $ varRescaleActivity s
  updateVO s v                    -- update the position in heap

-- | __Fig. 14 (p.19)__
{-# INLINABLE varDecayActivity #-}
varDecayActivity :: Solver -> IO ()
varDecayActivity Solver{..} = return () -- modify' varInc (/ variableDecayRate config)

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
clauseNew :: Solver -> Stack -> IO (Either Bool Clause)
clauseNew s@Solver{..} ps = do
  n <- get' ps
  sortStack ps
  let loop :: Int -> Int -> Lit -> IO Bool
      loop ((<= n) -> False) j _ = setNth ps 0 (j - 1) >> return False
      loop !i !j !l' = do l <- getNth ps i -- check the i-th literal's satisfiability
                          sat <- valueLit s l
                          if | sat == LiftedT || negateLit l == l' -> reset ps >> return True
                             | sat /= LiftedF && l /= l' -> setNth ps j l >> loop (i + 1) (j + 1) l
                             | otherwise -> loop (i + 1) j l'
  exit <- loop 1 1 LBottom
  k <- get' ps
  case k of
   0 -> return (Left exit)
   1 -> do l <- getNth ps 1
           Left <$> enqueue s l NullClause
   _ -> do c <- newClauseFromStack False ps
           let lstack = lits c
           l1 <- getNth lstack 1
           l2 <- getNth lstack 2
           pushClauseWithKey (getNthWatcher watches (negateLit l1)) c 0
           pushClauseWithKey (getNthWatcher watches (negateLit l2)) c 0
           return (Right c)

-- | returns @False@ if a conflict has occured.
-- This function is called only before the solving phase to register the given clauses (not learnt).
{-# INLINABLE addClause #-}
addClause :: Solver -> Stack -> IO Bool
addClause s@Solver{..} vecLits = do
  result <- clauseNew s vecLits
  case result of
   Left b  -> return b -- No clause is returned becaues a confilct occured or the clause is a literal
   Right c -> pushTo clauses c >> return True

-------------------------------------------------------------------------------- Clause Metrics

-- | returns a POSIVITE value of Literal Block Distance
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

-- | returns a vector index of NDD for the nth bit of a var
{-# INLINE varBit2vIndex #-}
varBit2vIndex :: Int -> Int -> Int
varBit2vIndex v ((`mod` 124) -> b)
  | 62 <= b   = 2 * v + 1
  | otherwise = 2 * v

-- | returns a bit index of NDD for the nth bit of a var
{-# INLINE varBit2bIndex #-}
varBit2bIndex :: Int -> Int -> Int
varBit2bIndex v b = mod b 62

-- | updates a /var/'s ndl, which is assigned by a 'reason' /clause/
{-# INLINE updateNddOf #-}
updateNddOf :: Solver -> Var -> Clause -> IO ()
updateNddOf Solver{..} v NullClause = do
  l <- getNth level v
  setNth ndd (varBit2vIndex v l) $ if l == 0 then 0 else setBit 0 (varBit2bIndex v l)

updateNddOf Solver{..} v Clause{..} = do
  n <- get' lits
  let iv = varBit2vIndex v 0
  setNth ndd iv 0
  setNth ndd (iv + 1) 0
  let loop :: Int -> Int -> Int -> IO ()
      loop ((<= n) -> False) low high = do setNth ndd iv low
                                           setNth ndd (iv + 1) high
      loop i low high = do v' <- lit2var <$> getNth lits i
                           let jv = varBit2vIndex v' 0
                           low' <- (low .|.) <$> getNth ndd jv
                           high' <- (high .|.) <$> getNth ndd (jv + 1)
                           loop (i + 1) low' high'
  loop 1 0 0

-- | updates all assigned vars' ndl
{-# INLINABLE updateNDD #-}
updateNDD :: Solver -> IO ()
updateNDD s@Solver{..} = do
  n <- get' trail
  let -- thr = if ns == 0 then 0 else floor . logBase 2 $ lv / ns :: Int
      update :: Int -> IO ()
      update ((<= n) -> False) = return ()
      update i = do v <- lit2var <$> getNth trail i
                    updateNddOf s v =<< getNth reason v
                    update (i + 1)
  update 1

-- | returns the NDL
{-# INLINABLE nddOf #-}
nddOf :: Solver -> Stack -> IO Int
nddOf Solver{..} stack = do
  n <- get' stack
  let loop :: Int -> Int -> Int -> IO Int -- var -> #lowbits -> #highbits
      loop ((<= n) -> False) low high = return $ popCount low + popCount high
      loop i low high = do v <- lit2var <$> getNth stack i
                           let iv = varBit2vIndex v 0
                           l <- getNth ndd iv
                           h <- getNth ndd (iv + 1)
                           loop (i + 1) (low .|. l) (high .|. h)
  max 1 <$> loop 1 0 0

-------------------------------------------------------------------------------- restart

-- | #62, #74, #91
checkRestartCondition :: Solver -> Int -> Int -> IO Bool
checkRestartCondition s@Solver{..} (fromIntegral -> lbd) (fromIntegral -> cLv) = do
  next <- get' nextRestart
  count <- getStat s NumOfBackjump -- it should be > 0
  nas <- fromIntegral <$> nAssigns s
  bLv <- fromIntegral <$> decisionLevel s
  df  <- updateEMA emaDFast lbd
  ds  <- updateEMA emaDSlow lbd
  af  <- updateEMA emaAFast nas
  as  <- updateEMA emaASlow nas
  void $ updateEMA emaCDLvl cLv
  nb <- getStat s NumOfBlockRestart
  nf <- getStat s NumOfRestart
  let bias = if | nb <= 10  -> 0
                | nb <= nf  -> 0.1 * (fromIntegral nf / fromIntegral nb) ** 2
                | otherwise -> 0.1 * negate ((fromIntegral nb / fromIntegral nf) ** 2)
      block = 1.25 * as < af
      force = (1.25 + bias) * ds < df
      updateParams ki = do
        gef <- (max 0) . (+ ki) <$> get' restartExp
        set' nextRestart $ count + 100 + ceiling (50 * gef)
        set' restartExp gef
      updateBDL = updateEMA emaBDLvl bLv >> return False
      restartBDL = do
        updateEMA emaBDLvl 0
        -- do z <- get' restartExp; when (0.4 < z) $ print (nb, nf, bias, z)
        when (3 == dumpSolverStatMode config) $ dumpStats DumpCSV s
        return True
  if | count < next -> updateBDL
     | block        -> do
         incrementStat s NumOfBlockRestart 1
         updateParams 1.0   >> updateBDL
     | force        -> do
         incrementStat s NumOfRestart 1
         updateParams (-0.1) >> restartBDL
     | otherwise    -> do
         updateParams (-0.9) >> updateBDL

-------------------------------------------------------------------------------- dump

emaLabels :: [(String, Solver -> EMA)]
emaLabels = [ ("emaAFast", emaAFast)
            , ("emaASlow", emaASlow)
            , ("emaBDLvl", emaBDLvl)
            , ("emaCDLvl", emaCDLvl)
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
  let fs :: (Solver -> EMA) -> IO String
      fs e = do x <- getEMA (e s)
                return $ showFFloat (Just 3) x ""
  vals <- mapM (fs . snd) emaLabels
  putStrLn . intercalate "," $ map (show . snd) sts ++ vals
-- | FIXME: use Util/Stat
dumpStats DumpJSON _ = return ()                -- mode 2: JSON
