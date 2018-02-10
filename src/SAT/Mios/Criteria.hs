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
  result <- clauseNew s vecLits False
  case result of
   Left b  -> return b   -- No new clause was returned becaues a confilct occured or the clause is a literal
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
updateNddOf :: Solver -> Int -> Var -> Clause -> IO ()
updateNddOf Solver{..} thr v NullClause = do
  l <- getNth level v
  setNth ndd (varBit2vIndex v l) $ if l <= thr then 0 else setBit 0 (varBit2bIndex v l)

updateNddOf Solver{..} _ v Clause{..} = do
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

{-
updateNdlOf :: Solver -> Var -> Clause -> IO ()
updateNdlOf Solver{..} v NullClause = do
  l <- getNth level v
  setNth ndl v $ if 0 == l then 0 else setBit 0 (63 .&. (l - 1))
updateNdlOf Solver{..} v Clause{..} = do
  n <- get' lits
  setNth ndl v 0
  let loop :: Int -> Int -> IO Int
      loop ((<= n) -> False) k = return k
      loop i k = do v' <- lit2var <$> getNth lits i
                    -- a <- getNth assigns v'
                    -- when (a == LBottom) $ error "unprepared path"
                    loop (i + 1) . (k .|.) =<< getNth ndl v'
  setNth ndl v =<< loop 1 0
-}

-- | updates all assigned vars' ndl
{-# INLINABLE updateNDD #-}
updateNDD :: Solver -> IO ()
updateNDD s@Solver{..} = do
  ns <- get' emaScale
  lv <- get' emaLSlow
  n <- get' trail
  let thr = if ns == 0 then 0 else floor . logBase 2 $ lv / ns :: Int
      update :: Int -> IO ()
      update ((<= n) -> False) = return ()
      update i = do v <- lit2var <$> getNth trail i
                    updateNddOf s thr v =<< getNth reason v
                    update (i + 1)
  update 1

-- | returns the NDL
{-# INLINABLE nddOf #-}
nddOf :: Solver -> Stack -> IO Int
nddOf Solver{..} stack = do
  n <- get' stack
  let loop :: Int -> Int -> Int -> Int -> IO Int -- var -> #unassigns -> #lowbits -> #highbits
      loop ((<= n) -> False) u low high = return $ u + popCount low + popCount high
      loop i u low high = do v <- lit2var <$> getNth stack i
                             a <- getNth assigns v
                             if a == LBottom
                               then loop (i + 1) (u + 1) low high
                               else do let iv = varBit2vIndex v 0
                                       l <- getNth ndd iv
                                       h <- getNth ndd (iv + 1)
                                       loop (i + 1) u (low .|. l) (high .|. h)
  max 1 <$> loop 1 0 0 0

{-
{-# INLINABLE ndlOf #-}
ndlOf :: Solver -> Stack -> IO Int
ndlOf Solver{..} stack = do
  n <- get' stack
  let loop :: Int -> Int -> Int -> IO Int -- var -> #unassigns -> #bits
      loop ((<= n) -> False) u k = return $ u + popCount k
      loop i u k = do v <- lit2var <$> getNth stack i
                      a <- getNth assigns v
                      if a == LBottom
                        then loop (i + 1) (u + 1) k
                        else loop (i + 1) u . (k .|.) =<< getNth ndl v
  loop 1 0 0
-}

-------------------------------------------------------------------------------- restart

-- | #62
checkRestartCondition :: Solver -> Int -> Int -> IO Bool
checkRestartCondition s@Solver{..} (fromIntegral -> lbd) (fromIntegral -> lrs) = do
  next <- get' nextRestart
  count <- getStat s NumOfBackjump -- it should be > 0
  nas <- fromIntegral <$> nAssigns s
  lvl <- fromIntegral <$> decisionLevel s
  let (cf, cs) = emaCoeffs config
      revise :: Double' -> Double -> Double -> IO Double
      revise e a x  = do v <- ((a * x) +) . ((1 - a) *) <$> get' e; set' e v; return v
  ns <- revise emaScale (1 / fromIntegral cs) 1
  let rescaleSlow :: Double -> Double
      rescaleSlow x = x / ns
  df <- revise emaDFast (1 / fromIntegral cf) lbd
  ds <- rescaleSlow <$> revise emaDSlow (1 / fromIntegral cs) lbd
  af <- revise emaAFast (1 / fromIntegral cf) nas
  as <- rescaleSlow <$> revise emaASlow (1 / fromIntegral cs) nas
  when (0 < dumpSolverStatMode config) $ do
    void $ {- rf <-                 -} revise emaRFast (1 / fromIntegral cf) lrs
    void $ {- rs <- rescaleSlow <$> -} revise emaRSlow (1 / fromIntegral cs) lrs
    void $ {- lf <-                 -} revise emaLFast (1 / fromIntegral cf) lvl
    void $ {- ls <- rescaleSlow <$> -} revise emaLSlow (1 / fromIntegral cs) lvl
  let step = restartExpansionS config
  if | count < next   -> return False
     | 1.25 * as < af -> do     -- -| BLOCKING RESTART |
         incrementStat s NumOfBlockRestart 1
         ki <- fromIntegral <$> getStat s NumOfRestart
         let gef = restartExpansionB config
         set' nextRestart $ count + ceiling (step + gef ** ki)
         -- set' nextRestart $ count + ceiling (step + 10 * logBase gef ki)
         when (3 == dumpSolverStatMode config) $ dumpStats DumpCSV s
         return False
     | 1.25 * ds < df -> do     -- | FORCING RESTART  |
         incrementStat s NumOfRestart 1
         ki <- fromIntegral <$> getStat s NumOfBlockRestart
         let gef = restartExpansionF config
         set' nextRestart $ count + ceiling (step + gef ** ki)
         -- set' nextRestart $ count + ceiling (step + 10 * logBase gef ki)
         when (3 == dumpSolverStatMode config) $ dumpStats DumpCSV s
         return True
     | otherwise      -> return False

-------------------------------------------------------------------------------- dump

emaLabels :: [String]
emaLabels = [ "emaDFast", "emaDSlow"
            , "emaAFast", "emaASlow"
            , "emaRFast", "emaRSlow"
            , "emaLFast", "emaLSlow"
            ]

{-# INLINABLE dumpStats #-}
-- | print statatistic data to stdio. This should be called after each restart.
dumpStats :: DumpMode -> Solver -> IO ()

dumpStats NoDump _ = return ()

dumpStats DumpCSVHeader s@Solver{..} = do
  sts <- init <$> getStats s
  putStrLn . intercalate "," $ map (show . fst) sts ++ emaLabels

dumpStats DumpCSV s@Solver{..} = do
  -- First update the stat data
  va <- get' trailLim
  setStat s NumOfVariable . (nVars -) =<< if va == 0 then get' trail else getNth trailLim 1
  setStat s NumOfAssigned =<< nAssigns s
  setStat s NumOfClause =<< get' clauses
  setStat s NumOfLearnt =<< get' learnts
  sts <- init <$> getStats s
  -- update EMAs, which type is Double
  ns <- get' emaScale
  let fs :: Double -> String
      fs x = showFFloat (Just 3) x ""
      rescaleSlow :: Double -> Double
      rescaleSlow x = x / ns
  df <- get' emaDFast
  ds <- rescaleSlow <$> get' emaDSlow
  af <- get' emaAFast
  as <- rescaleSlow <$> get' emaASlow
  rf <- get' emaRFast
  rs <- rescaleSlow <$> get' emaRSlow
  lf <- get' emaLFast
  ls <- rescaleSlow <$> get' emaLSlow
  putStrLn . intercalate "," $ map (show . snd) sts ++ map fs [df, ds, af, as, rf, rs, lf, ls]

-- | FIXME: use Util/Stat
dumpStats DumpJSON _ = return ()                -- mode 2: JSON
