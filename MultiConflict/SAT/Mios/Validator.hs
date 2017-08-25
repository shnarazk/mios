{-# LANGUAGE
    RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | validate an assignment
module SAT.Mios.Validator
       (
         validate
         -- * internal debug
--       , checkConsistency
--       , valueClause
--       , checkAssigns
--       , checkWatchLits
--       , checkWatches
--       , checkCurrentModel
--       , printReason
--       , printAnalyzeVars
       )
       where

import Control.Monad (forM_, when, unless)
import Data.Foldable (toList)
import Data.List (intersect, sort)
import Data.Maybe (fromMaybe)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.Solver

-- | validates the assignment even if the implementation of 'Solver' is wrong; we re-implement some functions here.
validate :: Traversable t => Solver -> CNFDescription -> t Int -> IO Bool
validate s desc (toList -> map int2lit -> lst) = do
  assignment <- newVec (1 + nVars s) (0 :: Int) :: IO (Vec Int)
  vec <- getClauseVector (clauses s)
  nc <- get' (clauses s)
  let
    injectLit :: Lit -> IO ()
    injectLit l = setNth assignment (lit2var l) $ if positiveLit l then LiftedTrue else LiftedFalse
    -- returns True if the literal is satisfied under the assignment
    satisfied :: Lit -> IO Bool
    satisfied l
      | positiveLit l = (LiftedTrue ==) <$> getNth assignment (lit2var l)
      | otherwise     = (LiftedFalse ==) <$> getNth assignment (lit2var l)
    -- returns True is any literal in the given list
    satAny :: [Lit] -> IO Bool
    satAny [] = return False
    satAny (l:ls) = do
      sat' <- satisfied l
      if sat' then return True else satAny ls
    -- traverses all clauses in 'clauses'
    loopOnVector :: Int -> IO Bool
    loopOnVector ((< nc) -> False) = return True
    loopOnVector i = do
      sat' <- satAny =<< asList =<< getNth vec i
      if sat' then loopOnVector (i + 1) else return False
  if null lst
    then errorWithoutStackTrace $ "# validator got an empty assignment for " ++ fromMaybe "" (_pathname desc) ++ ""
    else mapM_ injectLit lst >> loopOnVector 0

{-
copySolver :: Solver -> MiosConfiguration -> IO Solver
copySolver s conf = do
  nc <- (+) <$> nClauses s <*> nLearnts s
  let desc = CNFDescription Nothing (nVars s) nc
  s' <- newSolver conf desc
  let copy :: ClauseExtManager -> IO ()
      copy man = do
        n <- get' man
        v <- getClauseVector man
        let loop :: Int -> IO ()
            loop ((< n) -> False) = return ()
            loop i = do addClause s' =<< copyVec . lits =<< getNth v i
                        loop (i + 1)
        loop 0
  copy (clauses s)
  copy (learnts s)
  return s'
-}

checkCurrentModel :: Solver -> Bool -> IO ()
checkCurrentModel _ False = return ()
{-
checkCurrentModel s True = do
  let conf = MiosConfiguration 0.95 8000000000  False GP06CurrentConstant (minBound :: MultipleLearning) 1 1
  s' <- copySolver s conf
  x <- Certified.solve s' []
  if x
    then return () -- putStrLn "pass"
    else do i <- nLearnts s
            v <- getClauseVector (learnts s)
            c <- getNth v (i - 1)
            k <- dump "learnt:" c
            d <- decisionLevel s
            nb <- getStat s NumOfBackjumps
            putStrLn $ "Validator finds inconsistent state, at " ++ show (d, nb) ++ " maybe caused by adding " ++ k
            printReason s ("current reason (decision level = " ++ show d ++ ")") True
            errorWithoutStackTrace =<< dumpToString "" s (CNFDescription Nothing 0 0)
-}

{-
-- | returns @True@ if the solver is in inconsistent.
checkConsistency :: Solver -> IO Bool
checkConsistency s@Solver{..} = do
  vec <- getClauseVector clauses
  nc <- get' clauses
  let
    toInt :: Var -> IO Lit
    toInt v = (\p -> if LiftedTrue == p then v else negate v) <$> valueVar s v
    getM :: Int -> IO [Lit]
    getM ((<= nVars) -> False) = return []
    getM v = (:) <$> toInt v <*> getM (v + 1)
    poles :: [Lit] -> IO [Int]
    poles     [] = return []
    poles (l:ls) = (:) <$> valueLit s l <*> poles ls
    -- traverses all clauses in 'clauses'; returns True if any clause is unsat
    loopOnVector :: Int -> IO Bool
    loopOnVector ((< nc) -> False) = return False
    loopOnVector i = do c <- getNth vec i
                        x <- valueClause s c
                        if LiftedFalse == x
                          then do l <- asList c
                                  t2 <- poles l
                                  let l' = map lit2int l
                                  t0 <- dump "" c
                                  m <- getM 1
                                  putStrLn $ "Validator found conflicting clause: " ++ t0 ++ show l' ++ ": " ++ show (intersect l' m) ++ ": " ++ show t2
                                  return True
                          else loopOnVector (i + 1)
  res <- loopOnVector 0
  when res $ do
    m <- getM 1
    dl <- decisionLevel s
    putStrLn $ "decisionLevel: " ++ show dl
    print m -- $ filter (0 /=) m
    na <- nAssigns s
    putStrLn $ "number of assigned variable = " ++ show na
    putStrLn "*** Conflict ***"
  return res
-}

valueClause :: Solver -> Clause -> IO LiftedBool
valueClause _ NullClause = errorWithoutStackTrace "valueClause found NullClause"
valueClause s Clause{..} = do
  n <- get' lits
  let loop ((<= n) -> False) val = return val
      loop i ret = do
        x <- valueLit s =<< getNth lits i
        case x of
          LiftedTrue  -> return LiftedTrue
          BottomBool  -> loop (i + 1) BottomBool
          LiftedFalse -> loop (i + 1) ret
          _           -> errorWithoutStackTrace "valueClause found ConflictBool"
  loop 1 LiftedFalse

-- | returns @True@ in no problem
checkAssigns :: Solver -> Bool -> IO Bool
checkAssigns s@Solver{..} repair = do
  let
    loop :: Int -> Bool -> IO Bool
    loop ((<= nVars) -> False) _ = return True
    loop i found = do
      x <- getNth assigns i
      if x == ConflictBool
        then do l <- getNth level i
                unless (repair || found) $ do
                  putStrLn "### checkAssigns ###"
                  d <- decisionLevel s
                  putStrLn $ "Found Conflict in var: " ++ show i ++ " at level: " ++ show l ++ " current level = " ++ show d
                  tc <- get' trail
                  print . map lit2int . take tc =<< asList trail
                if repair
                  then do setNth assigns i =<< getNth phases i
                          loop (i + 1) True
                  else return False
        else loop (i + 1) found
  loop 1 False

checkUniqueness :: Solver -> Clause -> IO ()
checkUniqueness Solver{..} c = do
  n <- get' learnts
  cvec <- getClauseVector learnts
  cls <- sort <$> asList c
  let
    loop :: Int -> IO ()
    loop ((< n) -> False) = return ()
    loop i = do
      c' <- getNth cvec i
      cls' <- sort <$> asList c'
      when (cls' == cls) $ errorWithoutStackTrace "reinsert a same clause"
      loop (i + 1)
  loop 0

printAnalyzeVars :: Solver -> IO ()
printAnalyzeVars Solver{..} = do
  let stack2list :: Stack -> IO [Int]
      stack2list s = take <$> get' s <*> asList s
  reset an'stack
  reset an'toClear
  reset an'lastDL
  v1 <- filter (0 /=) <$> asList an'seen
  v2 <- filter (0 /=) <$> stack2list an'toClear
  v3 <- filter (0 /=) <$> stack2list an'stack
  v4 <- filter (0 /=) <$> stack2list an'lastDL
  unless (v1 == []) $ putStrLn ("an'seen: " ++ show v1)
  unless (v2 == []) $ putStrLn ("an'toClear: " ++ show v2)
  unless (v3 == []) $ putStrLn ("an'stack: " ++ show v3)
  unless (v4 == []) $ putStrLn ("an'lastDL: " ++ show v4)

{-
checkWatchLits :: Solver -> Bool -> Clause -> IO Bool
checkWatchLits s@Solver{..} emit c@Clause{..} = do
  n <- get' c
  dl <- decisionLevel s
  let levelOf :: Int -> IO Int
      levelOf i = do
        l <- getNth lits i
        val <- valueLit s l
        case abs val of
          BottomBool   -> return (-1)
          ConflictBool -> getNth level (lit2var l)
          LiftedTrue   -> getNth level (lit2var l)
  (t:lvs') <- mapM levelOf [1 .. n]
  let lvs = filter (dl /=) (tail lvs')
  case () of
    _ | t == -1          -> return False
    _ | null lvs         -> return False
    _ | t >= maximum lvs -> return False
    _ -> do c' <- dump "" c
            putStrLn $ c' ++ " levels: " ++ show (t:lvs') ++ "; decisionLevel = " ++ show dl
            if emit
              then errorWithoutStackTrace "condition violated"
              else return True

checkWatches :: Solver -> Bool -> IO ()
checkWatches s@Solver{..} emit = do
  n <- get' learnts
  cvec <- getClauseVector learnts
  let
    loop :: Int -> IO ()
    loop ((< n) -> False) = return ()
    loop i = do
      checkWatchLits s emit =<< getNth cvec i
      loop (i + 1)
  loop 0
-}

{-
printReason :: Solver -> String -> Bool -> IO ()
printReason _ _ False = return ()
printReason s mes True = do
  d <- decisionLevel s
  -- nb <- getStat s NumOfBackjumps
  dp'1 <- asList (assigns s)
  dp'2 <- asList (level s)
  let dp'3 = filter (\(a', l', _) -> a' /= 0 && l' <= d) (zip3 dp'1 dp'2 [1 ..])
  let asgs = map (\(a', l', i') -> if a' == ConflictBool then (i', -1) else (a' * i', l')) dp'3
  putStrLn $ "------------------ " ++ mes
  forM_ asgs $ \(lit, flag) -> do
    let showInt n = ((if flag == -1 then "*" else " ") ++) . reverse . take 4 . reverse $ ("    " ++ show n)
    lv <- getNth (level s) (lit2var lit)
    m <- dump "" =<< getNth (reason s) (lit2var lit)
    putStrLn $ showInt lit ++ "(" ++ showInt lv ++ ")" ++ " : " ++ m
  putStrLn $ "------------------ end"
-}

{-
{-# INLINABLE checkDuplicateConflictVar #-}
checkDuplicateConflictVar :: Solver -> Var -> IO Bool
checkDuplicateConflictVar Solver{..} v = do
  let manager = getNthWatcher watches 0
  n <- get' manager
  vec <- getKeyVector manager
  let
    loop :: Int -> IO Bool
    loop ((< n) -> False) = return False
    loop i = do
      v' <- getNth vec i
      if v == v' then return True else loop (i + 1)
  loop 0
-}
