{-# LANGUAGE
    BangPatterns
  , LambdaCase
  , ViewPatterns
#-}
{-# LANGUAGE Safe #-}

-- | Minisat-based Implementation and Optimization Study on SAT solver
module SAT.Mios
       (
         -- * Interface to the core of solver
         versionId
       , CNFDescription (..)
       , module SAT.Mios.OptionParser
       , runSolver
       , solveSAT
       , solveSATWithConfiguration
       , solve
       , getModel
         -- * Assignment Validator
       , validateAssignment
       , validate
         -- * For standalone programs
       , executeSolverOn
       , executeSolver
       , executeValidatorOn
       , executeValidator
         -- * File IO
       , parseCNF
       , injectClausesFromCNF
       , dumpAssigmentAsCNF
       )
       where

import Control.Concurrent (forkIO, killThread, myThreadId, threadDelay
                          , newEmptyMVar, putMVar, readMVar)
import Control.Exception
import Control.Monad ((<=<), unless, void, when)
import Data.Char
import qualified Data.ByteString.Char8 as B
import Numeric (showFFloat)
import System.CPUTime
import System.Exit
import System.IO

import SAT.Mios.Types
import SAT.Mios.Solver
import SAT.Mios.Main
import SAT.Mios.OptionParser
import SAT.Mios.Validator

-- | version name
versionId :: String
versionId = "mios-1.5.3WIP#parseOnFd -- https://github.com/shnarazk/mios"

reportElapsedTime :: Bool -> String -> Integer -> IO Integer
reportElapsedTime False _ 0 = return 0
reportElapsedTime False _ _ = getCPUTime
reportElapsedTime True mes t = do
  now <- getCPUTime
  let toSecond = 1000000000000 :: Double
  hPutStr stderr mes
  hPutStrLn stderr $ showFFloat (Just 3) (fromIntegral (now - t) / toSecond) " sec"
  return now

-- | executes a solver on the given CNF file.
-- This is the simplest entry to standalone programs; not for Haskell programs.
executeSolverOn :: FilePath -> IO ()
executeSolverOn path = executeSolver (miosDefaultOption { _targetFile = Just path })

-- | executes a solver on the given 'arg :: MiosConfiguration'.
-- This is another entry point for standalone programs.
executeSolver :: MiosProgramOption -> IO ()
executeSolver opts@(_targetFile -> target@(Just cnfFile)) = do
  t0 <- reportElapsedTime False "" $ if _confVerbose opts || 0 <= _confBenchmark opts then -1 else 0
  (desc, cls) <- parseCNF target <$> B.readFile cnfFile
  -- when (_numberOfVariables desc == 0) $ error $ "couldn't load " ++ show cnfFile
  token <- newEmptyMVar --  :: IO (MVar (Maybe Solver))
  solverId <- myThreadId
  handle (\case
             UserInterrupt -> putStrLn "User interrupt recieved."
             ThreadKilled  -> reportResult opts desc cls t0 =<< readMVar token
             e -> print e) $ do
    when (0 < _confBenchmark opts) $
      void $ forkIO $ do let fromMicro = 1000000 :: Int
                         threadDelay $ fromMicro * fromIntegral (_confBenchmark opts)
                         putMVar token Nothing
                         killThread solverId
    when (_confMaxSize opts < min (_numberOfVariables desc) (_numberOfClauses desc)) $ do
      if -1 == _confBenchmark opts
        then errorWithoutStackTrace $ "ABORT: too big CNF = " ++ show desc
        else putMVar token Nothing >> killThread solverId
    s <- newSolver (toMiosConf opts) desc
    injectClausesFromCNF s desc cls
    void $ reportElapsedTime (_confVerbose opts) ("## [" ++ showPath cnfFile ++ "] Parse: ") t0
    when (0 < _confDumpStat opts) $ dumpSolver DumpCSVHeader s
    void $ solve s []
    putMVar token (Just s)
    killThread solverId

executeSolver _ = return ()

reportResult :: MiosProgramOption -> CNFDescription -> B.ByteString -> Integer -> Maybe Solver -> IO ()
reportResult opts@(_targetFile -> Just cnfFile) _ _ _ Nothing = do
 putStrLn $ "\"" ++ takeWhile (' ' /=) versionId ++ "\","
   ++ (show (_confBenchSeq opts)) ++ ","
   ++ "\"" ++ cnfFile ++ "\","
   ++ show (_confBenchmark opts) ++ ",0"

reportResult opts@(_targetFile -> Just cnfFile) desc cls t0 (Just s) = do
  t2 <- reportElapsedTime (_confVerbose opts) ("## [" ++ showPath cnfFile ++ "] Total: ") t0
  satisfiable <- get' (ok s)
  case satisfiable of
    _ | 0 <= _confBenchmark opts -> return ()
    LiftedT | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "SATISFIABLE"
    LiftedF | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "UNSATISFIABLE"
    LiftedT -> print =<< getModel s
    LiftedF -> do          -- contradiction
      -- FIXME in future
      when (_confVerbose opts) $ hPutStrLn stderr "UNSAT"
      -- print =<< map lit2int <$> asList (conflict s)
      putStrLn "[]"
  case _outputFile opts of
    Just fname -> dumpAssigmentAsCNF fname (LiftedT == satisfiable) =<< getModel s
    Nothing -> return ()
  valid <- if (_confCheckAnswer opts) || (0 <= _confBenchmark opts)
           then do case satisfiable of
                     LiftedT -> do asg <- getModel s
                                   s' <- newSolver (toMiosConf opts) desc
                                   injectClausesFromCNF s' desc cls
                                   validate s' asg
                     LiftedF -> return True
                     _ -> return False
           else return True
  when (_confCheckAnswer opts) $ do
    if _confVerbose opts
      then hPutStrLn stderr $ if valid then "A vaild answer" else "Internal error: mios returns a wrong answer"
      else unless valid $ hPutStrLn stderr "Internal error: mios returns a wrong answer"
    void $ reportElapsedTime (_confVerbose opts) ("## [" ++ showPath cnfFile ++ "] Validate: ") t2
  when (0 <= _confBenchmark opts) $ do
    let fromPico = 1000000000000 :: Double
    putStrLn $ "\"" ++ takeWhile (' ' /=) versionId ++ "\","
      ++ (show (_confBenchSeq opts)) ++ ","
      ++ "\"" ++ cnfFile ++ "\","
      ++ if valid then showFFloat (Just 3) (fromIntegral (t2 - t0) / fromPico) "" else show (_confBenchmark opts)
      ++ "," ++ (if valid then "1" else "0")
  when (0 < _confDumpStat opts) $ dumpSolver DumpCSV s

reportResult _  _ _  _ _ = return ()

-- | new top-level interface that returns:
--
-- * conflicting literal set :: Left [Int]
-- * satisfiable assignment :: Right [Int]
--
runSolver :: Traversable t => MiosConfiguration -> CNFDescription -> t [Int] -> IO (Either [Int] [Int])
runSolver m d c = do
  s <- newSolver m d
  mapM_ ((s `addClause`) <=< (newStackFromList . map int2lit)) c
  noConf <- simplifyDB s
  if noConf
    then do
        x <- solve s []
        if x
            then Right <$> getModel s
            else Left .  map lit2int <$> asList (conflicts s)
    else return $ Left []

-- | The easiest interface for Haskell programs.
-- This returns the result @::[[Int]]@ for a given @(CNFDescription, [[Int]])@.
-- The first argument @target@ can be build by @Just target <- cnfFromFile targetfile@.
-- The second part of the first argument is a list of vector, which 0th element is the number of its real elements.
solveSAT :: Traversable m => CNFDescription -> m [Int] -> IO [Int]
solveSAT = solveSATWithConfiguration defaultConfiguration

-- | solves the problem (2rd arg) under the configuration (1st arg).
-- and returns an assignment as list of literals :: Int.
solveSATWithConfiguration :: Traversable m => MiosConfiguration -> CNFDescription -> m [Int] -> IO [Int]
solveSATWithConfiguration conf desc cls = do
  s <- newSolver conf desc
  -- mapM_ (const (newVar s)) [0 .. _numberOfVariables desc - 1]
  mapM_ ((s `addClause`) <=< (newStackFromList . map int2lit)) cls
  noConf <- simplifyDB s
  if noConf
    then do
        result <- solve s []
        if result
            then getModel s
            else return []
    else return []

-- | validates a given assignment from STDIN for the CNF file (2nd arg).
-- this is the entry point for standalone programs.
executeValidatorOn :: FilePath -> IO ()
executeValidatorOn path = executeValidator (miosDefaultOption { _targetFile = Just path })

-- | validates a given assignment for the problem (2nd arg).
-- This is another entry point for standalone programs; see app/mios.hs.
executeValidator :: MiosProgramOption -> IO ()
executeValidator opts@(_targetFile -> target@(Just cnfFile)) = do
  (desc, cls) <- parseCNF target <$> B.readFile cnfFile
  when (_numberOfVariables desc == 0) . error $ "couldn't load " ++ show cnfFile
  s <- newSolver (toMiosConf opts) desc
  injectClausesFromCNF s desc cls
  when (_confVerbose opts) $
    hPutStrLn stderr $ cnfFile ++ " was loaded: #v = " ++ show (_numberOfVariables desc) ++ " #c = " ++ show (_numberOfClauses desc)
  when (_confVerbose opts) $ do
    nc <- nClauses s
    nl <- nLearnts s
    hPutStrLn stderr $ "(nv, nc, nl) = " ++ show (nVars s, nc, nl)
  asg <- read <$> getContents
  unless (_confNoAnswer opts) $ print asg
  result <- s `validate` (asg :: [Int])
  if result
    then putStrLn ("It's a valid assignment for " ++ cnfFile ++ ".") >> exitSuccess
    else putStrLn ("It's an invalid assignment for " ++ cnfFile ++ ".") >> exitFailure

executeValidator _  = return ()

-- | returns True if a given assignment (2nd arg) satisfies the problem (1st arg).
-- if you want to check the @answer@ which a @slover@ returned, run @solver `validate` answer@,
-- where 'validate' @ :: Traversable t => Solver -> t Lit -> IO Bool@.
validateAssignment :: (Traversable m, Traversable n) => CNFDescription -> m [Int] -> n Int -> IO Bool
validateAssignment desc cls asg = do
  s <- newSolver defaultConfiguration desc
  mapM_ ((s `addClause`) <=< (newStackFromList . map int2lit)) cls
  s `validate` asg

-- | dumps an assigment to file.
-- 2nd arg is
--
-- * @True@ if the assigment is satisfiable assigment
--
-- * @False@ if not
--
-- >>> do y <- solve s ... ; dumpAssigmentAsCNF "result.cnf" y <$> model s
--
dumpAssigmentAsCNF :: FilePath -> Bool -> [Int] -> IO ()
dumpAssigmentAsCNF fname False _ = writeFile fname "UNSAT"

dumpAssigmentAsCNF fname True l = withFile fname WriteMode $ \h -> do hPutStrLn h "SAT"; hPutStrLn h . unwords $ map show l

--------------------------------------------------------------------------------
-- DIMACS CNF Reader
--------------------------------------------------------------------------------

parseCNF :: Maybe FilePath -> B.ByteString -> (CNFDescription, B.ByteString)
parseCNF target bs = if B.head bs == 'p'
                           then (parseP l, B.tail bs')
                           else parseCNF target (B.tail bs')
  where
    (l, bs') = B.span ('\n' /=) bs
    -- format: p cnf n m, length "p cnf" == 5
    parseP line = case B.readInt $ B.dropWhile (`elem` " \t") (B.drop 5 line) of
      Just (x, second) -> case B.readInt (B.dropWhile (`elem` " \t") second) of
        Just (y, _) -> CNFDescription x y target
        _ -> CNFDescription 0 0 target
      _ -> CNFDescription 0 0 target

-- | parses ByteString then injects the clauses in it into a solver
injectClausesFromCNF :: Solver -> CNFDescription -> B.ByteString -> IO ()
injectClausesFromCNF s (CNFDescription nv nc _) bs = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec (maxLit + 1) 0
  polvec <- newVec (maxLit + 1) 0
  let loop :: Int -> B.ByteString -> IO ()
      loop ((< nc) -> False) _ = return ()
      loop !i !b = loop (i + 1) =<< readClause s buffer polvec b
  loop 0 bs
  -- static polarity
  let asg = assigns s
      checkPolarity :: Int -> IO ()
      checkPolarity ((< nv) -> False) = return ()
      checkPolarity v = do
        p <- getNth polvec $ var2lit v True
        if p == LiftedF
          then setNth asg v p
          else do n <- getNth polvec $ var2lit v False
                  when (n == LiftedF) $ setNth asg v p
        checkPolarity $ v + 1
  checkPolarity 1

{-# INLINE skipWhitespace #-}
skipWhitespace :: B.ByteString -> B.ByteString
skipWhitespace !s
  | elem c " \t\n" = skipWhitespace $ B.tail s
  | otherwise = s
    where
      c = B.head s

-- | skip comment lines
-- __Pre-condition:__ we are on the benngining of a line
{-# INLINE skipComments #-}
skipComments :: B.ByteString -> B.ByteString
skipComments !s
  | c == 'c' = skipComments . B.tail . B.dropWhile (/= '\n') $ s
  | otherwise = s
  where
    c = B.head s

{-# INLINABLE parseInt #-}
parseInt :: B.ByteString -> (Int, B.ByteString)
parseInt !st = do
  let
    !zero = ord '0'
    loop :: B.ByteString -> Int -> (Int, B.ByteString)
    loop !s !val = case B.head s of
      c | '0' <= c && c <= '9'  -> loop (B.tail s) (val * 10 + ord c - zero)
      _ -> (val, B.tail s)
  case B.head st of
    '-' -> let (k, x) = loop (B.tail st) 0 in (negate k, x)
    '+' -> loop st (0 :: Int)
    c | '0' <= c && c <= '9'  -> loop st 0
    _ -> error "PARSE ERROR! Unexpected char"

{-# INLINABLE readClause #-}
readClause :: Solver -> Stack -> Vec Int -> B.ByteString -> IO B.ByteString
readClause s buffer bvec stream = do
  let
    loop :: Int -> B.ByteString -> IO B.ByteString
    loop !i !b = case parseInt $ skipWhitespace b of
                   (0, b') -> do setNth buffer 0 $ i - 1
                                 sortStack buffer
                                 void $ addClause s buffer
                                 return b'
                   (k, b') -> case int2lit k of
                                l -> do setNth buffer i l
                                        setNth bvec l LiftedT
                                        loop (i + 1) b'
  loop 1 . skipComments . skipWhitespace $ stream

showPath :: FilePath -> String
showPath str = replicate (len - length basename) ' ' ++ if elem '/' str then basename else basename'
  where
    len = 50
    basename = reverse . takeWhile (/= '/') . reverse $ str
    basename' = take len str
