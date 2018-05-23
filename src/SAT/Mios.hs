-- | (This file is a part of MIOS.)
-- Minisat-based Implementation and Optimization Study on SAT solver
{-# LANGUAGE
    BangPatterns
  , LambdaCase
  , ViewPatterns
#-}
{-# LANGUAGE Safe #-}

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
       , SolverResult
       , Certificate (..)
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
import SAT.Mios.Main
import SAT.Mios.OptionParser
import SAT.Mios.Validator

-- | version name
versionId :: String
versionId = "#85, #71 https://github.com/shnarazk/mios"

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
executeSolverOn path = executeSolver (miosDefaultOption { _targetFile = Left path })

-- | executes a solver on the given 'arg :: MiosConfiguration'.
-- This is another entry point for standalone programs.
executeSolver :: MiosProgramOption -> IO ()
executeSolver opts = do
  solverId <- myThreadId
  (desc, cls) <- parseCNF (_targetFile opts)
  -- when (_numberOfVariables desc == 0) $ error $ "couldn't load " ++ show cnfFile
  token <- newEmptyMVar --  :: IO (MVar (Maybe Solver))
  t0 <- reportElapsedTime False "" $ if _confVerbose opts || 0 <= _confBenchmark opts then -1 else 0
  handle (\case
             UserInterrupt -> putStrLn "User interrupt recieved."
             ThreadKilled  -> reportResult opts t0 =<< readMVar token
             HeapOverflow  -> if -1 == _confBenchmark opts
                              then putStrLn "Abort: a too large problem or heap exhausted (use '+RTS -M16g' if you need)"
                              else reportResult opts t0 (Left OutOfMemory)
             e -> if -1 == _confBenchmark opts then print e else reportResult opts t0 (Left TimeOut)
         ) $ do
    when (0 < _confBenchmark opts) $
      void $ forkIO $ do let -- getCPUTime returns a pico sec. :: Integer, 1000 * 1000 * 1000 * 1000
                             -- threadDelay requires a micro sec. :: Int,  1000 * 1000
                             req = 1000000000000 * fromIntegral (_confBenchmark opts) :: Integer
                             waiting = do elp <- getCPUTime
                                          when (elp < req) $ do
                                            threadDelay $ fromIntegral (req - elp) `div` 1000000
                                            waiting
                         waiting
                         putMVar token (Left TimeOut)
                         killThread solverId
    s <- newSolver (toMiosConf opts) desc
    -- ct <- reportElapsedTime True "- making a new solver: " t0
    injectClausesFromCNF s desc cls
    void $ reportElapsedTime (_confVerbose opts) ("## [" ++ showPathFixed opts ++ "] Parse: ") t0
    -- putMVar token (Left TimeOut)
    -- killThread solverId
    -- ct <- reportElapsedTime True "injecting w/ ByteString: " ct
    when (0 < _confDumpStat opts) $ dumpStats DumpCSVHeader s
    result <- solve s []
    putMVar token result
    killThread solverId

executeSolver _ = return ()

-- | print messages on solver's result
-- Note: the last field of benchmark CSV is:
--   * 0 if UNSAT
--   * 1 if satisfiable (by finding an assignment)
--   * other bigger values are used for aborted cases.
reportResult :: MiosProgramOption -> Integer -> SolverResult -> IO ()
-- abnormal cases, catching 'too large CNF', 'timeout' for now.
reportResult opts t0 (Left OutOfMemory) = do
  t2 <- reportElapsedTime (_confVerbose opts) ("## [" ++ showPathFixed opts ++ "] Total: ") t0
  when (0 <= _confBenchmark opts) $ do
    let fromPico = 1000000000000 :: Double
    putStrLn ("\"" ++ takeWhile (' ' /=) versionId ++ "\","
              ++ show (_confBenchSeq opts) ++ ","
              ++ "\"" ++ showPath opts ++ "\","
              ++ show (_confBenchmark opts) ++ "," ++ show (fromEnum OutOfMemory)
             )

reportResult opts t0 (Left TimeOut) = do
  t2 <- reportElapsedTime (_confVerbose opts) ("## [" ++ showPathFixed opts ++ "] Total: ") t0
  when (0 <= _confBenchmark opts) $ do
    let fromPico = 1000000000000 :: Double
    putStrLn ("\"" ++ takeWhile (' ' /=) versionId ++ "\","
              ++ show (_confBenchSeq opts) ++ ","
              ++ "\"" ++ showPath opts ++ "\","
              ++ showFFloat (Just 3) (fromIntegral t2 / fromPico) ","
              ++ show (fromEnum TimeOut)
             )

-- solver terminated normally
reportResult opts t0 (Right result) = do
  t2 <- reportElapsedTime (_confVerbose opts) ("## [" ++ showPathFixed opts ++ "] Total: ") t0
  case result of
    _ | 0 <= _confBenchmark opts -> return ()
    SAT _   | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "SATISFIABLE"
    UNSAT _ | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "UNSATISFIABLE"
    SAT asg -> print asg
    UNSAT t -> do when (_confVerbose opts) $ hPutStrLn stderr "UNSAT" -- contradiction
                  print t
  dumpAssigmentAsCNF (_outputFile opts) result
  valid <- if _confCheckAnswer opts -- || 0 <= _confBenchmark opts
           then case result of
                  SAT asg -> do (desc, cls) <- parseCNF (_targetFile opts)
                                s' <- newSolver (toMiosConf opts) desc
                                injectClausesFromCNF s' desc cls
                                validate s' asg
                  UNSAT _ -> return True
           else return True
  when (_confCheckAnswer opts) $ do
    if _confVerbose opts
      then hPutStrLn stderr $ if valid then "A vaild answer" else "Internal error: mios returns a wrong answer"
      else unless valid $ hPutStrLn stderr "Internal error: mios returns a wrong answer"
    void $ reportElapsedTime (_confVerbose opts) ("## [" ++ showPathFixed opts ++ "] Validate: ") t2
  when (0 <= _confBenchmark opts) $ do
    let fromPico = 1000000000000 :: Double
        phase = case result of { SAT _   -> 1; UNSAT _ -> 0::Int }
    putStrLn $ "\"" ++ takeWhile (' ' /=) versionId ++ "\","
      ++ show (_confBenchSeq opts) ++ ","
      ++ "\"" ++ showPath opts ++ "\","
      ++ if valid
         then showFFloat (Just 3) (fromIntegral t2 / fromPico) "," ++ show phase
         else show (_confBenchmark opts) ++ "," ++ show (fromEnum InternalInconsistent)

reportResult _ _ _ = return ()

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
        case x of
          Right (SAT a)   -> return $ Right a
          Right (UNSAT a) -> return $ Left a
          _ -> return $ Left []
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
    then do result <- solve s []
            case result of
              Right (SAT a) -> return a
              _             -> return []
    else return []

-- | validates a given assignment from STDIN for the CNF file (2nd arg).
-- this is the entry point for standalone programs.
executeValidatorOn :: FilePath -> IO ()
executeValidatorOn path = executeValidator (miosDefaultOption { _targetFile = Left path })

-- | validates a given assignment for the problem (2nd arg).
-- This is another entry point for standalone programs; see app/mios.hs.
executeValidator :: MiosProgramOption -> IO ()
executeValidator opts@(_targetFile -> target@(Left cnfFile)) = do
  (desc, cls) <- parseCNF target
  when (_numberOfVariables desc == 0) . error $ "couldn't load " ++ show cnfFile
  s <- newSolver (toMiosConf opts) desc
  injectClausesFromCNF s desc cls
  when (_confVerbose opts) $
    hPutStrLn stderr $ cnfFile ++ " was loaded: #v = " ++ show (_numberOfVariables desc) ++ " #c = " ++ show (_numberOfClauses desc)
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
-- >>> do y <- solve s ... ; dumpAssigmentAsCNF (Just "result.cnf") y <$> model s
--
dumpAssigmentAsCNF :: Maybe FilePath -> Certificate -> IO ()
dumpAssigmentAsCNF Nothing _ = return ()
-- | FIXME: swtich to DRAT
dumpAssigmentAsCNF (Just fname) (UNSAT _) =
  writeFile fname "s UNSAT\n0\n"
dumpAssigmentAsCNF (Just fname) (SAT l) =
  withFile fname WriteMode $ \h -> do hPutStrLn h "s SAT"; hPutStrLn h . (++ " 0") . unwords $ map show l

showPath :: MiosProgramOption -> String
showPath (_targetFile -> Left str) = str
showPath _ = "{a cnf embedded}"

showPathFixed :: MiosProgramOption -> String
showPathFixed (_targetFile -> Left str) = replicate (len - length basename) ' ' ++ if elem '/' str then basename else basename'
  where
    len = 50
    basename = reverse . takeWhile (/= '/') . reverse $ str
    basename' = take len str

showPathFixed (_targetFile -> Right _) = replicate (len - length basename) ' ' ++ basename
  where
    len = 50
    basename = "embedded data"

--------------------------------------------------------------------------------
-- DIMACS CNF Reader
--------------------------------------------------------------------------------

-- | parses the header of a CNF file
parseCNF :: Either FilePath String -> IO (CNFDescription, B.ByteString)
parseCNF pathOrData = do
  let -- format: p cnf n m, length "p cnf" == 5
      target = case pathOrData of
                 Left str -> str
                 Right _  -> ""
      parseP line = case parseInt (skipWhitespace (B.drop 5 line)) of
                      (x, second) -> case B.readInt (skipWhitespace second) of
                                       Just (y, _) -> CNFDescription x y target
      seek :: B.ByteString -> IO (CNFDescription, B.ByteString)
      seek !bs
        | B.head bs == 'p' = return (parseP l, B.tail bs')
        | otherwise = seek (B.tail bs')
        where (l, bs') = B.span ('\n' /=) bs
  case pathOrData of
    Left cnfFile -> seek =<< B.readFile cnfFile
    Right bdata  -> seek $ B.pack bdata

-- | parses ByteString then injects the clauses in it into a solver
{-# INLINABLE injectClausesFromCNF #-}
injectClausesFromCNF :: Solver -> CNFDescription -> B.ByteString -> IO ()
injectClausesFromCNF s (CNFDescription nv nc _) bs = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec (maxLit + 1) 0 :: IO (Vec Int)
  let skipComments :: B.ByteString -> B.ByteString
      skipComments !s = case B.uncons s of -- __Pre-condition:__ we are on the benngining of a line
                          Just ('c', b') -> skipComments . B.tail . B.dropWhile (/= '\n') $ b'
                          _ -> s
      readClause :: Int -> B.ByteString -> IO ()
      readClause ((< nc) -> False) _ = return ()
      readClause !i !stream = do
        let loop :: Int -> B.ByteString -> IO ()
            loop !j !b = case parseInt $ skipWhitespace b of
                           (k, b') -> if k == 0
                                      then do setNth buffer 0 $ j - 1
                                              void $ addClause s buffer
                                              readClause (i + 1) b'
                                      else do setNth buffer j (int2lit k)
                                              loop (j + 1) b'
        loop 1 . skipComments . B.dropWhile (`elem` " \t\n") $ stream
  readClause 0 bs

{-# INLINE skipWhitespace #-}
skipWhitespace :: B.ByteString -> B.ByteString
skipWhitespace !s = B.dropWhile (== ' ') {- (`elem` " \t") -} s

{-# INLINE parseInt #-}
parseInt :: B.ByteString -> (Int, B.ByteString)
parseInt !st = do
  let !zero = ord '0'
      loop :: (Int, B.ByteString) -> (Int, B.ByteString)
      loop (val, s) = case B.uncons s of
        Just (c, s') -> if '0' <= c && c <= '9' then loop (val * 10 + ord c - zero, s') else (val, s')
        -- _ -> error (">>>>" ++ take 80 (B.unpack s))
  case B.uncons st of
    Just ('-', st') -> let (k, x) = loop (0, st') in (negate k, x)
    Just ('0', st') -> (0, st')
    _ -> loop (0, st)
