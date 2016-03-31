{-# LANGUAGE ViewPatterns #-}
-- | Minisat-based Implementation and Optimization Study

module SAT.Solver.Mios
       (
         -- * SAT solver interface
         versionId
       , CNFDescription (..)
       , module SAT.Solver.Mios.OptionParser
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
         -- * output
       , dumpAssigmentAsCNF
       )
       where

import Control.Monad ((<=<), unless, void, when)
import Data.Char
import qualified Data.ByteString.Char8 as B
import Data.List
import qualified Data.Vector.Unboxed as U
import Numeric (showFFloat)
import System.CPUTime
import System.Exit
import System.IO

import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Solver
import SAT.Solver.Mios.M114
import SAT.Solver.Mios.OptionParser
import SAT.Solver.Mios.Validator

reportElapsedTime :: Bool -> String -> Integer -> IO Integer
reportElapsedTime False _ _ = return 0
reportElapsedTime _ _ 0 = getCPUTime
reportElapsedTime _ mes t = do
  now <- getCPUTime
  let toSecond = 1000000000000 :: Double
  hPutStr stderr mes
  hPutStrLn stderr $ showFFloat (Just 3) ((fromIntegral (now - t)) / toSecond) " sec"
  return now

-- | executes a solver on the given CNF file
-- This is the simplest entry to standalone programs; not for Haskell programs
executeSolverOn :: FilePath -> IO ()
executeSolverOn path = executeSolver (miosDefaultOption { _targetFile = Just path })

-- | executes a solver on the given 'arg :: MiosConfiguration'
-- | This is another entry point for standalone programs.
executeSolver :: MiosProgramOption -> IO ()
executeSolver opts@(_targetFile -> target@(Just cnfFile)) = do
  t0 <- reportElapsedTime (_confTimeProbe opts) "" 0
  (desc, cls) <- parseHeader target <$> B.readFile cnfFile
  when (_numberOfVariables desc == 0) $ error $ "couldn't load " ++ show cnfFile
  s <- newSolver (toMiosConf opts) desc
  parseClauses s desc cls
  t1 <- reportElapsedTime (_confTimeProbe opts) ("## [" ++ cnfFile ++ "] Parse: ") t0
  when (_confVerbose opts) $ do
    nc <- nClauses s
    hPutStrLn stderr $ cnfFile ++ " was loaded: #v = " ++ show (nVars s, _numberOfVariables desc) ++ " #c = " ++ show (nc, _numberOfClauses desc)
  res <- simplifyDB s
  when (_confVerbose opts) $ hPutStrLn stderr $ "`simplifyDB`: " ++ show res
  result <- solve s []
  case result of
    True  | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "SATISFIABLE"
    False | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "UNSATISFIABLE"
    True  -> print =<< getModel s
    False -> do          -- contradiction
      -- FIXMEin future
      when (_confVerbose opts) $ hPutStrLn stderr "UNSAT"
      -- print =<< map lit2int <$> asList (conflict s)
      putStrLn "[]"
  case _outputFile opts of
    Just fname -> dumpAssigmentAsCNF fname result =<< getModel s
    Nothing -> return ()
  t2 <- reportElapsedTime (_confTimeProbe opts) ("## [" ++ cnfFile ++ "] Solve: ") t1
  when (result && _confCheckAnswer opts) $ do
    asg <- getModel s
    s' <- newSolver (toMiosConf opts) desc
    parseClauses s' desc cls
    good <- validate s' asg
    if _confVerbose opts
      then hPutStrLn stderr $ if good then "A vaild answer" else "Internal error: mios returns a wrong answer"
      else unless good $ hPutStrLn stderr "Internal error: mios returns a wrong answer"
    void $ reportElapsedTime (_confTimeProbe opts) ("## [" ++ cnfFile ++ "] Validate: ") t2
  void $ reportElapsedTime (_confTimeProbe opts) ("## [" ++ cnfFile ++ "] Total: ") t0
  when (_confStatProbe opts) $ do
    hPutStr stderr $ "## [" ++ cnfFile ++ "] "
    hPutStrLn stderr . intercalate ", " . map (\(k, v) -> show k ++ ": " ++ show v) =<< getStats s

executeSolver _ = return ()

-- | new top-level interface that returns
--
-- * conflicting literal set :: Left [Int]
-- * satisfiable assignment :: Right [Int]
--
runSolver :: Traversable t => MiosConfiguration -> CNFDescription -> t [Int] -> IO (Either [Int] [Int])
runSolver m d c = do
  s <- newSolver m d
  mapM_ ((s `addClause`) <=< (newSizedVecIntFromList . map int2lit)) c
  noConf <- simplifyDB s
  if noConf
    then do
        x <- solve s []
        if x
            then Right <$> getModel s
            else Left .  map lit2int <$> asList (conflict s)
    else return $ Left []


-- | the easiest interface for Haskell programs
-- This returns the result @::[[Int]]@ for a given @(CNFDescription, [[Int]])@
-- The first argument @target@ can be build by @Just target <- cnfFromFile targetfile@.
-- The second part of the first argument is a list of vector, which 0th element is the number of its real elements
solveSAT :: Traversable m => CNFDescription -> m [Int] -> IO [Int]
solveSAT = solveSATWithConfiguration defaultConfiguration

-- | solves the problem (2rd arg) under the configuration (1st arg)
-- and returns an assignment as list of literals :: Int
solveSATWithConfiguration :: Traversable m => MiosConfiguration -> CNFDescription -> m [Int] -> IO [Int]
solveSATWithConfiguration conf desc cls = do
  s <- newSolver conf desc
  -- mapM_ (const (newVar s)) [0 .. _numberOfVariables desc - 1]
  mapM_ ((s `addClause`) <=< (newSizedVecIntFromList . map int2lit)) cls
  noConf <- simplifyDB s
  if noConf
    then do
        result <- solve s []
        if result
            then getModel s
            else return []
    else return []

-- | validates a given assignment from STDIN for the CNF file (2nd arg)
-- this is the entry point for standalone programs
executeValidatorOn :: FilePath -> IO ()
executeValidatorOn path = executeValidator (miosDefaultOption { _targetFile = Just path })

-- | validates a given assignment for the problem (2nd arg)
-- this is another entry point for standalone programs; see app/mios.hs
executeValidator :: MiosProgramOption -> IO ()
executeValidator opts@(_targetFile -> target@(Just cnfFile)) = do
  (desc, cls) <- parseHeader target <$> B.readFile cnfFile
  when (_numberOfVariables desc == 0) . error $ "couldn't load " ++ show cnfFile
  s <- newSolver (toMiosConf opts) desc
  parseClauses s desc cls
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
    then putStrLn "It's a valid assignment." >> exitSuccess
    else putStrLn "It's an invalid assignment." >> exitFailure

executeValidator _  = return ()

-- | returns True if a given assignment (2nd arg) satisfies the problem (1st arg)
-- if you want to check the @answer@ which a @slover@ returned, run @solver `validate` answer@,
-- where 'validate' @ :: Traversable t => Solver -> t Lit -> IO Bool@
validateAssignment :: (Traversable m, Traversable n) => CNFDescription -> m [Int] -> n Int -> IO Bool
validateAssignment desc cls asg = do
  s <- newSolver defaultConfiguration desc
  mapM_ ((s `addClause`) <=< (newSizedVecIntFromList . map int2lit)) cls
  s `validate` asg

-- | usage
--
-- @do y <- solve s ... ; dumpAssigmentAsCNF "result.cnf" y <$> model s @
--
dumpAssigmentAsCNF :: FilePath -> Bool -> [Int] -> IO ()
dumpAssigmentAsCNF fname False _ = do
  withFile fname WriteMode $ \h -> do
    hPutStrLn h "UNSAT"

dumpAssigmentAsCNF fname True l = do
  withFile fname WriteMode $ \h -> do
    hPutStrLn h "SAT"
    hPutStrLn h . unwords $ map show l

--------------------------------------------------------------------------------
-- DIMACS CNF Reader
--------------------------------------------------------------------------------

parseHeader :: Maybe FilePath -> B.ByteString -> (CNFDescription, B.ByteString)
parseHeader target bs = if B.head bs == 'p' then (parseP l, B.tail bs') else parseHeader target (B.tail bs')
  where
    (l, bs') = B.span ('\n' /=) bs
    -- format: p cnf n m, length "p cnf" == 5
    parseP line = case B.readInt $ B.dropWhile (`elem` " \t") (B.drop 5 line) of
      Just (x, second) -> case B.readInt (B.dropWhile (`elem` " \t") second) of
        Just (y, _) -> CNFDescription x y target
        _ -> CNFDescription 0 0 target
      _ -> CNFDescription 0 0 target

parseClauses :: Solver -> CNFDescription -> B.ByteString -> IO ()
parseClauses s (CNFDescription nv nc _) bs = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec $ maxLit + 1
  polvec <- newVecBool (maxLit + 1) False
  let
    loop :: Int -> B.ByteString -> IO ()
    loop ((< nc) -> False) _ = return ()
    loop i b = loop (i + 1) =<< readClause s buffer polvec b
  loop 0 bs
  -- static polarity
  let
    asg = assigns s
    checkPolarity :: Int -> IO ()
    checkPolarity ((< nv) -> False) = return ()
    checkPolarity v = do
      p <- getNthBool polvec $ var2lit v True
      n <- getNthBool polvec $ var2lit v False
      when (p == False || n == False) $ setNth asg v $ if p then lTrue else lFalse
      checkPolarity $ v + 1
  checkPolarity 1

skipWhitespace :: B.ByteString -> B.ByteString
skipWhitespace s
  | elem c " \t\n" = skipWhitespace $ B.tail s
  | otherwise = s
    where
      c = B.head s

-- | skip comment lines
-- __Pre-condition:__ we are on the benngining of a line
skipComments :: B.ByteString -> B.ByteString
skipComments s
  | c == 'c' = skipComments . B.tail . B.dropWhile (/= '\n') $ s
  | otherwise = s
  where
    c = B.head s

parseInt :: B.ByteString -> (Int, B.ByteString)
parseInt st = do
  let
    zero = ord '0'
    loop :: B.ByteString -> Int -> (Int, B.ByteString)
    loop s val = case B.head s of
      c | '0' <= c && c <= '9'  -> loop (B.tail s) (val * 10 + ord c - zero)
      _ -> (val, B.tail s)
  case B.head st of
    '-' -> let (k, x) = loop (B.tail st) 0 in (negate k, x)
    '+' -> loop st (0 :: Int)
    c | '0' <= c && c <= '9'  -> loop st 0
    _ -> error "PARSE ERROR! Unexpected char"

readClause :: Solver -> Vec -> FixedVecBool -> B.ByteString -> IO B.ByteString
readClause s buffer pvec stream = do
  let
    loop :: Int -> B.ByteString -> IO B.ByteString
    loop i b = do
      let (k, b') = parseInt b
      if k == 0
        then do
            -- putStrLn . ("clause: " ++) . show . map lit2int =<< asList stack
            setNth buffer 0 $ i - 1
            addClause s buffer
            return b'
        else do
            let l = int2lit k
            setNth buffer i l
            setNthBool pvec l True
            loop (i + 1) b'
  loop 1 . skipComments . skipWhitespace $ stream
