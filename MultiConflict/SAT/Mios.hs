{-# LANGUAGE
    TupleSections
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
       , parseCNFfile
       , dumpAssigmentAsCNF
       )
       where

import Control.Monad ((<=<), unless, void, when)
import Data.Char
import qualified Data.ByteString.Char8 as B
import Data.List
import Data.Maybe (fromMaybe)
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
versionId = "Mios #MultiConflict based on 1.4.0 -- https://github.com/shnarazk/mios"

reportElapsedTime :: Bool -> String -> Integer -> IO Integer
reportElapsedTime False _ _ = return 0
reportElapsedTime _ _ 0 = getCPUTime
reportElapsedTime _ mes t = do
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
  t0 <- reportElapsedTime (_confTimeProbe opts) "" 0
  (desc, cls) <- parseHeader target <$> B.readFile cnfFile
  when (_numberOfVariables desc == 0) $ error $ "couldn't load " ++ show cnfFile
  let header = "## " ++ pathHeader cnfFile
  s <- newSolver (toMiosConf opts) desc
  injectClauses s desc cls
  t1 <- reportElapsedTime (_confTimeProbe opts) (header ++ showPath cnfFile ++ ", Parse: ") t0
  when (_confVerbose opts) $ do
    nc <- nClauses s
    hPutStrLn stderr $ cnfFile ++ " was loaded: #v = " ++ show (nVars s, _numberOfVariables desc) ++ " #c = " ++ show (nc, _numberOfClauses desc)
  res <- simplifyDB s
  -- when (_confVerbose opts) $ hPutStrLn stderr $ "`simplifyDB`: " ++ show res
  -- when (_confVerbose opts) $ hPutStrLn stderr $ "`simplifyDB`: " ++ show res
  result <- if res then solve s [] else return False
  aborted <- (0 ==) <$> getStat s SatisfiabilityValue
  let debug = _confDebugPath opts
  case result of
    _ | debug && aborted && _confDumpStat opts -> return ()
    _ | debug && aborted && _confStatProbe opts -> hPutStrLn stderr "ABORT"
    _ | debug && aborted && _confNoAnswer opts -> hPutStrLn stderr "ABORT"
    _ | debug && aborted -> putStrLn $ "ABORT: " ++ show result
    True  | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "SATISFIABLE"
    True  | _confStatProbe opts -> hPrint stderr =<< getModel s
    True  -> print =<< getModel s
    False | _confNoAnswer opts -> when (_confVerbose opts) $ hPutStrLn stderr "UNSATISFIABLE"
    False | _confStatProbe opts -> hPutStrLn stderr "UNSAT"
    False -> putStrLn "[]"
  case _outputFile opts of
    Just fname -> dumpAssigmentAsCNF fname result =<< getModel s
    Nothing -> return ()
  t2 <- reportElapsedTime (_confTimeProbe opts) (header ++ showPath cnfFile ++ ", Solve: ") t1
  when (result && _confCheckAnswer opts) $ do
    asg <- getModel s
    s' <- newSolver (toMiosConf opts) desc
    injectClauses s' desc cls
    good <- validate s' desc asg
    if _confVerbose opts
      then hPutStrLn stderr $ if good then "A vaild answer" else "Internal error: mios returns a wrong answer"
      else unless good $ hPutStrLn stderr "Internal error: mios returns a wrong answer"
    void $ reportElapsedTime (_confTimeProbe opts) (header ++ showPath cnfFile ++ ", Validate: ") t2
  void $ reportElapsedTime (_confTimeProbe opts) (header ++ showPath cnfFile ++ ", Total: ") t0
  when (_confStatProbe opts) $ do
    let output = stdout
    hPutStr output $ fromMaybe "" ((++ ", ") <$> _confStatHeader opts)
    hPutStr output $ "Solver: " ++ show versionId ++ ", "
    hPutStr output $ showConf (config s) ++ ", "
    hPutStr output $ "File: \"" ++ showPath cnfFile ++ "\", "
    hPutStr output $ "NumOfVariables: " ++ show (_numberOfVariables desc) ++ ", "
    hPutStr output $ "NumOfClauses: " ++ show (_numberOfClauses desc) ++ ", "
    stat1 <- intercalate ", " . map (\(k, v) -> show k ++ ": " ++ show v) <$> getStats s
    hPutStr output stat1
    hPutStrLn output ""
  when (_confDumpStat opts) $ do
    asg <- getModel s
    s' <- newSolver (toMiosConf opts) desc
    injectClauses s' desc cls
    good <- validate s' desc asg
    unless good $ setStat s SatisfiabilityValue BottomBool
    putStrLn =<< dumpToString (fromMaybe versionId (_confStatHeader opts)) s desc

executeSolver _ = return ()

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
  (desc, cls) <- parseHeader target <$> B.readFile cnfFile
  when (_numberOfVariables desc == 0) . error $ "couldn't load " ++ show cnfFile
  s <- newSolver (toMiosConf opts) desc
  injectClauses s desc cls
  when (_confVerbose opts) $
    hPutStrLn stderr $ cnfFile ++ " was loaded: #v = " ++ show (_numberOfVariables desc) ++ " #c = " ++ show (_numberOfClauses desc)
  when (_confVerbose opts) $ do
    nc <- nClauses s
    nl <- nLearnts s
    hPutStrLn stderr $ "(nv, nc, nl) = " ++ show (nVars s, nc, nl)
  asg <- read <$> getContents
  unless (_confNoAnswer opts) $ print asg
  result <- validate s desc (asg :: [Int])
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
  validate s desc asg

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
dumpAssigmentAsCNF fname False _ = withFile fname WriteMode $ \h -> hPutStrLn h "UNSAT"
dumpAssigmentAsCNF fname True l =  withFile fname WriteMode $ \h -> do hPutStrLn h "SAT"; hPutStrLn h . unwords $ map show l

--------------------------------------------------------------------------------
-- DIMACS CNF Reader
--------------------------------------------------------------------------------

-- | parse a cnf file
parseCNFfile :: Maybe FilePath -> IO (CNFDescription, [[Int]])
parseCNFfile (Just cnfFile) = do
  (desc, bytes) <- parseHeader (Just cnfFile) <$> B.readFile cnfFile
  (desc, ) <$> parseClauses desc bytes
parseCNFfile Nothing = error "no file designated"

parseHeader :: Maybe FilePath -> B.ByteString -> (CNFDescription, B.ByteString)
parseHeader target bs = if B.head bs == 'p' then (parseP l, B.tail bs') else parseHeader target (B.tail bs')
  where
    (l, bs') = B.span ('\n' /=) bs
    -- format: p cnf n m, length "p cnf" == 5
    parseP line = case B.readInt $ B.dropWhile (`elem` " \t") (B.drop 5 line) of
      Just (x, second) -> case B.readInt (B.dropWhile (`elem` " \t") second) of
        Just (y, _) -> CNFDescription target x y
        _ -> CNFDescription  target 0 0
      _ -> CNFDescription target 0 0

parseClauses :: CNFDescription -> B.ByteString -> IO [[Int]]
parseClauses (CNFDescription _ nv nc) bs = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec (maxLit + 1) 0
  let
    loop :: Int -> B.ByteString -> [[Int]] -> IO [[Int]]
    loop ((< nc) -> False) _ l = return l
    loop i b l = do
      (c, b') <- readClause' buffer b
      loop (i + 1) b' (c : l)
  loop 0 bs []

injectClauses :: Solver -> CNFDescription -> B.ByteString -> IO ()
injectClauses s (CNFDescription _ nv nc) bs = do
  let maxLit = int2lit $ negate nv
  buffer <- newVec (maxLit + 1) 0
  polvec <- newVec (maxLit + 1) 0
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
      p <- getNth polvec $ var2lit v True
      n <- getNth polvec $ var2lit v False
      when (p == LiftedFalse || n == LiftedFalse) $ setNth asg v p
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

readClause :: Solver -> Stack -> Vec Int -> B.ByteString -> IO B.ByteString
readClause s buffer bvec stream = do
  let
    loop :: Int -> B.ByteString -> IO B.ByteString
    loop i b = do
      let (k, b') = parseInt $ skipWhitespace b
      if k == 0
        then do
            -- putStrLn . ("clause: " ++) . show . map lit2int =<< asList stack
            setNth buffer 0 $ i - 1
            void $ addClause s buffer
            return b'
        else do
            let l = int2lit k
            setNth buffer i l
            setNth bvec l LiftedTrue
            loop (i + 1) b'
  loop 1 . skipComments . skipWhitespace $ stream

readClause' :: Stack -> B.ByteString -> IO ([Int], B.ByteString)
readClause' buffer stream = do
  let
    loop :: Int -> B.ByteString -> IO ([Int], B.ByteString)
    loop i b = do
      let (k, b') = parseInt $ skipWhitespace b
      if k == 0
        then do
            -- putStrLn . ("clause: " ++) . show . map lit2int =<< asList stack
            setNth buffer 0 $ i - 1
            (, b') <$> (take <$> get' buffer <*> asList buffer)
        else do
            setNth buffer i k
            loop (i + 1) b'
  loop 1 . skipComments . skipWhitespace $ stream

showPath :: FilePath -> String
showPath str = {- replicate (len - length basename) ' ' ++ -} if elem '/' str then basename else basename'
  where
    len = 32
    basename = reverse . takeWhile (/= '/') . reverse $ str
    basename' = take len str

pathHeader :: FilePath -> String
pathHeader str = replicate (len - length basename) ' '
  where
    len = 32
    basename = reverse . takeWhile (/= '/') . reverse $ str

showConf :: MiosConfiguration -> String
showConf (MiosConfiguration vr pl _ _ _ _) =
  "VarDecayRate: " ++ showFFloat (Just 3) vr "" ++ ", PropagationLimit: " ++ show pl
