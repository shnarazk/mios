-- | A simple benchmarker to dump a result of testrun(s)
-- Requirement: GNU parallel installed in your PATH
-- Usage: sat-benchmark [OPTIONS] [solvers]
-- examples:
--   - sat-benchmark -3 250 minisat             # 3-SAT from 150 (default) to 250 vars
--   - sat-benchmark -3 250 -s mios             # 3-SATs and your set of structured problems
--   - sat-benchmark -o "-cla-decay 0.9" -s glucose     # options to solver
--   - sat-benchmark -t ./g2-ACG-15-10p1.cnf -s glucose # -t for a CNF file
--   - sat-benchmark -t '../test/*.cnf' -s glucose      # -t for CNF files
--
-- Note: edit @baseDir@ by yourself before compile
--
-- cabal settings
-- executable sat-benchmark
--   main-is:             sat-benchmark.hs
--   build-depends:       base >=4.7, unix >= 2.7, process >= 1.2
--   default-language:    Haskell2010
{-# LANGUAGE ViewPatterns #-}

import Control.Monad
import System.Console.GetOpt
import System.Environment (getArgs)
import System.Exit (ExitCode(..))
import System.IO (hFlush, stdout)
import System.Posix.Env (getEnvDefault)
import System.Process (system)
import Text.Printf

version :: String
version = "sat-benchmark 0.13.4"

data ConfigurationOption = ConfigurationOption
                     {
                       targets :: Maybe String
                     , rangeFrom :: Int
                     , rangeTo :: Int
                     , fundamentalExamSet :: Bool
                     , threeSATSet :: Bool
                     , structuredSATSet :: Bool
                     , solvers :: [String]
                     , timeout :: Int
                     , inParallel :: Int
                     , dumpAll :: Bool
                     , terminateHook :: String
                     , solverOptions :: String
                     , devNull :: Bool
                     , showID :: Bool
                     , showHelp :: Bool
                     , header :: Maybe String
                     , skipTitle :: Bool
                     , message :: String
                     , auxKey :: String
                     }
                         deriving (Show)

defaultConfigration = ConfigurationOption
  {
    targets = Nothing
  , rangeFrom = 175
  , rangeTo = 250
  , fundamentalExamSet = False
  , threeSATSet = False
  , structuredSATSet = False
  , solvers = []
  , timeout = 1260
  , inParallel = 1
  , dumpAll = False
  , terminateHook = "finished"
  , solverOptions = "" -- "-X" or "+RTS -K20M -RTS -X"
  , devNull = True
  , showID = False
  , showHelp = False
  , header = Nothing
  , skipTitle = False
  , message = ""
  , auxKey = ""
  }

options :: [OptDescr (ConfigurationOption -> ConfigurationOption)]
options =
  [
    Option ['t'] ["targets"]
     (ReqArg (\v c -> c { targets = Just v }) "'file pattern'")
     "quoted target files (w/ wild cards)"
  , Option ['f'] ["fundamental-exam"]
     (NoArg (\c -> c { fundamentalExamSet = True }))
     "run on fundamental problems"
  , Option ['3'] ["3SAT"]
     (ReqArg (\v c -> c { threeSATSet = True, rangeTo = read v}) (show (rangeTo defaultConfigration)))
     ("run on 3-SAT problems upto " ++ show (rangeTo defaultConfigration))
  , Option ['s'] ["structured"]
     (NoArg (\c -> c { structuredSATSet = True }))
     "run on structured problems"
  , Option ['L'] ["from"]
     (ReqArg (\v c -> c { rangeFrom = read v }) (show (rangeFrom defaultConfigration)))
     "set lower bound for 3-SAT problems (use w/ -3)"
  , Option ['U'] ["upto"]
     (ReqArg (\v c -> c { rangeTo = read v }) (show (rangeTo defaultConfigration)))
     "set upper bound for 3-SAT problems (use w/ -3)"
  , Option ['o'] ["options"]
     (ReqArg (\v c -> c { solverOptions = v }) (show (solverOptions defaultConfigration)))
     "set solver options"
  , Option ['T'] ["timeout"]
     (ReqArg (\v c -> c { timeout = read v }) (show (timeout defaultConfigration)))
     "set timeout [second]"
  , Option ['j'] ["parallel"]
     (ReqArg (\v c -> c { inParallel = read v }) (show (inParallel defaultConfigration)))
     "execute in parallel"
  , Option ['A'] ["dump-all", "all"]
     (NoArg (\c -> c { dumpAll = True }))
     "list all results instead of a summary"
{-
  , Option [] ["solvers"]
     (ReqArg (\v c -> c { solvers = read v, solverOptions = "" }) (show (solvers defaultConfigration)))
    "set solver name list"
-}
  , Option ['S'] ["show-output"]
     (NoArg (\c -> c { devNull = False }))
     "show the real output of solvers"
  , Option [] ["terminate-hook"]
     (ReqArg (\v c -> c { terminateHook = v }) (show (terminateHook defaultConfigration)))
     "set terminate hook, called when benchmark ends"
  , Option ['h'] ["help"]
     (NoArg (\c -> c { showHelp = True }))
     "display this help message"
  , Option [] ["version"]
     (NoArg (\c -> c { showID = True }))
     "display version id"
  , Option ['M'] ["message"]
     (ReqArg (\v c -> c { message = v }) (show (message defaultConfigration)))
     "set optional message used as a header of result"
  , Option ['H'] ["header"]
     (ReqArg (\v c -> c { header = Just $ undecodeNewline v }) "header")
     "set CSV header"
  , Option ['J'] ["SkipTitle"]
     (NoArg (\c -> c { skipTitle = True }))
     "skip experimental information"
  , Option ['K'] ["auxKey"]
     (ReqArg (\v c -> c { auxKey = v }) (show (auxKey defaultConfigration)))
     "set optional key string that is append to the solver name"
    ]

usage :: String
usage = "[" ++ version ++ "] Usage: sat-benchmark [OPTIONS] [solvers]"

parseOptions :: [String] -> IO ConfigurationOption
parseOptions argv =
    case getOpt Permute options argv of
      (o, [], []) -> do
        return $ foldl (flip id) defaultConfigration o
      (o, l, []) -> do
        let conf = foldl (flip id) defaultConfigration o
        return $ conf { solvers = l }
      (_, _, errs) -> ioError (userError (concat errs ++ usageInfo usage options))

undecodeNewline :: String -> String
undecodeNewline [] = []
undecodeNewline [a] = [a]
undecodeNewline ('\\' : 'n' : x) = '\n' : undecodeNewline x
undecodeNewline (a : x) = a : undecodeNewline x

setEnv :: String
setEnv = "export LC_ALL=C; export TIMEFORMAT=\" %2U\""

-- | returns an absolute path to your repository, given your $HOME
baseDir :: String -> String
baseDir home = home ++ add-your-directory

fundamentalProblems =
  let
    dir = "fundamental/"
    range = ["1000", "2000", "4000", "6000", "8000"]
    series key l = [(key ++ n, dir ++ key ++ "-" ++ n ++ ".cnf") | n <- l]
  in
   series "chain" range
   ++ series "zero" range
   ++ series "triangle" range

structuredProblems :: [(String, String)] -- pair of label and filname
structuredProblems =
  [ -- something like this
    ("itox", "test/data/itox_vc1130.cnf")
  , ("m283", "test/data/manthey_DimacsSorter_28_3.cnf")
  , ("38b", "test/data/38bits_10.dimacs.cnf")
  , ("44b", "test/data/44bits_11.dimacs.cnf")
  ]

main :: IO ()
main = do
  home <- getEnvDefault "HOME" ""
  args <- getArgs
  conf <- parseOptions $ args
  let base = baseDir home
  let singleSolver = length (solvers conf) == 1
  case () of
    _ | showHelp conf -> putStrLn $ usageInfo usage options
    _ | showID conf -> putStrLn $ version
    _ | null (solvers conf) -> putStrLn $ usageInfo usage options
    _ ->  do
      case header conf of
        Just h                 -> putStr h
        Nothing | dumpAll conf -> putStrLn "solver, num, seq, target, time"
        _                      -> putStrLn "solver, num, target, time"
      let extraMessage = if message conf == "" then "" else ", " ++ message conf
      when singleSolver $ do
        let solver = head (solvers conf)
        unless (skipTitle conf) . void . system $ printf "echo -n \\# $(ls -g -G --time-style=long-iso `which %s` | sed -e 's/[-rwx]* [1-9] [0-9]* //' -e 's/ \\([0-9][0-9]:[0-9][0-9]\\).*/T\\1/') '%s; '; %s --version" solver solver solver
        return ()
      unless (skipTitle conf) . void . system $ printf "echo \"# %s, j=%d, t=%d, p='%s' on `hostname` @ `date -Iseconds`%s\"" version (inParallel conf) (timeout conf) (solverOptions conf) extraMessage
      let opts = solverOptions conf
      forM_ (solvers conf) $ \solver -> do
        val <- system $ "which " ++ solver ++ " > /dev/null"
        when (val == ExitSuccess) $ do
          unless singleSolver $ do
            unless (skipTitle conf) . void . system $ printf "echo -n \\# $(ls -g -G --time-style=long-iso `which %s` | sed -e 's/[-rwx]* [1-9] [0-9]* //' -e 's/ \\([0-9][0-9]:[0-9][0-9]\\).*/T\\1/') '%s; '; %s --version" solver solver solver
            return ()
          let
            threes = [rangeFrom conf, rangeFrom conf + 25 .. rangeTo conf]
            nums :: Int -> [Int]
            nums 0 = [ 1 :: Int .. ]
            nums 1 = drop (if fundamentalExamSet conf then length fundamentalProblems else 0) $ nums 0
            nums 2 = drop (if threeSATSet conf then length threes else 0) $ nums 1
            nums _ = nums 0
            withNum n l = zip (nums n) l
          case targets conf of
            Just s -> executeTargets conf solver opts s
            Nothing -> do
              when (fundamentalExamSet conf) $ mapM_ (execute conf solver opts base) $ withNum 0 fundamentalProblems
              when (threeSATSet conf) $ mapM_ (execute3SATs conf solver opts base) $ withNum 1 threes
              when (structuredSATSet conf) $ mapM_ (execute conf solver opts base) $ withNum 2 structuredProblems
      unless (null (terminateHook conf)) $ void (system (terminateHook conf))

-- | target is a list of files (for SAT-RACE benchmark)
executeTargets conf solver options files = do
  hFlush stdout
  let flagJ = "-j " ++ show (inParallel conf)
  let solverName = solver ++ auxKey conf
  if devNull conf
    then system $ printf "%s; (parallel --keep-order --joblog satbench.log %s \"echo -n '\\\"%s\\\", {#}, \\\"{}\\\", '; time timeout -k %d %d %s %s {} > /dev/null \" ::: %s ; ) 2>&1" setEnv flagJ solverName (timeout conf) (timeout conf) solver options files
    else system $ printf "%s; (parallel --keep-order --joblog satbench.log %s \"echo -n '\\\"%s\\\", {#}, \\\"{}\\\", '; time timeout -k %d %d %s %s {} \" ::: %s ; ) 2>&1" setEnv flagJ solverName (timeout conf) (timeout conf) solver options files
  hFlush stdout

-- | [dump for DEBUG] target is a list of files (for SAT-RACE benchmark)
execute3SATs conf@(dumpAll -> True) solver options dir (num, targets) = do
  hFlush stdout
  let flagJ = "-j " ++ show (inParallel conf)
  let solverName = solver ++ auxKey conf
  if devNull conf
     then system $ printf "%s; (parallel --keep-order %s \"echo -n '\\\"%s\\\", %d, {#}, \\\"{}\\\", '; time timeout -k %d %d %s %s {} > /dev/null\" ::: %s/3-SAT/UF%s/uf*.cnf;) 2>&1" setEnv flagJ solverName num (timeout conf) (timeout conf) solver options dir (show targets)
     else system $ printf "%s; (parallel --keep-order %s \"echo -n '\\\"%s\\\", %d {#}, \\\"{}\\\", '; time timeout -k %d %d %s %s {} \" ::: %s/3-SAT/UF%s/uf*.cnf;) 2>&1" setEnv flagJ solverName num (timeout conf) (timeout conf) solver options dir (show targets)

-- | only show the average or total result of targets (for 3-SAT problems)
execute3SATs conf solver options dir (num, targets) = do
  let q s = "\"" ++ s ++ "\""
  let solverName = solver ++ auxKey conf
  let flagJ = "-j " ++ show (inParallel conf)
  putStr $ q solverName ++ ", " ++ show num ++ ", " ++ show targets ++ ",\t"
  hFlush stdout
  if devNull conf
     then system $ printf "%s; (time timeout -k %d %d parallel --keep-order %s \"%s %s {} > /dev/null\" ::: %s/3-SAT/UF%s/uf*.cnf;) 2>&1" setEnv (timeout conf) (timeout conf) flagJ solver options dir (show targets)
     else system $ printf "%s; (time timeout -k %d %d parallel --keep-order %s \"%s %s {} \" ::: %s/3-SAT/UF%s/uf*.cnf;) 2>&1" setEnv (timeout conf) (timeout conf) flagJ solver options dir (show targets)

-- | [dump for DEBUG] only show the average or total result of targets (for 3-SAT problems)
execute conf@(dumpAll -> True) solver options dir (num, (key, target)) = do
  hFlush stdout
  let flagJ = "-j " ++ show (inParallel conf)
  let solverName = solver ++ auxKey conf
  if devNull conf
    then system $ printf "%s; (parallel --keep-order %s \"echo -n '\\\"%s\\\", %d, {#}, \\\"{}\\\", '; time timeout -k %d %d %s %s {} > /dev/null \" ::: %s/%s ; ) 2>&1" setEnv flagJ solverName num (timeout conf) (timeout conf) solver options dir target
    else system $ printf "%s; (parallel --keep-order %s \"echo -n '\\\"%s\\\", %d, {#}, \\\"{}\\\", '; time timeout -k %d %d %s %s {} \" ::: %s/%s ; ) 2>&1" setEnv flagJ solverName num (timeout conf) (timeout conf) solver options dir target
  hFlush stdout

-- | target is one of defined problem sets: fundamentalProblems, structuredProblems
execute conf solver options dir (num, (key, target)) = do
  let q s = "\"" ++ s ++ "\""
  let flagJ = "-j " ++ show (inParallel conf)
  let solverName = solver ++ auxKey conf
  putStr $ q solverName ++ ", " ++ show num ++ ", " ++ q key ++ ",\t"
  hFlush stdout
  if devNull conf
    then system $ printf "%s; (parallel --keep-order %s \"time timeout -k %d %d %s %s {} > /dev/null \" ::: %s/%s ; ) 2>&1" setEnv flagJ (timeout conf) (timeout conf) solver options dir target
    else system $ printf "%s; (parallel --keep-order %s \"time timeout -k %d %d %s %s {} \" ::: %s/%s ; ) 2>&1" setEnv flagJ (timeout conf) (timeout conf) solver options dir target
  hFlush stdout
