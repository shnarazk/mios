{-# LANGUAGE Safe #-}

-- | command line option parser for mios
module SAT.Mios.OptionParser
       (
         MiosConfiguration (..)
       , defaultConfiguration
       , MiosProgramOption (..)
       , miosDefaultOption
       , miosOptions
       , miosUsage
       , miosParseOptions
       , miosParseOptionsFromArgs
       , toMiosConf
       )
       where

import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import System.Console.GetOpt (ArgDescr(..), ArgOrder(..), getOpt, OptDescr(..), usageInfo)
import System.Environment (getArgs)
import SAT.Mios.Types (MiosConfiguration(..), defaultConfiguration)

-- | configuration swithces
data MiosProgramOption = MiosProgramOption
                     {
                       _targetFile :: Maybe String
                     , _outputFile :: Maybe String
                     , _confPropagationLimit :: Int
                     , _confVariableDecayRate :: !Double
--                     , _confClauseDecayRate :: Double
--                     , _confRandomDecisionRate :: Int
                     , _confCheckAnswer :: !Bool
                     , _confVerbose :: !Bool
                     , _confTimeProbe :: !Bool
                     , _confStatProbe :: !Bool
                     , _confNoAnswer :: !Bool
                     , _validateAssignment :: !Bool
                     , _displayHelp :: !Bool
                     , _displayVersion :: !Bool
                     , _confStatHeader :: Maybe String
                     , _confDebugPath :: !Bool
                     , _confMiosParameter1 :: Maybe Double
                     , _confMiosParameter2 :: Maybe Double
                     , _confMiosParameter3 :: Maybe Int
                     , _confMiosParameter4 :: Maybe Int
                     , _confDumpStat :: !Bool
                     }

-- | default option settings
miosDefaultOption :: MiosProgramOption
miosDefaultOption = MiosProgramOption
  {
    _targetFile = Nothing
  , _outputFile = Nothing
  , _confPropagationLimit = propagationLimit defaultConfiguration
  , _confVariableDecayRate = variableDecayRate defaultConfiguration
--  , _confClauseDecayRate = clauseDecayRate defaultConfiguration
--  , _confRandomDecisionRate = randomDecisionRate defaultConfiguration
  , _confCheckAnswer = False
  , _confVerbose = False
  , _confTimeProbe = False
  , _confStatProbe = False
  , _confNoAnswer = False
  , _validateAssignment = False
  , _displayHelp = False
  , _displayVersion = False
  , _confDebugPath = False
  , _confStatHeader = Nothing
  , _confMiosParameter1 = Nothing
  , _confMiosParameter2 = Nothing
  , _confMiosParameter3 = Nothing
  , _confMiosParameter4 = Nothing
  , _confDumpStat = False
  }

-- | definition of mios option
miosOptions :: [OptDescr (MiosProgramOption -> MiosProgramOption)]
miosOptions =
  [
    Option [] ["limit"]
    (ReqArg (\v c -> c { _confPropagationLimit = read v }) (show (_confPropagationLimit miosDefaultOption)))
    "[solver] propagation limit (zero means no limit)"
  , Option ['d'] ["var-decay"]
    (ReqArg (\v c -> c { _confVariableDecayRate = read v }) (show (_confVariableDecayRate miosDefaultOption)))
    "[solver] variable activity decay rate (0.0 - 1.0)"
--  , Option ['c'] ["clause-decay-rate"]
--    (ReqArg (\v c -> c { _confClauseDecayRate = read v }) (show (_confClauseDecayRate miosDefaultOption)))
--    "[solver] clause activity decay rate (0.0 - 1.0)"
--  , Option ['r'] ["random-decision-rate"]
--    (ReqArg (\v c -> c { _confRandomDecisionRate = read v }) (show (_confRandomDecisionRate miosDefaultOption)))
--    "[solver] random selection rate (0 - 1000)"
  , Option [':'] ["validate"]
    (NoArg (\c -> c { _validateAssignment = True }))
    "[solver] read and validate an assignment from STDIN"
  , Option [] ["self-validate"]
    (NoArg (\c -> c { _confCheckAnswer = True }))
    "[solver] self-check the (satisfied) answer"
  , Option ['o'] ["output"]
    (ReqArg (\v c -> c { _outputFile = Just v }) "file")
    "[option] filename to store the result"
{-
  , Option [] ["stdin"]
    (NoArg (\c -> c { _targetFile = Nothing }))
    "[option] read a CNF from STDIN instead of a file"
-}
  , Option ['v'] ["verbose"]
    (NoArg (\c -> c { _confVerbose = True }))
    "[option] display misc information"
  , Option ['X'] ["hide-solution"]
    (NoArg (\c -> c { _confNoAnswer = True }))
    "[option] hide the solution"
  , Option [] ["time"]
    (NoArg (\c -> c { _confTimeProbe = True }))
    "[option] display execution time"
  , Option [] ["stat"]
    (NoArg (\c -> c { _confStatProbe = True }))
    "[option] display statistics information"
  , Option ['1'] ["parameter1"]
    (ReqArg (\v c -> c { _confMiosParameter1 = Just (read v) })
     (show (gpParameter1 defaultConfiguration)))
    "[MCB] greedy propagation parameter 1"
  , Option ['2'] ["parameter2"]
    (ReqArg (\v c -> c { _confMiosParameter2 = Just (read v) })
     (show (gpParameter2 defaultConfiguration)))
    "[MCB] greedy propagation parameter 2"
  , Option ['3'] ["parameter3"]
    (ReqArg (\v c -> c { _confMiosParameter3 = Just (read v) })
     (show (extraParameter3 defaultConfiguration)))
    "[devel/RS] parameter 3"
  , Option ['4'] ["parameter4"]
    (ReqArg (\v c -> c { _confMiosParameter4 = Just (read v) })
     (show (extraParameter4 defaultConfiguration)))
    "[devel/RS] parameter 4"
  , Option ['h'] ["help"]
    (NoArg (\c -> c { _displayHelp = True }))
    "[misc] display this help message"
  , Option [] ["version"]
    (NoArg (\c -> c { _displayVersion = True }))
    "[misc] display program ID"
  , Option ['D'] ["dump"]
    (NoArg (\c -> c { _confNoAnswer = True, _confStatProbe = False, _confDumpStat = True }))
    "[devel] dump statistics information"
  , Option ['H'] ["dump-header"]
    (ReqArg (\v c -> c { _confStatHeader = Just v }) "string")
    "[devel] alternative header in dump"
  , Option [] ["DEBUG", "dp"]
    (NoArg (\c -> c { _confDebugPath = True }))
    "[devel] only for developer"
  ]

-- | generates help message
miosUsage :: String -> String
miosUsage mes = usageInfo mes miosOptions

-- | builds "MiosProgramOption" from string given as command option
miosParseOptions :: String -> [String] -> IO MiosProgramOption
miosParseOptions mes argv =
    case getOpt Permute miosOptions argv of
      (o,  [], []) -> return $ foldl (flip id) miosDefaultOption o
      (o, n:_, []) -> do
        let conf = foldl (flip id) miosDefaultOption o
        return $ conf { _targetFile = Just n }
      (_, _, errs) -> ioError (userError (concat errs ++ miosUsage mes))

-- | builds "MiosProgramOption" from a String
miosParseOptionsFromArgs :: String -> IO MiosProgramOption
miosParseOptionsFromArgs mes = miosParseOptions mes =<< getArgs

-- | converts "MiosProgramOption" into "SIHConfiguration"
toMiosConf :: MiosProgramOption -> MiosConfiguration
toMiosConf opts =
  case () of
    _ | p1 < 0 -> errorWithoutStackTrace $ "parameter1 " ++ show p1 ++ " is out of range"
    _ | p2 < 0 -> errorWithoutStackTrace $ "parameter2 " ++ show p2 ++ " is out of range"
    _ ->   MiosConfiguration
           {
             propagationLimit = _confPropagationLimit opts
           , variableDecayRate = _confVariableDecayRate opts
           -- , clauseDecayRate = _confClauseDecayRate opts
           -- , randomDecisionRate = _confRandomDecisionRate opts
           , gpParameter1 = p1
           , gpParameter2 = p2
           , extraParameter3 = p3
           , extraParameter4 = p4
           }
    where
      p1 = fromMaybe (gpParameter1 defaultConfiguration) (_confMiosParameter1 opts)
      p2 = fromMaybe (gpParameter2 defaultConfiguration) (_confMiosParameter2 opts)
      p3 = fromMaybe (extraParameter3 defaultConfiguration) (_confMiosParameter3 opts)
      p4 = fromMaybe (extraParameter4 defaultConfiguration) (_confMiosParameter4 opts)
