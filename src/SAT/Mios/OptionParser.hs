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

import System.Console.GetOpt (ArgDescr(..), ArgOrder(..), getOpt, OptDescr(..), usageInfo)
import System.Environment (getArgs)
import SAT.Mios.Types (MiosConfiguration (..), defaultConfiguration)

-- | configuration swithces
data MiosProgramOption = MiosProgramOption
                     {
                       _targetFile :: Maybe String
                     , _outputFile :: Maybe String
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
                     }

-- | default option settings
miosDefaultOption :: MiosProgramOption
miosDefaultOption = MiosProgramOption
  {
    _targetFile = Nothing
  , _outputFile = Nothing
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
  }

-- | definition of mios option
miosOptions :: [OptDescr (MiosProgramOption -> MiosProgramOption)]
miosOptions =
  [
    Option ['d'] ["variable-decay-rate"]
    (ReqArg (\v c -> c { _confVariableDecayRate = read v }) (show (_confVariableDecayRate miosDefaultOption)))
    "[solver] variable activity decay rate (0.0 - 1.0)"
--  , Option ['c'] ["clause-decay-rate"]
--    (ReqArg (\v c -> c { _confClauseDecayRate = read v }) (show (_confClauseDecayRate miosDefaultOption)))
--    "[solver] clause activity decay rate (0.0 - 1.0)"
--  , Option ['r'] ["random-decision-rate"]
--    (ReqArg (\v c -> c { _confRandomDecisionRate = read v }) (show (_confRandomDecisionRate miosDefaultOption)))
--    "[solver] random selection rate (0 - 1000)"
  , Option [':'] ["validate-assignment"]
    (NoArg (\c -> c { _validateAssignment = True }))
    "[solver] read an assignment from STDIN and validate it"
  , Option [] ["validate"]
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
  , Option ['h'] ["help"]
    (NoArg (\c -> c { _displayHelp = True }))
    "[misc] display this help message"
  , Option [] ["version"]
    (NoArg (\c -> c { _displayVersion = True }))
    "[misc] display program ID"
  ]

-- | generates help message
miosUsage :: String -> String
miosUsage mes = usageInfo mes miosOptions

-- | builds "MiosProgramOption" from string given as command option
miosParseOptions :: String -> [String] -> IO MiosProgramOption
miosParseOptions mes argv =
    case getOpt Permute miosOptions argv of
      (o, [], []) -> return $ foldl (flip id) miosDefaultOption o
      (o, n:_, []) -> do
        let conf = foldl (flip id) miosDefaultOption o
        return $ conf { _targetFile = Just n }
      (_, _, errs) -> ioError (userError (concat errs ++ miosUsage mes))

-- | builds "MiosProgramOption" from a String
miosParseOptionsFromArgs :: String -> IO MiosProgramOption
miosParseOptionsFromArgs mes = miosParseOptions mes =<< getArgs

-- | converts "MiosProgramOption" into "SIHConfiguration"
toMiosConf :: MiosProgramOption -> MiosConfiguration
toMiosConf opts = MiosConfiguration
                 {
                   variableDecayRate = _confVariableDecayRate opts
--                 , clauseDecayRate = _confClauseDecayRate opts
--                 , randomDecisionRate = _confRandomDecisionRate opts
                 }
