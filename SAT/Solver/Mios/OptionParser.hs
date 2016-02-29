{-# LANGUAGE Trustworthy #-}
-- | command line option parser for mios
module SAT.Solver.Mios.OptionParser
       (
         MiosConfiguration (..)
       , defaultConfiguration
       , MiosConfigurationOption (..)
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
import SAT.Solver.Mios.Internal (MiosConfiguration (..), defaultConfiguration)

-- | configuration swithces
data MiosConfigurationOption = MiosConfigurationOption
                     {
                       _targetFile :: Maybe String
                     , _confVariableDecayRate :: Double
                     , _confClauseDecayRate :: Double
                     , _confRandomDecisionRate :: Int
                     , _confCheckAnswer :: Bool
                     , _confVerbose :: Bool
                     , _confNoAnswer :: Bool
                     , _validateAssignment :: Bool
                     , _displayHelp :: Bool
                     , _displayVersion :: Bool
                     }

-- | default option settings
miosDefaultOption :: MiosConfigurationOption
miosDefaultOption = MiosConfigurationOption
  {
    _targetFile = Just ""
  , _confVariableDecayRate = variableDecayRate defaultConfiguration
  , _confClauseDecayRate = clauseDecayRate defaultConfiguration
  , _confRandomDecisionRate = randomDecisionRate defaultConfiguration
  , _confCheckAnswer = False
  , _confVerbose = False
  , _confNoAnswer = False
  , _validateAssignment = False
  , _displayHelp = False
  , _displayVersion = False
  }

-- | definition of mios option
miosOptions :: [OptDescr (MiosConfigurationOption -> MiosConfigurationOption)]
miosOptions =
  [
    Option ['d'] ["variable-decay-rate"]
    (ReqArg (\v c -> c { _confVariableDecayRate = read v }) (show (_confVariableDecayRate miosDefaultOption)))
    "[solver] variable activity decay rate (0.0 - 1.0)"
  , Option ['c'] ["clause-decay-rate"]
    (ReqArg (\v c -> c { _confClauseDecayRate = read v }) (show (_confClauseDecayRate miosDefaultOption)))
    "[solver] clause activity decay rate (0.0 - 1.0)"
  , Option ['r'] ["random-decision-rate"]
    (ReqArg (\v c -> c { _confRandomDecisionRate = read v }) (show (_confRandomDecisionRate miosDefaultOption)))
    "[solver] random selection rate (0 - 1000)"
{-
  , Option [] ["stdin"]
    (NoArg (\c -> c { _targetFile = Nothing }))
    "[option] read a CNF from STDIN instead of a file"
-}
  , Option [] ["validate"]
    (NoArg (\c -> c { _confCheckAnswer = True }))
    "[option] self-check the (satisfied) answer"
  , Option ['v'] ["verbose"]
    (NoArg (\c -> c { _confVerbose = True }))
    "[option] display misc information"
  , Option ['X'] ["hide-solution"]
    (NoArg (\c -> c { _confNoAnswer = True }))
    "[option] hide the solution"
  , Option [':'] ["validate-assignment"]
    (NoArg (\c -> c { _validateAssignment = True }))
    "[option] read an assignment from STDIN and validate it"
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

-- | builds "MiosConfigurationOption" from string given as command option
miosParseOptions :: String -> [String] -> IO MiosConfigurationOption
miosParseOptions mes argv =
    case getOpt Permute miosOptions argv of
      (o, [], []) -> do
        return $ foldl (flip id) miosDefaultOption o
      (o, (n:_), []) -> do
        let conf = foldl (flip id) miosDefaultOption o
        return $ conf { _targetFile = Just n }
      (_, _, errs) -> ioError (userError (concat errs ++ miosUsage mes))

-- | builds "MiosConfigurationOption" from a String
miosParseOptionsFromArgs :: String -> IO MiosConfigurationOption
miosParseOptionsFromArgs mes = miosParseOptions mes =<< getArgs

-- | converts "MiosConfigurationOption" into "SIHConfiguration"
toMiosConf :: MiosConfigurationOption -> MiosConfiguration
toMiosConf opts = MiosConfiguration
                 {
                   variableDecayRate = _confVariableDecayRate opts
                 , clauseDecayRate = _confClauseDecayRate opts
                 , randomDecisionRate = _confRandomDecisionRate opts
                 }
