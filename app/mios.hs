{-# LANGUAGE
    MultiWayIf
  , TemplateHaskell
  #-}
-- | Executable of 'Minisat Implementation and Optimization Study'
module Main
       (
         main
       )
       where

import SAT.Mios
import Development.GitRev

gitId :: String
gitId = "mios " ++ versionId ++ "/commit/" ++ $(gitHash)

usage :: String
usage = miosUsage $ gitId ++ "\nUsage: mios [OPTIONS] target.cnf"

-- | main
main :: IO ()
main = do opts <- miosParseOptionsFromArgs versionId
          if | _displayVersion opts        -> putStrLn gitId
             | _displayHelp opts           -> putStrLn usage
             | _targetFile opts == Left "" -> putStrLn usage
             | _validateAssignment opts    -> executeValidator opts =<< buildSolver opts
             | otherwise                   -> executeSolver opts =<< buildSolver opts

