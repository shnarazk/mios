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
gitId = " (" ++ take 8 $(gitHash) ++ "@" ++ $(gitBranch) ++ ")"

usage :: String
usage = miosUsage $ versionId ++ gitId ++ "\nUsage: mios [OPTIONS] target.cnf"

-- | main
main :: IO ()
main = do opts <- miosParseOptionsFromArgs versionId
          if | _displayVersion opts        -> putStrLn (versionId ++ gitId)
             | _displayHelp opts           -> putStrLn usage
             | _targetFile opts == Nothing -> putStrLn usage
             | _validateAssignment opts    -> executeValidator opts
             | otherwise                   -> executeSolver opts

