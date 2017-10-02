{-# LANGUAGE
   MultiWayIf
  #-}
-- | Executable of 'Minisat Implementation and Optimization Study'
module Main
       (
         main
       )
       where

import SAT.Mios

usage :: String
usage = miosUsage $ versionId ++ "\nUsage: mios [OPTIONS] target.cnf"

-- | main
main :: IO ()
main = do opts <- miosParseOptionsFromArgs versionId
          if | _displayVersion opts        -> putStrLn versionId
             | _displayHelp opts           -> putStrLn usage
             | _targetFile opts == Nothing -> putStrLn usage
             | _validateAssignment opts    -> executeValidator opts
             | otherwise                   -> executeSolver opts

