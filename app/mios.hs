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

import Development.GitRev
import SAT.Mios

gitId :: String
gitId = versionId ++ "/commit/" ++ $(gitHash)

usage :: String
usage = miosUsage $ gitId ++ "\nUsage: mios [OPTIONS] target.cnf"

-- | main
main :: IO ()
main = do opts <- miosParseOptionsFromArgs versionId
          if | _displayVersion opts        -> putStrLn gitId
             | _displayHelp opts           -> putStrLn usage
             | _targetFile opts == Nothing -> putStrLn usage
             | _validateAssignment opts    -> executeValidator opts
             | otherwise                   -> executeSolver opts
