-- | Executable of 'Minisat Implementation and Optimization Study'
module Main
       (
         main
       )
       where

import SAT.Solver.Mios

-- | main
main :: IO ()
main = do
  opts <- miosParseOptionsFromArgs versionId
  case () of
    _ | _displayVersion opts        -> putStrLn versionId
    _ | _displayHelp opts           -> putStrLn $ miosUsage $ versionId ++ "\nUsage: mios [OPTIONS] target.cnf"
    _ | _targetFile opts == Just "" -> putStrLn $ miosUsage $ versionId ++ "\nUsage: mios [OPTIONS] target.cnf"
    _ | _validateAssignment opts    -> runValidator opts
    _ | otherwise                   -> runSolver opts

