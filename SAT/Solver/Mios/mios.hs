-- | MINISAT Implementation On Sih4 (mios)
module Main
       (
         main
       )
       where

import SAT.Solver.Mios

-- | main
main :: IO ()
main = do
  opts <- miosParseOptionsFromArgs idString
  case () of
    _ | _displayVersion opts -> putStrLn idString
    _ | _displayHelp opts    -> putStrLn $ miosUsage $ idString ++ "\nUsage: mios [OPTIONS] target.cnf"
    _ | otherwise            -> runSolverWithOption opts $ _targetFile opts

