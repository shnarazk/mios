module Main where

import Criterion.Main
import SAT.Solver.Mios

targets =
  [
    "test/data/uf200-012.cnf"
  , "test/data/uf225-025.cnf"
  , "test/data/uf250-050.cnf"
  , "test/data/38bits_10.dimacs.cnf"
  ]

conf :: FilePath -> MiosConfigurationOption
conf path = miosDefaultOption { _targetFile = Just path, _confNoAnswer = True }

basename :: String -> String
basename = reverse . takeWhile ('/' ==) . reverse

main :: IO ()
main = defaultMain [ bench (basename name) . nfIO . runSolver . conf $ name | name <- targets ]


