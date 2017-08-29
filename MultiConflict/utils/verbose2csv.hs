-- | Usage: by running as `runhaskell verbose2csv.hs < a.log > a.csv`
-- | convert a log with the following format:
--   > ## [  uf100-01.cnf] NumOfBackjump: 156, NumOfRestart: 1, NumOfPropagation: 16067
--   to csv with the following format;
--   > 1, uf100-01.cnf, 156, 1, 16067
--   with the header:
--   > num, problem, nbackjump, nrestart, npropagation
module Main where

import Data.List
import Text.ParserCombinators.ReadP

main :: IO ()
main = interact (merge . map f . lines)
  where
    header = "num, problem, nbackjump, nrestart, npropagation\n"
    merge :: [String] -> String
    merge l = header ++ concat (zipWith (\i s -> show i ++ ", " ++ s ++ "\n") [1 :: Int ..] l)

f :: String -> String
f s = intercalate ", " x
  where
    x = fst . head $ readP_to_S parse s

parse :: ReadP [String]
parse = do
  fn <- string "## [ " *> skipSpaces *> munch (']' /=)
  nb <- string "] NumOfBackjump: " *> munch (',' /=)
  nr <- string ", NumOfRestart: " *> munch (',' /=)
  np <- string ", NumOfPropagation: " *> munch ('\n' /=)
  return [fn, nb, nr, np]

