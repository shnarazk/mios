{-# LANGUAGE TupleSections #-}

module Main where

import Control.Arrow
import Control.Monad
import Data.Maybe
import Criterion.Main
import SAT.Solver.Mios

targets =
  [
    "test/data/uf200-012.cnf"
--  , "test/data/uf225-025.cnf"
--  , "test/data/uf250-050.cnf"
  ]

main = do
  cnfs <- catMaybes . map (uncurry ((<$>) . (,))) <$> mapM (uncurry ((<$>) . (,)) . (id &&& cnfFromFile . Just)) targets
  defaultMain [ bench name $ nfIO (solveSAT cnf) | (name, cnf) <- cnfs ]
