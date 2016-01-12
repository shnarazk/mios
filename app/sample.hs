module Main
       (
         main
       )
       where

import qualified Data.Vector.Unboxed as U -- used for representing clauses
import SAT.Solver.Mios (CNFDescription (..), solveSAT)

-- | a sample CNF
clauses :: [[Int]]
clauses =
  [
    [ 1,  2]
  , [ 1,  3]
  , [-1, -2]
  , [1, -2, 3]
  , [-3]
  ]

-- | a property holder
desc :: CNFDescription
desc = CNFDescription		-- :: Int -> Int -> Maybe String -> CNFDescription
       (maximum . map abs . concat $ clauses) -- number of variables
       (length clauses)                       -- number of clauses
       Nothing                                -- Just pathname or Nothing

main :: IO ()
main = do
  -- the 0th element of a clause vector is the number of literals in it
  let clausesWithSize = map (\l -> length l : l) clauses
  -- solveSAT :: (CNFDescription, [U.Vector Int]) -> IO [Int]
  asg <- solveSAT (desc, map U.fromList clausesWithSize)
  putStrLn $ if null asg then "unsatisfiable" else show asg
