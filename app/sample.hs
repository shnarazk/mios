module Main where
import SAT.Mios (CNFDescription (..), solveSAT)

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
desc = CNFDescription           -- :: Int -> Int -> Maybe String -> CNFDescription
       (maximum . map abs . concat $ clauses) -- number of variables
       (length clauses)                       -- number of clauses
       Nothing                                -- Just pathname or Nothing

main :: IO ()
main = do
  -- solveSAT :: Traversable m => CNFDescription -> m [Int] -> IO [Int]
  asg <- solveSAT desc clauses
  putStrLn $ if null asg then "unsatisfiable" else show asg
