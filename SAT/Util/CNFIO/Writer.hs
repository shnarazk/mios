{-# LANGUAGE Safe #-}
-- | Write SAT data to CNF file

module SAT.Util.CNFIO.Writer
       (
         -- * Interface
         toFile
       , toCNFString
       , toString
       , toLatexString
       )
       where
import Data.List (intercalate, nub, sort)
import System.IO

-- | Write the CNF to file 'f', using 'toCNFString'
toFile :: FilePath -> [[Int]] -> IO ()
toFile f l = writeFile f $ toCNFString l

-- | Convert [Clause] to String, where Clause is [Int]
--
-- >>> toCNFString []
-- "p cnf 0 0\n"
--
-- >>> toCNFString [[-1, 2], [-3, -4]]
-- "p cnf 4 2\n-1 2 0\n-3 -4 0\n"
--
-- >>> toCNFString [[1], [-2], [-3, -4], [1,2,3,4]]
-- "p cnf 4 4\n1 0\n-2 0\n-3 -4 0\n1 2 3 4 0\n"
--
toCNFString :: [[Int]] -> String
toCNFString l = hdr ++ str
  where
    hdr = "p cnf " ++ show numV ++ " " ++ show numC ++ "\n"
    numC = length l
    numV = last $ nub $ sort $ map abs $ concat l
    str = concat [intercalate " " (map show c) ++ " 0\n" | c <- l]

toString  :: [[Int]] -> String -> String -> String
toString l and' or' = intercalate a ["(" ++ intercalate o [ lit x | x <- c] ++ ")" | c <- l]
  where
    lit x
      | 0 <= x = "X" ++ show x
      | otherwise = "-X" ++ show (abs x)
    a = pad and'
    o = pad or'
    pad s = " " ++ s ++ " "

toLatexString  :: [[Int]] -> String
toLatexString l = "\\begin{eqnarray*}\n" ++ intercalate a ["(" ++ intercalate o [ lit x | x <- c] ++ ")" | c <- l] ++ "\n\\end{eqnarray*}"
  where
    lit x
      | 0 <= x = "X_{" ++ show x ++ "}"
      | otherwise = "\\overline{X_{" ++ show (abs x) ++ "}}"
    a = " \n\\wedge "
    o = " \\vee "
