-- | Prints
--   - the CNF filename,
--   - the number of literals /n/,
--   - the number of clauses /m/,
--   - the number of literal occurences in the file /o/,
--   - the average number of literals in a clause /k/
{-# LANGUAGE
    MultiWayIf
  , ViewPatterns
  #-}
module Main
       (
         main
       )
       where

import Control.Monad (when)
import qualified Data.ByteString.Char8 as B
import Data.List
import Numeric (showFFloat)
import SAT.Mios
import SAT.Mios.Types (getNth, get')
import SAT.Mios.Clause (Clause(..))
import SAT.Mios.ClauseManager (getClauseVector)
import SAT.Mios.Solver (newSolver, Solver(..))

-- version id
vid :: String
vid = "cnf-stats version 0.1"

usage :: String
usage = miosUsage $ vid ++ "\n" ++ "Usage: cnf-stats cnf+"

-- | main
main :: IO ()
main = do opts <- miosParseOptionsFromArgs vid
          if | _displayVersion opts -> putStrLn vid
             | _displayHelp opts    -> putStrLn usage
             | null (_targets opts) -> putStrLn usage
             | otherwise            -> mapM_ (analyzeCNF opts) (_targets opts)

analyzeCNF :: MiosProgramOption -> FilePath -> IO ()
analyzeCNF opts cnfFile = do
  (desc, cls) <- parseCNF (Just cnfFile) <$> B.readFile cnfFile
  let n = _numberOfVariables desc
  when (n /= 0) $ do
    s <- newSolver (toMiosConf opts) desc
    injectClausesFromCNF s desc cls
    vec <- getClauseVector (clauses s)
    m <- get' (clauses s)
    let countLiterals :: Int -> Int -> IO Int
        countLiterals ((< m) -> False) t = return t
        countLiterals i t = countLiterals (i + 1) . (t +) =<< get' =<< getNth vec i
    o <- countLiterals 0 0
    putStrLn $ intercalate ","
      [ cnfFile
      , show n
      , show m
      , show o
      , showf $ fromIntegral o / fromIntegral m
      ]

showf :: Double -> String
showf x = showFFloat (Just 2) x ""
