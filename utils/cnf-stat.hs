-- | Prints
--   - the CNF filename,
--   - the number of literals /n/,
--   - the number of clauses /m/,
--   - the number of literal occurences in the file /o/,
--   - the average number of literals in a clause /k/
{-# LANGUAGE
    MultiWayIf
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
import System.IO

-- version id
vid :: String
vid = "cnf-stats version 0.2"

usage :: String
usage = miosUsage $ vid ++ "\n" ++ "Usage: cnf-stats cnf+"

-- | main
main :: IO ()
main = do opts <- miosParseOptionsFromArgs vid
          if | _displayVersion opts -> putStrLn vid
             | _displayHelp opts    -> putStrLn usage
             | null (_targets opts) -> putStrLn usage
             | otherwise            -> mapM_ (countLiterals opts) (_targets opts)

countLiterals :: MiosProgramOption -> FilePath -> IO ()
countLiterals opts cnfFile = do
  (desc, cls) <- parseCNF (Just cnfFile)
  let n = _numberOfVariables desc
  let m = _numberOfClauses desc
  when (n /= 0) $ do
    let o = length . filter ("0" /=) . words $ B.unpack cls
    putStrLn $ intercalate ","
      [ cnfFile
      , show n
      , show m
      , show o
      , showf $ fromIntegral o / fromIntegral m
      ]

showf :: Double -> String
showf x = showFFloat (Just 2) x ""
