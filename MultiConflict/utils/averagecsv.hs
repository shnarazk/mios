-- | Usage:
-- > mios-averagecsv < a.csv > ave.csv
module Main where

import Data.List (sort)
import SAT.Mios.Util.Stat

main :: IO ()
main = do
  putStrLn $ fst (header :: (String, MergedDump))
  d <- parseBy [(fst (header :: (String, MiosDump)), fromCSV)] <$> getContents
  mapM_ (putStrLn . toCSV) . sort =<< merge d

