-- | Usage:
-- > mios --stat -X ... | mios-stat2csv > a.csv
module Main where

import SAT.Mios.Util.Stat

main :: IO ()
main = do
  putStrLn $ fst (header :: (String, MiosDump))
  mapM_ (putStrLn . toCSV) =<< parseBy [("", fromStat)] <$> getContents
