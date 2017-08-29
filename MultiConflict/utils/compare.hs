{-# LANGUAGE ViewPatterns #-}
-- | Usage:
-- > mios-summary < average.csv > summary.tbl (for org-mode or github-flavored markdown)
module Main where

import Data.List (intercalate, lookup, nub)
import Data.Maybe (fromMaybe)
import Numeric (showFFloat)
import SAT.Mios.Types
import SAT.Mios.Util.Stat

showf :: Double -> String
showf x = showFFloat (Just 2) x ""

showl :: Either Double Int -> String
showl (Left x) = showf x
showl (Right x) = showf (fromIntegral x)

headerHead :: (String, String)
headerHead = ( "|   n |   p1 |   p2 |   p3|   p4 |"
             , "| --- | ---- | ---- | ---- | ---- |")
headerData :: (String, String)
headerData = ( " STR | backjump |  res |  propagation |   learnt | rate | pr/bj |"
             , " --- | -------- | ---- |  ----------- | -------- | ---- | ----- |")

main :: IO ()
main = do
  l <- parseBy [(fst (header :: (String, MergedDump)), fromMergedCSV)] <$> getContents
  let nst = length . nub . map toStrategy $ l
  putStrLn "#-*-mode:org-*-\n"
  putStrLn . (fst headerHead ++) . concat . take nst . repeat . fst $ headerData
  putStrLn . (snd headerHead ++) . concat . take nst . repeat . snd $ headerData
  mapM_ putStrLn $ toColumns l

type Key = (Int, Double, Int, Bool, Double, Double, Int, Int)

showKey :: Key -> String
showKey (n, _, _, _, p1, p2, p3, p4) = intercalate " | " [show n, showf p1, showf p2, show p3, show p4]

toKey :: MergedDump -> Key
toKey (MergedDump (_, (MiosConfiguration vd pl dp _ p1 p2 p3 p4)) n _ _) = (n, vd, pl, dp, p1, p2, p3, p4)

toStrategy :: MergedDump -> MultipleLearning
toStrategy (_mergedConf -> snd -> (MiosConfiguration _ _ _ st _ _ _ _)) = st

toColumns ::[MergedDump] -> [String]
toColumns l = map gather . nub $ map toKey l
  where gather :: Key -> String
        gather k = (\s -> "| " ++ s ++ " |") .  intercalate " | " $ showKey k : map toSummary (filter ((k ==) . toKey) l)

toSummary :: MergedDump -> String
toSummary (MergedDump (_, (MiosConfiguration _ _ _ s1 _ _ _ _)) _ (MiosStats l) _) = intercalate " | " [m', s', showf pr]
  where
    m' = intercalate " | " [show s1]
    s' = intercalate " | " $ map (showl . snd) (tail . init $ l)
    pr = fromMaybe 0 $ (\(Left a) (Left b) -> a / b) <$> lookup PropagationS l <*> lookup BackjumpS l
