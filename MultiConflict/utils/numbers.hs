-- | Usage:
-- > mios-summary < average.csv > summary.tbl (for org-mode or github-flavored markdown)
{-# LANGUAGE ViewPatterns #-}
module Main where

import Data.List (intercalate, lookup, minimumBy, nub)
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Numeric (showFFloat)
import System.Console.GetOpt (ArgDescr(..), ArgOrder(..), getOpt, OptDescr(..), usageInfo)
import System.Environment (getArgs)
import SAT.Mios.Types
import SAT.Mios.Util.Stat

data Opt = Opt
  {
    threshold :: Double
  , p1 :: (Double, Double)
  , p2 :: (Double, Double)
  , p3 :: (Int, Int)
  , p4 :: (Int, Int)
  , message :: String
  , help :: Bool
  }

optDefault :: Opt
optDefault = Opt 0 (0, 10) (0, 10) (0, 10) (0, 10) "#-*-mode:org-*-" False

options ::[OptDescr (Opt -> Opt)]
options =
  [
    Option ['t'] ["threshold"]
    (ReqArg (\v c -> c { threshold = read v }) "0.0") "threshold for p1"
  , Option [] ["UF250"]
    (NoArg (\c -> c { threshold = 12109075.01 })) "threshold for UF250; 12109075.01 (7.083)"
  , Option [] ["38bits"]
    (NoArg (\c -> c { threshold = 191761341.00 })) "threshold for 38bits; 191761341.00 (8.283)"
  , Option [] ["44bits"]
    (NoArg (\c -> c { threshold = 5204447789.00 })) "threshold for 44bits; 5204447789.00 (9.716)"
  , Option ['1'] ["p1"]
    (ReqArg (\v c -> c { p1 = read v }) "\"(0,10)\"") "range of p1"
  , Option ['2'] ["p2"]
    (ReqArg (\v c -> c { p2 = read v }) "\"(0,10)\"") "range of p2"
  , Option ['3'] ["p3"]
    (ReqArg (\v c -> c { p3 = read v }) "\"(0,10)\"") "range of p3"
  , Option ['4'] ["p4"]
    (ReqArg (\v c -> c { p4 = read v }) "\"(0,10)\"") "range of p4"
  , Option ['m'] ["message"]
    (ReqArg (\v c -> c { message = undecodeNewline v }) "\"\"") "extra message embeded into output"
  , Option ['h'] ["help"]
    (NoArg (\c -> c { help = True })) "display help message"
  ]

parseOptions :: String -> [String] -> IO Opt
parseOptions mes argv =
    case getOpt Permute options argv of
      (o,  [], []) -> return $ foldl (flip id) optDefault o
      (o,   _, []) -> return $ foldl (flip id) optDefault o
      (_,   _, err) -> ioError (userError (concat err ++ usageInfo mes options))

-- | builds "MiosProgramOption" from a String
parseOptionsFromArgs :: String -> IO Opt
parseOptionsFromArgs mes = parseOptions mes =<< getArgs

undecodeNewline :: String -> String
undecodeNewline [] = []
undecodeNewline [a] = [a]
undecodeNewline ('\\' : 'n' : x) = '\n' : undecodeNewline x
undecodeNewline (a : x) = a : undecodeNewline x

showf :: Double -> String
showf x = showFFloat (Just 2) x ""

main :: IO ()
main = do
  opts <- parseOptionsFromArgs "gp-summary"
  if help opts
    then putStrLn $ usageInfo "" options
    else do putStrLn $ message opts
            putStrLn ""
            putStrLn "| p1   | good | bad |"
            putStrLn "| ---- | ---- | --- |"
            result <- pickup opts . parseBy [(fst (header :: (String, MergedDump)), fromMergedCSV)] <$> getContents
            mapM_ (putStrLn . toString) result
            let ngs = sum $ map (fst . snd) result
                nbs = sum $ map (snd . snd) result
            putStrLn $ intercalate "," [showf (fromIntegral ngs / fromIntegral (ngs + nbs)), show (ngs + nbs) ++ "/" ++ show (ngs, nbs)]

toString :: (Double, (Int, Int))  -> String
toString (p1, (ng, nb)) = "| " ++ intercalate " | " [showf p1, show ng, show nb] ++ " |"

pickup :: Opt -> [MergedDump] -> [(Double, (Int, Int))]
pickup opts l = filter notEmpty $ map gather keys
  where
    notEmpty (_, (0, 0)) = False
    notEmpty _ = True
    thr = threshold opts
    keys = nub $ map (gpParameter1 .  snd. _mergedConf) l
    gather :: Double -> (Double, (Int, Int))
    gather key = (key, (ng, length targets - ng))
      where
        targets' :: [MergedDump]
        targets' = filter ((key ==) . gpParameter1 .  snd. _mergedConf) l
        inBand :: MergedDump -> Bool
        inBand (_mergedConf -> snd -> conf) = c1 && c2 && c3 && c4
          where
            c1 = inPair (p1 opts) (gpParameter1 conf)
            c2 = inPair (p2 opts) (gpParameter2 conf)
            c3 = inPair (p3 opts) (extraParameter3 conf)
            c4 = inPair (p4 opts) (extraParameter4 conf)
            inPair :: (Num a, Ord a) => (a, a) -> a -> Bool
            inPair (b, t) x = b <= x && x <= t
        targets = filter inBand targets'
        ng = length $ filter (< thr) (map value targets)
    value :: MergedDump -> Double
    value m = case lookup PropagationS . (\(MiosStats s) -> s) . _mergedStat $ m of
      Just (Right v) -> fromIntegral v
      Just (Left v)  -> v
      Nothing        -> 10000000
