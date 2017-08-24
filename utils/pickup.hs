-- | Usage:
-- > mios-summary < average.csv > summary.tbl (for org-mode or github-flavored markdown)
module Main where

import Data.List (intercalate, lookup, maximumBy, minimumBy, nub)
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Numeric (showFFloat)
import System.Console.GetOpt (ArgDescr(..), ArgOrder(..), getOpt, OptDescr(..), usageInfo)
import System.Environment (getArgs)
import SAT.Mios.Types
import SAT.Mios.Util.Stat

data Opt = Opt
  {
    message :: String
  , useLog :: Bool
  , help :: Bool
  }

optDefault :: Opt
optDefault = Opt "#-*-mode:org-*-" False False

options ::[OptDescr (Opt -> Opt)]
options =
  [
    Option ['m'] ["message"]
    (ReqArg (\v c -> c { message = undecodeNewline v }) "\"string\"") "extra message embeded into output"
  , Option ['l'] ["useLog"]
    (NoArg (\c -> c { useLog = True })) "use Logarithmic value for propagation"
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

showi :: Int -> String
showi x
  | 3 <= length s = s
  | otherwise = reverse . take 3 . (++ "   ") . reverse $ s
  where s = show x

showl :: Either Double Int -> String
showl (Left x) = showf x
showl (Right x) = showf (fromIntegral x)

main :: IO ()
main = do
  opts <- parseOptionsFromArgs "gp-summary"
  if help opts
    then putStrLn $ usageInfo "" options
    else do let parsers = [ (fst (header :: (String, MiosDump)), toMerge <$> fromCSV)
                          , (fst (header :: (String, MergedDump)), fromMergedCSV)]
            putStrLn $ message opts
            putStrLn ""
            if useLog opts
              then do putStrLn "|   n |   p1 |   p2 |  p3 |  p4 | log(P) | conflict |   learnt | backjump | re-st | rate |  extra | pr/bj |"
                      putStrLn "| --- | ---- | ---- | --- | --- | ------ | -------- | -------- | -------- | ----- | ---- |  ----- | ----- |"
              else do putStrLn "|   n |   p1 |   p2 |  p3 |  p4 | propagation | conflict |   learnt | backjump | re-st | rate |  extra | pr/bj |"
                      putStrLn "| --- | ---- | ---- | --- | --- | ----------- | -------- | -------- | -------- | ----- | ---- |  ----- | ----- |"
            d <- parseBy parsers <$> getContents
            mapM_ (putStrLn . toSummary (useLog opts)) $ pickup True d
            putStrLn ""
            mapM_ (putStrLn . toSummary (useLog opts)) $ pickup False d
            putStrLn ""

toSummary :: Bool -> MergedDump -> String
toSummary uLog (MergedDump (_, MiosConfiguration _ _ p1 p2 p3 p4) n (MiosStats l) _) =
  "| " ++ intercalate " | " [show n, m', s', showf pr] ++ " |"
  where
    m' = intercalate " | " [showf p1, showf p2, showi p3, showi p4]
    s' = intercalate " | " $ map (showl . snd) (convert uLog l) -- (tail . init $ l)
    convert :: Bool -> [DumpedValue] -> [DumpedValue]
    convert uL ks
      | uL = logOf PropagationS : map valOf [ConflictS .. ExtraS]
      | otherwise = map valOf [PropagationS .. ExtraS]
      where
        logOf :: DumpTag -> DumpedValue
        logOf key = (key, Left $ logBase 10 (val key))
        valOf key = (key, Left $ val key)
        val :: DumpTag -> Double
        val key
          | Just (Left x) <- lookup key ks = x
          | Just (Right x) <- lookup key ks = fromIntegral x
          | otherwise = 0
    pr = fromMaybe 0 $ div' <$> lookup PropagationS l <*> lookup BackjumpS l
    div' :: Either Double Int -> Either Double Int -> Double
    div' (Right a) (Right b) = fromIntegral a / fromIntegral b
    div' (Right a) (Left b)  = fromIntegral a / b
    div' (Left a) (Right b)  = a / fromIntegral b
    div' (Left a) (Left b)   = a / b

pickup :: Bool -> [MergedDump] -> [MergedDump]
pickup good l = map selectData keys
  where
    keys = nub $ map (gpParameter1 .  snd. _mergedConf) l
    selectData :: Double -> MergedDump
    selectData key
      | good      = minimumBy (comparing value) $ filter ((key ==) . gpParameter1 .  snd. _mergedConf) l
      | otherwise = maximumBy (comparing value) $ filter ((key ==) . gpParameter1 .  snd. _mergedConf) l
    value :: MergedDump -> Double
    value m = case lookup PropagationS . (\(MiosStats s) -> s) . _mergedStat $ m of
      Just (Right v) -> fromIntegral v
      Just (Left v)  -> v
      Nothing        -> 10000000
