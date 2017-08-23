-- | inject nvar and nclause fields into an old format csv
module Main where

import Control.Monad
import Data.List
import Data.Maybe
import Text.ParserCombinators.ReadP

-- | (filenam, data)
type Info =  (String, (String, String))

type Result =
  ( String                      -- filename
  , (String, String, String)    -- parameters
  , String                      -- number
  , (String, String, String)    -- stats
  )

newHeader :: String
newHeader = "strategy, ncnfl, expand, num, file, nvar, nclause, nbackjump, nrestart, npropagation"

origHeader :: String
origHeader = "solver,strategy, ncnfl, expand, no, file, nvar, nclause, nbackjump, nrestart, npropagation"

toResult :: ReadP Result
toResult = do
  p1 <- munch (',' /=)
  p2 <- getToken
  p3 <- getToken
  no <- getToken
  fn <- getToken
  nb <- getToken
  nr <- getToken
  np <- getToken
  return (canonizeFilename fn, (p1, p2, p3), no, (nb, nr, np))

main :: IO ()
main = do
  s <- parseBy [(origHeader, parse1)] <$> readFile "/home/narazaki/Repositories/B4-themes/2016/Benchmark/stragegy-comparison/SR2015subset1-stats-0.csv"
  d <- parseBy [("", toResult)] <$> getContents
  putStrLn newHeader
  mapM_ putStrLn $ merge d s

merge :: [Result] -> [Info] -> [String]
merge rs is = map shaper rs
  where
    shaper (fn, (p1, p2, p3), no, (s1, s2, s3)) = intercalate ", " [p1, p2, p3, no, fn, nv, nc, s1, s2, s3]
      where
        (nv, nc) = fromMaybe ("-1", "-1") $ snd <$> find ((fn ==) . fst) is

parseBy :: [(String, ReadP s)] -> String -> [s]
parseBy fs l
  | Just (_, f) <- find ((h ==) . fst) fs = map (fst. head . readP_to_S f) ls
  | Just (_, f) <- find (("" ==) . fst) fs = map (fst. head . readP_to_S f) ls
  | otherwise = error $ "no handler for: [" ++ show h ++ "]\n" ++ intercalate "\n" (map fst fs)
  where
    (h : ls) = lines l

getToken :: ReadP String
getToken = string "," *> skipSpaces *> (munch (',' /=) +++ look)

parse1 :: ReadP Info
parse1 = do
  void $ munch (',' /=)
  void getToken
  void getToken
  void getToken
  void getToken
  fn <- getToken
  nv <- getToken
  nc <- getToken
  void getToken
  void getToken
  void getToken
  return (canonizeFilename fn, (nv, nc))

canonizeFilename :: String -> String
canonizeFilename = quote . withDir . unquote
  where
    quote s  = "\"" ++ s ++ "\""
    unquote s
      | head s == '"' && last s == '"' = init $ tail s
      | head s == '"' = error "unbalanced paren"
      | last s == '"' = error "unbalanced paren"
      | otherwise = s
    withDir s = case break ('/' ==) s of
                    (a, []) -> "SR2015subset1/" ++ a
                    ("SR2015subset1", _) -> s
                    (a, _) -> error $ "unknown dir: " ++ a
    removeDir s = case break ('/' ==) s of
                    (a, []) -> a
                    (_, b) -> tail b
      
