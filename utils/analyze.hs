-- | USAGE: mios-49 -X --dump-clauses='' a.cnf | runhaskell analyze.hs -k '"a.cnf"'
module Main where
import Data.List
import Data.Maybe (fromMaybe)
import System.Console.GetOpt (ArgDescr(..), ArgOrder(..), getOpt, OptDescr(..), usageInfo)
import System.Environment (getArgs)

main :: IO ()
main = do
  opts <- parseOptions "analyze biclause" defaultParams =<< getArgs
  (cs, ls) <- case input opts of
                     Nothing -> read <$> getContents :: IO ([[Int]], [[Int]])
                     Just f  -> read <$> readFile f  :: IO ([[Int]], [[Int]])
  let f = fromMaybe (keyword opts) (input opts)
  let bs = filter ((2 ==) . length) ls
      cs' = analyze cs bs
      ls' = analyze ls bs
  putStrLn $ intercalate ","
    [ f
    , show (length bs)
    , show (length cs)
    , show (length cs')
    , show (length ls)
    , show (length ls')
    ]

analyze :: [[Int]] -> [[Int]] -> [[Int]]
analyze l [] = l
analyze l ([a,b]:x') = analyze l' x'
  where l' = filter (\cls -> notElem a cls && notElem b cls) l

data Params = Params
  {
    keyword :: String
  , input   :: Maybe String
  , _help   :: Bool
  }

defaultParams :: Params
defaultParams = Params "" Nothing False

options :: [OptDescr (Params -> Params)]
options =
  [
    Option ['k'] ["keyword"]
    (ReqArg (\v c -> c { keyword = v }) "")
    "server's address"
  , Option ['i'] ["input"]
    (ReqArg (\v c -> c { input = read v }) "")
    "server's port number"
  , Option ['h', '?'] ["help"]
    (NoArg (\c -> c { _help = True}))
    "print this help message"
  ]

parseOptions :: String -> Params -> [String] -> IO Params
parseOptions mes params argv =
    case getOpt Permute options argv of
      (o, _, []) -> do let ps = foldl (flip id) params o
                       if _help ps
                         then errorWithoutStackTrace $ usageInfo mes options
                         else return ps
      (_, _, errs) -> ioError (userError (concat errs ++ usageInfo mes options))
