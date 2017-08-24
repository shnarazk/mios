{-# LANGUAGE
    RecordWildCards
  , TupleSections
#-}
{-# LANGUAGE Safe #-}

module SAT.Mios.Util.Stat
  ( Dumpable (..)
  , MiosDump (..)
  , MergedDump (..)
  , merge
  , parseBy
  , fromDump
  , fromStat
  , fromCSV
  , fromMergedCSV
  , toMerge
  )
where

import Data.Bits
import qualified Data.IORef as IORef
import Data.List
import Numeric (showFFloat)
import Text.ParserCombinators.ReadP
import SAT.Mios.Types ( MiosConfiguration(..)
                      , CNFDescription(..)
                      , DumpTag(..)
                      , MiosStats(..)
                      , QuadLearntC(..)
                      , MiosDump(..)
                      )

logBase2 :: Int -> Int
logBase2 x
  | x <= 0 = 0
  | otherwise =finiteBitSize x - 1 - countLeadingZeros x

showf :: Double -> String
showf x = showFFloat (Just 2) x ""

(+.) :: Either Double Int -> Either Double Int -> Either Double Int
(Right x) +. (Right y) = Right (x + y)
(Right x) +. (Left y) = Left (fromIntegral x + y)
(Left x) +. (Right y) = Left (x + fromIntegral y)
(Left x) +. (Left y) = Left (x + y)

(/.) :: Either Double Int -> Int -> Either Double Int
_ /. 0 = Left 0
(Right x) /. n = Left $ fromIntegral x / fromIntegral n
(Left x) /. n = Left $ x / fromIntegral n

class Monoid s => Dumpable s where
  -- higher level functions over Monoid methods
  divideBy :: Int -> s -> s
  divideBy _ _ = mempty
  average :: [s] -> s
  average l = divideBy (length l) (mconcat l)
  unaccumulate :: s -> s
  unaccumulate l = error "default method of unaccumulate"
  --
  header :: (String, s)
  header = ("undefined", mempty)
  toCSV :: s -> String
  toCSV _ = "undefined:"
  {-# MINIMAL #-}

instance Monoid CNFDescription where
  mempty = CNFDescription (Just "") 0 0
  mappend _ _ = mempty
  mconcat _ = mempty

instance Dumpable CNFDescription where
  header = ("file, nvar, nclause", mempty)
  toCSV (CNFDescription (Just f) v c) = intercalate "," [show f, show v, show c]
  toCSV (CNFDescription Nothing v c) = intercalate "," ["", show v, show c]

instance Monoid MiosConfiguration where
  mempty = MiosConfiguration 0 0 0 0 0 0
  mappend a b
    | a == b = a
    | otherwise = error "invalid configurations to mappend"
  mconcat [] = error "invalid configurations to sconcat"
  mconcat (a:l)
    | all (a ==) l = a
    | otherwise = error "invalid configurations to mconcat"

instance Dumpable MiosConfiguration where
  header = (intercalate "," ["vDecay", "propLim", "par1", "par2", "par3", "par4"], mempty)
  toCSV MiosConfiguration{..} =
    intercalate "," [ show variableDecayRate
                    , show (logBase2 propagationLimit)
                    , showf gpParameter1
                    , showf gpParameter2
                    , show extraParameter3
                    , show extraParameter4]
  average = mconcat

instance Monoid MiosStats where
  mempty = MiosStats $ map (, Right 0) [minBound :: DumpTag .. maxBound]
  mappend (MiosStats x) (MiosStats y) = MiosStats $ zipWith add x y
    where
      add (k1, v1) (k2, v2)
        | k1 == k2 = (k1, v1 +. v2)
        | otherwise = error "unbalanced stats"

instance Dumpable MiosStats where
  header = ( intercalate "," $ map toHeader [minBound :: DumpTag .. maxBound]
           , mempty
           )
    where
      toHeader TerminateS = "result"
      toHeader BackjumpS = "backjump"
      toHeader RestartS = "restart"
      toHeader PropagationS = "propagation"
      toHeader ConflictS = "conflict"
      toHeader LearntS = "learnt"
      toHeader LearningRateS = "lRate"
      toHeader ExtraS = "extra"
  toCSV (MiosStats l) = intercalate "," $ map val [minBound :: DumpTag .. maxBound]
    where
      val k = case lookup k l of
                Just (Right v) -> show v
                Just (Left v) -> showf v
                Nothing -> "0"
  divideBy n (MiosStats x) = MiosStats $ map (\(k,v) -> (k, v /. n)) x

instance Monoid QuadLearntC where
  mempty = QuadLearntC (0, 0, 0) (0, 0, 0) (0, 0, 0) (0, 0, 0)
  mappend (QuadLearntC a1 b1 c1 d1) (QuadLearntC a2 b2 c2 d2)  = QuadLearntC (a1 +.+ a2) (b1 +.+ b2) (c1 +.+ c2) (d1 +.+ d2)
    where (a1, a2, a3) +.+ (b1, b2, b3) = (a1 + b1, a2 + b2, a3 + b3)

instance Dumpable QuadLearntC where
  header = ("bl0,bl1,bl2,blx,ll0,ll1,ll2,llx,sl0,sl1,sl2,slx", mempty)
  toCSV (QuadLearntC (b0, l0, s0) (b1, l1, s1) (b2, l2, s2) (b3, l3, s3)) = intercalate "," $ map showf [b0, b1, b2, b3, l0, l1, l2, l3, s0, s1, s2, s3]
  divideBy n (QuadLearntC a b c d) = QuadLearntC (a /./ n') (b /./ n') (c /./ n') (d /./ n')
    where
      n' = fromIntegral n
      (a1, a2, a3) /./ n = (a1 / n, a2 / n, a3 / n)

instance Monoid MiosDump where
  mempty = MiosDump ("solver", mempty) mempty mempty mempty
  mappend _ _ = error "MiosDump is not allowed to mappend; convert to MergedDump"

instance Dumpable MiosDump where
  header = ( intercalate "," [ "solver"
                               , fst (header :: (String, MiosConfiguration))
                               , fst (header :: (String, CNFDescription))
                               , fst (header :: (String, MiosStats))
                               , fst (header :: (String, QuadLearntC))
                               ]
             , mempty
             )
  toCSV (MiosDump (i, m) d s q) = intercalate "," [show i, toCSV m, toCSV d, toCSV s, toCSV q]
  average _ = error "MiosDump is not alloved to average; convert to MergedDump"
  divideBy _ _ = error "MiosDump is not alloved to divideBy; convert to MergedDump"

data MergedDump =
  MergedDump { _mergedConf :: (String, MiosConfiguration) -- solver configuration = key
              , _merged :: Int                             -- number of problems
              , _mergedStat :: MiosStats
              , _mergedLCat :: QuadLearntC
              }
  deriving (Eq, Ord, Read)

instance Monoid MergedDump where
  mempty = MergedDump ("", mempty) 0 mempty mempty
  mappend (MergedDump m n s l) (MergedDump m' n' s' l')
    | m == m' = MergedDump m (n + n') (mappend s s') (mappend l l')
    | otherwise = error "invalid mergeddumps to mappend"
  mconcat [] = mempty
  mconcat (a:l) = foldl mappend a l

instance Dumpable MergedDump where
  header = (intercalate "," ["solver"
                              , fst (header :: (String, MiosConfiguration))
                              , "problem"
                              , fst (header :: (String, MiosStats))
                              , fst (header :: (String, QuadLearntC))
                              ]
             , mempty
             )
  toCSV (MergedDump (i, m) n s q) = intercalate "," [show i, toCSV m, show n, toCSV s, toCSV q]
  divideBy n (MergedDump (i, m) k s q) = MergedDump (i, m) k (divideBy n s) (divideBy n q)
  unaccumulate d = divideBy (_merged d) d

toMerge :: MiosDump -> MergedDump
toMerge (MiosDump m _ s c) = MergedDump m 1 s c

merge :: [MiosDump] -> IO [MergedDump]
merge l = do
  let aborted ::MiosDump -> Bool
      aborted (MiosDump _ _ (MiosStats vals) _)
        | Just (Right 0) <- lookup TerminateS vals = True
        | Nothing <- lookup TerminateS vals = True
        | otherwise = False
      inject :: [((String, MiosConfiguration), IORef.IORef MergedDump)] -> [MiosDump] -> IO [MergedDump]
      inject h [] = map unaccumulate <$> mapM (IORef.readIORef . snd) h
      inject h (d:ds)
        | aborted d = inject h ds
        | Just x <- lookup k h = do
            IORef.modifyIORef x (mappend (toMerge d))
            inject h ds
        | otherwise = do
            n <- (k ,) <$> IORef.newIORef (toMerge d)
            inject (n : h) ds
        where k = _dumpedConf d
  inject [] l

-- |
parseBy :: [(String, ReadP s)] -> String -> [s]
parseBy fs l'
  | null l = []
  | Just (h, f) <- find ((head l ==) . fst) fs = map (fst. head . readP_to_S f) $ filter (h /=) (tail l)
  | Just (_, f) <- find (("" ==) . fst) fs     = map (fst. head . readP_to_S f) l
  | otherwise = error $ "ABORT\nheader: \n" ++ (head l) ++ "\nis not matches to\n" ++ intercalate "\n" (map fst fs)
  where
    l = filter (('#' /=) . head) $ lines l'

-- | read a token separated by commas
getToken :: String -> ReadP String
getToken s = string s *> skipSpaces *> (munch (',' /=) +++ look)

-- | read a string separated by commas
getQuote :: String -> ReadP String
getQuote s = string s *> skipSpaces *> string "\"" *> munch ('\"' /=) <* string "\""

fromDump :: ReadP MiosDump
fromDump = read <$> munch ('\n' /=)

fromStat :: ReadP MiosDump
fromStat = do
  so <- getQuote "Solver:"
  va <- getToken ", VarDecayRate:"
  pr <- getToken ", PropagationLimit:"
  fl <- getQuote ", File:"
  nv <- getToken ", NumOfVariables:"
  nc <- getToken ", NumOfClauses:"
  sa <- getToken ", SatisfiabilityValue:"
  np <- getToken ", NumOfPropagations:"
  cf <- getToken ", NumOfConflicts:"
  nl <- getToken ", NumOfLearnts:"
  nb <- getToken ", NumOfBackjumps:"
  nr <- getToken ", NumOfRestarts:"
  l1 <- getToken ", NumOfBirthLevel1:"
  l2 <- getToken ", NumOfBirthLevel2:"
  l3 <- getToken ", NumOfBirthLevelX:"
  let  nl' = read nl
       n1' = read l1
       n2' = read l2
       n3' = read l3
       di :: Double -> Double
       di n = if nl' == 0 then 0 else n / nl'
  return $
    MiosDump
      (so, MiosConfiguration (read va) (read pr) 0 0 0 0)
      (CNFDescription (Just fl) (read nv) (read nc))
      (MiosStats (sort
                  [ (TerminateS, Right (read sa)), (BackjumpS, Right (read nb)), (RestartS, Right (read nr))
                  , (PropagationS, Right (read np)), (ConflictS, Right (read cf)), (LearntS, Right (read nl))
                  , (LearningRateS, Left (read nl / read nb)), (ExtraS, Left 0)
                  ]))
      (QuadLearntC (di (nl' - n1' - n2' - n3'), 0, 0) (di n1', 0, 0) (di n2', 0, 0) (di n3', 0, 0))

fromCSV :: ReadP MiosDump
fromCSV = do
  so <- getQuote ""  -- solver
  vd <- getToken "," -- vardecayrace
  pl <- getToken "," -- propagationlimit
  p1 <- getToken "," -- parameter1
  p2 <- getToken "," -- parameter2
  p3 <- getToken "," -- parameter3
  p4 <- getToken "," -- parameter4
  fl <- getQuote "," -- file
  nv <- getToken "," -- nvar
  nc <- getToken "," -- nclause
  sa <- getToken "," -- satisfiability
  np <- getToken "," -- npropagation
  cf <- getToken "," -- nconflicts
  nl <- getToken "," -- nlearning
  nb <- getToken "," -- nbackjump
  nr <- getToken "," -- nrestart
  la <- getToken "," -- learningrate
  ev <- getToken "," -- extravalue
  b0 <- getToken "," -- born level 0
  b1 <- getToken "," -- born level 1
  b2 <- getToken "," -- born level 2
  b3 <- getToken "," -- born level +
  l0 <- getToken "," -- living level 0
  l1 <- getToken "," -- living level 1
  l2 <- getToken "," -- living level 2
  l3 <- getToken "," -- living level +
  s0 <- getToken "," -- suvive level 0
  s1 <- getToken "," -- suvive level 1
  s2 <- getToken "," -- suvive level 2
  s3 <- getToken "," -- suvive level +
  return $
    MiosDump
        (so, MiosConfiguration (read vd) (2 ^ ((read pl) :: Int)) (read p1) (read p2) (read p3) (read p4))
        (CNFDescription (Just fl) (read nv) (read nc))
        (MiosStats (sort
                    [ (TerminateS, Right (read sa))
                    , (PropagationS, Right (read np)), (ConflictS, Right (read cf)), (LearntS, Right (read nl))
                    , (BackjumpS, Right (read nb)), (RestartS, Right (read nr))
                    , (LearningRateS, Left (read la)), (ExtraS, Left (read ev))
                    ]))
        (QuadLearntC (read b0, read l0, read s0) (read b1, read l1, read s1) (read b2, read l2, read s2) (read b3, read l3, read s3))

fromMergedCSV :: ReadP MergedDump
fromMergedCSV = do
  so <- getQuote ""  -- solver
  vd <- getToken "," -- vardecayrace
  pl <- getToken "," -- propagationlimit
  p1 <- getToken "," -- parameter1
  p2 <- getToken "," -- parameter2
  p3 <- getToken "," -- parameter3
  p4 <- getToken "," -- parameter4
  nn <- getToken "," -- problem
  rs <- getToken "," -- result
  np <- getToken "," -- propagation
  cf <- getToken "," -- conflict
  nl <- getToken "," -- learning
  nb <- getToken "," -- backjump
  nr <- getToken "," -- restart
  la <- getToken "," -- learningrate
  ev <- getToken "," -- extravalue
  b0 <- getToken "," -- birth level 0
  b1 <- getToken "," -- birth level 1
  b2 <- getToken "," -- birth level 2
  b3 <- getToken "," -- birth level +
  d0 <- getToken "," -- dead level 0
  d1 <- getToken "," -- dead level 1
  d2 <- getToken "," -- dead level 2
  d3 <- getToken "," -- dead level +
  e0 <- getToken "," -- survive level 0
  e1 <- getToken "," -- survive level 1
  e2 <- getToken "," -- survive level 2
  e3 <- getToken "," -- survive level +
  return $
    MergedDump
        (so, MiosConfiguration (read vd) (2 ^ ((read pl) :: Int)) (read p1) (read p2) (read p3) (read p4))
        (read nn)
        (MiosStats (sort
                    [ (TerminateS, Right (read rs))
                    , (PropagationS, Left (read np)), (ConflictS, Left (read cf)), (LearntS, Left (read nl))
                    , (BackjumpS, Left (read nb)), (RestartS, Left (read nr))
                    , (LearningRateS, Left (read la)), (ExtraS, Left (read ev))
                    ]))
        (QuadLearntC
          (read b0, read d0, read e0)
          (read b1, read d1, read e1)
          (read b2, read d2, read e2)
          (read b3, read d3, read e3)
        )
