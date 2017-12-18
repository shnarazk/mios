{-# LANGUAGE Safe #-}

-- | Read an output file of minisat
module SAT.Mios.Util.DIMACS.MinisatReader
       (
         -- * Interface
         fromMinisatOutput
       , clauseListFromMinisatOutput
       )
       where
-- import Control.Applicative ((<$>), (<*>), (<*), (*>))
import Data.Char
import Text.ParserCombinators.ReadP

-- parser
-- |parse a non-signed integer
{-# INLINE pint #-}
pint :: ReadP Int
pint = do
  n <- munch isDigit
  return (read n :: Int)

{-# INLINE mint #-}
mint :: ReadP Int
mint = do
  char '-'
  n <- munch isDigit
  return (- (read n::Int))

-- |parse a (signed) integer
{-# INLINE int #-}
int :: ReadP Int
int = mint <++ pint

-- |return integer list that terminates at zero
{-# INLINE seqNums #-}
seqNums :: ReadP [Int]
seqNums = do
  skipSpaces
  x <- int
  skipSpaces
  if x == 0 then return []  else (x :) <$> seqNums

-- |top level interface for parsing CNF
{-# INLINE parseMinisatOutput #-}
parseMinisatOutput :: ReadP ((Int, Int), [Int])
parseMinisatOutput = do
  string "SAT"
  skipSpaces
  l <- seqNums
  return ((length l,0), l)

-- |read a minisat output:
-- ((numbefOfVariables, 0), [Literal])
--
-- >>>  fromFile "result"
-- ((3, 0), [1, -2, 3])
--
{-# INLINE fromMinisatOutput #-}
fromMinisatOutput :: FilePath -> IO (Maybe ((Int, Int), [Int]))
fromMinisatOutput f = do
  c <- readFile f
  case readP_to_S parseMinisatOutput c of
    [(a, _)] -> return $ Just a
    _ -> return Nothing

-- | return clauses as [[Int]] from 'file'
--
-- >>> clauseListFromMinisatOutput "result"
-- [1,-2,3]
--
clauseListFromMinisatOutput :: FilePath -> IO [Int]
clauseListFromMinisatOutput l = do
  res <- fromMinisatOutput l
  case res of
    Just p -> return (snd p)
    _ -> return []
