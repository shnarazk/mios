{-# LANGUAGE Safe #-}

-- | Read a CNF file without haskell-platform
module SAT.Util.CNFIO.Reader
       (
         -- * Interface
         fromFile
       , clauseListFromFile
       )
       where
import Control.Applicative ((<$>), (<*>), (<*), (*>))
import Data.Char
import Text.ParserCombinators.ReadP

-- parser
{-# INLINE newline #-}
newline = char '\n'

{-# INLINE digit #-}
digit = satisfy isDigit

{-# INLINE spaces #-}
spaces = munch (`elem` " \t")

{-# INLINE noneOf #-}
noneOf s = satisfy (`notElem` s)

-- |parse a non-signed integer
{-# INLINE pint #-}
pint = do
  n <- munch isDigit
  return (read n :: Int)

{-# INLINE mint #-}
mint = do
  char '-'
  n <- munch isDigit
  return (- (read n::Int))

-- |parse a (signed) integer
{-# INLINE int #-}
int = mint <++ pint

-- |Parse something like: p FORMAT VARIABLES CLAUSES
{-# INLINE problemLine #-}
problemLine = do
  char 'p'
  skipSpaces
  (string "cnf" <++ string "CNF")
  skipSpaces
  vars <- pint
  skipSpaces
  clas <- pint
  spaces
  newline
  return (vars, clas)

-- |Parse something like: c This in an example of a comment line.
{-# INLINE commentLines #-}
commentLines = do
  l <- look
  if (head l)  == 'c'
    then do
      munch ('\n' /=)
      newline
      commentLines
    else return ()

_commentLines = do
  char 'c'
  munch ('\n' /=)
  newline
  l <- look
  if (head l)  == 'c' then commentLines else return ()

-- |Parse the preamble part
{-# INLINE preambleCNF #-}
preambleCNF = do
  commentLines
  problemLine

-- |return integer list that terminates at zero
{-# INLINE seqNums #-}
seqNums = do
  skipSpaces
  x <- int
  skipSpaces
  if (x == 0) then return []  else (x :) <$> seqNums

-- |Parse something like: 1 -2 0 4 0 -3 0
{-# INLINE parseClauses #-}
parseClauses :: Int -> ReadP [[Int]]
parseClauses n = count n seqNums

-- |top level interface for parsing CNF
{-# INLINE parseCNF #-}
parseCNF :: ReadP ((Int, Int), [[Int]])
parseCNF = do
  a <- preambleCNF
  b <- parseClauses (snd a)
  return (a, b)

-- |driver:: String -> Either ParseError Int
driver input = readP_to_S (parseClauses 1) input

-- |read a CNF file and return:
-- ((numbefOfVariables, numberOfClauses), [Literal])
--
-- >>> fromFile "acnf"
-- ((3, 4), [[1, 2], [-2, 3], [-1, 2, -3], [3]]
--
{-# INLINE fromFile #-}
fromFile :: FilePath -> IO (Maybe ((Int, Int), [[Int]]))
fromFile f = do
  c <- readFile f
  case readP_to_S parseCNF c of
    [(a, _)] -> return $ Just a
    _ -> return Nothing

-- | return clauses as [[Int]] from 'file'
--
-- >>> clauseListFromFile "a.cnf"
-- [[1, 2], [-2, 3], [-1, 2, -3], [3]]
--
clauseListFromFile :: FilePath -> IO [[Int]]
clauseListFromFile l = do
  res <- fromFile l
  case res of
    Just (_, l) -> return l
    _ -> return []
