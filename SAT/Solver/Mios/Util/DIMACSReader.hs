-- This is a modified version of Laguage.CNF.Parse.ParseDIMACS (parse-dimacs hackage)
-- to use Unboxed Vector instead of UArray
{-

    parse-dimacs is free software: it is released under the BSD3 open source
    license.  You can find details of this license in the file LICENSE at the
    root of the source tree.

    Copyright 2008 Denis Bueno
-}

{-# LANGUAGE
    BangPatterns
  , MagicHash
  , UnboxedTuples
 #-}
{-# LANGUAGE Trustworthy #-}

-- | A simple module for parsing CNF files in DIMACS format.
module SAT.Solver.Mios.Util.DIMACSReader
       (
         -- * Interface
         MaybeCNF
       , cnfFromFile
       , SizedVectorInt
       , CNFDescription (..)
       )
       where

import Control.Monad
import qualified Data.Vector.Unboxed as U
import Data.ByteString.Char8 (ByteString)
import System.IO (hClose, hPutStrLn)
import System.IO.Temp (withSystemTempFile)
import Text.Parsec( ParseError, SourceName )
import Text.Parsec.ByteString
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim( many, try, unexpected, runParser )
import qualified Text.Parsec.Token as T

-- | SizedVectorInt is a vector holding literal :: Int
type SizedVectorInt = U.Vector Int

-- | holder for DIMACS CNF format
data CNFDescription = CNFDescription
  {
    numberOfVariables :: !Int		-- ^ number of variables
  , numberOfClauses :: !Int      	-- ^ number of clauses
  , pathname :: Maybe String           	-- ^ given filename
  }
  deriving (Eq, Ord, Show)

-- | return value of CNF reader
type MaybeCNF = Maybe (CNFDescription, [SizedVectorInt])

-- | top-level function to read a CNF file
cnfFromFile :: Maybe FilePath -> IO MaybeCNF
cnfFromFile f = do
  res <- parseFile f
  case res of
    Left _ -> return Nothing
    Right (CNF nv nc v) -> do
      return $ Just (CNFDescription nv nc f, v)

data CNF = CNF
    { numVars    :: !Int
    -- ^ The number of variables in the problem as reported by the cnf header.
    , numClauses :: !Int
    -- ^ The number of clauses in the problem as reported by the cnf header.
    , clauses    :: ![SizedVectorInt] } deriving Show

-- | Parse a file containing DIMACS CNF data.
parseFile :: Maybe FilePath -> IO (Either ParseError CNF)
parseFile Nothing = do
  str <- getContents
  withSystemTempFile "sih4.cnf" $ \f h -> do
    hPutStrLn h str
    hClose h
    parseFromFile cnf f

parseFile (Just f) = parseFromFile cnf f

-- | Parse a byte string containing DIMACS CNF data.  The source name is only
-- | used in error messages and may be the empty string.
-- parseByteString :: SourceName -> ByteString -> Either ParseError CNF
-- parseByteString = runParser cnf ()

-- A DIMACS CNF file contains a header of the form "p cnf <numVars>
-- <numClauses>" and then a bunch of 0-terminated clauses.
cnf :: Parser CNF
cnf = uncurry CNF `fmap` cnfHeader `ap` lexeme (many clause)

-- Parses into `(numVars, numClauses)'.
cnfHeader :: Parser (Int, Int)
cnfHeader = do
    whiteSpace
    char 'p' >> many1 space -- Can't use symbol here because it uses
                            -- whiteSpace, which will treat the following
                            -- "cnf" as a comment.
    symbol "cnf"
    (,) `fmap` natural `ap` natural

clause :: Parser SizedVectorInt
clause = do ints <- lexeme int `manyTill` try (symbol "0")
            let !l = U.fromList $! length ints : ints
            return $! l

-- token parser
tp = T.makeTokenParser $ T.LanguageDef 
   { T.commentStart = ""
   , T.commentEnd = ""
   , T.commentLine = "c"
   , T.nestedComments = False
   , T.identStart = unexpected "ParseDIMACS bug: shouldn't be parsing identifiers..."
   , T.identLetter = unexpected "ParseDIMACS bug: shouldn't be parsing identifiers..."
   , T.opStart = unexpected "ParseDIMACS bug: shouldn't be parsing operators..."
   , T.opLetter = unexpected "ParseDIMACS bug: shouldn't be parsing operators..."
   , T.reservedNames = ["p", "cnf"]
   , T.reservedOpNames = []
   , T.caseSensitive = True
   }

natural :: Parser Int
natural = fromIntegral `fmap` T.natural tp
int :: Parser Int
int = fromIntegral `fmap` T.integer tp
symbol = T.symbol tp
whiteSpace = T.whiteSpace tp
lexeme = T.lexeme tp
