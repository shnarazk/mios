{-# LANGUAGE Safe #-}

-- | Read/Write a CNF file only with ghc standard libraries
module SAT.Util.CNFIO
       (
         -- * Input
         fromFile
       , clauseListFromFile
       , fromMinisatOutput
       , clauseListFromMinisatOutput
         -- * Output
       , toFile
       , toCNFString
       , asCNFString
       , asCNFString_
         -- * Bool Operation
       , module SAT.Util.BoolExp
       )
       where
import SAT.Util.CNFIO.Reader
import SAT.Util.CNFIO.Writer
import SAT.Util.CNFIO.MinisatReader
import SAT.Util.BoolExp

-- | String from BoolFrom
asCNFString :: BoolForm -> String
asCNFString = toCNFString . asList

-- | String from BoolFrom
asCNFString_ :: BoolForm -> String
asCNFString_ = toCNFString . asList_
