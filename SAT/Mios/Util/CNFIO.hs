{-# LANGUAGE Safe #-}

-- | Read/Write a CNF file only with ghc standard libraries
module SAT.Mios.Util.CNFIO
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
       , module SAT.Mios.Util.BoolExp
       )
       where
import SAT.Mios.Util.CNFIO.Reader
import SAT.Mios.Util.CNFIO.Writer
import SAT.Mios.Util.CNFIO.MinisatReader
import SAT.Mios.Util.BoolExp

-- | String from BoolFrom
asCNFString :: BoolForm -> String
asCNFString = toCNFString . asList

-- | String from BoolFrom
asCNFString_ :: BoolForm -> String
asCNFString_ = toCNFString . asList_
