{-# LANGUAGE Safe #-}

-- | Read/Write a CNF file only with ghc standard libraries
module SAT.Mios.Util.DIMACS
       (
         -- * Input
         fromFile
       , clauseListFromFile
       , fromMinisatOutput
       , clauseListFromMinisatOutput
         -- * Output
       , toFile
       , toDIMACSString
       , asDIMACSString
       , asDIMACSString_
         -- * Bool Operation
       , module SAT.Mios.Util.BoolExp
       )
       where
import SAT.Mios.Util.DIMACS.Reader
import SAT.Mios.Util.DIMACS.Writer
import SAT.Mios.Util.DIMACS.MinisatReader
import SAT.Mios.Util.BoolExp

-- | String from BoolFrom
asDIMACSString :: BoolForm -> String
asDIMACSString = toDIMACSString . asList

-- | String from BoolFrom
asDIMACSString_ :: BoolForm -> String
asDIMACSString_ = toDIMACSString . asList_
