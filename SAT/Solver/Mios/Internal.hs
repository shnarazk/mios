module SAT.Solver.Mios.Internal
       (
         versionId
-- <<<<
       , module SAT.Solver.Mios.Data.FixedVecDouble
       , module SAT.Solver.Mios.Data.FixedVecInt
-- ----
--       , module SAT.Solver.Mios.Data.FixedUVecOf
-- >>>>
--       , module SAT.Solver.Mios.Data.FixedVecOf
       , module SAT.Solver.Mios.Data.ListOf
       , module SAT.Solver.Mios.Data.ListOfInt
       , module SAT.Solver.Mios.Data.QueueOfBoundedInt
       , module SAT.Solver.Mios.Data.Singleton
       , MiosConfiguration (..)
       , defaultConfiguration
       )
       where
-- <<<<
import SAT.Solver.Mios.Data.FixedVecDouble
import SAT.Solver.Mios.Data.FixedVecInt
-- ----
-- import SAT.Solver.Mios.Data.FixedUVecOf
-- >>>>
-- import SAT.Solver.Mios.Data.FixedVecOf
import SAT.Solver.Mios.Data.ListOf
import SAT.Solver.Mios.Data.ListOfInt
import SAT.Solver.Mios.Data.QueueOfBoundedInt
import SAT.Solver.Mios.Data.Singleton

-- | version name
versionId :: String
versionId = "mios WIP1.0.3 cv heap nr"

-- | solver configuration
data MiosConfiguration = MiosConfiguration
                         {
                           variableDecayRate  :: Double
                         , clauseDecayRate    :: Double
                         , randomDecisionRate :: Int -- used in Solver.select
                         }

-- | dafault configuration
-- Minisat-1.14 uses (0.95, 0.999, 0.2 = 20 / 1000).
-- Minisat-2.20 uses (0.95, 0.999, 0).
defaultConfiguration :: MiosConfiguration
defaultConfiguration = MiosConfiguration 0.95 0.999 0
