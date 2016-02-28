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
       , module SAT.Solver.Mios.Data.QueueOfBoundedInt
       , module SAT.Solver.Mios.Data.Singleton
       , module SAT.Solver.Mios.Data.StackOfInt
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
import SAT.Solver.Mios.Data.QueueOfBoundedInt
import SAT.Solver.Mios.Data.Singleton
import SAT.Solver.Mios.Data.StackOfInt

-- | version name
versionId :: String
versionId = "mios M22"

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
