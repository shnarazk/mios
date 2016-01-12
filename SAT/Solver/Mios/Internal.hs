module SAT.Solver.Mios.Internal
       (
         versionId
-- <<<<
       , module SAT.Solver.Mios.Implementation.FixedVecDouble
       , module SAT.Solver.Mios.Implementation.FixedVecInt
-- ----
--       , module SAT.Solver.Mios.Implementation.FixedUVecOf
-- >>>>
       , module SAT.Solver.Mios.Implementation.FixedVecOf
       , module SAT.Solver.Mios.Implementation.ListOf
       , module SAT.Solver.Mios.Implementation.ListOfInt
       , module SAT.Solver.Mios.Implementation.QueueOfBoundedInt
       , module SAT.Solver.Mios.Implementation.IntSingleton
       , MiosConfiguration (..)
       , defaultConfiguration
       )
       where
-- <<<<
import SAT.Solver.Mios.Implementation.FixedVecDouble
import SAT.Solver.Mios.Implementation.FixedVecInt
-- ----
-- import SAT.Solver.Mios.Implementation.FixedUVecOf
-- >>>>
import SAT.Solver.Mios.Implementation.FixedVecOf
import SAT.Solver.Mios.Implementation.ListOf
import SAT.Solver.Mios.Implementation.ListOfInt
import SAT.Solver.Mios.Implementation.QueueOfBoundedInt
import SAT.Solver.Mios.Implementation.IntSingleton

-- | version name
versionId :: String
versionId = "mios version 1.0.0, #hofo" -- #heapOfFoolishOptimizations > #rigorousEmulatonOfMinisat-1.14

-- | solver configuration
data MiosConfiguration = MiosConfiguration
                         {
                           variableDecayRate  :: Double
                         , clauseDecayRate    :: Double
                         , randomDecisionRate :: Int -- used in Solver.select
                         }

-- | dafault configuration
-- Minisat-1.14 uses the identical values: (0.95, 0.999, 0.2 = 20 / 1000)
defaultConfiguration :: MiosConfiguration
defaultConfiguration = MiosConfiguration 0.95 0.999 20
