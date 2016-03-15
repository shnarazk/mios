module SAT.Solver.Mios.Internal
       (
         versionId
       , MiosConfiguration (..)
       , defaultConfiguration
       , module Plumbing
       )
       where
import SAT.Solver.Mios.Data.FixedVecBool as Plumbing
import SAT.Solver.Mios.Data.FixedVecDouble as Plumbing
import SAT.Solver.Mios.Data.Stack as Plumbing

-- | version name
versionId :: String
versionId = "mios M114; bitEncode, singleStack"

-- | solver's parameter configuration
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
