-- | Internal Settings
module SAT.Solver.Mios.Internal
       (
         versionId
       , MiosConfiguration (..)
       , defaultConfiguration
       , module Plumbing
       )
       where
import SAT.Solver.Mios.Data.VecBool as Plumbing
import SAT.Solver.Mios.Data.VecDouble as Plumbing
import SAT.Solver.Mios.Data.Stack as Plumbing

-- | version name
versionId :: String
versionId = "mios 1.2" -- blocking literal + lbd + phase-saving

-- | solver's parameters; random decision rate was dropped.
data MiosConfiguration = MiosConfiguration
                         {
                           variableDecayRate  :: Double  -- ^ decay rate for variable activity
                         , clauseDecayRate    :: Double  -- ^ decay rate for clause activity
                         , collectStats       :: Bool    -- ^ whether collect and report statistics
                         }

-- | dafault configuration
--
-- * Minisat-1.14 uses @(0.95, 0.999, 0.2 = 20 / 1000)@.
-- * Minisat-2.20 uses @(0.95, 0.999, 0)@.
-- * Gulcose-4.0  uses @(0.8 , 0.999, 0)@.
-- * Mios-1.2     uses @(0.95, 0.999, 0)@.
--
defaultConfiguration :: MiosConfiguration
defaultConfiguration = MiosConfiguration 0.95 0.999 {- 0 -} False
