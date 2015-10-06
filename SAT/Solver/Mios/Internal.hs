module SAT.Solver.Mios.Internal
       (
         idString
       , module SAT.Solver.Mios.Implementation.FixedVecDouble
       , module SAT.Solver.Mios.Implementation.FixedVecInt
       , module SAT.Solver.Mios.Implementation.FixedVecOf
       , module SAT.Solver.Mios.Implementation.ListOf
       , module SAT.Solver.Mios.Implementation.QueueOfBoundedInt
       )
       where
import SAT.Solver.Mios.Implementation.FixedVecDouble
import SAT.Solver.Mios.Implementation.FixedVecInt
import SAT.Solver.Mios.Implementation.FixedVecOf
import SAT.Solver.Mios.Implementation.ListOf
import SAT.Solver.Mios.Implementation.QueueOfBoundedInt

-- | sets to the version name : @"mios v0.9 #validVarOrder"@
idString :: String
idString = "mios v0.9 #validVarOrder"
