module SAT.Solver.Mios.Internal
       (
         idString
       , module SAT.Solver.Mios.Implementation.VecOf
       , module SAT.Solver.Mios.Implementation.FixedVecDouble
       , module SAT.Solver.Mios.Implementation.FixedVecInt
       , module SAT.Solver.Mios.Implementation.FixedVecOf
       , module SAT.Solver.Mios.Implementation.FixedUVecOf
       , module SAT.Solver.Mios.Implementation.FixedQueueOf
       , module SAT.Solver.Mios.Implementation.StackOfLit
       )
       where
import SAT.Solver.Mios.Implementation.VecOf
import SAT.Solver.Mios.Implementation.FixedVecDouble
import SAT.Solver.Mios.Implementation.FixedVecInt
import SAT.Solver.Mios.Implementation.FixedVecOf
import SAT.Solver.Mios.Implementation.FixedUVecOf
import SAT.Solver.Mios.Implementation.FixedQueueOf
import SAT.Solver.Mios.Implementation.StackOfLit

-- | sets to the version name : @"mios v0.7 #optimization"@
idString :: String
idString = "mios v0.7 #optimization"
