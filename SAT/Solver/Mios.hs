-- | yet another Minisat Implementation On SIH4
module SAT.Solver.Mios
       (
         newVar
       , addClause
       , add
       , simplifyDB
       , solve
       , model
       )
       where

import SAT.Solver.Mios.Solver

