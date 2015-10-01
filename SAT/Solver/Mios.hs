-- | Minisat Implementation Optimization Study
module SAT.Solver.Mios
       (
         idString
       , solveSAT
       , solveSATWithOption
       , runSolver
       , runSolverWithOption
       , module SAT.Solver.Mios.OptionParser
       , newVar
       , addClause
       , simplifyDB
       , solve
       , model
       , cnfFromFile
       )
       where

import Control.Monad ((<=<), mapM_, unless, when)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Solver
import SAT.Solver.Mios.Util.DIMACSReader
import SAT.Solver.Mios.Internal (idString)
import SAT.Solver.Mios.Implementation.FixedVecInt (FixedVecInt, newSizedVecIntFromUVector)
import SAT.Solver.Mios.Implementation.ListOf (ListOf, newList)
import SAT.Solver.Mios.OptionParser

runSolverWithOption :: MiosConfigurationOption -> Maybe String -> IO ()
runSolverWithOption _ Nothing = return ()
runSolverWithOption opts targetfile = do
  when (_confVerbose opts) $ putStrLn idString
  sat <- cnfFromFile targetfile
  case sat of
   Nothing -> error $ "couldn't load " ++ show targetfile
   Just (desc, vecs) -> do
     when (_confVerbose opts) $ do
       putStrLn $ "loaded : #v = " ++ show (numberOfVariables desc) ++ " #c = " ++ show (numberOfClauses desc)
     s <- newSolver
     -- mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
     s <- setInternalState s $ numberOfVariables desc
     mapM_ ((s `addClause`) <=< newSizedVecIntFromUVector) vecs
     when (_confVerbose opts) $ do
       nv <- nVars s
       nc <- nConstraints s
       nl <- nLearnts s
       putStrLn $ "(nv, nc, nl) = " ++ show (nv, nc, nl)
     res <- simplifyDB s
     when (_confVerbose opts) $ putStrLn $ "`simplifyDB`: " ++ show res
     result <- solve s =<< newList
     unless (_confNoAnswer opts) $ do
       if result
         then print . zipWith (\n s -> if s then n else negate n) [1 .. ] =<< asList (model s)
         else putStrLn "[]"

runSolver = runSolverWithOption miosDefaultOption

-- | the easiest interface
-- returns the result @::[[Int]]@ for a given @(CNFDescription, [SizedVectorInt])@
-- The first argument @target@ can be build by @Just target <- cnfFromFile targetfile@.
solveSAT :: (CNFDescription, [SizedVectorInt]) -> IO [Int]
solveSAT = solveSATWithOption miosDefaultOption

solveSATWithOption :: MiosConfigurationOption -> (CNFDescription, [SizedVectorInt]) -> IO [Int]
solveSATWithOption opts (desc, vecs) = do
  s <- newSolver
  -- mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
  s <- setInternalState s $ numberOfVariables desc
  mapM_ ((s `addClause`) <=< newSizedVecIntFromUVector) vecs
  simplifyDB s
  result <- solve s =<< newList
  if result
    then zipWith (\n s -> if s then n else negate n) [1 .. ] <$> asList (model s)
    else return []
