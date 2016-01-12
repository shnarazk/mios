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
import Data.IORef
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Solver
import SAT.Solver.Mios.Util.DIMACSReader
import SAT.Solver.Mios.Internal (idString, FixedVecInt, ListOf, newList, newSizedVecIntFromUVector)
import SAT.Solver.Mios.OptionParser

runSolverWithOption :: MiosConfigurationOption -> Maybe String -> IO ()
runSolverWithOption _ Nothing = return ()
runSolverWithOption opts targetfile = do
  when (_confVerbose opts) $ putStrLn idString
  sat <- cnfFromFile targetfile
  case sat of
   Nothing -> error $ "couldn't load " ++ show targetfile
   Just (desc, vecs) -> do
     when (_confVerbose opts) $
       putStrLn $ "loaded : #v = " ++ show (numberOfVariables desc) ++ " #c = " ++ show (numberOfClauses desc)
     s <- flip setInternalState (numberOfVariables desc) =<< newSolver (toMiosConf opts)
     -- mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
     mapM_ ((s `addClause`) <=< newSizedVecIntFromUVector) vecs
     when (_confVerbose opts) $ do
       nc <- nConstraints s
       nl <- nLearnts s
       putStrLn $ "(nv, nc, nl) = " ++ show (nVars s, nc, nl)
     res <- simplifyDB s
     when (_confVerbose opts) $ putStrLn $ "`simplifyDB`: " ++ show res
     result <- solve s =<< newList
     unless (_confNoAnswer opts) $
       if result
         then print . zipWith (\n b -> if b then n else negate n) [1 .. ] =<< asList (model s)
         else putStrLn "[]"

runSolver :: Maybe String -> IO ()
runSolver = runSolverWithOption miosDefaultOption

-- | the easiest interface
-- returns the result @::[[Int]]@ for a given @(CNFDescription, [SizedVectorInt])@
-- The first argument @target@ can be build by @Just target <- cnfFromFile targetfile@.
solveSAT :: (CNFDescription, [SizedVectorInt]) -> IO [Int]
solveSAT = solveSATWithOption miosDefaultOption

solveSATWithOption :: MiosConfigurationOption -> (CNFDescription, [SizedVectorInt]) -> IO [Int]
solveSATWithOption opts (desc, vecs) = do
  s <- flip setInternalState (numberOfVariables desc) =<< newSolver (toMiosConf opts)
  -- mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
  mapM_ ((s `addClause`) <=< newSizedVecIntFromUVector) vecs
  simplifyDB s
  result <- solve s =<< newList
  if result
    then zipWith (\n b -> if b then n else negate n) [1 .. ] <$> asList (model s)
    else return []
