-- | yet another Minisat Implementation On SIH4
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

import Control.Monad
import qualified Data.Vector.Unboxed as V
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.SolverRelation
import SAT.Solver.Mios.Solver
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Util.DIMACSReader
import SAT.Solver.Mios.OptionParser

runSolverWithOption :: MiosConfigurationOption -> Maybe String -> IO ()
runSolverWithOption _ Nothing = return ()
runSolverWithOption opts targetfile = do
  when (_confVerbose opts) $ putStrLn idString -- >> checkImplementation
  sat <- cnfFromFile targetfile
  case sat of
   Nothing -> error $ "couldn't load " ++ show targetfile
   Just (desc, vecs) -> do
     when (_confVerbose opts) $ do
       putStrLn $ "loaded : #v = " ++ show (numberOfVariables desc) ++ " #c = " ++ show (numberOfClauses desc)
     s <- newSolver
     mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
     s <- setInternalState s $ numberOfVariables desc
     mapM_ ((s `addClause`) . V.toList) vecs
     when (_confVerbose opts) $ do
       nv <- nVars s
       nc <- nConstraints s
       nl <- nLearnts s
       putStrLn $ "(nv, nc, nl) = " ++ show (nv, nc, nl)
       -- putStrLn "literal  1 watched by: "
       -- putStrLn . intercalate ", " =<< mapM dumpClause =<< asList =<< watches s .! 0
       -- putStrLn "literal -1 watched by: "
       -- putStrLn . intercalate ", " =<< mapM dumpClause =<< asList =<< watches s .! 1
     res <- simplifyDB s
     when (_confVerbose opts) $ putStrLn $ "`simplifyDB`: " ++ show res
     result <- solve s =<< emptyVec
     unless (_confNoAnswer opts) $ do
       if result
         then print . zipWith (\n s -> if s then n else negate n) [1 .. ] =<< asList (model s)
         else putStrLn "[]"

runSolver = runSolverWithOption miosDefaultOption

-- | the easiest interface
-- returns the result @::[[Int]]@ for a given @(CNFDescription, [RawClause])@
-- The first argument @target@ can be build by @Just target <- cnfFromFile targetfile@.
solveSAT :: (CNFDescription, [RawClause]) -> IO [Int]
solveSAT = solveSATWithOption miosDefaultOption

solveSATWithOption :: MiosConfigurationOption -> (CNFDescription, [RawClause]) -> IO [Int]
solveSATWithOption opts (desc, vecs) = do
  s <- newSolver
  mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
  s <- setInternalState s $ numberOfVariables desc
  mapM_ ((s `addClause`) . V.toList) vecs
  res <- simplifyDB s
  result <- solve s =<< emptyVec
  if result
    then zipWith (\n s -> if s then n else negate n) [1 .. ] <$> asList (model s)
    else return []
