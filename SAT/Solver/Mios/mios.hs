-- | MINISAT Implementation On Sih4 (mios)
module Main
       (
         main
       )
       where

import Control.Monad
import Data.List (intercalate)
import qualified Data.Vector.Unboxed as V
import System.Environment (getArgs)
import System.IO (hFlush, stdout)

import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Solver
import SAT.Solver.Mios.Internal
import SAT.Solver.SIH.Data.Types (RawClause, CNFDescription (..))
import SAT.Solver.SIH.Data.DIMACSReader
import SAT.Solver.Mios.OptionParser

-- | main
main :: IO ()
main = do
  opts <- miosParseOptionsFromArgs idString
  case () of
    _ | _displayVersion opts -> putStrLn idString
    _ | _displayHelp opts    -> putStrLn $ miosUsage $ idString ++ "\nUsage: mios [OPTIONS] target.cnf"
    _ | otherwise            -> execute opts $ _targetFile opts

execute :: MiosConfigurationOption -> Maybe String -> IO ()
execute _ Nothing = return ()
execute opts targetfile = do
  when (_confVerbose opts) $ putStrLn idString -- >> checkImplementation
  sat <- cnfFromFile targetfile
  case sat of
   Nothing -> error $ "couldn't load " ++ show targetfile
   Just (desc, vecs) -> do
     when (_confVerbose opts) $ do
       putStrLn $ "loaded : #v = " ++ show (numberOfVariables desc) ++ " #c = " ++ show (numberOfClauses desc)
     s <- newSolver
     mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
     s <- setInternalState s
     mapM_ ((s `addClause`) . V.toList) vecs
     when (_confVerbose opts) $ do
       nv <- nVars s
       nc <- nConstraints s
       nl <- nLearnts s
       putStrLn $ "(nv, nc, nl) = " ++ show (nv, nc, nl)
       putStrLn "literal  1 watched by: "
       putStrLn . intercalate ", " =<< mapM dumpClause =<< asList =<< watches s .! 0
       putStrLn "literal -1 watched by: "
       putStrLn . intercalate ", " =<< mapM dumpClause =<< asList =<< watches s .! 1
     res <- simplifyDB s
     when (_confVerbose opts) $ putStrLn $ "`simplifyDB`: " ++ show res
     result <- solve s =<< emptyVec
     unless (_confNoAnswer opts) $ do
       if result
         then print . zipWith (\n s -> if s then n else negate n) [1 .. ] =<< asList (model s)
         else putStrLn "[]"
