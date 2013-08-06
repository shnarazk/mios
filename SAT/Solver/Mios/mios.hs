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
import SAT.Solver.Mios.Implementation.V01
import SAT.Solver.SIH.Data.Types (RawClause, CNFDescription (..))
import SAT.Solver.SIH.Data.DIMACSReader

-- | main
main :: IO ()
main = do
  putStrLn idString
  -- checkImplementation
  args <- getArgs
  unless (null args) $ do
    sat <- cnfFromFile . Just $ head args
    case sat of
     Nothing -> putStrLn "couldn't load"
     Just (desc, vecs) -> do
       -- putStrLn $ "loaded : #v = " ++ show (numberOfVariables desc) ++ " #c = " ++ show (numberOfClauses desc)
       s <- newSolver
       mapM_ (const (newVar s)) [0 .. numberOfVariables desc - 1]
       mapM_ ((s `addClause`) . V.toList) vecs
       nv <- nVars s
       nc <- nConstraints s
       nl <- nLearnts s
       putStrLn $ "(nv, nc, nl) = " ++ show (nv, nc, nl)
       putStrLn "literal  1 watched by: "
       putStrLn . intercalate ", " =<< mapM dumpClause =<< asList =<< watches s .! 0
       putStrLn "literal -1 watched by: "
       putStrLn . intercalate ", " =<< mapM dumpClause =<< asList =<< watches s .! 1
       putStrLn . ("`simplifyDB`: " ++) . show =<< simplifyDB s
       result <- solve s =<< emptyVec
       if result
         then do
             asg <- asList (model s)
             print asg
             print $ zipWith (\n s -> if s then n else negate n) [1 .. ] asg
         else putStrLn "[]"
