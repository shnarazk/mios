{-# LANGUAGE ViewPatterns #-}
-- | Minisat-based Implementation and Optimization Study

module SAT.Solver.Mios
       (
         -- * SAT solver interface
         versionId
       , CNFDescription (..)
       , module SAT.Solver.Mios.OptionParser
       , solveSAT
       , solveSATWithConfiguration
--       , cnfFromFile
       , newVar
       , addClause
       , simplifyDB
       , solve
       , model
         -- * Assignment Validator
       , validateAssignment
       , validate
         -- * For standalone programs
       , runSolverOn
       , runSolver
       , runValidatorOn
       , runValidator
       )
       where

import Control.Monad ((<=<), unless, when)
import qualified Data.ByteString.Char8 as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import System.Exit

import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Solver
import SAT.Solver.Mios.Internal (versionId)
import SAT.Solver.Mios.OptionParser
import SAT.Solver.Mios.Validator

-- | SizedVectorInt is an Int vector with the number of 'active' elements
-- namely,
-- * v[0]            == the number of using elements
-- * v[1] .. v[v[0]] == using elements
-- v[v[0] + 1] ..    == allocated but not-in-use elements
type SizedVectorInt = U.Vector Int

-- | runs a solver on the given CNF file 
-- This is the simplest entry to standalone programs; not for Haskell programs
runSolverOn :: FilePath -> IO ()
runSolverOn path = runSolver (miosDefaultOption { _targetFile = Just path })

-- | runs a solver on the given 'arg :: MiosConfiguration'
-- | This is another entry point for standalone programs.
runSolver :: MiosConfigurationOption -> IO ()
runSolver opts@(_targetFile -> target@(Just cnfFile)) = do
  str <- B.readFile cnfFile
  let ((n, m), clauses) = buildDescription str
  let desc = CNFDescription n m target
  case (n, m) of
   (0, 0) -> error $ "couldn't load " ++ show cnfFile
   _ -> do
     when (_confVerbose opts) $
       putStrLn $ "loaded : #v = " ++ show (_numberOfVariables desc) ++ " #c = " ++ show (_numberOfClauses desc)
     s <- newSolver (toMiosConf opts) >>= (`setInternalState` desc)
     injectClauses s n m clauses
     when (_confVerbose opts) $ do
       nc <- nConstraints s
       nl <- nLearnts s
       putStrLn $ "(nv, nc, nl) = " ++ show (nVars s, nc, nl)
     res <- simplifyDB s
     when (_confVerbose opts) $ putStrLn $ "`simplifyDB`: " ++ show res
     result <- solve s []
     unless (_confNoAnswer opts) $
       if result
         then print . zipWith (\n b -> if b then n else negate n) [1 .. ] =<< asList (model s)
         else putStrLn "[]"
     when (result && _confCheckAnswer opts) $ do
       asg <- zipWith (\n b -> if b then n else negate n) [1 .. ] <$> asList (model s)
       s' <- newSolver (toMiosConf opts) >>= (`setInternalState` desc)
       injectClauses s' n m clauses
       ok <- validate s' asg
       if _confVerbose opts
         then putStrLn $ if ok then "a vaild answer" else "mios returns a wrong answer"
         else unless ok $ error "mios returns a wrong answer"

runSolver _ = return ()

{-# INLINE injectClauses #-}
injectClauses :: Solver -> Int -> Int -> B.ByteString -> IO ()
injectClauses solver n m str = do
  let
    initialSize = 3
    -- | skip comment lines and whitespaces
    -- CAVEAT: this code interpretes 'c' as a comment designator even if it is placed in the middle of a line
    skipToInt :: B.ByteString -> B.ByteString
    skipToInt str = if B.head bol == 'c' then skipToInt $ B.dropWhile ('\n' /=) bol else bol
      where bol = B.dropWhile (`elem` " \t\n") str
    -- | read an Int and store it to /j/-th literal of /i/-th clause
    loop :: Int -> Int -> B.ByteString -> Vec -> IO ()
    loop i j str vec = do
      case B.readInt (skipToInt str) of
        Just (0, str') -> do
          setNth vec 0 (j - 1)
          solver `addClause` vec
          let i' = i + 1
          if m == i' then return () else loop i' 1 str' =<< newVec initialSize
        Just (l, str') -> do
          len <- sizeOfVector vec
          if len <= j
            then do
                vec' <- UM.unsafeGrow vec len
                setNth vec' j l >> loop i (j + 1) str' vec'
            else setNth vec j l >> loop i (j + 1) str' vec
        Nothing -> return ()
  loop 0 1 str =<< newVec n

buildDescription :: B.ByteString -> ((Int, Int), B.ByteString)
buildDescription bs = if B.head bs == 'p' then (parseP l, B.tail bs') else buildDescription (B.tail bs')
  where
    (l, bs') = B.span ('\n' /=) bs
    -- format: p cnf n m, length "p cnf" == 5
    parseP l = case B.readInt $ B.dropWhile (`elem` " \t") (B.drop 5 l) of
      Just (x, snd) -> case B.readInt (B.dropWhile (`elem` " \t") snd) of
        Just (y, rest) -> (x, y)
        _ -> (0, 0)
      _ -> (0, 0)

-- | the easiest interface for Haskell programs
-- This returns the result @::[[Int]]@ for a given @(CNFDescription, [[Int]])@
-- The first argument @target@ can be build by @Just target <- cnfFromFile targetfile@.
-- The second part of the first argument is a list of vector, which 0th element is the number of its real elements
solveSAT :: Traversable m => (CNFDescription, m [Int]) -> IO [Int]
solveSAT = solveSATWithConfiguration defaultConfiguration

-- | solves the problem (2rd arg) under the configuration (1st arg)
-- and returns an assignment as list of literals :: Int
solveSATWithConfiguration :: Traversable m => MiosConfiguration -> (CNFDescription, m [Int]) -> IO [Int]
solveSATWithConfiguration conf (desc, clauses) = do
  s <- newSolver conf >>= (`setInternalState` desc)
  -- mapM_ (const (newVar s)) [0 .. _numberOfVariables desc - 1]
  mapM_ ((s `addClause`) <=< (newSizedVecIntFromList . (\c -> length c : c))) clauses
  noConf <- simplifyDB s
  if noConf
    then do
        result <- solve s []
        if result
            then zipWith (\n b -> if b then n else negate n) [1 .. ] <$> asList (model s)
            else return []
    else return []

-- | validates a given assignment from STDIN for the CNF file (2nd arg)
-- this is the entry point for standalone programs
runValidatorOn :: FilePath -> IO ()
runValidatorOn path = runValidator (miosDefaultOption { _targetFile = Just path })

-- | validates a given assignment for the problem (2nd arg)
-- this is another entry point for standalone programs; see app/mios.hs
runValidator :: MiosConfigurationOption -> IO ()
runValidator opts@(_targetFile -> target@(Just cnfFile)) = do
  str <- B.readFile cnfFile
  let ((n, m), clauses) = buildDescription str
  let desc = CNFDescription n m target
  case (n, m) of
   (0, 0) -> error $ "couldn't load " ++ show cnfFile
   _ -> do
     when (_confVerbose opts) $
       putStrLn $ "loaded : #v = " ++ show (_numberOfVariables desc) ++ " #c = " ++ show (_numberOfClauses desc)
     s <- newSolver (toMiosConf opts) >>= (`setInternalState` desc)
     injectClauses s n m clauses
     when (_confVerbose opts) $ do
       nc <- nConstraints s
       nl <- nLearnts s
       putStrLn $ "(nv, nc, nl) = " ++ show (nVars s, nc, nl)
     asg <- read <$> getContents
     result <- s `validate` (asg :: [Int])
     if result
       then putStrLn "It's a valid assignment." >> exitSuccess
       else putStrLn "It's an invalid assignment." >> exitFailure

runValidator _  = return ()

-- | returns True if a given assignment (2nd arg) satisfies the problem (1st arg)
-- if you want to check the @answer@ which a @slover@ returned, run @solver `validate` answer@,
-- where 'validate' @ :: Traversable t => Solver -> t Lit -> IO Bool@
validateAssignment :: (Traversable m, Traversable n) => (CNFDescription, m [Int]) -> n Int -> IO Bool
validateAssignment (desc, clauses) asg = do
  s <- newSolver defaultConfiguration >>= (`setInternalState` desc)
  mapM_ ((s `addClause`) <=< (newSizedVecIntFromList . (\c -> length c : c))) clauses
  s `validate` asg
