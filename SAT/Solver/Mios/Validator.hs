{-# LANGUAGE
    ViewPatterns
  #-}
module SAT.Solver.Mios.Validator
       (
         validate
       )
       where

import Data.Foldable (toList)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.ClauseManager
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Solver

-- | validate the assignment even if the implementation of 'Solver' is wrong; we re-implement some functions here.
validate :: Traversable t => Solver -> t Lit -> IO Bool
validate s (toList -> lst) = do
  assignment <- newVec $ 1 + nVars s
  vec <- getClauseVector (constrs s)
  nc <- numberOfClauses (constrs s)
  let
    inject :: Lit -> IO ()
    inject l = setNthInt (abs l) assignment (signum l)
    -- return True if the literal is satisfied under the assignment
    satisfied :: Lit -> IO Bool
    satisfied n = (signum n ==) . signum <$> getNthInt (abs n) assignment  
    -- return True is any literal in the given list
    satAny :: [Lit] -> IO Bool
    satAny [] = return False
    satAny (l:ls) = do
      sat' <- satisfied l
      if sat' then return True else satAny ls
    -- traverse all clauses in 'constrs'
    loopOnVector :: Int -> IO Bool
    loopOnVector ((< nc) -> False) = return True
    loopOnVector i = do
      c <- getNthClause vec i
      sat' <- satAny =<< asList c
      if sat' then loopOnVector (i + 1) else return False
  if null lst
    then error "validator got an empty assignment."
    else mapM_ inject lst >> loopOnVector 0
