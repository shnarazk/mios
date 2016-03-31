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
import SAT.Solver.Mios.ClauseManager
import SAT.Solver.Mios.Solver

-- | validate the assignment even if the implementation of 'Solver' is wrong; we re-implement some functions here.
validate :: Traversable t => Solver -> t Int -> IO Bool
validate s (toList -> map int2lit -> lst) = do
  assignment <- newVec $ 1 + nVars s
  vec <- getClauseVector (clauses s)
  nc <- numberOfClauses (clauses s)
  let
    inject :: Lit -> IO ()
    inject l = setNth assignment (lit2var l) $ if positiveLit l then lTrue else lFalse
    -- return True if the literal is satisfied under the assignment
    satisfied :: Lit -> IO Bool
    satisfied l
      | positiveLit l = (lTrue ==) <$> getNth assignment (lit2var l)
      | otherwise     = (lFalse ==) <$> getNth assignment (lit2var l)
    -- return True is any literal in the given list
    satAny :: [Lit] -> IO Bool
    satAny [] = return False
    satAny (l:ls) = do
      sat' <- satisfied l
      if sat' then return True else satAny ls
    -- traverse all clauses in 'clauses'
    loopOnVector :: Int -> IO Bool
    loopOnVector ((< nc) -> False) = return True
    loopOnVector i = do
      c <- getNthClause vec i
      sat' <- satAny =<< asList c
      if sat' then loopOnVector (i + 1) else return False
  if null lst
    then error "validator got an empty assignment."
    else mapM_ inject lst >> loopOnVector 0
