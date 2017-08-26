{-# LANGUAGE
    ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | validate an assignment
module SAT.Mios.Validator
       (
         validate
       )
       where

import Data.Foldable (toList)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.Solver

-- | validates the assignment even if the implementation of 'Solver' is wrong; we re-implement some functions here.
validate :: Traversable t => Solver -> t Int -> IO Bool
validate s (toList -> map int2lit -> lst) = do
  assignment <- newVec (1 + nVars s) (0 :: Int) :: IO (Vec Int)
  vec <- getClauseVector (clauses s)
  nc <- get' (clauses s)
  let
    inject :: Lit -> IO ()
    inject l = setNth assignment (lit2var l) $ if positiveLit l then lTrue else lFalse
    -- returns True if the literal is satisfied under the assignment
    satisfied :: Lit -> IO Bool
    satisfied l
      | positiveLit l = (lTrue ==) <$> getNth assignment (lit2var l)
      | otherwise     = (lFalse ==) <$> getNth assignment (lit2var l)
    -- returns True is any literal in the given list
    satAny :: [Lit] -> IO Bool
    satAny [] = return False
    satAny (l:ls) = do
      sat' <- satisfied l
      if sat' then return True else satAny ls
    -- traverses all clauses in 'clauses'
    loopOnVector :: Int -> IO Bool
    loopOnVector ((< nc) -> False) = return True
    loopOnVector i = do
      sat' <- satAny =<< asList =<< getNth vec i
      if sat' then loopOnVector (i + 1) else return False
  if null lst
    then error "validator got an empty assignment."
    else mapM_ inject lst >> loopOnVector 0
