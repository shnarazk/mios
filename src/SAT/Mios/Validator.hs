-- | (This is a part of MIOS.)
-- Validate an assignment
{-# LANGUAGE
    RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Mios.Validator
       (
         validate
--       , checkUniqueness
       )
       where

import Control.Monad (when)
import Data.Foldable (toList)
import Data.List (sort)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.Solver

-- | validates the assignment even if the implementation of 'Solver' is wrong; we re-implement some functions here.
validate :: Traversable t => Solver -> t Int -> IO Bool
validate s t = do
  assignment <- newVec (1 + nVars s) (0 :: Int) :: IO (Vec Int)
  vec <- getClauseVector (clauses s)
  nc <- get' (clauses s)
  let
    lst = map int2lit $ toList t
    inject :: Lit -> IO ()
    inject l = setNth assignment (lit2var l) $ lit2lbool l
    -- returns True if the literal is satisfied under the assignment
    satisfied :: Lit -> IO Bool
    satisfied l
      | positiveLit l = (LiftedT ==) <$> getNth assignment (lit2var l)
      | otherwise     = (LiftedF ==) <$> getNth assignment (lit2var l)
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

-- | checks uniqueness of learnts
checkUniqueness :: Solver -> Clause -> IO ()
checkUniqueness Solver{..} c = do
  n <- get' learnts
  cvec <- getClauseVector learnts
  cls <- sort <$> asList c
  let
    loop :: Int -> IO ()
    loop ((< n) -> False) = return ()
    loop i = do
      c' <- getNth cvec i
      cls' <- sort <$> asList c'
      when (cls' == cls) $ errorWithoutStackTrace "reinsert a same clause"
      loop (i + 1)
  loop 0
