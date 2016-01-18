module SAT.Solver.Mios.Validator
       (
         validate
       )
       where

import Data.Foldable (toList)
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.ClauseList
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Solver

-- | validate the assignment even if the implementation of 'Solver' is wrong; we re-implement some functions here.
validate :: Traversable t => Solver -> t Lit -> IO Bool
validate s asg = do
  assignment <- newVec $ 1 + nVars s
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
      s <- satisfied l
      if s then return True else satAny ls
    -- traverse all clauses in 'constrs'
    loop :: Clause -> IO Bool
    loop pre = do
      c <- nextClause (constrs s) pre
      if c == NullClause
        then return True
        else do
            s <- satAny =<< asList c
            if s then loop c else return False
  mapM_ inject (toList asg)
  loop NullClause
