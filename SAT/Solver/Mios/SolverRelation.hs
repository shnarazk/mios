{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , RecordWildCards
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | define 'Solver'and 'BoolConstraint'
--
-- For a standard SAT-problem, the interface is used in the following way:
-- Variables are introduced by calling 'newVar'. From these variables,
-- clauses are built and added by 'addClause'. Trivial conflicts, such as
-- two unit clauses @{x}@ and @{!x}@ being added, can be detected by
-- 'addClause', in which case it returns @False@. From this point on, the
-- solver sate is undefined and must not be used further. If no such
-- trivial conflict is detected during the clause insertion phase, 'solve'
-- is called with an empty list of assumptions. It returns @False@ if the
-- problem is /unsatisfiable/, and @True@ if it is /satisfiable/, in which
-- case the model can be read from the public vector 'model'.
--
-- The 'simplifyDB' method cab be used before calling 'solve' to simplify
-- the set of problem constraints (often called the /constraint database/).
-- In our implementation, 'simplifyDB' will first propagate all unit
-- information, then remove all satisfied constraints. As for 'addClause',
-- the simplifier can sometimes detect a conflict, in which case @False@ is
-- returned and the solver state is, again, undefined and must not be used
-- further.
module SAT.Solver.Mios.SolverRelation
       (
         SolverState (..)
       , BoolConstraint (..)
       )
       where
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Clause
import SAT.Solver.Mios.WatchList

-- | __Fig. 3.(p.9)__
-- Small helper methods of 'Solver'. for instance, `nLearnts` returns the number
-- of learnt clauses.
class SolverState s where
 -- | returns the number of 'Var'
 nVars         :: s -> IO Int
 -- | returns the number of current assigments
 nAssigns      :: s -> IO Int
 -- | returns the number of constraints (clauses)
 nConstraints  :: s -> IO Int
 -- | returns the number of learnt clauses
 nLearnts      :: s -> IO Int
 -- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Var'
 valueVar         :: s -> Var -> IO Int
 -- | returns the assignment (:: 'LBool' = @[-1, 0, -1]@) from 'Lit'
 valueLit      :: s -> Lit -> IO Int
 -- | returns decisionLevel
 decisionLevel :: s -> IO Int
 -- | returns an everything-is-initialized solver from the argument
 setInternalState :: s -> Int -> IO s

-- | - 4.2 Constraints
--
-- __Constructor.__ The 'constructor' may only be called at the top-level.
-- It must create and add the constraint to appropriate watcher lists
-- after enqueuing any unit information derivable under the current
-- top-level assignment. Should a conflict arise, this must be
-- communicated to the caller.
class (SolverState s) => BoolConstraint s c where
  -- | __Remove.__ The 'remove' method supplants the destructor by receiving
  -- the solver state as a parameter. It should dispose the constraint and
  -- remove it from the watcher lists.
  remove :: c -> s -> IO ()

  -- | __Propagate.__ The 'propagateLit' method is called if the constraint is found
  -- in a watcher list during propagation of unit information /p/. The constraint
  -- is removed from the list and is required to insert itself into a new or
  -- the same watcher list. Any unit information derivable as a consequence of /p/
  -- should enqueued. If successful, @True@ is returned; if a conflict is detected,
  -- @False@ is returned. The constraint may add itself to the undo list of @var(p)@
  -- if it needs to be updated when /p/ becomes unbound.
  propagateLit :: c -> s -> Lit -> IO Bool

  -- | __Simplify.__ At the top-level, a constraint may be given the opportunity to
  -- simplify its representation (returns @False@) or state that the constraint is
  -- satisfied under the current assignment and can be removed (returns @True@).
  -- A constraint must /not/ be simplifiable to produce unit information or to be
  -- conflicting; in that case the propagation has not been correctly defined.
  simplify :: c -> s -> IO Bool
  -- defaults to return false
  simplify _ _ = return False

  -- | __Undo.__ During backtracking, this method is called if the constaint added itself
  -- to the undo list of /var(p)/ in 'propagateLit'.The current variable assignments are
  -- guaranteed to be identical to that of the moment before 'propagateLit' was called.
  undoConstraint :: c -> s -> Lit -> IO ()
  -- defaults to do nothing
  undoConstraint _ _ _ = return ()

  -- | __Calculate Reason.__ Thi method is given a literal /p/ and an empty vector.
  -- The constraint is the /reason/ for /p/ being true, that is, during
  -- propagation, the current constraint enqueued /p/. The received vector is
  -- extended to include a set of assignments (represented as literals)
  -- implying /p/ The current variable assignments are guaranteed to be
  -- identical to that of the moment before the constraint propagated /p/.
  -- The literal /p/ is also allowed to be the special constant 'bottomLit'
  -- in which case the reason for the clause being conflicting should be
  -- returned through the vector.
  --
  -- 'calcReason` is invoked from 'analyze'
  calcReason :: c -> s -> Lit -> VecOf Lit -> IO ()
