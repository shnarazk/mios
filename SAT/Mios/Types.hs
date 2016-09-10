{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Safe #-}

-- | Basic data types used throughout mios.
module SAT.Mios.Types
       (
         module SAT.Mios.Vec
         -- *  Variable
       , Var
       , bottomVar
       , int2var
         -- * Internal encoded Literal
       , Lit
       , lit2int
       , int2lit
       , bottomLit
--       , newLit
       , positiveLit
       , lit2var
       , var2lit
       , negateLit
         -- * Assignment on the lifted Bool domain
--       , LiftedBool (..)
--       , lbool
       , lFalse
       , lTrue
       , lBottom
       , VarOrder (..)
         -- * CNF
       , CNFDescription (..)
         -- * Solver Configuration
       , MiosConfiguration (..)
       , defaultConfiguration
       )
       where

import Data.Bits
import SAT.Mios.Vec

-- | represents "Var"
type Var = Int

-- | Special constant in 'Var' (p.7)
bottomVar :: Var
bottomVar = 0

-- | converts a usual Int as literal to an internal 'Var' presentation
--
-- >>> int2var 1
-- 1  -- the first literal is the first variable
-- >>> int2var 2
-- 2  -- literal @2@ is variable 2
-- >>> int2var (-2)
-- 2 -- literal @-2@ is corresponding to variable 2
--
{-# INLINE int2var #-}
int2var = abs

-- | The literal data has an 'index' method which converts the literal to
-- a "small" integer suitable for array indexing. The 'var'  method returns
-- the underlying variable of the literal, and the 'sign' method if the literal
-- is signed (False for /x/ and True for /-x/).
type Lit = Int

-- | Special constant in 'Lit' (p.7)
bottomLit :: Lit
bottomLit = 0

{-
-- | converts "Var" into 'Lit'
newLit :: Var -> Lit
newLit = error "newLit undefined"
-}

-- | returns @True@ if the literal is positive
{-# INLINE positiveLit #-}
positiveLit :: Lit -> Bool
positiveLit = even

-- | negates literal
--
-- >>> negateLit 2
-- 3
-- >>> negateLit 3
-- 2
-- >>> negateLit 4
-- 5
-- >>> negateLit 5
-- 4
{-# INLINE negateLit #-}
negateLit :: Lit -> Lit
negateLit l = complementBit l 0 -- if even l then l + 1 else l - 1

----------------------------------------
----------------- Var
----------------------------------------

-- | converts 'Lit' into 'Var'
--
-- >>> lit2var 2
-- 1
-- >>> lit2var 3
-- 1
-- >>> lit2var 4
-- 2
-- >>> lit2var 5
-- 2
{-# INLINE lit2var #-}
lit2var :: Lit -> Var
lit2var !n = shiftR n 1

-- | converts a 'Var' to the corresponing literal
--
-- >>> var2lit 1 True
-- 2
-- >>> var2lit 1 False
-- 3
-- >>> var2lit 2 True
-- 4
-- >>> var2lit 2 False
-- 5
{-# INLINE var2lit #-}
var2lit :: Var -> Bool -> Lit
var2lit !v True = shiftL v 1
var2lit !v _ = shiftL v 1 + 1

----------------------------------------
----------------- Int
----------------------------------------

-- | converts 'Int' into 'Lit' as @lit2int . int2lit == id@
--
-- >>> int2lit 1
-- 2
-- >>> int2lit (-1)
-- 3
-- >>> int2lit 2
-- 4
-- >>> int2lit (-2)
-- 5
--
{-# INLINE int2lit #-}
int2lit :: Int -> Lit
int2lit n
  | 0 < n = 2 * n
  | otherwise = -2 * n + 1

-- | converts `Lit' into 'Int' as @int2lit . lit2int == id@
--
-- >>> lit2int 2
-- 1
-- >>> lit2int 3
-- -1
-- >>> lit2int 4
-- 2
-- >>> lit2int 5
-- -2
{-# INLINE lit2int #-}
lit2int :: Lit -> Int
lit2int l = case divMod l 2 of
  (i, 0) -> i
  (i, _) -> - i

{-
-- | Lifted Boolean domain (p.7) that extends 'Bool' with "⊥" means /undefined/
-- design note: _|_ should be null = 0; True literals are coded to even numbers. So it should be 2.
data LiftedBool = Bottom | LFalse | LTrue
  deriving (Bounded, Eq, Ord, Read, Show)

instance Enum LiftedBool where
  {-# SPECIALIZE INLINE toEnum :: Int -> LiftedBool #-}
  toEnum        1 = LTrue
  toEnum     (-1) = LFalse
  toEnum        _ = Bottom
  {-# SPECIALIZE INLINE fromEnum :: LiftedBool -> Int #-}
  fromEnum Bottom = 0
  fromEnum LFalse = 1
  fromEnum LTrue  = 2

-- | converts 'Bool' into 'LBool'
{-# INLINE lbool #-}
lbool :: Bool -> LiftedBool
lbool True = LTrue
lbool False = LFalse
-}

-- | /FALSE/ on the Lifted Bool domain
lFalse:: Int
lFalse = -1

-- | /TRUE/ on the Lifted Bool domain
lTrue :: Int
lTrue = 1

-- | /UNDEFINED/ on the Lifted Bool domain
lBottom :: Int
lBottom = 0

-- | Assisting ADT for the dynamic variable ordering of the solver.
-- The constructor takes references to the assignment vector and the activity
-- vector of the solver. The method 'select' will return the unassigned variable
-- with the highest activity.
class VarOrder o where
{-
  -- | constructor
  newVarOrder :: (VecFamily v1 Bool, VecFamily v2 Double) => v1 -> v2 -> IO o
  newVarOrder _ _ = error "newVarOrder undefined"

  -- | Called when a new variable is created.
  newVar :: o -> IO Var
  newVar = error "newVar undefined"
-}
  -- | should be called when a variable has increased in activity.
  update :: o -> Var -> IO ()
  update _  = error "update undefined"
{-
  -- | should be called when all variables have been assigned.
  updateAll :: o -> IO ()
  updateAll = error "updateAll undefined"
-}
  -- | should be called when a variable becomes unbound (may be selected again).
  undo :: o -> Var -> IO ()
  undo _ _  = error "undo undefined"

  -- | returns a new, unassigned var as the next decision.
  select :: o -> IO Var
  select    = error "select undefined"

-- | Misc information on a CNF
data CNFDescription = CNFDescription
  {
    _numberOfVariables :: !Int           -- ^ the number of variables
  , _numberOfClauses :: !Int             -- ^ the number of clauses
  , _pathname :: Maybe FilePath          -- ^ given filename
  }
  deriving (Eq, Ord, Show)

-- | solver's parameters; random decision rate was dropped.
data MiosConfiguration = MiosConfiguration
                         {
                           variableDecayRate  :: !Double  -- ^ decay rate for variable activity
--                         , clauseDecayRate    :: !Double  -- ^ decay rate for clause activity
                         }

-- | dafault configuration
--
-- * Minisat-1.14 uses @(0.95, 0.999, 0.2 = 20 / 1000)@.
-- * Minisat-2.20 uses @(0.95, 0.999, 0)@.
-- * Gulcose-4.0  uses @(0.8 , 0.999, 0)@.
-- * Mios-1.2     uses @(0.95, 0.999, 0)@.
--
defaultConfiguration :: MiosConfiguration
defaultConfiguration = MiosConfiguration 0.95 {- 0.999 -} {- 0 -}
