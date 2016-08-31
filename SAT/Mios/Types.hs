{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Basic data types used throughout mios.
module SAT.Mios.Types
       (
         -- Singleton
         module SAT.Mios.Data.Singleton
         -- Fixed Unboxed Mutable Int Vector
       , module SAT.Mios.Data.Vec
         -- Abstract interfaces
       , VectorFamily (..)
         -- *  Variable
       , Var
       , bottomVar
       , int2var
         -- * Internal encoded Literal
       , Lit
       , lit2int
       , int2lit
       , bottomLit
       , newLit
       , positiveLit
       , lit2var
       , var2lit
       , negateLit
         -- * Assignment
       , LiftedBool (..)
       , lbool
       , lFalse
       , lTrue
       , lBottom
       , VarOrder (..)
         -- * CNF
       , CNFDescription (..)
       )
       where

import Control.Monad (forM)
import Data.Bits
import qualified Data.Vector.Unboxed.Mutable as UV
import SAT.Mios.Data.Singleton
import SAT.Mios.Data.Vec

-- | Public interface as /Container/
class VectorFamily s t | s -> t where
  -- * Size operations
  -- | erases all elements in it
  clear :: s -> IO ()
  clear = error "no default method for clear"
  -- * Debug
  -- | dump the contents
  dump :: Show t => String -> s -> IO String
  dump msg _ = error $ msg ++ ": no defalut method for dump"
  -- | get a raw data
  asVec :: s -> UV.IOVector Int
  asVec = error "asVector undefined"
  -- | converts into a list
  asList :: s -> IO [t]
  asList = error "asList undefined"
  {-# MINIMAL dump #-}

-- | provides 'clear' and 'size'
instance VectorFamily Vec Int where
  clear = error "Vec.clear"
  {-# SPECIALIZE INLINE asList :: Vec -> IO [Int] #-}
  asList v = forM [0 .. UV.length v - 1] $ UV.unsafeRead v
  dump str v = (str ++) . show <$> asList v
  {-# SPECIALIZE INLINE asVec :: Vec -> Vec #-}
  asVec = id

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

-- | converts "Var" into 'Lit'
newLit :: Var -> Lit
newLit = error "newLit undefined"

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
negateLit !l = complementBit l 0 -- if even l then l + 1 else l - 1

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

-- | A contant representing False
lFalse:: Int
lFalse = -1

-- | A constant representing True
lTrue :: Int
lTrue = 1

-- | A constant for "undefined"
lBottom :: Int
lBottom = 0

-- | Assisting ADT for the dynamic variable ordering of the solver.
-- The constructor takes references to the assignment vector and the activity
-- vector of the solver. The method 'select' will return the unassigned variable
-- with the highest activity.
class VarOrder o where
  -- | constructor
  newVarOrder :: (VectorFamily v1 Bool, VectorFamily v2 Double) => v1 -> v2 -> IO o
  newVarOrder _ _ = error "newVarOrder undefined"

  -- | Called when a new variable is created.
  newVar :: o -> IO Var
  newVar = error "newVar undefined"

  -- | Called when variable has increased in activity.
  update :: o -> Var -> IO ()
  update _  = error "update undefined"

  -- | Called when all variables have been assigned new activities.
  updateAll :: o -> IO ()
  updateAll = error "updateAll undefined"

  -- | Called when variable is unbound (may be selected again).
  undo :: o -> Var -> IO ()
  undo _ _  = error "undo undefined"

  -- | Called to select a new, unassigned variable.
  select :: o -> IO Var
  select    = error "select undefined"

-- | misc information on CNF
data CNFDescription = CNFDescription
  {
    _numberOfVariables :: !Int           -- ^ number of variables
  , _numberOfClauses :: !Int             -- ^ number of clauses
  , _pathname :: Maybe FilePath          -- ^ given filename
  }
  deriving (Eq, Ord, Show)
