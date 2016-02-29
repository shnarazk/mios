{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , MultiParamTypeClasses
  , TypeFamilies
  , UnboxedTuples
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Basic abstract data types used throughout the code.
module SAT.Solver.Mios.Types
       (
         -- Abstract interfaces
         ContainerLike (..)
       , VectorLike (..)
         -- * misc function
       , Var
       , bottomVar
       , Lit
       , bottomLit
       , newLit
       , var
       , index
       , index2lit
       , LBool
       , lbool
       , lFalse
       , lTrue
       , lBottom
       , VarOrder (..)
         -- * CNF
       , CNFDescription (..)
       )
       where

import GHC.Exts (Int(..))
import GHC.Prim
import qualified Data.Vector.Unboxed.Mutable as UV

-- | Public interface as /Container/
class ContainerLike s t | s -> t where
  -- * Size operations
  -- | erases all elements in it
  clear :: s -> IO ()
  clear = error "no default method for clear"
  -- * Debug
  -- | dump the contents
  dump :: Show t => String -> s -> IO String
  dump msg _ = error $ msg ++ ": no defalut method for dump"
  -- | get raw data
  asVector :: s -> UV.IOVector Int
  asVector = error "asVector undefined"
  -- | converts into a list
  asList :: s -> IO [t]
  asList = error "asList undefined"
  {-# MINIMAL dump #-}

-- | The vector data type can push a default constructed element by the 'push` method
-- with no argument. The 'moveTo' method will move the contents of a vector to another
-- vector in constant time, crearing the source vector.
class ContainerLike v t => VectorLike v t | v -> t where
  -- * Constructors
  -- | returns a /n/ length uninitialized new vector
  newVec :: Int -> IO v
  newVec = error "newVecSized undefined"
  -- | returns a /n/ length nev vector whose elements are set to the 2nd arg
  newVecWith :: Int -> t -> IO v
  newVecWith = error "newVecWith undefined"
  -- * Conversion
  -- | converts from @list :: [t]@ in a monadic context
  newFromList :: [t] -> IO v
  newFromList = error "newFromList undefined"
  -- * Vector interface
  -- | get the value at /n/-th field of the vector
  getAt :: Int -> v -> IO t
  getAt _ _ = error "getAt undefined"
  -- | set an value to the /n/-th field of the vector
  setAt :: Int -> v -> t -> IO ()
  setAt _ _ _ = error "setAt undefined"
  -- | update the /n/-th field of the vector
  modifyAt :: Int -> v -> (t -> t) -> IO ()
  modifyAt _ _ _ = error "modifyAt undefined"
  {-# MINIMAL newVec #-}

-- | Pointer-based implementation of "equality"
--
-- __Note:__ this requires strict evaluation; use @BangPatterns@
--
-- >>> let x = [2,3]
-- >>> let y = [2,3]
-- >>> let z = x
-- >>> let z' = z in print =<< sequence [x <==> x, x <==> y, x <==> z, x <==> z']
-- [True, False, True, True]
--
-- (<==>) :: a -> a -> IO Bool
-- (<==>) !a !b = (==) <$> makeStableName a <*> makeStableName b
-- (<==>) !x !y = return $! x `seq` y `seq` tagToEnum# (reallyUnsafePtrEquality# x y)

-- | represents "Var"
type Var = Int

-- | Special constant in 'Var' (p.7)
bottomVar :: Var
bottomVar = I# 0#

-- | The literal data has an 'index' method which converts the literal to
-- a "small" integer suitable for array indexing. The 'var'  method returns
-- the underlying variable of the literal, and the 'sign' method if the literal
-- is signed (False for /x/ and True for /-x/).
type Lit = Int

-- | Special constant in 'Lit' (p.7)
bottomLit :: Lit
bottomLit = I# 0#

-- | converts "Var" into 'Lit'
newLit :: Var -> Lit
newLit = error "newLit undefined"

-- sign :: l -> Bool

-- | converts 'Lit' into 'Var'
{-# INLINE var #-}
var :: Lit -> Var
var = abs

-- | converts 'Lit' into valid 'Int'
-- folding @Lit = [ -N, -N + 1  .. -1] ++ [1 .. N]@,
-- to @[0 .. 2N - 1]
{-# INLINE index #-}
index :: Lit -> Int
index (I# l#) = if tagToEnum# (0# <# l#) then I# (2# *# (l# -# 1#)) else I# (-2# *# l# -# 1#)

-- | revese convert to 'Lit' from index
{-# INLINE index2lit #-}
index2lit :: Int -> Int
index2lit (I# n#) =
  case quotRemInt# n# 2# of
   (# q#, 0# #) -> I# (q# +# 1#)
   (# q#, _ #) -> I# (negateInt# (q# +# 1#))

-- index2lit (I# n#) = (div n 2 + 1) * if odd n then -1 else 1

-- | Lifted Boolean domain (p.7) that extends 'Bool' with "⊥" means /undefined/
type LBool = Int

-- | converts 'Bool' into 'LBool'
{-# INLINE lbool #-}
lbool :: Bool -> LBool
lbool True = lTrue
lbool False = lFalse

-- | A contant representing False
lFalse:: LBool
lFalse = I# -1#

-- | A constant representing True
lTrue :: LBool
lTrue = I# 1#

-- | A constant for "undefined"
lBottom :: LBool
lBottom = I# 0#

-- | Assisting ADT for the dynamic variable ordering of the solver.
-- The constructor takes references to the assignment vector and the activity
-- vector of the solver. The method 'select' will return the unassigned variable
-- with the highest activity.
class VarOrder o where
  -- | constructor
  newVarOrder :: (VectorLike v1 Bool, VectorLike v2 Double) => v1 -> v2 -> IO o
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
