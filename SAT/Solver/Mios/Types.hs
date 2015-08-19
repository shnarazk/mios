{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , MultiParamTypeClasses
  , TypeFamilies
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
       , QueueLike (..)
         -- * misc function
       , (<==>)
       , Var
       , bottomVar
       , Lit
       , bottomLit
       , newLit
       , var
       , index
       , LBool
       , lbool
       , lFalse
       , lTrue
       , lBottom
       , VarOrder (..)
       )
       where

import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed.Mutable as UV
import System.Mem.StableName

-- | Public interface as /Container/
class ContainerLike s where
  -- | erases all elements in it
  clear :: s -> IO ()
  clear = error "no default method for clear"
  -- | returns the numeber of its elements in a monadic context
  size :: s -> IO Int
  size = error "no default method for size"
  {-# MINIMAL size #-}

-- | The vector data type can push a default constructed element by the 'push` method
-- with no argument. The 'moveTo' method will move the contents of a vector to another
-- vector in constant time, crearing the source vector.
class ContainerLike v => VectorLike v t | v -> t where
  -- * Constructors
  -- | returns a new empty vector; no need to pickup an value
  emptyVec :: IO v
  emptyVec = error "emptyVec undefined"
  -- | returns a new (emply) vector
  newVec :: IO v
  newVec = error "newVec undefined"
  -- | returns a /n/ length uninitialized new vector
  newVecSized :: Int -> IO v
  newVecSized = error "newVecSized undefined"
  -- | returns a /n/ length nev vector whose elements are set to the 2nd arg
  newVecSizedWith :: Int -> t -> IO v
  newVecSizedWith = error "newVecSizedWith undefined"
  -- * Conversion
  -- | converts from @list :: [t]@ in a monadic context
  newFromList :: [t] -> IO v
  newFromList = error "newFromList undefined"
  -- | converts to a list (@:: [t]@) in a monadic context
  asList :: v -> IO [t]
  asList = error "asList undefined"
  -- * Size operations
  -- | deletes the last /n/ elements
  shrink :: Int -> v -> IO ()
  shrink = error "shrink undefined"
  -- | resizes to /n/ sized vector
  growTo :: v -> Int -> IO ()   -- (v `growTo`) n  :: OOPL style
  growTo = error "growTo undefined"
  -- | resizes to /n/ sized vector and store the 3rd value into the new places
  -- __Not in use__
  growToWith :: v -> Int -> IO ()
  growToWith = error "growToWith undefined"
  -- * Stack operations
  -- | deletes the last 'push'ed element and returns none.
  pop :: v -> IO ()
  pop = error "pop undefined"
  -- | add a default value into the tail.
  push' :: v -> IO ()
  push' = error "push' undefined"
  -- | add a given value into the tail.
  push :: v -> t -> IO ()
  push = error "push undefined"
  -- | returns the last 'push'ed element (not the first)
  lastE :: v -> IO t
  lastE = error "lastE undefined"
  -- | searchs an element and deletes its all occurrences.
  removeElem :: t -> v -> IO ()
  removeElem _ _ = error "no def removeElem"
  -- * Vector interface
  -- | accesss /n/th element from the 0-based vector
  (.!) :: v -> Int -> IO t
  (.!) = error "(.!) undefined"
  -- | set an value to the /n/-th field of the vector
  setAt :: v -> Int -> t -> IO ()
  setAt = error "setAt undefined"
  -- * Duplication
  -- | copies the vector itself of the 1st arg to one of the 2nd arg
  -- __Not in use__
  copyTo :: v -> v -> IO ()
  copyTo = error "copyTo undefined"
  -- | meves the vector itself of the 1st arg to one of the 2nd arg
  moveTo :: v -> v -> IO ()     -- Note: it should be O(1) !!
  moveTo = error "moveTo undefined"
  -- * Debug
  -- | check values of elements
  checkConsistency :: String -> v -> (t -> IO Bool) -> IO ()
  checkConsistency _ _ _ = return ()
  -- | returns a representative string (@:: String@) in a monadic context
  dump :: Show t => String -> v -> IO String
  dump msg _ = error $ msg ++ ": no defalut method for dump"
  {-# MINIMAL newVec, newVecSized, newVecSizedWith, growTo, shrink, pop, push, lastE, removeElem, (.!), setAt, moveTo #-}

-- | Public interface as "Queue"
class ContainerLike q => QueueLike q t | q -> t where
  -- | returns an empty queue
  newQueue :: IO q
  newQueue = error "newQueue undefined"
  -- | returns an empty queue
  growQueueSized :: Int -> q -> IO ()
  growQueueSized = error "newQueueSizd undefined"
  -- | inserts the 2nd arg into the trail
  insert :: q -> t -> IO ()
  insert = error "insert undefined"
  -- | returns the top element of this queue and delete it from this queue
  dequeue :: q -> IO t
  dequeue = error "dequeue undefined"
  {-# MINIMAL newQueue, insert, dequeue #-}

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
(<==>) :: a -> a -> IO Bool
(<==>) !a !b = (==) <$> makeStableName a <*> makeStableName b

-- | represents "Var"
type Var = Int

-- | Special constant in 'Var' (p.7)
bottomVar :: Var
bottomVar = 0

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

-- sign :: l -> Bool

-- | converts 'Lit' into 'Var'
var :: Lit -> Var
var = abs

-- | converts 'Lit' into valid 'Int'
-- folding @Lit = [ -N, -N + 1  .. -1] ++ [1 .. N]@,
-- to @[0 .. 2N - 1]
index :: Lit -> Int
index l@((< 0) -> True) = -2 * l - 1
index l = 2 * (l - 1)

-- | Lifted Boolean domain (p.7) that extends 'Bool' with "⊥" means /undefined/
type LBool = Int

-- | converts 'Bool' into 'LBool'
lbool :: Bool -> LBool
lbool True = lTrue
lbool False = lFalse

-- | A contant representing False
lFalse:: LBool
lFalse = -1

-- | A constant representing True
lTrue :: LBool
lTrue = 1

-- | A constant for "undefined"
lBottom :: LBool
lBottom = 0

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
