{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , UnboxedTuples
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- |
module SAT.Solver.Mios.Clause
       (
         Clause (..)
       , ClausePointer
       , derefClausePointer
       , newClausePointer
       , setClausePointer
       , getNthLiteral
       , setNthLiteral
       , shrinkClause
       , newClauseFromVec
       , selectWatcher
       , sizeOfClause
       , VecOfClause (..)
       , sizeOfClauses
       , getNthClause
       , setNthClause
       )
       where

import GHC.Prim (tagToEnum#, reallyUnsafePtrEquality#)
import Data.IORef
import Data.List (intercalate)
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..), Lit)
import SAT.Solver.Mios.Internal (FixedVecInt, FixedVecOf(..), getNthInt, setNthInt)
-- import qualified Data.Vector.Storable.Mutable as SM
-- import SAT.Solver.Mios.Implementation.IntSingleton

{-
import Foreign.StablePtr

newtype ClausePointer = ClausePointer (SM.IOVector (StablePtr Clause))

newClausePointer :: Clause -> IO ClausePointer
newClausePointer !c = do
  v <- SM.new 1
  !p <- newStablePtr $! c
  SM.unsafeWrite v 0 $! p
  return $ ClausePointer v

{-# INLINE setClausePointer #-}
setClausePointer :: ClausePointer -> Clause -> IO ()
setClausePointer (ClausePointer v) NullClause = do
  !x <- newStablePtr NullClause
  SM.unsafeWrite v 0 $! x
setClausePointer (ClausePointer v) c = do
  !x <- newStablePtr c
  -- z!x <- SM.unsafeRead v' 0
  SM.unsafeWrite v 0 $! x

{-# INLINE derefClausePointer #-}
derefClausePointer :: ClausePointer -> IO Clause
derefClausePointer (ClausePointer v) = deRefStablePtr =<< SM.unsafeRead v 0
-}

type ClausePointer = IORef Clause

{-# INLINE newClausePointer #-}
newClausePointer :: Clause -> IO ClausePointer
newClausePointer = newIORef

{-# INLINE setClausePointer #-}
setClausePointer :: ClausePointer -> Clause -> IO ()
setClausePointer = writeIORef

{-# INLINE derefClausePointer #-}
derefClausePointer :: ClausePointer -> IO Clause
derefClausePointer = readIORef

-- | __Fig. 7.(p.11)__
-- Clause
data Clause = Clause
              {
                learnt     :: Bool           -- ^ whether this is a learnt clause
              , activity   :: IORef Double   -- ^ activity of this clause
              , nextWatch1 :: ClausePointer -- ^ the next clause that watches lits[0]
              , nextWatch2 :: ClausePointer -- ^ the next clause that watches lits[1]
              , nextOf     :: ClausePointer -- ^ the next generated clause
              , lits       :: FixedVecInt    -- ^ which this clause consists of
              }
            | NullClause

-- | __Version 0.6__
--
-- The equality on 'Clause' is defined by pointer equivalencce.
instance Eq Clause where
  (==) x y = x `seq` y `seq` tagToEnum# (reallyUnsafePtrEquality# x y)

instance Show Clause where
  show NullClause = "NullClause"
  show _ = "a clause"

-- | supports a restricted set of 'ContainerLike' methods
instance ContainerLike Clause Lit where
  dump mes NullClause = return $ "NullClause" ++ if mes == "" then "" else "(" ++ mes ++ ")"
  dump mes Clause{..} = do
    a <- show <$> readIORef activity
    (len:ls) <- asList lits
    return $ mes ++ "C" ++ show len ++ "{" ++ intercalate "," [show learnt, a, show (take len ls)] ++ "}"
  {-# SPECIALIZE INLINE asList :: Clause -> IO [Int] #-}
  asList NullClause = return []
  asList Clause{..} = do
    (n : ls)  <- asList lits
    return $ take n ls

{-# INLINE getNthLiteral #-}
getNthLiteral :: Int -> Clause -> IO Int
getNthLiteral !i Clause{..} = getNthInt (1 + i) lits

{-# INLINE setNthLiteral #-}
setNthLiteral :: Int -> Clause -> Int -> IO ()
setNthLiteral !i Clause{..} x = setNthInt (1 + i) lits x

{-# INLINABLE shrinkClause #-}
shrinkClause :: Int -> Clause -> IO ()
shrinkClause !n Clause{..} = setNthInt 0 lits . subtract n =<< getNthInt 0 lits

{-# INLINE newClauseFromVec #-}
newClauseFromVec :: Bool -> FixedVecInt -> IO Clause
newClauseFromVec l vec = do
  act <- newIORef 0
  n1 <- newClausePointer NullClause
  n2 <- newClausePointer NullClause
  n <- newClausePointer NullClause
  return $! Clause l act n1 n2 n vec

-- | returns /the pointer/ to the next clause watching /the lit/
{-# INLINE selectWatcher #-}
selectWatcher :: Lit -> Clause -> IO ClausePointer
selectWatcher !l !c = do
  !l0 <- getNthInt 1 $ lits c
  return $! if l0 == negate l then nextWatch1 c else nextWatch2 c

newtype VecOfClause = VecOfClause
              {
                clauses :: IORef [Clause] -- ^ reference pointer to the data
              }

-- | provides 'clear' and 'size'
instance ContainerLike VecOfClause Clause where
  clear VecOfClause{..} = writeIORef clauses []
  asList VecOfClause{..} = readIORef clauses
  dump str VecOfClause{..} = (str ++) . show <$> readIORef clauses

{-# INLINE sizeOfClauses #-}
sizeOfClauses :: VecOfClause -> IO Int
sizeOfClauses VecOfClause{..} = length <$> readIORef clauses

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike VecOfClause Clause where
  -- * Constructors
  newVec n = VecOfClause <$> newIORef (replicate n undefined)
  newVecWith n x = VecOfClause <$> newIORef (replicate n x)
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: VecOfClause -> Int -> IO Clause #-}
  (.!) VecOfClause{..} !n = (!! n) <$> readIORef clauses
  {-# SPECIALIZE INLINE setAt :: VecOfClause -> Int -> Clause -> IO () #-}
  setAt VecOfClause{..} !n x = do
    l <- readIORef clauses
    writeIORef clauses $! take n l ++ (x : drop (n + 1) l)
  -- * Conversion
  newFromList l = VecOfClause <$> newIORef l

-- sortVecClause :: (Ord b) => (Clause -> IO b) -> VecOfClause -> IO ()
-- sortVecClause f VecOfClause{..} = writeIORef clauses . map fst . sortOn snd =<< mapM (uncurry ((<$>) . (,)) . (id &&& f)) =<< readIORef clauses

{-# INLINE sizeOfClause #-}
sizeOfClause :: Clause -> IO Int
sizeOfClause !c = getNthInt 0 (lits c)

{-# INLINE getNthClause #-}
getNthClause :: Int -> FixedVecOf Clause -> IO Clause
getNthClause !i !(FixedVecOf fv) = MV.unsafeRead fv i

{-# INLINE setNthClause #-}
setNthClause :: Int -> FixedVecOf Clause -> Clause -> IO ()
setNthClause !i !(FixedVecOf fv) !c = MV.unsafeWrite fv i c
