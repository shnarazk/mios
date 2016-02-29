{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Clause
module SAT.Solver.Mios.Clause
       (
         Clause (..)
       , getNthLiteral
       , setNthLiteral
       , shrinkClause
       , newClauseFromVec
       , sizeOfClause
       )
       where

import GHC.Prim (tagToEnum#, reallyUnsafePtrEquality#)
import Data.List (intercalate)
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..), Lit)
import SAT.Solver.Mios.Internal (FixedVecInt, getNthInt, setNthInt, DoubleSingleton, getDouble, newDouble)

-- | __Fig. 7.(p.11)__
-- clause, null, binary clause.
-- This matches both of @Clause@ and @GClause@ in MiniSat
-- TODO: GADTs is better?
data Clause = Clause
              {
                learnt     :: Bool            -- ^ whether this is a learnt clause
              , activity   :: DoubleSingleton -- ^ activity of this clause
              , lits       :: FixedVecInt     -- ^ which this clause consists of
              }
  | BinaryClause Int            -- binary clause consists of only a propagating literal
  | NullClause                  -- as null pointer

-- | The equality on 'Clause' is defined by pointer equivalence.
instance Eq Clause where
  {-# SPECIALIZE INLINE (==) :: Clause -> Clause -> Bool #-}
  (==) x y = x `seq` y `seq` tagToEnum# (reallyUnsafePtrEquality# x y)

instance Show Clause where
  show NullClause = "NullClause"
  show _ = "a clause"

-- | supports a restricted set of 'ContainerLike' methods
instance ContainerLike Clause Lit where
  dump mes NullClause = return $ mes ++ "[Null]"
  dump mes Clause{..} = do
    a <- show <$> getDouble activity
    (len:ls) <- asList lits
    return $ mes ++ "C" ++ show len ++ "{" ++ intercalate "," [show learnt, a, show (take len ls)] ++ "}"
  {-# SPECIALIZE INLINE asList :: Clause -> IO [Int] #-}
  asList NullClause = return []
  asList Clause{..} = do
    (n : ls)  <- asList lits
    return $ take n ls

-- | returns True if it is a 'BinaryClause'
isLit :: Clause -> Bool
isLit (BinaryClause _) = True
isLit _ = False

-- | coverts a binary clause to normal clause in order to reuse map-on-literals-in-a-clause codes
liftToClause :: Clause -> Clause
liftToClause (BinaryClause _) = error "So far I use generic function approach instead of lifting"

-- | returns the nth literal in a clause
-- Valid range: [0 .. sizeOfClause c - 1]
-- | If the given clause is a BinaryClause, returns the literal, ignorirng the index.
{-# INLINE getNthLiteral #-}
getNthLiteral :: Int -> Clause -> IO Int
getNthLiteral !i Clause{..} = getNthInt (1 + i) lits
getNthLiteral _ (BinaryClause l) = return l

{-# INLINE setNthLiteral #-}
setNthLiteral :: Int -> Clause -> Int -> IO ()
setNthLiteral !i Clause{..} x = setNthInt (1 + i) lits x

{-# INLINABLE shrinkClause #-}
shrinkClause :: Int -> Clause -> IO ()
shrinkClause !n Clause{..} = setNthInt 0 lits . subtract n =<< getNthInt 0 lits

{-# INLINE newClauseFromVec #-}
newClauseFromVec :: Bool -> FixedVecInt -> IO Clause
newClauseFromVec l vec = Clause l <$> newDouble 0 <*> return vec

-- | returns the numeber of literals in a clause, even if the given clause is a binary clause
{-# INLINE sizeOfClause #-}
sizeOfClause :: Clause -> IO Int
sizeOfClause (BinaryClause _) = return 1
sizeOfClause !c = getNthInt 0 (lits c)
