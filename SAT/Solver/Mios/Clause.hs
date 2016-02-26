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
-- Clause
data Clause = Clause
              {
                learnt     :: Bool            -- ^ whether this is a learnt clause
              , activity   :: DoubleSingleton -- ^ activity of this clause
              , lits       :: FixedVecInt     -- ^ which this clause consists of
              }
            | NullClause

-- | __Version 0.6__
--
-- The equality on 'Clause' is defined by pointer equivalencce.
instance Eq Clause where
  {-# SPECIALIZE INLINE (==) :: Clause -> Clause -> Bool #-}
  (==) x y = x `seq` y `seq` tagToEnum# (reallyUnsafePtrEquality# x y)

instance Show Clause where
  show NullClause = "NullClause"
  show _ = "a clause"

-- | supports a restricted set of 'ContainerLike' methods
instance ContainerLike Clause Lit where
  dump mes NullClause = return $ "NullClause" ++ if mes == "" then "" else "(" ++ mes ++ ")"
  dump mes Clause{..} = do
    a <- show <$> getDouble activity
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
newClauseFromVec l vec = Clause l <$> newDouble 0 <*> return vec

{-# INLINE sizeOfClause #-}
sizeOfClause :: Clause -> IO Int
sizeOfClause !c = getNthInt 0 (lits c)
