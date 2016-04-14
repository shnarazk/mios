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
       , isLit
       , getLit
       , shrinkClause
       , newClauseFromVec
       , sizeOfClause
       )
       where

import Control.Monad (forM_)
import GHC.Prim (tagToEnum#, reallyUnsafePtrEquality#)
import qualified Data.Vector.Unboxed.Mutable as UV
import Data.List (intercalate)
import SAT.Solver.Mios.Types

-- | __Fig. 7.(p.11)__
-- clause, null, binary clause.
-- This matches both of @Clause@ and @GClause@ in MiniSat
-- TODO: GADTs is better?
data Clause = Clause
              {
                learnt   :: !Bool            -- ^ whether this is a learnt clause
              , activity :: !DoubleSingleton -- ^ activity of this clause
              , lbd    :: !IntSingleton      -- ^ storing the LBD; values are computed in Solver
              , lits     :: !Vec             -- ^ which this clause consists of
              }
  | BinaryClause Lit                        -- binary clause consists of only a propagating literal
  | NullClause                              -- as null pointer

-- | The equality on 'Clause' is defined by pointer equivalence.
instance Eq Clause where
  {-# SPECIALIZE INLINE (==) :: Clause -> Clause -> Bool #-}
  (==) x y = x `seq` y `seq` tagToEnum# (reallyUnsafePtrEquality# x y)

instance Show Clause where
  show NullClause = "NullClause"
  show _ = "a clause"

-- | supports a restricted set of 'VectorFamily' methods
instance VectorFamily Clause Lit where
  dump mes NullClause = return $ mes ++ "Null"
  dump mes Clause{..} = do
    a <- show <$> getDouble activity
    (len:ls) <- asList lits
    return $ mes ++ "C" ++ show len ++ "{" ++ intercalate "," [show learnt, a, show . map lit2int . take len $ ls] ++ "}"
  {-# SPECIALIZE INLINE asVec :: Clause -> Vec #-}
  asVec Clause{..} = UV.unsafeTail lits
  {-# SPECIALIZE INLINE asList :: Clause -> IO [Int] #-}
  asList NullClause = return []
  asList Clause{..} = do
    (n : ls)  <- asList lits
    return $ take n ls

-- | returns True if it is a 'BinaryClause'
-- FIXME: this might be discarded in minisat 2.2
isLit :: Clause -> Bool
isLit (BinaryClause _) = True
isLit _ = False

-- | returns the literal in a BinaryClause
-- FIXME: this might be discarded in minisat 2.2
getLit :: Clause -> Lit
getLit (BinaryClause x) = x

-- | coverts a binary clause to normal clause in order to reuse map-on-literals-in-a-clause codes
liftToClause :: Clause -> Clause
liftToClause (BinaryClause _) = error "So far I use generic function approach instead of lifting"

{-# INLINABLE shrinkClause #-}
shrinkClause :: Int -> Clause -> IO ()
shrinkClause !n Clause{..} = setNth lits 0 . subtract n =<< getNth lits 0

-- | copies /vec/ and return a new 'Clause'
-- Since 1.0.100 DIMACS reader should use a scratch buffer allocated statically.
{-# INLINE newClauseFromVec #-}
newClauseFromVec :: Bool -> Vec -> IO Clause
newClauseFromVec l vec = do
  n <- getNth vec 0
  v <- newVec $ n + 1
  forM_ [0 .. n] $ \i -> setNth v i =<< getNth vec i
  Clause l <$> newDouble 0 <*> newInt n <*> return v

-- | returns the number of literals in a clause, even if the given clause is a binary clause
{-# INLINE sizeOfClause #-}
sizeOfClause :: Clause -> IO Int
sizeOfClause (BinaryClause _) = return 1
sizeOfClause !c = getNth (lits c) 0
