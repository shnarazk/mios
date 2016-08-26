{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Clause, supporting pointer-based equality
module SAT.Solver.Mios.Clause
       (
         Clause (..)
--       , isLit
--       , getLit
       , shrinkClause
       , newClauseFromVec
       , sizeOfClause
         -- * Vector of Clause
       , ClauseVector
       , newClauseVector
       , getNthClause
       , setNthClause
       , swapClauses
       )
       where

import Control.Monad (forM_)
import GHC.Prim (tagToEnum#, reallyUnsafePtrEquality#)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed.Mutable as UV
import Data.List (intercalate)
import SAT.Solver.Mios.Types

-- | __Fig. 7.(p.11)__
-- clause, null, binary clause.
-- This matches both of @Clause@ and @GClause@ in MiniSat
-- TODO: GADTs is better?
data Clause = Clause
              {
                learnt     :: !Bool            -- ^ whether this is a learnt clause
--              , rank       :: !IntSingleton    -- ^ goodness like LBD; computed in 'Ranking'
              , activity   :: !DoubleSingleton -- ^ activity of this clause
              , protected  :: !BoolSingleton   -- ^ protected from reduce
              , lits       :: !Vec             -- ^ which this clause consists of
              }
  | NullClause                              -- as null pointer
--  | BinaryClause Lit                        -- binary clause consists of only a propagating literal

-- | The equality on 'Clause' is defined with 'reallyUnsafePtrEquality'.
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

-- returns True if it is a 'BinaryClause'
-- FIXME: this might be discarded in minisat 2.2
-- isLit :: Clause -> Bool
-- isLit (BinaryClause _) = True
-- isLit _ = False

-- returns the literal in a BinaryClause
-- FIXME: this might be discarded in minisat 2.2
-- getLit :: Clause -> Lit
-- getLit (BinaryClause x) = x

-- coverts a binary clause to normal clause in order to reuse map-on-literals-in-a-clause codes
-- liftToClause :: Clause -> Clause
-- liftToClause (BinaryClause _) = error "So far I use generic function approach instead of lifting"

-- | copies /vec/ and return a new 'Clause'
-- Since 1.0.100 DIMACS reader should use a scratch buffer allocated statically.
{-# INLINE newClauseFromVec #-}
newClauseFromVec :: Bool -> Vec -> IO Clause
newClauseFromVec l vec = do
  n <- getNth vec 0
  v <- newVec $ n + 1
  forM_ [0 .. n] $ \i -> setNth v i =<< getNth vec i
  Clause l <$> {- newInt 0 <*> -} newDouble 0 <*> newBool False <*> return v

-- | returns the number of literals in a clause, even if the given clause is a binary clause
{-# INLINE sizeOfClause #-}
sizeOfClause :: Clause -> IO Int
-- sizeOfClause (BinaryClause _) = return 1
sizeOfClause !c = getNth (lits c) 0

-- | drop the last /N/ literals in a 'Clause' to eliminate unsatisfied literals
{-# INLINABLE shrinkClause #-}
shrinkClause :: Int -> Clause -> IO ()
shrinkClause n !c = modifyNth (lits c) (subtract n) 0

--------------------------------------------------------------------------------

-- | Mutable 'Clause' Vector
type ClauseVector = MV.IOVector Clause

instance VectorFamily ClauseVector Clause where
  asList cv = V.toList <$> V.freeze cv
  dump mes cv = do
    l <- asList cv
    sts <- mapM (dump ",") (l :: [Clause])
    return $ mes ++ tail (concat sts)

-- | returns a new 'ClauseVector'
newClauseVector  :: Int -> IO ClauseVector
newClauseVector n = do
  v <- MV.new (max 4 n)
  MV.set v NullClause
  return v

-- | returns the nth 'Clause'
{-# INLINE getNthClause #-}
getNthClause :: ClauseVector -> Int -> IO Clause
getNthClause = MV.unsafeRead

-- | sets the nth 'Clause'
{-# INLINE setNthClause #-}
setNthClause :: ClauseVector -> Int -> Clause -> IO ()
setNthClause = MV.unsafeWrite

-- | swaps the two 'Clause's
{-# INLINE swapClauses #-}
swapClauses :: ClauseVector -> Int -> Int -> IO ()
swapClauses = MV.unsafeSwap
