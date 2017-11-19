-- | This file is a part of MIOS.
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
module SAT.Mios.Clause
       (
         Clause (..)
--       , isLit
--       , getLit
       , newClauseFromStack
         -- * Vector of Clause
       , ClauseVector
       , newClauseVector
       )
       where

import GHC.Prim (tagToEnum#, reallyUnsafePtrEquality#)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
-- import Data.List (intercalate)
import SAT.Mios.Types

-- | __Fig. 7.(p.11)__
-- normal, null (and binary) clause.
-- This matches both of @Clause@ and @GClause@ in MiniSat.
data Clause = Clause
              {
                rank       :: !Int'     -- ^ goodness like LBD; computed in 'Ranking'
              , activity   :: !Double'  -- ^ activity of this clause
              , lits       :: !Stack    -- ^ which this clause consists of
              }
  | NullClause                          -- as null pointer
  | BiClause Lit Lit                    -- binary clause consists of only propagating literals

-- | The equality on 'Clause' is defined with 'reallyUnsafePtrEquality'.
instance Eq Clause where
  {-# SPECIALIZE INLINE (==) :: Clause -> Clause -> Bool #-}
  (==) x y = x `seq` y `seq` tagToEnum# (reallyUnsafePtrEquality# x y)

instance Show Clause where
  show NullClause = "NullClause"
  show (BiClause a b) = "Binary" ++ show (a, b)
  show _ = "a clause"

-- | 'Clause' is a 'VecFamily' of 'Lit'.
instance VecFamily Clause Lit where
  {-# SPECIALIZE INLINE getNth :: Clause -> Int -> IO Int #-}
  getNth Clause{..} n = error "no getNth for Clause"
  {-# SPECIALIZE INLINE setNth :: Clause -> Int -> Int -> IO () #-}
  setNth Clause{..} n x = error "no setNth for Clause"
  -- | returns a vector of literals in it.
  asList NullClause = return []
  asList (BiClause a b) = return [a, b]
  asList Clause{..} = take <$> get' lits <*> (tail <$> asList lits)
  -- dump mes NullClause = return $ mes ++ "Null"
  -- dump mes Clause{..} = return $ mes ++ "a clause"
{-
  dump mes Clause{..} = do
    a <- show <$> get' activity
    n <- get' lits
    l <- asList lits
    return $ mes ++ "C" ++ show n ++ "{" ++ intercalate "," [show learnt, a, show (map lit2int l)] ++ "}"
-}

-- | 'Clause' is a 'SingleStorage' on the number of literals in it.
instance SingleStorage Clause Int where
  -- | returns the number of literals in a clause, even if the given clause is a binary clause
  {-# SPECIALIZE INLINE get' :: Clause -> IO Int #-}
  get' = get' . lits
  -- getSize (BiClause _) = return 1
  -- | sets the number of literals in a clause, even if the given clause is a binary clause
  {-# SPECIALIZE INLINE set' :: Clause -> Int -> IO () #-}
  set' c n = set' (lits c) n
  -- getSize (BiClause _) = return 1

-- | 'Clause' is a 'Stackfamily'on literals since literals in it will be discared if satisifed at level = 0.
instance StackFamily Clause Lit where
  -- | drop the last /N/ literals in a 'Clause' to eliminate unsatisfied literals
  {-# SPECIALIZE INLINE shrinkBy :: Clause -> Int -> IO () #-}
  shrinkBy c n = modifyNth (lits c) (subtract n) 0

-- returns True if it is a 'BiClause'.
-- FIXME: this might be discarded in minisat 2.2
-- isLit :: Clause -> Bool
-- isLit (BiClause _) = True
-- isLit _ = False

-- returns the literal in a BiClause.
-- FIXME: this might be discarded in minisat 2.2
-- getLit :: Clause -> Lit
-- getLit (BiClause x) = x

-- coverts a binary clause to normal clause in order to reuse map-on-literals-in-a-clause codes.
-- liftToClause :: Clause -> Clause
-- liftToClause (BiClause _) = error "So far I use generic function approach instead of lifting"

-- | copies /vec/ and return a new 'Clause'.
-- Since 1.0.100 DIMACS reader should use a scratch buffer allocated statically.
{-# INLINABLE newClauseFromStack #-}
newClauseFromStack :: Bool -> Stack -> IO Clause
newClauseFromStack l vec = do
  n <- get' vec
  if n == -2
    then do BiClause <$> getNth vec 1 <*> getNth vec 2
    else do v <- newStack n
            let loop ((<= n) -> False) = return ()
                loop i = (setNth v i =<< getNth vec i) >> loop (i + 1)
            loop 0
            Clause <$> new' (if l then 1 else 0) <*> new' 0.0 {- <*> new' False -} <*> return v

-------------------------------------------------------------------------------- Clause Vector

-- | Mutable 'Clause' Vector
type ClauseVector = MV.IOVector Clause

-- | 'ClauseVector' is a vector of 'Clause'.
instance VecFamily ClauseVector Clause where
  {-# SPECIALIZE INLINE getNth :: ClauseVector -> Int -> IO Clause #-}
  getNth = MV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: ClauseVector -> Int -> Clause -> IO () #-}
  setNth = MV.unsafeWrite
  {-# SPECIALIZE INLINE swapBetween :: ClauseVector -> Int -> Int -> IO () #-}
  swapBetween = MV.unsafeSwap
  asList cv = V.toList <$> V.freeze cv -- mapM (asList <=< getNth vec) [0 .. ???]
{-
  dump mes cv = do
    l <- asList cv
    sts <- mapM (dump ",") (l :: [Clause])
    return $ mes ++ tail (concat sts)
-}

-- | returns a new 'ClauseVector'.
newClauseVector  :: Int -> IO ClauseVector
newClauseVector n = do
  v <- MV.new (max 4 n)
  MV.set v NullClause
  return v
