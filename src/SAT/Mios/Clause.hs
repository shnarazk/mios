-- | (This is a part of MIOS.)
-- Clause, supporting pointer-based equality
{-# LANGUAGE
    FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Mios.Clause
       (
         Clause (..)
       , makeNullClause
       , newClauseFromStack
       , getRank
       , setRank
       , getActivity
       , setActivity
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
newtype Clause = Clause Stack          -- ^ literals and rank
--  | BinaryClause Lit                 -- binary clause consists of only a propagating literal

-- | The equality on 'Clause' is defined with 'reallyUnsafePtrEquality'.
instance Eq Clause where
  {-# SPECIALIZE INLINE (==) :: Clause -> Clause -> Bool #-}
  (==) x y = x `seq` y `seq` tagToEnum# (reallyUnsafePtrEquality# x y)

instance Show Clause where
--  show NullClause = "NullClause"
  show _ = "a clause"

-- | 'Clause' is a 'VecFamily' of 'Lit'.
instance VecFamily Clause Lit where
  {-# SPECIALIZE INLINE getNth :: Clause -> Int -> IO Int #-}
  getNth _ n = error "no getNth for Clause"
  {-# SPECIALIZE INLINE setNth :: Clause -> Int -> Int -> IO () #-}
  setNth _ n x = error "no setNth for Clause"
  -- | returns a vector of literals in it.
--  asList NullClause = return []
  asList cls = take <$> get' cls <*> (tail <$> asList cls)
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
  get' (Clause c) = get' c
  -- getSize (BinaryClause _) = return 1
  -- | sets the number of literals in a clause, even if the given clause is a binary clause
  {-# SPECIALIZE INLINE set' :: Clause -> Int -> IO () #-}
  set' (Clause c) n = set' c n
  -- getSize (BinaryClause _) = return 1

-- | 'Clause' is a 'Stackfamily'on literals since literals in it will be discared if satisifed at level = 0.
instance StackFamily Clause Lit where
  -- | drop the last /N/ literals in a 'Clause' to eliminate unsatisfied literals
  {-# SPECIALIZE INLINE shrinkBy :: Clause -> Int -> IO () #-}
  shrinkBy (Clause c) n = modifyNth c (subtract n) 0

-- coverts a binary clause to normal clause in order to reuse map-on-literals-in-a-clause codes.
-- liftToClause :: Clause -> Clause
-- liftToClause (BinaryClause _) = error "So far I use generic function approach instead of lifting"

-- | copies /vec/ and return a new 'Clause'.
-- Since 1.0.100 DIMACS reader should use a scratch buffer allocated statically.
{-# INLINABLE newClauseFromStack #-}
newClauseFromStack :: Bool -> Stack -> IO Clause
newClauseFromStack l vec = do
  n <- get' vec
  v <- newStack (n + 2)         -- n + rank + activity
  let loop ((<= n) -> False) = setNth vec (n + 1) (if l then 1 else 0) >> setNth vec (n + 2) 1
      loop i = (setNth v i =<< getNth vec i) >> loop (i + 1)
  loop 0
  return $ Clause v

makeNullClause :: IO Clause
makeNullClause = do v <- newStack 0; set' v 0; return $ Clause v

{-# INLINE getRank #-}
getRank :: Clause -> IO Int
getRank (Clause c) = do n <- get' c; getNth c (n + 1)

{-# INLINE setRank #-}
setRank :: Clause -> Int -> IO ()
setRank (Clause c) k = do n <- get' c; setNth c (n + 1) k

{-# INLINE getActivity #-}
getActivity :: Clause -> IO Int
getActivity (Clause c) = do n <- get' c; getNth c (n + 2)

{-# INLINE setActivity #-}
setActivity :: Clause -> Int -> IO ()
setActivity (Clause c) k = do n <- get' c; setNth c (n + 2) k

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
newClauseVector  :: Int -> Clause -> IO ClauseVector
newClauseVector n nullC = do
  v <- MV.new (max 4 n)
  MV.set v nullC
  return v
