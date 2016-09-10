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
-- clause, null, binary clause.
-- This matches both of @Clause@ and @GClause@ in MiniSat
-- TODO: GADTs is better?
data Clause = Clause
              {
                learnt     :: !Bool     -- ^ whether this is a learnt clause
--              , rank     :: !Int'     -- ^ goodness like LBD; computed in 'Ranking'
              , activity   :: !Double'  -- ^ activity of this clause
              , protected  :: !Bool'    -- ^ protected from reduce
              , lits       :: !Stack    -- ^ which this clause consists of
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

instance ContainerFamily Clause Lit where
  dump mes NullClause = return $ mes ++ "Null"
  dump mes Clause{..} = return $ mes ++ "a clause"
{-
  dump mes Clause{..} = do
    a <- show <$> get' activity
    n <- get' lits
    l <- asList lits
    return $ mes ++ "C" ++ show n ++ "{" ++ intercalate "," [show learnt, a, show (map lit2int l)] ++ "}"
-}
  {-# SPECIALIZE INLINE asUVector :: Clause -> UVector Int #-}
  asUVector = asUVector . lits
  asList NullClause = return []
  asList Clause{..} = take <$> get' lits <*> asList lits

-- | 'Clause' is a 'SingleStorage' on the number of literals in it.
instance SingleStorage Clause Int where
  -- | returns the number of literals in a clause, even if the given clause is a binary clause
  {-# SPECIALIZE INLINE get' :: Clause -> IO Int #-}
  get' = get' . lits
  -- getSize (BinaryClause _) = return 1
  -- | sets the number of literals in a clause, even if the given clause is a binary clause
  {-# SPECIALIZE INLINE set' :: Clause -> Int -> IO () #-}
  set' c n = set' (lits c) n
  -- getSize (BinaryClause _) = return 1

-- | 'Clause' is a 'Stackfamily'on literals since literals in it will be discared if satisifed at level = 0.
instance StackFamily Clause Lit where
  -- | drop the last /N/ literals in a 'Clause' to eliminate unsatisfied literals
  {-# SPECIALIZE INLINE shrinkBy :: Clause -> Int -> IO () #-}
  shrinkBy c n = modifyNth (lits c) (subtract n) 0

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
{-# INLINABLE newClauseFromStack #-}
newClauseFromStack :: Bool -> Stack -> IO Clause
newClauseFromStack l vec = do
  n <- get' vec
  v <- newStack n
  let
    loop ((<= n) -> False) = return ()
    loop i = (setNth v i =<< getNth vec i) >> loop (i + 1)
  loop 0
  Clause l <$> {- new' 0 <*> -} new' 0.0 <*> new' False <*> return v

--------------------------------------------------------------------------------

-- | Mutable 'Clause' Vector
type ClauseVector = MV.IOVector Clause

instance ContainerFamily ClauseVector Clause where
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

instance VecFamily ClauseVector Clause where
  {-# SPECIALIZE INLINE getNth :: ClauseVector -> Int -> IO Clause #-}
  getNth = MV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: ClauseVector -> Int -> Clause -> IO () #-}
  setNth = MV.unsafeWrite
  {-# SPECIALIZE INLINE swapBetween :: ClauseVector -> Int -> Int -> IO () #-}
  swapBetween = MV.unsafeSwap
