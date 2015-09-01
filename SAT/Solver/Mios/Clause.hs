{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- |
module SAT.Solver.Mios.Clause
       (
         Clause (..)
       , selectWatcher
       )
       where

import GHC.Prim
import Data.IORef
import Data.List
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal

-- | __Fig. 7.(p.11)__
-- Clause
data Clause = Clause
              {
                learnt   :: Bool           -- ^ whether this is a learnt clause
              , activity :: IORef Double   -- ^ activity of this clause
              , nextWatch1 :: IORef Clause -- ^ the next clause that watches lits[0]
              , nextWatch2 :: IORef Clause -- ^ the next clause that watches lits[1]
              , lits     :: FixedLitVec    -- ^ which this clause consists of
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
  size Clause{..} = lits .! 0
  dump mes NullClause = return $ "NullClause" ++ if mes == "" then "" else "(" ++ mes ++ ")"
  dump mes c@Clause{..} = do
    a <- show <$> readIORef activity
    (len:ls) <- asList lits
    return $ mes ++ "C" ++ show len ++ "{" ++ intercalate "," [show learnt, a, show (take len ls)] ++ "}"
  asList NullClause = return []
  asList Clause{..} = do
    (n : ls)  <- asList lits
    return $ take n ls

-- | supports a restricted set of 'VectorLike' methods
instance VectorLike Clause Lit where
  NullClause .! _ = error "(.!) on NullClause"
  Clause{..} .! i = lits .! (1 + i)
  setAt NullClause _ _ = error "setAt on NullClause"
  setAt Clause{..} i x = setAt lits (1 + i) x
  shrink n Clause{..} = do
    m <- lits .! 0
    setAt lits 0 (m - n)

-- | returns /the pointer/ to the next clause watching /the lit/
selectWatcher :: Lit -> Clause -> IO (IORef Clause)
selectWatcher l !c = do
  l0 <- c .! 0
  return $ if l0 == negate l then nextWatch1 c else nextWatch2 c
{-
selectWatcher l NullClause = error "selectWatcher called with NullClause"
selectWatcher l !c = do
  l0 <- c .! 0
  l1 <- c .! 1
  let l' = negate l
  case () of
   _ | l0 == l' -> return $ nextWatch1 c
   _ | l1 == l' -> return $ nextWatch2 c
   _ | l0 == l -> error "l0 == l"
   _ | l1 == l -> error "l1 == l"
   _            -> do
     lc <- asList c
     error $ "no watcher" ++ show (l, (l0, l1), lc)
-}
