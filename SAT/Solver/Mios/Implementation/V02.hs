{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TypeFamilies
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | version 2 using Vectors
module SAT.Solver.Mios.Solver where

import Control.Monad
import Data.IORef
import Data.List
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed.Mutable as UV
import System.Mem.StableName
import SAT.Solver.Mios.Types

-- | 'Clause' Container
type VecClause = MV.IOVector Clause
instance ContainerLike VecClause
instance VectorLike VecClause Clause where
  newVec = undefined
  newVecSized = undefined
  newVecSizedWith = undefined
  shrink = undefined
  pop = undefined
  growTo = undefined
  growToWith = undefined
  push' = undefined
  push = undefined
  lastE = undefined
  copyTo = undefined
  moveTo = undefined

-- | Set-of-`Clause` Container
type VecVecClause = MV.IOVector VecClause
instance ContainerLike VecVecClause
instance VectorLike VecVecClause VecClause

type VecDoubleAndInt = MV.IOVector (Double, Int)
instance ContainerLike VecDoubleAndInt
instance VectorLike VecDoubleAndInt (Double, Int)

-- | FIXME: this has a bad order computation cost
sortByFst :: VecDoubleAndInt -> IO ()
sortByFst v = do
  n <- subtract 1 <$> size v
  l <- forM [0 .. n] $ \i -> v .! i
  forM_ (zip [0 ..] $ sortOn fst l) $ \(i, x) -> setAt v i x


