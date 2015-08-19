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

-- | This is the implementation pack __version 0.4 #FixedVector + List-based Vector__ 
--
-- * __FixedVec a__ @:: MV.IOVector a@ -- data type that contains a mutable list of elements
--
-- * __Vec a__  @:: IORef [a]@ -- data type that contains a mutable list of elements
--
-- * __VerOrder__ @:: IORef [Var]@
--
-- * __QueueOf Lit__ @:: UV.IOVector Int@
--
module SAT.Solver.Mios.Implementation.V04 where

import Control.Monad
import Data.IORef
import Data.List
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed.Mutable as UV
import System.Mem.StableName
import SAT.Solver.Mios.Types

-- | sets to the version name : @"mios v0.4 #FixedVector + List-based Vector"@
idString :: String
idString = "mios v0.4 #FixedVector + List-based Vector"

-- | __version 0.1__
--
-- Costs of all operations are /O/(/n/)
data VecOf a = VecOf
              {
                ptr :: IORef [a] -- ^ reference pointer to the data
              }

-- | provides 'clear' and 'size'
instance ContainerLike (VecOf a) where
  clear VecOf{..} = writeIORef ptr []
  size VecOf{..} = length <$> readIORef ptr

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (VecOf a) a where
  -- * Constructors
  emptyVec = VecOf <$> newIORef []
  newVec = VecOf <$> newIORef []
  newVecSized n = VecOf <$> newIORef (replicate n undefined)
  newVecSizedWith n x = VecOf <$> newIORef (replicate n x)
  -- * Size operations
  shrink n VecOf{..} = do
    writeIORef ptr . take n =<< readIORef ptr
  growTo _ _ = return ()
  growToWith _ _ = return ()
  -- * Stack operations
  pop VecOf{..} = do
    l <- readIORef ptr
    unless (null l) $ writeIORef ptr $ init l
  push VecOf{..} x = do
    l <- readIORef ptr
    writeIORef ptr $ l ++ [x]
  lastE VecOf{..} = do
    l <- readIORef ptr
    return $ last l
  removeElem x VecOf{..} = do
    l <- readIORef ptr
    writeIORef ptr =<< deleteWOEq x l
  -- * Vector operations
  (.!) VecOf{..} n = (!! n) <$> readIORef ptr
  setAt VecOf{..} n x = do
    l <- readIORef ptr
    writeIORef ptr $ take n l ++ (x : drop (n + 1) l)
  -- * Duplication
  copyTo v1 v2 = do
    l1 <- readIORef (ptr v1)
    writeIORef (ptr v2) l1
  moveTo v1 v2 = do
    l1 <- readIORef (ptr v1)
    writeIORef (ptr v2) l1
    writeIORef (ptr v1) []
  -- * Conversion
  newFromList l = VecOf <$> newIORef l
  asList VecOf{..} = readIORef ptr
  checkConsistency str VecOf{..} func = do
    res <- and <$> (mapM func =<< readIORef ptr)
    unless res $ error str
  dump str VecOf{..} = (str ++) . show <$> readIORef ptr

-- | A normal implementation of 'removeElem' would use
-- @delete :: Eq a => a -> [a] -> [a]@. But this means
-- the element type of 'VecOf' has 'Eq' type constraint. It make difficult
-- to handle mutable types. Thus I use an equality checker based on
-- pointer equivalency.
deleteWOEq :: a -> [a] -> IO [a]
deleteWOEq _ [] = return []
deleteWOEq x (y:l) = do
  e <- x <==> y
  if e
    then deleteWOEq x l
    else (y :) <$> deleteWOEq x l

-- | unit test function
checkImplementation :: IO ()
checkImplementation = do
  return ()

-- | sort elements in /big-to-small/ order
sortByFst :: VecOf (Double, Int) -> IO ()
sortByFst VecOf{..} = writeIORef ptr . reverse . sortOn fst =<< readIORef ptr

-- | __version 0.4__
--
-- Costs of all operations are /O/(/1/)
data FixedVectorOf a = FixedVectorOf
                          {
                            fVec :: MV.IOVector a
                          }

-- | provides 'clear' and 'size'
instance ContainerLike (FixedVectorOf a) where
  clear FixedVectorOf{..} = error "FixedVector.clear"
  size FixedVectorOf{..} = return $ MV.length fVec

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (FixedVectorOf a) a where
  -- * Constructors
  emptyVec = FixedVectorOf <$> MV.new 0
  newVec = FixedVectorOf <$> MV.new 0
  newVecSized n = FixedVectorOf <$> MV.new n
  newVecSizedWith n x = FixedVectorOf <$> MV.replicate n x
  -- * Size operations
  shrink n FixedVectorOf{..} = error "FixedVectorOf.shrink"
  growTo _ _ = error "FixedVectorOf.growTo"
  growToWith _ _ = error "FixedVectorOf.growToWith"
  -- * Stack operations
  pop FixedVectorOf{..} = error "FixedVectorOf.pop"
  push FixedVectorOf{..} x = error "FixedVectorOf.push"
  lastE FixedVectorOf{..} = error "FixedVectorOf.lastE"
  removeElem x FixedVectorOf{..} = error "FixedVectorOf.removeElem"
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedVectorOf a -> Int -> IO a #-}
  (.!) FixedVectorOf{..} n = MV.read fVec n
  {-# SPECIALIZE INLINE setAt :: FixedVectorOf a -> Int -> a -> IO () #-}
  setAt FixedVectorOf{..} n x = MV.write fVec n x
  -- * Duplication
  copyTo v1 v2 = error "FixedVectorOf.copyTo"
  moveTo v1 v2 = error "FixedVectorOf.moveTo"
  -- * Conversion
  newFromList (l) = error "FixedVectorOf.newFromList"
  asList FixedVectorOf{..} = forM [0 .. MV.length fVec - 1] $ MV.read fVec
  checkConsistency str FixedVectorOf{..} func = error "FixedVectorOf.checkConsistency"
  dump str FixedVectorOf{..} = return $ str ++ "FixedVectorOf"

-- | __version 0.3__
--
-- Costs of all operations are /O/(/1/)
data FixedLitVector = FixedLitVector
                          {
                            litVec :: UV.IOVector Int
                          }

-- | provides 'clear' and 'size'
instance ContainerLike FixedLitVector where
  clear FixedLitVector{..} = error "FixedLitVector.clear"
  size FixedLitVector{..} = return $ UV.length litVec

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike FixedLitVector Lit where
  -- * Constructors
  emptyVec = FixedLitVector <$> UV.new 0
  newVec = FixedLitVector <$> UV.new 0
  newVecSized n = FixedLitVector <$> UV.new 0
  newVecSizedWith n x = FixedLitVector <$> UV.new 0
  -- * Size operations
  shrink n FixedLitVector{..} = error "FixedLitVector.shrink"
  growTo _ _ = error "FixedLitVector.growTo"
  growToWith _ _ = error "FixedLitVector.growToWith"
  -- * Stack operations
  pop FixedLitVector{..} = error "FixedLitVector.pop"
  push FixedLitVector{..} x = error "FixedLitVector.push"
  lastE FixedLitVector{..} = error "FixedLitVector.lastE"
  removeElem x FixedLitVector{..} = error "FixedLitVector.removeElem"
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedLitVector -> Int -> IO Lit #-}
  (.!) FixedLitVector{..} n = UV.unsafeRead litVec n
  {-# SPECIALIZE INLINE setAt :: FixedLitVector -> Int -> Lit -> IO () #-}
  setAt FixedLitVector{..} n x = UV.unsafeWrite litVec n x
  -- * Duplication
  copyTo v1 v2 = error "FixedLitVector.copyTo"
  moveTo v1 v2 = error "FixedLitVector.moveTo"
  -- * Conversion
  newFromList (nub -> l) = do
    v <- UV.new $ length l
    forM_ (zip [0 .. length l - 1] l) $ \(i, j) -> UV.unsafeWrite v i j
    return $ FixedLitVector v
  asList FixedLitVector{..} = forM [0 .. UV.length litVec - 1] $ UV.unsafeRead litVec
  checkConsistency str FixedLitVector{..} func = error "FixedLitVector.checkConsistency"
  dump str FixedLitVector{..} = return $ str ++ "FixedLitVector"

-- | __version 0.2__
--
-- a shrinked version of 'MutableRings' (a single-linked memory chunk)
--
-- __Layout__
--
-- This is n+3 length vector for n variables.
--
-- * ring[0] is the queue length
--
-- * ring[1] is the first assgined literal
--
-- * ring[2] is the last (latest) assigned literal
--
-- * ring[n+2] == the literal assigned after variable /n/
--
-- __Definition__ (an empty case is eliminated)
--
-- * insert x = @do x' <- ring .! 2; setAt ring (abs x' + 2) x; setAt ring 2 x@
--
-- * dequeue = @do x <- ring .! 1; x' <- ring .! (abs x + 2); setAt ring 1 x'; return x@
--
-- * initialization = @setAt ring 0 0; setAt ring 1 0; setAt ring 2 0@
--
data QueueOf a = QueueOf
              {
                ring :: UV.IOVector a -- ^ emulate linked data structure on mutable vector
              }

-- | provides 'clear' and 'size'
instance ContainerLike (QueueOf Lit) where
  clear QueueOf{..} = do UV.write ring 0 0; UV.write ring 1 0; UV.write ring 2 0
  size QueueOf{..} = UV.read ring 0

-- | 'Lit' Container
-- this is a derived type, thus no need to instanciation for 'ContainerLike'
instance QueueLike (QueueOf Lit) Int where
  newQueue = do
     q <- UV.new 200
     UV.write q 0 0
     UV.write q 1 0
     UV.write q 2 0
     return $ QueueOf q
  growQueueSized n QueueOf{..} = return ()
{-
     UV.grow ring $ n + 3
     UV.write ring 0 n
     UV.write ring 1 3
     UV.write ring 2 3
-}
  insert QueueOf{..} x = do
     x' <- UV.read ring 2
     UV.write ring (abs x' + 2) x
     UV.write ring 2 x
     x'' <- UV.read ring 1
     UV.modify ring ((1 :: Int) +) 0
     when (x'' == 0) $ UV.write ring 1  x
  dequeue QueueOf{..} = do
     x <- UV.read ring 1
     x' <- UV.read ring (abs x + 2)
     UV.write ring 1 x'
     x'' <- UV.read ring 2
     UV.modify ring (subtract 1) 0
     when (x'' == x) $ UV.write ring 1 0
     return x
