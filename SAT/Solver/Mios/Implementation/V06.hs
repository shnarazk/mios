{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
  , TypeFamilies
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | This is the implementation pack __version 0.6 #activityEstimation
--
-- * __FixedVec a__ @:: MV.IOVector a@ -- data type that contains a mutable list of elements
--
-- * __Vec a__  @:: IORef [a]@ -- data type that contains a mutable list of elements
--
-- * __VerOrder__ @:: IORef [Var]@
--
-- * __FixedQueueOf Lit__ @:: UV.IOVector Int@
--
module SAT.Solver.Mios.Implementation.V06 where

import Control.Monad
import Data.IORef
import Data.List hiding (insert)
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed.Mutable as UV
import System.Mem.StableName
import SAT.Solver.Mios.Types

-- | sets to the version name : @"mios v0.6 #activityEstimation"@
idString :: String
idString = "mios v0.6 #activityEstimation"

-- | __version 0.1__
--
-- Costs of all operations are /O/(/n/)
data VecOf a = VecOf
              {
                ptr :: IORef [a] -- ^ reference pointer to the data
              }

-- | provides 'clear' and 'size'
instance ContainerLike (VecOf a) a where
  clear VecOf{..} = writeIORef ptr []
  size VecOf{..} = length <$> readIORef ptr
  asList VecOf{..} = readIORef ptr
  dump str VecOf{..} = (str ++) . show <$> readIORef ptr

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (VecOf a) a where
  -- * Constructors
  emptyVec = VecOf <$> newIORef []
  newVec = VecOf <$> newIORef []
  newVecSized n = VecOf <$> newIORef (replicate n undefined)
  newVecSizedWith n x = VecOf <$> newIORef (replicate n x)
  -- * Size operations
  shrink n VecOf{..} = do
    when (0 < n) $ do
      x <- readIORef ptr
      writeIORef ptr $ take (length x - n) x
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
  -- | A normal implementation of 'removeElem' would use
  -- @delete :: Eq a => a -> [a] -> [a]@. But this means
  -- the element type of 'VecOf' has 'Eq' type constraint. It make difficult
  -- to handle mutable types. Thus I use an equality checker based on
  -- pointer equivalency.
  removeElem x VecOf{..} = do
    l <- readIORef ptr
    writeIORef ptr =<< filterM (x <==>) l
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
  checkConsistency str VecOf{..} func = do
    res <- and <$> (mapM func =<< readIORef ptr)
    unless res $ error str

-- | unit test function
checkImplementation :: IO ()
checkImplementation = do
  return ()

sortVecOn :: (Ord b) => (a -> IO b) -> VecOf a -> IO ()
sortVecOn f VecOf{..} = writeIORef ptr . map snd . sortOn fst =<< mapM (\i -> (, i) <$> f i) =<< readIORef ptr

-- | __version 0.4__
--
-- Costs of all operations are /O/(/1/)
data FixedVecOf a = FixedVecOf
                          {
                            fVec :: MV.IOVector a
                          }

-- | provides 'clear' and 'size'
instance ContainerLike (FixedVecOf a) a where
  clear FixedVecOf{..} = error "FixedVec.clear"
  size FixedVecOf{..} = return $ MV.length fVec
  asList FixedVecOf{..} = forM [0 .. MV.length fVec - 1] $ MV.read fVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (FixedVecOf a) a where
  -- * Constructors
  emptyVec = FixedVecOf <$> MV.new 0
  newVec = FixedVecOf <$> MV.new 0
  newVecSized n = FixedVecOf <$> MV.new n
  newVecSizedWith n x = FixedVecOf <$> MV.replicate n x
  -- * Size operations
  shrink n FixedVecOf{..} = error "FixedVecOf.shrink"
  growTo _ _ = error "FixedVecOf.growTo"
  growToWith _ _ = error "FixedVecOf.growToWith"
  -- * Stack operations
  pop FixedVecOf{..} = error "FixedVecOf.pop"
  push FixedVecOf{..} x = error "FixedVecOf.push"
  lastE FixedVecOf{..} = error "FixedVecOf.lastE"
  removeElem x FixedVecOf{..} = error "FixedVecOf.removeElem"
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedVecOf a -> Int -> IO a #-}
  (.!) FixedVecOf{..} n = MV.unsafeRead fVec n
  {-# SPECIALIZE INLINE setAt :: FixedVecOf a -> Int -> a -> IO () #-}
  setAt FixedVecOf{..} n x = MV.unsafeWrite fVec n x
  -- * Duplication
  copyTo v1 v2 = error "FixedVecOf.copyTo"
  moveTo v1 v2 = error "FixedVecOf.moveTo"
  -- * Conversion
  newFromList (l) = error "FixedVecOf.newFromList"
  checkConsistency str FixedVecOf{..} func = error "FixedVecOf.checkConsistency"

-- | sort elements in /big-to-small/ order
sortByFst :: FixedVecOf (Double, Int) -> IO ()
sortByFst v@FixedVecOf{..} = do
  vals <- reverse . sortOn fst <$> asList v
  forM_ (zip [0 ..] vals) $ \(i, x) -> MV.write fVec i x

-- | __version 0.3__
--
-- Costs of all operations are /O/(/1/)
data FixedLitVec = FixedLitVec
                          {
                            litVec :: UV.IOVector Int
                          }

-- | provides 'clear' and 'size'
instance ContainerLike FixedLitVec Lit where
  clear FixedLitVec{..} = error "FixedLitVec.clear"
  size FixedLitVec{..} = return $ UV.length litVec
  asList FixedLitVec{..} = forM [0 .. UV.length litVec - 1] $ UV.read litVec
  dump str v = (str ++) . show <$> asList v

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike FixedLitVec Lit where
  -- * Constructors
  emptyVec = FixedLitVec <$> UV.new 0
  newVec = FixedLitVec <$> UV.new 0
  newVecSized n = FixedLitVec <$> UV.new n
  newVecSizedWith n x = error "FixedLitVec.newVecSizedWith" -- FixedLitVec <$> UV.new n
  -- * Size operations
  shrink n FixedLitVec{..} = error "FixedLitVec.shrink"
  growTo _ _ = error "FixedLitVec.growTo"
  growToWith _ _ = error "FixedLitVec.growToWith"
  -- * Stack operations
  pop FixedLitVec{..} = error "FixedLitVec.pop"
  push FixedLitVec{..} x = error "FixedLitVec.push"
  lastE FixedLitVec{..} = error "FixedLitVec.lastE"
  removeElem x FixedLitVec{..} = error "FixedLitVec.removeElem"
  -- * Vector operations
  {-# SPECIALIZE INLINE (.!) :: FixedLitVec -> Int -> IO Lit #-}
  (.!) FixedLitVec{..} n = UV.unsafeRead litVec n
  {-# SPECIALIZE INLINE setAt :: FixedLitVec -> Int -> Lit -> IO () #-}
  setAt FixedLitVec{..} n x = UV.unsafeWrite litVec n x
  -- * Duplication
  copyTo v1 v2 = error "FixedLitVec.copyTo"
  moveTo v1 v2 = error "FixedLitVec.moveTo"
  -- * Conversion
  newFromList l = do
    v <- UV.new $ length l
    forM_ (zip [0 .. length l - 1] l) $ \(i, j) -> UV.write v i j
    return $ FixedLitVec v
  checkConsistency str FixedLitVec{..} func = error "FixedLitVec.checkConsistency"

-- | __version 0.5__
--
-- a shrinked version of 'MutableRings' (a single-linked memory chunk)
--
-- __Layout__
--
-- This is 2*n+3 length vector for n variables.
--
-- * ring[0] is the queue length
--
-- * ring[1] is the first assgined literal
--
-- * ring[2] is the last (latest) assigned literal
--
-- * ring[index(n)+2] == the literal assigned after Literl /n/
--
-- __Definition__ (an empty case is eliminated)
--
-- * insert x = @do x' <- ring .! 2; setAt ring (index x' + 2) x; setAt ring 2 x@
--
-- * dequeue = @do x <- ring .! 1; x' <- ring .! (index x + 2); setAt ring 1 x'; return x@
--
-- * initialization = @setAt ring 0 0; setAt ring 1 0; setAt ring 2 0@
--
data FixedQueueOf a = FixedQueueOf
              {
                ring :: UV.IOVector a -- ^ emulate a linked data structure on mutable vector
              }

-- | provides 'clear' and 'size'
instance ContainerLike (FixedQueueOf Lit) Lit where
  clear FixedQueueOf{..} = forM_ [0 .. UV.length ring - 1] $ flip (UV.write ring) 0
  size FixedQueueOf{..} = UV.read ring 0
  asList = traverseQueue
  dump str q@FixedQueueOf{..} = do
    n <- UV.read ring 0
    s <- UV.read ring 1
    e <- UV.read ring 2
    l <- asList q
    return $ str ++ "Q" ++ show (n, s, e) ++ ":" ++ show l

-- | 'Lit' Container
-- this is a derived type, thus no need to instanciation for 'ContainerLike'
instance QueueLike (FixedQueueOf Lit) Int where
  newQueue = do
     q <- UV.new 3
     UV.write q 0 0
     UV.write q 1 0
     UV.write q 2 0
     return $ FixedQueueOf q
  newQueueSized n = do
     q <- UV.new $ 3 + n
     UV.write q 0 0
     UV.write q 1 0
     UV.write q 2 0
     return $ FixedQueueOf q
  insert q@FixedQueueOf{..} x = do
    n <- UV.read ring 0
    check <- (0 /=) <$> UV.read ring (index x + 3)
    case () of
     _ | check -> return ()
     _ | 0 == n -> do
           UV.write ring 1 x
           UV.write ring 2 x
           UV.write ring (index x + 3) 0
           UV.write ring 0 1
     _ | 1 <= n -> do
           i <- (3 +) .index <$> UV.read ring 2 -- the slot for the current last element
           UV.write ring i x                    -- points 'x` now
           UV.write ring 2 x                    -- and the pointer points 'x'
           UV.write ring (index x + 3) 0
           UV.write ring 0 $ n + 1
  dequeue q@FixedQueueOf{..} = do
    n <- UV.read ring 0
    case () of
     _ | 0 == n -> error "tried to dequeue from zero length queue"
     _ | 1 == n -> do
           x <- UV.read ring 1
           UV.write ring (index x + 3) 0
           UV.write ring 0 0
           UV.write ring 1 0
           UV.write ring 2 0
           return x
     _ | otherwise -> do
           x <- UV.read ring 1
           i <- UV.read ring $ index x + 3
           UV.write ring (index x + 3) 0    -- clear the dequeued field
           UV.write ring 1 i                -- and the pointer points the element
           UV.write ring 0 $ n - 1
           return x

traverseQueue :: FixedQueueOf Int -> IO [Int]
traverseQueue FixedQueueOf{..} = do
  let
    loop l 0 = return $ reverse l
    loop l x = loop (x:l) =<< UV.read ring (index x + 3)
  loop [] =<< UV.read ring 1


data StackOfLit = StackOfLit
                  {
                    stackL :: UV.IOVector Int
                  }

instance ContainerLike StackOfLit Int where
  clear StackOfLit{..} = forM_ [0 .. UV.length stackL - 1] $ flip (UV.write stackL) 0
  size StackOfLit{..} = UV.read stackL 0
  asList = traverseStack
  dump str s@StackOfLit{..} = do
    n <- UV.read stackL 0
    e <- UV.read stackL 1
    l <- asList s
    return $ str ++ "Stack" ++ show (n, e) ++ ":" ++ show l

traverseStack :: StackOfLit -> IO [Int]
traverseStack StackOfLit{..} = do
  let
    loop l 0 = return $ reverse l
    loop l x = loop (x:l) =<< UV.read stackL (index x + 2)
  loop [] =<< UV.read stackL 1

instance VectorLike StackOfLit Int where
  emptyVec = StackOfLit <$> UV.new 0
  newVec = StackOfLit <$> UV.new 0
  newVecSized n = StackOfLit <$> UV.new (2 + n)
  newVecSizedWith n x = error "StackOfLit.newVecSizedWith" -- FixedLitVec <$> UV.new n
  -- * Size operations
  shrink _ _ = error "StackOfLit.shrink"
  growTo _ _ = error "StackOfLit.growTo"
  growToWith _ _ = error "StackOfLit.growToWith"
  -- * Stack operations
  pop StackOfLit{..} = do
    n <- UV.read stackL 0
    if n == 0
      then error "StackOfLit.pop zero"
      else do
          l <- UV.read stackL 1
          l' <- UV.read stackL $ index l + 2
          UV.write stackL 1 l'
          UV.write stackL 0 $ n - 1
          return ()
  push StackOfLit{..} x = do
    n <- UV.read stackL 0
    if n == 0
      then do
          UV.write stackL 1 x
          UV.write stackL 0 1
      else do
          l <- UV.read stackL 1
          UV.write stackL (index x + 2) l
          UV.write stackL 1 x
          UV.write stackL 0 $ n + 1
  lastE StackOfLit{..} = UV.read stackL 1
  removeElem _ _ = error "StackOfLit.removeElem"
