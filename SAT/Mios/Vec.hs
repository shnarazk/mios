{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  , TypeFamilies
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Abstraction Layer for Mutable Vectors
module SAT.Mios.Vec
       (
         -- * Vector class
         VecFamily (..)
         -- * Vectors
       , UVector
       , Vec (..)
         -- * SingleStorage
       , SingleStorage (..)
       , Bool'
       , Double'
       , Int'
         -- * Stack
       , StackFamily (..)
       , Stack
       , newStackFromList
       )
       where

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV

-- | Interface on vectors.
class VecFamily v a | v -> a where
  -- | returns the /n/-th value.
  getNth ::v -> Int -> IO a
  -- | sets the /n/-th value.
  setNth :: v -> Int -> a -> IO ()
  -- | erases all elements in it.
  reset:: v -> IO ()
  -- | converts to an Int vector.
  asUVector :: (a ~ Int) => v -> UVector Int
  -- | returns the /n/-th value (index starts from zero in any case).
  -- | swaps two elements.
  swapBetween :: v -> Int -> Int -> IO ()
  -- | calls the update function.
  modifyNth :: v -> (a -> a) -> Int -> IO ()
  -- | returns a new vector.
  newVec :: Int -> a -> IO v
  -- | sets all elements.
  setAll :: v -> a -> IO ()
  -- | extends the size of stack by /n/; note: values in new elements aren't initialized maybe.
  growBy :: v -> Int -> IO v
  -- | (FOR DEBUG) converts to a list.
  asList :: v -> IO [a]
  -- | (FOR DEBUG) dump the contents.
  dump :: Show a => String -> v -> IO String
  {-# MINIMAL getNth, setNth #-}
  reset = error "no default method: reset"
  asUVector = error "no default method: asUVector"
  swapBetween = error "no default method: swapBetween"
  modifyNth = error "no default method: modifyNth"
  newVec = error "no default method: newVec"
  setAll = error "no default method: setAll"
  asList = error "no default method: asList"
  growBy = error "no default method: growBy"
  dump msg _ = error $ msg ++ ": no defalut method for dump"

-------------------------------------------------------------------------------- UVector

-- | A thin abstract layer for Mutable unboxed Vector
type UVector a = UV.IOVector a

instance VecFamily (UVector Int) Int where
  {-# SPECIALIZE INLINE getNth :: UVector Int -> Int -> IO Int #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Int -> Int -> Int -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Int -> (Int -> Int) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Int -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE newVec :: Int -> Int -> IO (UVector Int) #-}
  newVec n 0 = UV.new n
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE setAll :: UVector Int -> Int -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growBy :: UVector Int -> Int -> IO (UVector Int) #-}
  growBy = UV.unsafeGrow
  asList v = mapM (UV.unsafeRead v) [0 .. UV.length v - 1]
  dump str v = (str ++) . show <$> asList v

instance VecFamily (UVector Double) Double where
  {-# SPECIALIZE INLINE getNth :: UVector Double -> Int -> IO Double #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Double -> Int -> Double -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Double -> (Double -> Double) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Double -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE newVec :: Int -> Double -> IO (UVector Double) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE setAll :: UVector Double -> Double -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growBy :: UVector Double -> Int -> IO (UVector Double) #-}
  growBy = UV.unsafeGrow
  asList v = mapM (UV.unsafeRead v) [0 .. UV.length v - 1]
  dump str v = (str ++) . show <$> asList v

-------------------------------------------------------------------------------- Vec

-- | Another abstraction layer on 'UVector'.
--
-- __Note__: the 0-th element of @Vec Int@ is reserved for internal tasks. If you want to use it, use @UVector Int@.
newtype Vec a  = Vec (UVector a)

instance VecFamily (Vec Int) Int where
  {-# SPECIALIZE INLINE getNth :: Vec Int -> Int -> IO Int #-}
  getNth (Vec v) = UV.unsafeRead v
  {-# SPECIALIZE INLINE setNth :: Vec Int -> Int -> Int -> IO () #-}
  setNth (Vec v) = UV.unsafeWrite v
  {-# SPECIALIZE INLINE reset :: Vec Int -> IO () #-}
  reset (Vec v) = setNth v 0 0
  {-# SPECIALIZE INLINE asUVector :: Vec Int -> UVector Int #-}
  asUVector (Vec a) = UV.unsafeTail a
  {-# SPECIALIZE INLINE modifyNth :: Vec Int -> (Int -> Int) -> Int -> IO () #-}
  modifyNth (Vec v) = UV.unsafeModify v
  {-# SPECIALIZE INLINE swapBetween :: Vec Int -> Int -> Int -> IO () #-}
  swapBetween (Vec v) = UV.unsafeSwap v
  {-# SPECIALIZE INLINE newVec :: Int -> Int -> IO (Vec Int) #-}
  newVec n x = Vec <$> newVec (n + 1) x
  {-# SPECIALIZE INLINE setAll :: Vec Int -> Int -> IO () #-}
  setAll (Vec v) = UV.set v
  {-# SPECIALIZE INLINE growBy :: Vec Int -> Int -> IO (Vec Int) #-}
  growBy (Vec v) n = Vec <$> UV.unsafeGrow v n
  asList (Vec v) = mapM (getNth v) [1 .. UV.length v - 1]
  dump str _ = return $ str ++ "Vec dump"

instance VecFamily (Vec Double) Double where
  {-# SPECIALIZE INLINE getNth :: Vec Double -> Int -> IO Double #-}
  getNth (Vec v) = UV.unsafeRead v
  {-# SPECIALIZE INLINE setNth :: Vec Double -> Int -> Double -> IO () #-}
  setNth (Vec v) = UV.unsafeWrite v
  {-# SPECIALIZE INLINE modifyNth :: Vec Double -> (Double -> Double) -> Int -> IO () #-}
  modifyNth (Vec v) = UV.unsafeModify v
  {-# SPECIALIZE INLINE swapBetween :: Vec Double -> Int -> Int -> IO () #-}
  swapBetween (Vec v) = UV.unsafeSwap v
  {-# SPECIALIZE INLINE newVec :: Int -> Double -> IO (Vec Double) #-}
  newVec n x = Vec <$> newVec (n + 1) x
  {-# SPECIALIZE INLINE setAll :: Vec Double -> Double -> IO () #-}
  setAll (Vec v) = UV.set v
  {-# SPECIALIZE INLINE growBy :: Vec Double -> Int -> IO (Vec Double) #-}
  growBy (Vec v) n = Vec <$> UV.unsafeGrow v n

-------------------------------------------------------------------------------- SingleStorage

-- | Interface for single mutable data
class SingleStorage s t | s -> t where
  -- | allocates and returns an new data.
  new' :: t -> IO s
  -- | gets the value.
  get' :: s -> IO t
  -- | sets the value.
  set' :: s -> t -> IO ()
  -- | calls an update function on it.
  modify' :: s -> (t -> t) -> IO ()
  {-# MINIMAL get', set' #-}
  new' = undefined
  modify' = undefined

-- | Mutable Int
-- __Note:__  Int' is the same with 'Stack'
type Int' = UV.IOVector Int

instance SingleStorage Int' Int where
  {-# SPECIALIZE INLINE new' :: Int -> IO Int' #-}
  new' k = do
    s <- UV.new 1
    UV.unsafeWrite s 0 k
    return s
  {-# SPECIALIZE INLINE get' :: Int' -> IO Int #-}
  get' val = UV.unsafeRead val 0
  {-# SPECIALIZE INLINE set' :: Int' -> Int -> IO () #-}
  set' val !x = UV.unsafeWrite val 0 x
  {-# SPECIALIZE INLINE modify' :: Int' -> (Int -> Int) -> IO () #-}
  modify' val f = UV.unsafeModify val f 0

-- | Mutable Bool
type Bool' = UV.IOVector Bool

instance SingleStorage Bool' Bool where
  {-# SPECIALIZE INLINE new' :: Bool -> IO Bool' #-}
  new' k = do
    s <- UV.new 1
    UV.unsafeWrite s 0 k
    return s
  {-# SPECIALIZE INLINE get' :: Bool' -> IO Bool #-}
  get' val = UV.unsafeRead val 0
  {-# SPECIALIZE INLINE set' :: Bool' -> Bool -> IO () #-}
  set' val !x = UV.unsafeWrite val 0 x
  {-# SPECIALIZE INLINE modify' :: Bool' -> (Bool -> Bool) -> IO () #-}
  modify' val f = UV.unsafeModify val f 0

-- | Mutable Double
type Double' = UV.IOVector Double

instance SingleStorage Double' Double where
  {-# SPECIALIZE INLINE new' :: Double -> IO Double' #-}
  new' k = do
    s <- UV.new 1
    UV.unsafeWrite s 0 k
    return s
  {-# SPECIALIZE INLINE get' :: Double' -> IO Double #-}
  get' val = UV.unsafeRead val 0
  {-# SPECIALIZE INLINE set' :: Double' -> Double -> IO () #-}
  set' val !x = UV.unsafeWrite val 0 x
  {-# SPECIALIZE INLINE modify' :: Double' -> (Double -> Double) -> IO () #-}
  modify' val f = UV.unsafeModify val f 0

-------------------------------------------------------------------------------- Stack

-- | Interface on stacks
class SingleStorage s Int => StackFamily s t | s -> t where
  -- | returns a new stack.
  newStack :: Int -> IO s
  -- | pushs an value to the tail of the stack.
  pushTo :: s -> t-> IO ()
  -- | pops the last element.
  popFrom :: s -> IO ()
  -- | peeks the last element.
  lastOf :: s -> IO t
  -- | shrinks the stack.
  shrinkBy :: s -> Int -> IO ()
  newStack = undefined
  pushTo = undefined
  popFrom = undefined
  lastOf = undefined
  shrinkBy = undefined

-- | Alias of @Vec Int@. The 0-th element holds the number of elements.
type Stack = Vec Int

instance SingleStorage Stack Int where
  {-# SPECIALIZE INLINE get' :: Stack -> IO Int #-}
  get' (Vec v) = UV.unsafeRead v 0
  {-# SPECIALIZE INLINE set' :: Stack -> Int -> IO () #-}
  set' (Vec v) !x = UV.unsafeWrite v 0 x
  {-# SPECIALIZE INLINE modify' :: Stack -> (Int -> Int) -> IO () #-}
  modify' (Vec v) f = UV.unsafeModify v f 0

instance StackFamily Stack Int where
  {-# SPECIALIZE INLINE newStack :: Int -> IO Stack #-}
  newStack n = newVec n 0
  {-# SPECIALIZE INLINE pushTo :: Stack -> Int -> IO () #-}
  pushTo (Vec v) x = do
    i <- (+ 1) <$> UV.unsafeRead v 0
    UV.unsafeWrite v i x
    UV.unsafeWrite v 0 i
  {-# SPECIALIZE INLINE popFrom :: Stack -> IO () #-}
  popFrom (Vec v) = UV.unsafeModify v (subtract 1) 0
  {-# SPECIALIZE INLINE lastOf :: Stack -> IO Int #-}
  lastOf (Vec v) = UV.unsafeRead v =<< UV.unsafeRead v 0
  {-# SPECIALIZE INLINE shrinkBy :: Stack -> Int -> IO () #-}
  shrinkBy (Vec v) k = UV.unsafeModify v (subtract k) 0

-- | returns a new 'Stack' from @[Int]@.
{-# INLINABLE newStackFromList #-}
newStackFromList :: [Int] -> IO Stack
newStackFromList !l = Vec <$> U.unsafeThaw (U.fromList (length l : l))
