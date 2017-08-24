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
         -- * Vector class and type
         VecFamily (..)
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

import qualified Data.Vector.Unboxed.Mutable as UV
import qualified Data.Primitive.ByteArray as BA
import Control.Monad.Primitive

-------------------------------------------------------------------------------- VecFamily
-- | The interface on vectors.
class VecFamily v a | v -> a where
  -- | returns the /n/-th value.
  getNth ::v -> Int -> IO a
  -- | sets the /n/-th value.
  setNth :: v -> Int -> a -> IO ()
  -- | erases all elements in it.
  reset:: v -> IO ()
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
  -- | converts to a list.
  asList :: v -> IO [a]
  {-# MINIMAL getNth, setNth #-}
  reset = errorWithoutStackTrace "no default method: reset"
  swapBetween = errorWithoutStackTrace "no default method: swapBetween"
  modifyNth = errorWithoutStackTrace "no default method: modifyNth"
  newVec = errorWithoutStackTrace "no default method: newVec"
  setAll = errorWithoutStackTrace "no default method: setAll"
  asList = errorWithoutStackTrace "no default method: asList"
  growBy = errorWithoutStackTrace "no default method: growBy"
  -- | (FOR DEBUG) dump the contents.
  -- dump :: Show a => String -> v -> IO String
  -- dump msg v = (msg ++) . show <$> asList v

-------------------------------------------------------------------------------- Vec
-- | Another abstraction layer on 'Vector' which reserves zero element for internal use.
-- __Note__: If you want to use the 0-th element, use @UVector Int@.

data family Vec a;

-------------------------------------------------------------------------------- UVector

-- | A thin abstract layer for mutable unboxed Vector
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
  newVec n x = do v <- UV.new n
                  UV.set v x
                  return v
  {-# SPECIALIZE INLINE setAll :: UVector Int -> Int -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growBy :: UVector Int -> Int -> IO (UVector Int) #-}
  growBy = UV.unsafeGrow
  asList v = mapM (UV.unsafeRead v) [0 .. UV.length v - 1]

-- Note: type @[Int]@ is selected for 'UVector' not to export it.
data instance Vec [Int] = Vec (UVector Int)

instance VecFamily (Vec [Int]) Int where
  {-# SPECIALIZE INLINE getNth :: Vec [Int] -> Int -> IO Int #-}
  getNth (Vec v) = UV.unsafeRead v
  {-# SPECIALIZE INLINE setNth :: Vec [Int] -> Int -> Int -> IO () #-}
  setNth (Vec v) = UV.unsafeWrite v
  {-# SPECIALIZE INLINE reset :: Vec [Int] -> IO () #-}
  reset (Vec v) = setNth v 0 0
  {-# SPECIALIZE INLINE modifyNth :: Vec [Int] -> (Int -> Int) -> Int -> IO () #-}
  modifyNth (Vec v) = UV.unsafeModify v
  {-# SPECIALIZE INLINE swapBetween :: Vec [Int] -> Int -> Int -> IO () #-}
  swapBetween (Vec v) = UV.unsafeSwap v
  {-# SPECIALIZE INLINE newVec :: Int -> Int -> IO (Vec [Int]) #-}
  newVec n x = Vec <$> newVec (n + 1) x
  {-# SPECIALIZE INLINE setAll :: Vec [Int] -> Int -> IO () #-}
  setAll (Vec v) = UV.set v
  {-# SPECIALIZE INLINE growBy :: Vec [Int] -> Int -> IO (Vec [Int]) #-}
  growBy (Vec v) n = Vec <$> UV.unsafeGrow v n
  asList (Vec v) = mapM (getNth v) [1 .. UV.length v - 1]

{- NOT IN USE
data instance Vec [Double] = Vec (UVector Double)

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
  newVec n x = do v <- UV.new n
                  UV.set v x
                  return v
  {-# SPECIALIZE INLINE setAll :: UVector Double -> Double -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growBy :: UVector Double -> Int -> IO (UVector Double) #-}
  growBy = UV.unsafeGrow
  asList v = mapM (UV.unsafeRead v) [0 .. UV.length v - 1]

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
-}

-------------------------------------------------------------------------------- ByteArray

data instance Vec Int = ByteArrayInt (BA.MutableByteArray RealWorld)
data instance Vec Double = ByteArrayDouble (BA.MutableByteArray RealWorld)

type ByteArrayInt = Vec Int
type ByteArrayDouble = Vec Double

instance VecFamily ByteArrayInt Int where
  {-# SPECIALIZE INLINE getNth :: ByteArrayInt -> Int -> IO Int #-}
  getNth (ByteArrayInt v) i = BA.readByteArray v i
  {-# SPECIALIZE INLINE setNth :: ByteArrayInt -> Int -> Int -> IO () #-}
  setNth (ByteArrayInt v) i x = BA.writeByteArray v i x
  {-# SPECIALIZE INLINE modifyNth :: ByteArrayInt -> (Int -> Int) -> Int -> IO () #-}
  modifyNth (ByteArrayInt v) f i = BA.writeByteArray v i . f =<< BA.readByteArray v i
  {-# SPECIALIZE INLINE swapBetween:: ByteArrayInt -> Int -> Int -> IO () #-}
  swapBetween (ByteArrayInt v) i j = do x <- BA.readByteArray v i
                                        y <- BA.readByteArray v j
                                        BA.writeByteArray v i (y :: Int)
                                        BA.writeByteArray v j (x :: Int)
  {-# SPECIALIZE INLINE reset :: ByteArrayInt -> IO () #-}
  reset (ByteArrayInt v) = BA.writeByteArray v 0 (0 :: Int)
  newVec n k = do v <- BA.newByteArray (8 * (n + 1))
                  BA.writeByteArray v 0 (0 :: Int)
                  BA.setByteArray v 1 n k
                  return $ ByteArrayInt v
  asList (ByteArrayInt v) = mapM (BA.readByteArray v) [1 .. div (BA.sizeofMutableByteArray v) 8 - 1]

instance VecFamily ByteArrayDouble Double where
  {-# SPECIALIZE INLINE getNth :: ByteArrayDouble -> Int -> IO Double #-}
  getNth (ByteArrayDouble v) i = BA.readByteArray v i
  {-# SPECIALIZE INLINE setNth :: ByteArrayDouble -> Int -> Double -> IO () #-}
  setNth (ByteArrayDouble v) i x = BA.writeByteArray v i x
  {-# SPECIALIZE INLINE modifyNth :: ByteArrayDouble -> (Double -> Double) -> Int -> IO () #-}
  modifyNth (ByteArrayDouble v) f i = BA.writeByteArray v i . f =<< BA.readByteArray v i
  {-# SPECIALIZE INLINE swapBetween:: ByteArrayDouble -> Int -> Int -> IO () #-}
  swapBetween (ByteArrayDouble v) i j = do x <- BA.readByteArray v i
                                           y <- BA.readByteArray v j
                                           BA.writeByteArray v i (y :: Int)
                                           BA.writeByteArray v j (x :: Int)
  {-# SPECIALIZE INLINE reset :: ByteArrayDouble -> IO () #-}
  reset (ByteArrayDouble v) = BA.writeByteArray v 0 (0 :: Double)
  newVec n k = do v <- BA.newByteArray (8 * (n + 1))
                  BA.writeByteArray v 0 (0 :: Double)
                  BA.setByteArray v 1 n k
                  return $ ByteArrayDouble v
  asList (ByteArrayDouble v) = mapM (BA.readByteArray v) [1 .. div (BA.sizeofMutableByteArray v) 8 - 1]

-------------------------------------------------------------------------------- SingleStorage

-- | Interface for single (one-length vector) mutable data
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

-- | Mutable Bool
type Bool' = UV.IOVector Bool

instance SingleStorage Bool' Bool where
  {-# SPECIALIZE INLINE new' :: Bool -> IO Bool' #-}
  new' k = do s <- UV.new 1
              UV.unsafeWrite s 0 k
              return s
  {-# SPECIALIZE INLINE get' :: Bool' -> IO Bool #-}
  get' val = UV.unsafeRead val 0
  {-# SPECIALIZE INLINE set' :: Bool' -> Bool -> IO () #-}
  set' val !x = UV.unsafeWrite val 0 x
  {-# SPECIALIZE INLINE modify' :: Bool' -> (Bool -> Bool) -> IO () #-}
  modify' val f = UV.unsafeModify val f 0

-- | Mutable Int
-- __Note:__  Int' is identical to 'Stack'
type Int' = ByteArrayInt

instance SingleStorage ByteArrayInt Int where
  {-# SPECIALIZE INLINE new' :: Int -> IO ByteArrayInt #-}
  new' k = do s <- BA.newByteArray 8
              BA.writeByteArray s 0 k
              return $ ByteArrayInt s
  {-# SPECIALIZE INLINE get' :: ByteArrayInt -> IO Int #-}
  get' (ByteArrayInt v) = BA.readByteArray v 0
  {-# SPECIALIZE INLINE set' :: ByteArrayInt -> Int -> IO () #-}
  set' (ByteArrayInt v) !x = BA.writeByteArray v 0 x
  {-# SPECIALIZE INLINE modify' :: ByteArrayInt -> (Int -> Int) -> IO () #-}
  modify' (ByteArrayInt v) f = BA.writeByteArray v 0 . f =<< BA.readByteArray v 0

-- | Mutable Double
type Double' = ByteArrayDouble

instance SingleStorage ByteArrayDouble Double where
  {-# SPECIALIZE INLINE new' :: Double -> IO ByteArrayDouble #-}
  new' k = do s <- BA.newByteArray 8
              BA.writeByteArray s 0 k
              return $ ByteArrayDouble s
  {-# SPECIALIZE INLINE get' :: ByteArrayDouble -> IO Double #-}
  get' (ByteArrayDouble v) = BA.readByteArray v 0
  {-# SPECIALIZE INLINE set' :: ByteArrayDouble -> Double -> IO () #-}
  set' (ByteArrayDouble v) !x = BA.writeByteArray v 0 x
  {-# SPECIALIZE INLINE modify' :: ByteArrayDouble -> (Double -> Double) -> IO () #-}
  modify' (ByteArrayDouble v) f = BA.writeByteArray v 0 . f =<< BA.readByteArray v 0

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

type Stack = Vec Int

instance StackFamily ByteArrayInt Int where
  {-# SPECIALIZE INLINE newStack :: Int -> IO ByteArrayInt #-}
  newStack n = do s <- newVec (2 * n) 0
                  setNth s 0 (0::Int)
                  return s
  {-# SPECIALIZE INLINE pushTo :: ByteArrayInt -> Int -> IO () #-}
  pushTo (ByteArrayInt v) x = do i <- (+ 1) <$> (BA.readByteArray v 0 :: IO Int)
                                 BA.writeByteArray v i x
                                 BA.writeByteArray v 0 i
  {-# SPECIALIZE INLINE popFrom :: ByteArrayInt -> IO () #-}
  popFrom (ByteArrayInt v) = BA.writeByteArray v 0 . subtract 1 =<< (BA.readByteArray v 0 :: IO Int)
  {-# SPECIALIZE INLINE lastOf :: ByteArrayInt -> IO Int #-}
  lastOf (ByteArrayInt v) = BA.readByteArray v =<< BA.readByteArray v 0
  {-# SPECIALIZE INLINE shrinkBy :: ByteArrayInt -> Int -> IO () #-}
  shrinkBy (ByteArrayInt v) k = BA.writeByteArray v 0 . subtract k =<< (BA.readByteArray v 0 :: IO Int)

-- | returns a new 'Stack' from @[Int]@.
{-# INLINABLE newStackFromList #-}
newStackFromList :: [Int] -> IO Stack
newStackFromList l = do
  v <- BA.newByteArray (8 * (length l + 1))
  let loop :: [Int] -> Int -> IO Stack
      loop [] _ = return $ ByteArrayInt v
      loop (x:l') i = BA.writeByteArray v i x >> loop l' (i + 1)
  loop (length l : l) 0
