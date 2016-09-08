{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Trustworthy #-}

-- | Abstraction Layer for Mutable Unboxed Vectors
module SAT.Mios.Vec
       (
         -- * Unboxed Vector
         UVector
         -- * Vector
       , VectorFamily (..)
       , Vec (..)
       , VecFamily (..)
         -- * Stack
       , StackFamily (..)
       , Stack
       , newStackFromList
         -- * SingleStroage
       , SingleStorage (..)
       , Bool'
       , Double'
       , Int'
       )
       where

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UV

-- | Public interface as /Container/
class VectorFamily s t | s -> t where
  -- * Size operations
  -- | erases all elements in it
  clear :: s -> IO ()
  clear = error "no default method for clear"
  -- | get a raw data
  asUVector :: s -> UVector Int
  asUVector = error "asVector undefined"
  -- | converts into a list
  asList :: s -> IO [t]
  asList = error "asList undefined"
  {-# MINIMAL dump #-}
  -- * Debug
  -- | dump the contents
  dump :: Show t => String -> s -> IO String
  dump msg _ = error $ msg ++ ": no defalut method for dump"

-- | provides 'clear' and 'size'

{-
instance VectorFamily (Vec Bool) Bool where
  asList (Vec v) = mapM (getNth v) [1 .. UV.length v]
  dump str _ = return $ str ++ "Vec dump"
-}

instance UV.Unbox a => VectorFamily (UVector a) a where
  asList v = mapM (UV.unsafeRead v) [0 .. UV.length v - 1]
  dump str v = (str ++) . show <$> asList v

instance VectorFamily (Vec Int) Int where
  clear (Vec v) = setNth v 0 0
  asUVector (Vec a) = UV.unsafeTail a
  asList (Vec v) = mapM (getNth v) [1 .. UV.length v - 1]
  dump str _ = return $ str ++ "Vec dump"

-- | A thin abstract layer for Mutable unboxed Vector

type UVector a = UV.IOVector a

class VecFamily v a | v -> a where
  newVec :: Int -> a -> IO v
  getNth ::v -> Int -> IO a
  setNth :: v -> Int -> a -> IO ()
  modifyNth :: v -> (a -> a) -> Int -> IO ()
  swapBetween :: v -> Int -> Int -> IO ()
  setAll :: v -> a -> IO ()
  growVec :: v -> Int -> IO v

instance VecFamily (UVector Int) Int where
  {-# SPECIALIZE INLINE newVec :: Int -> Int -> IO (UVector Int) #-}
  newVec n 0 = UV.new n
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: UVector Int -> Int -> IO Int #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Int -> Int -> Int -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Int -> (Int -> Int) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Int -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: UVector Int -> Int -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growVec :: UVector Int -> Int -> IO (UVector Int) #-}
  growVec = UV.unsafeGrow

instance VecFamily (UVector Bool) Bool where
  {-# SPECIALIZE INLINE newVec :: Int -> Bool -> IO (UVector Bool) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: UVector Bool -> Int -> IO Bool #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Bool -> Int -> Bool -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Bool -> (Bool -> Bool) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Bool -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: UVector Bool -> Bool -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growVec :: UVector Bool -> Int -> IO (UVector Bool) #-}
  growVec = UV.unsafeGrow

instance VecFamily (UVector Double) Double where
  {-# SPECIALIZE INLINE newVec :: Int -> Double -> IO (UVector Double) #-}
  newVec n x = do
    v <- UV.new n
    UV.set v x
    return v
  {-# SPECIALIZE INLINE getNth :: UVector Double -> Int -> IO Double #-}
  getNth = UV.unsafeRead
  {-# SPECIALIZE INLINE setNth :: UVector Double -> Int -> Double -> IO () #-}
  setNth = UV.unsafeWrite
  {-# SPECIALIZE INLINE modifyNth :: UVector Double -> (Double -> Double) -> Int -> IO () #-}
  modifyNth = UV.unsafeModify
  {-# SPECIALIZE INLINE swapBetween:: UVector Double -> Int -> Int -> IO () #-}
  swapBetween = UV.unsafeSwap
  {-# SPECIALIZE INLINE setAll :: UVector Double -> Double -> IO () #-}
  setAll = UV.set
  {-# SPECIALIZE INLINE growVec :: UVector Double -> Int -> IO (UVector Double) #-}
  growVec = UV.unsafeGrow

--------------------------------------------------------------------------------

newtype Vec a  = Vec (UVector a)

instance VecFamily (Vec Int) Int where
  newVec n x = Vec <$> newVec (n + 1) x
  {-# SPECIALIZE INLINE getNth :: Vec Int -> Int -> IO Int #-}
  getNth (Vec v) = UV.unsafeRead v
  {-# SPECIALIZE INLINE setNth :: Vec Int -> Int -> Int -> IO () #-}
  setNth (Vec v) = UV.unsafeWrite v
  {-# SPECIALIZE INLINE modifyNth :: Vec Int -> (Int -> Int) -> Int -> IO () #-}
  modifyNth (Vec v) = UV.unsafeModify v
  {-# SPECIALIZE INLINE swapBetween :: Vec Int -> Int -> Int -> IO () #-}
  swapBetween (Vec v) = UV.unsafeSwap v
  {-# SPECIALIZE INLINE setAll :: Vec Int -> Int -> IO () #-}
  setAll (Vec v) = UV.set v
  {-# SPECIALIZE INLINE growVec :: Vec Int -> Int -> IO (Vec Int) #-}
  growVec (Vec v) n = Vec <$> UV.unsafeGrow v n

{-
instance VecFamily (Vec Bool) Bool where
  newVec n x = Vec <$> newVec (n + 1) x
  {-# SPECIALIZE INLINE getNth :: Vec Bool -> Int -> IO Bool #-}
  getNth (Vec v) = UV.unsafeRead v
  {-# SPECIALIZE INLINE setNth :: Vec Bool -> Int -> Bool -> IO () #-}
  setNth (Vec v) = UV.unsafeWrite v
  {-# SPECIALIZE INLINE modifyNth :: Vec Bool -> (Bool -> Bool) -> Int -> IO () #-}
  modifyNth (Vec v) = UV.unsafeModify v
  {-# SPECIALIZE INLINE swapBetween :: Vec Bool -> Int -> Int -> IO () #-}
  swapBetween (Vec v) = UV.unsafeSwap v
  {-# SPECIALIZE INLINE setAll :: Vec Bool -> Bool -> IO () #-}
  setAll (Vec v) = UV.set v
  {-# SPECIALIZE INLINE growVec :: Vec Bool -> Int -> IO (Vec Bool) #-}
  growVec (Vec v) n = Vec <$> UV.unsafeGrow v n
-}

instance VecFamily (Vec Double) Double where
  newVec n x = Vec <$> newVec (n + 1) x
  {-# SPECIALIZE INLINE getNth :: Vec Double -> Int -> IO Double #-}
  getNth (Vec v) = UV.unsafeRead v
  {-# SPECIALIZE INLINE setNth :: Vec Double -> Int -> Double -> IO () #-}
  setNth (Vec v) = UV.unsafeWrite v
  {-# SPECIALIZE INLINE modifyNth :: Vec Double -> (Double -> Double) -> Int -> IO () #-}
  modifyNth (Vec v) = UV.unsafeModify v
  {-# SPECIALIZE INLINE swapBetween :: Vec Double -> Int -> Int -> IO () #-}
  swapBetween (Vec v) = UV.unsafeSwap v
  {-# SPECIALIZE INLINE setAll :: Vec Double -> Double -> IO () #-}
  setAll (Vec v) = UV.set v
  {-# SPECIALIZE INLINE growVec :: Vec Double -> Int -> IO (Vec Double) #-}
  growVec (Vec v) n = Vec <$> UV.unsafeGrow v n

-------------------------------------------------------------------------------- Stack

type Stack = Vec Int

class StackFamily s t | s -> t where
  newStack :: Int -> IO s
  sizeOf :: s -> IO Int
  pushTo :: s -> t-> IO ()
  popFrom :: s -> IO ()
  lastOf :: s -> IO t
  shrinkBy :: s -> Int -> IO ()
  
instance StackFamily Stack Int where
  newStack n = newVec n 0
  {-# SPECIALIZE INLINE sizeOf :: Stack -> IO Int #-}
  sizeOf (Vec v) = getNth v 0
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

-- | returns a new 'Stack' from a @[Int]@
{-# INLINE newStackFromList #-}
newStackFromList :: [Int] -> IO Stack
newStackFromList !l = Vec <$> U.unsafeThaw (U.fromList (length l : l))

-------------------------------------------------------------------------------- Single storage

class SingleStorage s t | s -> t, t -> s where
  new' :: t -> IO s
  get' :: s -> IO t
  set' :: s -> t -> IO ()
  modify' :: s -> (t -> t) -> IO ()

-- | mutable Int
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

-- | mutable Bool
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

-- | mutable Double
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
