-- | A fast(est) mutable data
{-# LANGUAGE
    BangPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Solver.Mios.Data.Singleton
       (
         -- * Bool
         BoolSingleton
       , newBool
       , getBool
       , setBool
       , modifyBool
         -- * Int
       , IntSingleton
       , newInt
       , getInt
       , setInt
       , modifyInt
         -- * Double
       , DoubleSingleton
       , newDouble
       , getDouble
       , setDouble
       , modifyDouble
       )
       where
{-
----------------------------------------
-- Implementation 1. :: IORef
----------------------------------------

import Data.IORef

type BoolSingleton = IORef Bool

newBool :: Bool -> IO BoolSingleton
newBool = newIORef

{-# INLINE getBool #-}
getBool :: BoolSingleton -> IO Bool
getBool = readIORef

{-# INLINE setBool #-}
setBool :: BoolSingleton -> Bool -> IO ()
setBool = writeIORef

{-# INLINE modifyBool #-}
modifyBool :: BoolSingleton -> (Bool -> Bool) -> IO ()
modifyBool = modifyIORef'

type IntSingleton = IORef Int

newInt :: Int -> IO IntSingleton
newInt = newIORef

{-# INLINE getInt #-}
getInt :: IntSingleton -> IO Int
getInt = readIORef

{-# INLINE setInt #-}
setInt :: IntSingleton -> Int -> IO ()
setInt = writeIORef

{-# INLINE modifyInt #-}
modifyInt :: IntSingleton -> (Int -> Int) -> IO ()
modifyInt = modifyIORef'

type DoubleSingleton = IORef Double

newDouble :: Double -> IO DoubleSingleton
newDouble = newIORef

{-# INLINE getDouble #-}
getDouble :: DoubleSingleton -> IO Double
getDouble = readIORef

{-# INLINE setDouble #-}
setDouble :: DoubleSingleton -> Double -> IO ()
setDouble = writeIORef

{-# INLINE modifyDouble #-}
modifyDouble :: DoubleSingleton -> (Double -> Double) -> IO ()
modifyDouble = modifyIORef'
-}
{-
----------------------------------------
-- Implementation 2. :: Data.Mutable.IOURef
----------------------------------------

import qualified Data.Mutable as M

newtype IntSingleton = IntSingleton
                       {
                         mutableInt :: M.IOURef Int
                       }

newInt :: IO IntSingleton
newInt = IntSingleton <$> M.newRef 0

{-# INLINE getInt #-}
getInt :: IntSingleton -> IO Int
getInt !(IntSingleton val) = M.readRef val

{-# INLINE setInt #-}
setInt :: IntSingleton -> Int -> IO ()
setInt !(IntSingleton val) !x = M.writeRef val x

{-# INLINE modifyInt #-}
modifyInt :: IntSingleton -> (Int -> Int) -> IO ()
modifyInt !(IntSingleton val) !f = M.modifyRef' val f
-}

-- {-
----------------------------------------
-- Implementation 3. :: Data.Vector.Unboxed.Mutable
----------------------------------------

import qualified Data.Vector.Unboxed.Mutable as UV

type IntSingleton = UV.IOVector Int

newInt :: Int -> IO IntSingleton
newInt k = do
  s <- UV.new 1
  UV.unsafeWrite s 0 k
  return s

{-# INLINE getInt #-}
getInt :: IntSingleton -> IO Int
getInt val = UV.unsafeRead val 0

{-# INLINE setInt #-}
setInt :: IntSingleton -> Int -> IO ()
setInt val !x = UV.unsafeWrite val 0 x

{-# INLINE modifyInt #-}
modifyInt :: IntSingleton -> (Int -> Int) -> IO ()
modifyInt val !f = UV.unsafeModify val f 0

type BoolSingleton = UV.IOVector Bool

newBool :: Bool -> IO BoolSingleton
newBool b = do
  s <- UV.new 1
  UV.unsafeWrite s 0 b
  return s

{-# INLINE getBool #-}
getBool :: BoolSingleton -> IO Bool
getBool val = UV.unsafeRead val 0

{-# INLINE setBool #-}
setBool :: BoolSingleton -> Bool -> IO ()
setBool val !x = UV.unsafeWrite val 0 x

{-# INLINE modifyBool #-}
modifyBool :: BoolSingleton -> (Bool -> Bool) -> IO ()
modifyBool val !f = UV.unsafeModify val f 0

type DoubleSingleton = UV.IOVector Double

newDouble :: Double -> IO DoubleSingleton
newDouble d = do
  s <- UV.new 1
  UV.unsafeWrite s 0 d
  return s

{-# INLINE getDouble #-}
getDouble :: DoubleSingleton -> IO Double
getDouble val = UV.unsafeRead val 0

{-# INLINE setDouble #-}
setDouble :: DoubleSingleton -> Double -> IO ()
setDouble val !x = UV.unsafeWrite val 0 x

{-# INLINE modifyDouble #-}
modifyDouble :: DoubleSingleton -> (Double -> Double) -> IO ()
modifyDouble val !f = UV.unsafeModify val f 0
-- -}
