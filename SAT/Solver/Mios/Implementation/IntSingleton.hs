{-# LANGUAGE
    BangPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module SAT.Solver.Mios.Implementation.IntSingleton
       (
         IntSingleton
       , newInt
       , getInt
       , setInt
       , modifyInt
       )
       where

import Data.IORef

type IntSingleton = IORef Int

newInt :: IO IntSingleton
newInt = newIORef 0

{-# INLINE getInt #-}
getInt :: IntSingleton -> IO Int
getInt = readIORef

{-# INLINE setInt #-}
setInt :: IntSingleton -> Int -> IO ()
setInt = writeIORef

{-# INLINE modifyInt #-}
modifyInt :: IntSingleton -> (Int -> Int) -> IO ()
modifyInt = modifyIORef'

{-
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
{-
import qualified Data.Vector.Unboxed.Mutable as UV

newtype IntSingleton = IntSingleton
                       {
                         mutableInt :: UV.IOVector Int
                       }

newInt :: IO IntSingleton
newInt = IntSingleton <$> UV.new 1

{-# INLINE getInt #-}
getInt :: IntSingleton -> IO Int
getInt !(IntSingleton val) = UV.unsafeRead val 0

{-# INLINE setInt #-}
setInt :: IntSingleton -> Int -> IO ()
setInt !(IntSingleton val) !x = UV.unsafeWrite val 0 x

{-# INLINE modifyInt #-}
modifyInt :: IntSingleton -> (Int -> Int) -> IO ()
modifyInt !(IntSingleton val) !f = UV.unsafeModify val f 0
-}
