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
-- * __VecOf a__  @:: IORef [a]@ -- data type that contains a mutable list of elements
--
module SAT.Solver.Mios.Implementation.VecOf
       (
         VecOf (..)
       , sizeOfVec
       , push'
       , pop'
       , lastE'
       )
       where

import Control.Monad (unless, when)
import Data.IORef
import Data.List (sortOn)
import SAT.Solver.Mios.Types (ContainerLike(..), VectorLike(..))

-- | __version 0.1__
--
-- Costs of all operations are /O/(/n/)
newtype VecOf a = VecOf
                  {
                    ptr :: IORef [a] -- ^ reference pointer to the data
                  }

sizeOfVec :: VecOf a -> IO Int
sizeOfVec VecOf{..} = length <$> readIORef ptr

-- | provides 'clear' and 'size'
instance ContainerLike (VecOf a) a where
  clear VecOf{..} = writeIORef ptr []
  asList VecOf{..} = readIORef ptr
  dump str VecOf{..} = (str ++) . show <$> readIORef ptr

-- | constructors, resize, stack, vector, and duplication operations
instance VectorLike (VecOf a) a where
  -- * Constructors
  newVec n = VecOf <$> newIORef (replicate n undefined)
  newVecWith n x = VecOf <$> newIORef (replicate n x)
  -- * Vector operations
  {--- # SPECIALIZE INLINE getAt :: Int -> VecOf a -> IO a #-}
  getAt n VecOf{..} = (!! n) <$> readIORef ptr
  {--- # SPECIALIZE INLINE setAt :: Int -> VecOf a -> a -> IO () #-}
  setAt n VecOf{..} x = do
    l <- readIORef ptr
    writeIORef ptr $ take n l ++ (x : drop (n + 1) l)
  -- * Conversion
  newFromList l = VecOf <$> newIORef l

{-# INLINE push' #-}
push' :: VecOf Int -> Int -> IO ()
push' !VecOf{..} !x = modifyIORef' ptr (x :)

{-# INLINE pop' #-}
pop' :: VecOf Int -> IO ()
pop' VecOf{..} = do
  l <- readIORef ptr
  unless (null l) $ writeIORef ptr $ tail l

{-# INLINE lastE' #-}
lastE' :: VecOf Int -> IO Int
lastE' VecOf{..} = head <$> readIORef ptr

-- | unit test function
checkImplementation :: IO ()
checkImplementation = do
  return ()

sortVecOn :: (Ord b) => (a -> IO b) -> VecOf a -> IO ()
sortVecOn f VecOf{..} = writeIORef ptr . map snd . sortOn fst =<< mapM (\i -> (, i) <$> f i) =<< readIORef ptr
