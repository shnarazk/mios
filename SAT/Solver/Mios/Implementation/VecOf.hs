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
  removeElem x VecOf{..} = error "VecOf.removeElem undefined"
  -- * Vector operations
  {--- # SPECIALIZE INLINE (.!) :: VecOf a -> Int -> IO a #-}
  (.!) VecOf{..} n = (!! n) <$> readIORef ptr
  {--- # SPECIALIZE INLINE setAt :: VecOf a -> Int -> a -> IO () #-}
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
