{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , UndecidableInstances
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

-- | __Version 0.8__
--
-- Watcher list structure based on /pointer/
module SAT.Solver.Mios.WatchList
       (
         WatchLink
       , newWatchLink
       , nextWatcher
       , pushWatcher
       , unlinkWatcher
       , removeWatcher
       , mergeWatcher
       , traverseWatcher
       , asListWatchers
         -- * the watcher manager
       , WatcherList
       , newWatcherList
       , getNthWatchLink
       )
       where

import Control.Monad (forM_, when)
import Data.IORef
import Data.List (sort)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import SAT.Solver.Mios.Types (ContainerLike(..), Lit)
import SAT.Solver.Mios.Clause (Clause(..), ClausePointer, derefClausePointer, newClausePointer, setClausePointer, selectWatcher)


-- | __Version 0.5__
-- the definition of 'watcher'
type WatchLink = (ClausePointer, ClausePointer)

newWatchLink :: IO WatchLink
newWatchLink = (,) <$> newClausePointer NullClause <*> newClausePointer NullClause

-- | returns a watcher next to /the given clause/, or returns NullClause if no more watcher.
-- If the given clause is NullClasue, this returns the first clause of the watcher list.
{-# INLINE nextWatcher #-}
nextWatcher :: WatchLink -> Lit -> Clause -> IO Clause
nextWatcher !(b, _) _ NullClause = derefClausePointer b
nextWatcher _ l c                = derefClausePointer =<< selectWatcher l c

-- | adds a clause to the end of a watcher list
{-# INLINE pushWatcher #-}
pushWatcher :: WatchLink -> Lit -> Clause -> IO ()
pushWatcher !(b, e) !l !c = do
  c' <- derefClausePointer e
  n <- if c' == NullClause then return b else selectWatcher l c'
  setClausePointer n c
  setClausePointer e c
  n' <- selectWatcher l c
  setClausePointer n' NullClause

-- | unlinks a clause from the previous clasue and returns the new next clause.
-- If the given clause is @NullClause@, then the watcher list for /lit/ is updated.
-- This is the case to remove the first clause of a watcher list.
{-# INLINE unlinkWatcher #-}
unlinkWatcher :: WatchLink -> Lit -> Clause -> IO Clause
unlinkWatcher !(b, e) !l !c = do
  n <- if c == NullClause then return b else selectWatcher l c
  c' <- derefClausePointer n
  c'' <- derefClausePointer =<< selectWatcher l c'
  setClausePointer n c''
  when (c'' == NullClause) $ setClausePointer e c
  return c'

-- | __O(n) search and delete operation__
-- Don't use it in critial path.
{-# INLINE removeWatcher #-}
removeWatcher :: WatchLink -> Lit -> Clause -> IO ()
removeWatcher !w@(b, _) !l !c = do
  let
    -- invaliant: c should be included in the watcher list
    loop :: Clause -> IO ()
    loop !pre = do
      !c' <- if pre == NullClause then derefClausePointer b else nextWatcher w l pre
      if c == c'
        then unlinkWatcher w l pre >> return ()
        else loop c'
  loop NullClause

traverseWatcher :: WatchLink -> Lit -> IO [[Lit]]
traverseWatcher (b, _) lit = do
  let
    loop :: Clause -> IO [[Lit]]
    loop NullClause = return []
    loop c = do
      l' <- asList c
      (l' :) <$> (loop =<< derefClausePointer =<< selectWatcher lit c)
  loop =<< derefClausePointer b

{-# INLINE mergeWatcher #-}
mergeWatcher :: WatchLink -> Lit -> WatchLink -> IO ()
mergeWatcher !(b, e) !l !(b', e') = do
  c <- derefClausePointer b
  if c == NullClause
    then do
        setClausePointer b =<< derefClausePointer b'
        setClausePointer e =<< derefClausePointer e'
    else do
        -- append 'from' to 'to'
        n <- selectWatcher l =<< derefClausePointer e
        setClausePointer n =<< derefClausePointer b'
        setClausePointer e =<< derefClausePointer e'

asListWatchers :: WatchLink -> Lit -> IO [[Lit]]
asListWatchers w lit = map sort <$> traverseWatcher w lit

newtype WatcherList = WatcherList
                      {
                        v2w :: V.Vector WatchLink
                      }

newWatcherList :: Int -> IO WatcherList
newWatcherList n = do
--  v <- MV.new n
--  forM_ [0 .. n - 1]  $ \i -> MV.unsafeWrite v i =<< newWatchLink
  WatcherList . V.fromList <$> mapM (\_ -> newWatchLink) [0 .. n -1]

{-# INLINE getNthWatchLink #-}
getNthWatchLink :: Int -> WatcherList -> WatchLink
getNthWatchLink !i !(WatcherList v) = V.unsafeIndex v i
