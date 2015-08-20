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

-- |
module SAT.Solver.Mios.WatchList
       (
         WatchList (..)
       , WatchLink
       , traverseWatcher
       )
       where

import GHC.Prim
import Control.Monad
import Data.IORef
import Data.List
import SAT.Solver.Mios.Types
import SAT.Solver.Mios.Internal
import SAT.Solver.Mios.Clause

-- | __Version 0.5__
--
-- Abstract watcher list structure based on /pointer/
class WatchList w where
  -- | returns a watcher next to /the given clause/, or returns NullClause if no more watcher.
  -- If the given clause is NullClasue, this returns the first clause of the watcher list.
  nextWatcher :: w -> Lit -> Clause -> IO Clause
  -- | adds a clause to the end of a watcher list
  pushWatcher :: w -> Lit -> Clause -> IO ()
  -- | unlinks a clause from the previous clasue and returns the new next clause.
  -- If the given clause is @NullClause@, then the watcher list for /lit/ is updated.
  -- This is the case to remove the first clause of a watcher list.
  unlinkWatcher :: w -> Lit -> Clause -> IO Clause
  -- | __O(n) search and delete operation__
  -- Don't use it in critial path.
  removeWatcher :: w -> Lit -> Clause -> IO ()

-- | __Version 0.5__
-- the element of 'watcher'
type WatchLink = (IORef Clause, IORef Clause)

instance WatchList WatchLink where
  nextWatcher (b, _) _ NullClause = readIORef b
  nextWatcher _ l c               = readIORef =<< selectWatcher l c
  pushWatcher (b, e) l c = do
    !c' <- readIORef e
    n <- if c' == NullClause then return b else selectWatcher l c'
    writeIORef n c
    writeIORef e c
    n' <- selectWatcher l c
    writeIORef n' NullClause
  unlinkWatcher (b, e) l c = do
    n <- if c == NullClause then return b else selectWatcher l c
    c' <- readIORef n
    c'' <- readIORef =<< selectWatcher l c'
    writeIORef n c''
    when (c'' == NullClause) $ writeIORef e c
    return c'
  removeWatcher w@(b, e) l c = do
    let
      -- invaliant: c should be included in the watcher list
      loop !pre = do
        !c' <- if pre == NullClause then readIORef b else nextWatcher w l pre
        if c == c'
          then unlinkWatcher w l pre >> return ()
          else if c' == NullClause then return () else loop c'
    loop NullClause

traverseWatcher :: WatchLink -> Lit -> IO [[Lit]]
traverseWatcher (b, e) lit = do
  let
    loop l NullClause = return $ reverse l
    loop l c = do
      l' <- asList c
      loop (l' : l) =<< readIORef =<< selectWatcher lit c
  loop [] =<< readIORef b

asListWatchers :: WatchLink -> Lit -> IO [[Lit]]
asListWatchers w lit = map sort <$> traverseWatcher w lit
