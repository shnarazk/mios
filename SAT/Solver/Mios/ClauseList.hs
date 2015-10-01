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
module SAT.Solver.Mios.ClauseList
       (
         ClauseLink
       , newClauseLink
       , numberOfClauses
       , nextClause
       , pushClause
       , unlinkClause
       , removeClause
       , asListOfClauses
       )
       where

import Control.Monad (when)
import Data.IORef
import Data.List (sort)
import SAT.Solver.Mios.Types (ContainerLike(..), Lit)
import SAT.Solver.Mios.Clause (Clause(..), selectWatcher)


-- | __Version 0.5__
-- the definition of 'watcher'
type ClauseLink = (IORef Int, IORef Clause, IORef Clause)

newClauseLink :: IO ClauseLink
newClauseLink = (,,) <$> newIORef 0 <*> newIORef NullClause <*> newIORef NullClause

numberOfClauses :: ClauseLink -> IO Int
numberOfClauses (n, _, _) = readIORef n

-- | returns a watcher next to /the given clause/, or returns NullClause if no more watcher.
-- If the given clause is NullClasue, this returns the first clause of the watcher list.
{-# INLINE nextClause #-}
nextClause :: ClauseLink -> Clause -> IO Clause
nextClause (_, b, _) NullClause = readIORef b
nextClause _ Clause{..}      = readIORef nextOf

-- | adds a clause to the end of a watcher list
{-# INLINE pushClause #-}
pushClause :: ClauseLink -> Clause -> IO ()
pushClause !(k, b, e) !c = do
  !c' <- readIORef e
  let n = if c' == NullClause then b else nextOf c'
  writeIORef n c
  writeIORef e c
  writeIORef (nextOf c) NullClause
  modifyIORef' k (+ 1)

-- | unlinks a clause from the previous clasue and returns the new next clause.
-- If the given clause is @NullClause@, then the watcher list for /lit/ is updated.
-- This is the case to remove the first clause of a watcher list.
{-# INLINE unlinkClause #-}
unlinkClause :: ClauseLink -> Clause -> IO Clause
unlinkClause !(k, b, e) !c = do
  let n = if c == NullClause then b else nextOf c
  c' <- readIORef n
  c'' <- readIORef $ nextOf c'
  writeIORef n c''
  when (c'' == NullClause) $ writeIORef e c
  modifyIORef' k (subtract 1)
  return c'

-- | __O(n) search and delete operation__
-- Don't use it in critial path.
{-# INLINE removeClause #-}
removeClause :: ClauseLink -> Clause -> IO ()
removeClause !w@(n, b, e) !c = do
  let
    -- invaliant: c should be included in the watcher list
    loop !pre = do
      !c' <- if pre == NullClause then readIORef b else nextClause w pre
      if c == c'
        then unlinkClause w pre >> modifyIORef' n (subtract 1) >> return ()
        else if c' == NullClause then return () else loop c'
  loop NullClause

asListOfClauses :: ClauseLink -> IO [Clause]
asListOfClauses (_, b, e) = do
  let
    loop l NullClause = return $ reverse l
    loop l c = do
      loop (c : l) =<< readIORef (nextOf c)
  loop [] =<< readIORef b
