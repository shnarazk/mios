{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MagicHash
  , MultiParamTypeClasses
  , RecordWildCards
  , TupleSections
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
       , clearLink
       , nextClause
       , pushClause
       , pushClause'
       , unlinkClause
       , removeClause
       , asListOfClauses
       )
       where

import Control.Monad (when)
import Data.List (sort)
import SAT.Solver.Mios.Types (ContainerLike(..), Lit)
import SAT.Solver.Mios.Clause (Clause(..), ClausePointer, derefClausePointer, newClausePointer, setClausePointer, selectWatcher)
import SAT.Solver.Mios.Data.Singleton

-- | __Version 0.5__
-- the definition of 'watcher'
-- * number of elements
-- * pointer to the head
-- * pointer to the tail
type ClauseLink = (IntSingleton, ClausePointer, ClausePointer)

newClauseLink :: IO ClauseLink
newClauseLink = do
  v <- newInt 0
  setInt v 0
  (v,,) <$> newClausePointer NullClause <*> newClausePointer NullClause

clearLink :: ClauseLink -> IO ()
clearLink (n, b, e) = do
  setInt n 0
  setClausePointer b NullClause
  setClausePointer e NullClause

{-# INLINE numberOfClauses #-}
numberOfClauses :: ClauseLink -> IO Int
numberOfClauses (n, _, _) = getInt n

-- | returns a watcher next to /the given clause/, or returns NullClause if no more watcher.
-- If the given clause is NullClasue, this returns the first clause of the watcher list.
{-# INLINE nextClause #-}
nextClause :: ClauseLink -> Clause -> IO Clause
nextClause (_, b, _) NullClause = derefClausePointer b
nextClause _ Clause{..}      = derefClausePointer nextOf

-- | adds a clause to the end of a watcher list
{-# INLINE pushClause #-}
pushClause :: ClauseLink -> Clause -> IO ()
pushClause !(k, b, e) !c = do
  !c' <- derefClausePointer e
  let n = if c' == NullClause then b else nextOf c'
  setClausePointer n c
  setClausePointer e c
  setClausePointer (nextOf c) NullClause
  modifyInt k (+ 1)

-- | adds a clause to the head of a watcher list
{-# INLINE pushClause' #-}
pushClause' :: ClauseLink -> Clause -> IO ()
pushClause' !(k, b, e) !c = do
  !c' <- derefClausePointer b
  setClausePointer b c
  setClausePointer (nextOf c) c'
  !c'' <- derefClausePointer e
  when (c'' == NullClause) $ setClausePointer e c
  modifyInt k (+ 1)

-- | unlinks a clause from the previous clasue and returns the new next clause.
-- If the given clause is @NullClause@, then the watcher list for /lit/ is updated.
-- This is the case to remove the first clause of a watcher list.
{-# INLINE unlinkClause #-}
unlinkClause :: ClauseLink -> Clause -> IO Clause
unlinkClause !(k, b, e) !c = do
  let n = if c == NullClause then b else nextOf c
  !c' <- derefClausePointer n
  !c'' <- derefClausePointer $ nextOf c'
  setClausePointer n c''
  when (c'' == NullClause) $ setClausePointer e c
  modifyInt k (subtract 1)
  return c'

-- | __O(n) search and delete operation__
-- Don't use it in critial path.
{-# INLINE removeClause #-}
removeClause :: ClauseLink -> Clause -> IO ()
removeClause !w@(n, b, e) !c = do
  let
    -- invaliant: c should be included in the watcher list
    loop !pre = do
      !c' <- if pre == NullClause then derefClausePointer b else nextClause w pre
      if c == c'
        then unlinkClause w pre >> modifyInt n (subtract 1) >> return ()
        else if c' == NullClause then return () else loop c'
  loop NullClause

asListOfClauses :: ClauseLink -> IO [Clause]
asListOfClauses (_, b, _) = do
  let
    loop l NullClause = return l
    loop l c = do
      loop (c : l) =<< derefClausePointer (nextOf c)
  loop [] =<< derefClausePointer b
