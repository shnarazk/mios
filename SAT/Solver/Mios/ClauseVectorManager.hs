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
-- | Universal data structure for Clauses
-- | Both of watchlists and @learnt@ are implemented by this.
module SAT.Solver.Mios.ClauseVectorManager
       (
         -- * Vector of Clause
         ClauseVector
       , getNthClause
       , setNthClause
         -- * higher level interface for ClauseVector
       , ClauseVectorManager (..)
       , newClauseVectorManager
       , numberOfClauses
       , clearClauseVectorManager
       , getClauseVector
       , pushClause
       , removeClause
       )
       where

import Control.Monad (when)
import qualified Data.IORef as IORef
import qualified Data.Vector.Mutable as MV
import qualified SAT.Solver.Mios.Clause as C
import SAT.Solver.Mios.Data.Singleton

type ClauseVector = MV.IOVector C.Clause

getNthClause :: ClauseVector -> Int -> IO C.Clause
getNthClause = MV.unsafeRead

setNthClause :: ClauseVector -> Int -> C.Clause -> IO ()
setNthClause = MV.unsafeWrite


data ClauseVectorManager =
  ClauseVectorManager
  {
    _nActives     :: IntSingleton
  , _clauseVector :: IORef.IORef ClauseVector
  }

newClauseVectorManager :: Int -> IO ClauseVectorManager
newClauseVectorManager k = do
  i <- newInt k
  v <- MV.new k
  ClauseVectorManager i <$> IORef.newIORef v

numberOfClauses :: ClauseVectorManager -> IO Int
numberOfClauses ClauseVectorManager{..} = getInt _nActives

clearClauseVectorManager :: ClauseVectorManager -> IO ()
clearClauseVectorManager ClauseVectorManager{..} = setInt _nActives 0

getClauseVector :: ClauseVectorManager -> IO ClauseVector
getClauseVector ClauseVectorManager{..} = IORef.readIORef _clauseVector

-- | O(1) inserter
pushClause :: ClauseVectorManager -> C.Clause -> IO ()
pushClause ClauseVectorManager{..} c = do
  n <- getInt _nActives
  v <- IORef.readIORef _clauseVector
  v' <- if MV.length v <= n
       then do
        v' <- MV.grow v 200 
        IORef.writeIORef _clauseVector v'
        return v' 
       else return v
  MV.unsafeWrite v' n c
  modifyInt _nActives (1 +)

-- | O(n) but lightweight remove and compactor
removeClause :: ClauseVectorManager -> C.Clause -> IO ()
removeClause ClauseVectorManager{..} c = do
  n <- getInt _nActives
  v <- IORef.readIORef _clauseVector
  let
    seekIndex :: Int -> IO Int
    seekIndex k = do
      c' <- MV.unsafeRead v k
      if c' == c then return k else seekIndex $ k + 1
  j <- seekIndex 0
  MV.unsafeSwap v j (n - 1)     -- swap the last active element and it
  modifyInt _nActives (subtract 1)
