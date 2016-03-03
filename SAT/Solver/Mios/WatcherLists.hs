{-# LANGUAGE
    FlexibleInstances
  , MultiParamTypeClasses
  , UndecidableInstances
  #-}
{-# LANGUAGE Trustworthy #-}

-- | WatcherLists since 1.0.3
module SAT.Solver.Mios.WatcherLists
       (
         WatcherLists
       , newWatcherLists
       , getNthWatchers
       )
       where

import Control.Monad (forM)
import qualified Data.List as L
import qualified Data.Vector as V
import SAT.Solver.Mios.Types
import qualified SAT.Solver.Mios.Clause as C
import SAT.Solver.Mios.ClauseManager

type WatcherLists = V.Vector ClauseManager

newWatcherLists :: Int -> Int -> IO WatcherLists
newWatcherLists n m = V.fromList <$> (forM [0 .. n] $ \_ -> newClauseManager m)

-- | returns the watcher List :: "ClauseManager" for "Literal" /l/
{-# INLINE getNthWatchers #-}
getNthWatchers :: WatcherLists -> Lit-> ClauseManager
getNthWatchers = V.unsafeIndex

instance VectorFamily WatcherLists C.Clause where
  dump mes wl = (mes ++) . L.concat <$> (forM [1 .. V.length wl - 1] $ \i -> dump ("\n" ++ show (lit2int i) ++ "' watchers:") (getNthWatchers wl i))
