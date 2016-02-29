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

-- | WatcherLists since 1.0.3
module SAT.Solver.Mios.WatcherLists
       (
         WatcherLists
       , newWatcherLists
       , getNthWatchers
       )
       where

import Control.Monad (forM, forM_, when)
import qualified Data.List as L
import qualified Data.Vector as V
import SAT.Solver.Mios.Types (ContainerLike(..), Lit, index2lit)
import qualified SAT.Solver.Mios.Clause as C
import SAT.Solver.Mios.ClauseManager

type WatcherLists = V.Vector ClauseManager

newWatcherLists :: Int -> Int -> IO WatcherLists
newWatcherLists n m = V.fromList <$> (forM [0 .. n - 1] $ \_ -> newClauseManager m)

{-# INLINE getNthWatchers #-}
getNthWatchers :: WatcherLists -> Int -> ClauseManager
getNthWatchers = V.unsafeIndex

instance ContainerLike WatcherLists C.Clause where
  dump mes wl = (mes ++) . L.concat <$> (forM [0 .. V.length wl - 1] $ \i -> dump ("\n" ++ show (index2lit i) ++ "' watchers:") (getNthWatchers wl i))
