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
       , numberOfRegisteredClauses
       )
       where

import Control.Monad (forM)
import qualified Data.List as L
import qualified Data.Vector as V
import SAT.Solver.Mios.Types
import qualified SAT.Solver.Mios.Clause as C
import SAT.Solver.Mios.ClauseManager

type WatcherLists = V.Vector ClauseManager

-- | /n/ is the number of 'Var', /m/ is default size of each watcher list
-- | For /n/ vars, we need [0 .. 2 + 2 * n - 1] slots, namely /2 * (n + 1)/-length vector
newWatcherLists :: Int -> Int -> IO WatcherLists
newWatcherLists n m = V.fromList <$> (forM [0 .. int2lit (negate n) + 1] $ \_ -> newClauseManager m)

-- | returns the watcher List :: "ClauseManager" for "Literal" /l/
{-# INLINE getNthWatchers #-}
getNthWatchers :: WatcherLists -> Lit-> ClauseManager
getNthWatchers = V.unsafeIndex

instance VectorFamily WatcherLists C.Clause where
  dump mes wl = (mes ++) . L.concat <$> (forM [1 .. V.length wl - 1] $ \i -> dump ("\n" ++ show (lit2int i) ++ "' watchers:") (getNthWatchers wl i))

numberOfRegisteredClauses :: WatcherLists -> IO Int
numberOfRegisteredClauses ws = sum <$> V.mapM numberOfClauses ws

{-
-- | for debug
checkConsistency :: WatcherLists -> IO ()
checkConsistency wl = do
  forM_ [2 .. V.length wl - 1] $ \i -> do
    let cm = getNthWatchers wl i
    vec <- getClauseVector cm
    n <- numberOfClauses cm
    forM_ [0 .. n - 1] $ \k -> do
      c <- getNthClause vec k
      when (c == C.NullClause) $ error "checkConsistency failed"
  l <- forM [2 .. V.length wl - 1] (numberOfClauses . getNthWatchers wl)
  putStrLn $ "checkConsistency passed: " ++ show l
-}
