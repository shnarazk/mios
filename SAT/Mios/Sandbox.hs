{-# LANGUAGE
    BangPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | This is a part of MIOS; make a copy of a running solver
module SAT.Mios.Sandbox
       (
         -- copy solver
         makeSandbox
       , checkClone
       )
        where

import Control.Monad (forM_, when)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.Solver

-- | returns a copy of a solver that doesn't share any data with the original
makeSandbox :: Solver -> IO Solver
makeSandbox Solver{..} = do
  model' <- copyVec model
  conflicts' <- copyVec conflicts
  clauses' <- copyVec clauses         -- 1/5 clauses; complete
  learnts' <- copyVec learnts         -- 2/5 learnts; complete
  watches' <- newWatcherList nVars 0  -- 3/5 watches; incomplete
  assigns' <- copyVec assigns
  phases' <- copyVec phases
  trail' <- copyVec trail
  trailLim' <- copyVec trailLim
  qHead' <- new' =<< get' qHead
  reason' <- copyVec reason           -- 4/5 reason; incomplete
  level' <- copyVec level
  activities' <- copyVec activities
  order' <- copyVec order
  varInc' <- new' =<< get' varInc
  rootLevel' <- new' =<< get' rootLevel
  ok' <- new' =<< get' ok
  an'seen' <- copyVec an'seen
  an'toClear' <- copyVec an'toClear
  an'stack' <- copyVec an'stack
  an'lastDL' <- copyVec an'lastDL
  litsLearnt' <- copyVec litsLearnt
  newLearnts' <- copyVec newLearnts   -- 5/5 newLearnts; complete
  stats' <- copyVec stats
  intForDump' <- copyVec intForDump
  forM_ [0 .. var2lit nVars False] $ \i -> do  -- 3/5 watches; complete
    let wm = getNthWatcher watches i
    let wm' = getNthWatcher watches' i
    inject wm wm'
    v1 <- getClauseVector wm
    v2 <- getClauseVector wm'
    injectPartially clauses v1 clauses' v2
    injectPartially learnts v1 learnts' v2
  -- 4/5 reason complete
  injectPartially clauses reason clauses' reason'
  injectPartially learnts reason learnts' reason'
  let clone = Solver
                model'
                conflicts'
                clauses'
                learnts'
                watches'
                assigns'
                phases'
                trail'
                trailLim'
                qHead'
                reason'
                level'
                activities'
                order'
                config
                nVars
                varInc'
                rootLevel'
                ok'
                an'seen'
                an'toClear'
                an'stack'
                an'lastDL'
                litsLearnt'
                newLearnts'
                stats'
                intForDump'
  return clone

injectPartially :: ClauseExtManager -> ClauseVector -> ClauseExtManager -> ClauseVector -> IO ()
injectPartially v f v' f' = do
  vv <- getClauseVector v
  v'v <- getClauseVector v'
  m <- get' v
  let n = lenClauseVector f' -- destination vectors might have more proper length than source vectors
  let
    -- vv[i]  -> f[j]    : toJ
    --  |         |
    --  v         v
    -- v'v[i] -> f'[j]
    toJ :: Int -> Clause -> IO Int
    toJ ((< n) -> False) _ = return (-1)
    toJ i c = do
      c' <- getNth f i
      if c == c' then return i else toJ (i + 1) c
    loop :: Int -> IO ()
    loop ((< m) -> False) = return ()
    loop i = do
      j <- toJ 0 =<< getNth vv i
      when (0 <= j) $ setNth f' j =<< getNth v'v i
      loop (i + 1)
  loop 0

checkClone :: Solver -> IO ()
checkClone s = do
  state1 <- toTuple s
  s' <- makeSandbox s
  let injectOn f = inject (f s') (f s)
  -- numerical values
  injectOn model
  injectOn conflicts
  injectOn assigns
  injectOn phases
  injectOn trail
  injectOn trailLim
  set' (qHead s) =<< get' (qHead s')
  injectOn level
  injectOn activities
  injectOn (heap . order)
  injectOn (idxs . order)
  set' (varInc s) =<< get' (varInc s')
  set' (rootLevel s) =<< get' (rootLevel s')
  set' (ok s) =<< get' (ok s')
  injectOn an'seen
  injectOn an'toClear
  injectOn an'stack
  injectOn an'lastDL
  injectOn litsLearnt
  injectOn stats
  injectOn intForDump
  -- clause category
  injectOn clauses                -- 1/5 clauses complete
  injectOn learnts                -- 2/5 learnts complete
  injectOn newLearnts             -- 5/5 newLearnts compelte
  -- 3/5 watches complete
  forM_ [0 .. var2lit (nVars s) False] $ \i -> do
    let wm = getNthWatcher (watches s) i
    let wm' = getNthWatcher (watches s') i
    inject wm' wm
    v1 <- getClauseVector wm'
    v2 <- getClauseVector wm
    injectPartially (clauses s') v1 (clauses s) v2
    injectPartially (learnts s') v1 (learnts s) v2
  -- 4/5 reason complete
  injectPartially (clauses s') (reason s') (clauses s) (reason s)
  injectPartially (learnts s') (reason s') (learnts s) (reason s)
  state2 <- toTuple s
  let diff (a1, b1, c1) (a2, b2, c2) = (p a1 a2, p b1 b2, p c1 c2)
        where p a b = if a == b then [] else [a, b]
  if state1 == state2 then putStrLn "clone check: pass" else errorWithoutStackTrace (show (diff state1 state2))

toTuple :: Solver -> IO ([(String, [Int])], [(String, [(Int, [Int])])], [(String, [[(Int, [Int])]])])
toTuple Solver{..} = do
  _model <- asList model
  _conflicts <- asList conflicts
  _clauses <- mapM (\(c, i) -> (i,) <$> asList c) =<< asList clauses
  _learnts <- mapM (\(c, i) -> (i,) <$> asList c) =<< asList learnts
  _watches <- mapM (mapM (\(c, i) -> (i,) <$> asList c)) =<< mapM asList =<< asList watches
  _assigns <- asList assigns
  _trail <- asList trail
  return ( [ ("model", _model)
           , ("conflicts", _conflicts)
           , ("asigns", _assigns)
           , ("trails", _trail)
           ]
         , [ ("clauses", _clauses)
           , ("learnts", _learnts)
           ]
         , [ ("watches", _watches)
           ]
         )
