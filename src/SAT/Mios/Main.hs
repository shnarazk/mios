-- | (This is a part of MIOS.)
-- Main part of solving satisfiability problem.
{-# LANGUAGE
    BangPatterns
  , MultiWayIf
  , RecordWildCards
  , ScopedTypeVariables
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Mios.Main
       (
         -- * Interface to 'Solver', imported from 'SAT.Mios.Criteria'
         Solver
       , newSolver
       , setAssign
       , addClause
       , dumpStats
         -- * Main function
       , simplifyDB
       , solve
       )
        where

import Control.Monad (unless, void, when)
import Data.Bits
import Data.Foldable (foldrM)
import Data.Int
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.Solver
import SAT.Mios.ClausePool
import SAT.Mios.Criteria

-- | #114: __RemoveWatch__
{-# INLINABLE removeWatch #-}
removeWatch :: Solver -> Clause -> IO ()
removeWatch Solver{..} c = do
  let lstack = lits c
  l1 <- negateLit <$> getNth lstack 1
  markClause (getNthWatcher watches l1) c
  l2 <- negateLit <$> getNth lstack 2
  markClause (getNthWatcher watches l2) c
  putBackToPool clsPool c

--------------------------------------------------------------------------------
-- Operations on 'Clause'
--------------------------------------------------------------------------------

-- | __Fig. 8. (p.12)__ creates a new LEARNT clause and adds it to watcher lists.
-- This is a strippped-down version of 'newClause' in Solver.
newLearntClause :: Solver -> Stack -> IO Int
newLearntClause s@Solver{..} ps = do
  -- ps is a 'SizedVectorInt'; ps[0] is the number of active literals
  -- Since this solver must generate only healthy learnt clauses, we need not to run misc check in 'newClause'
  k <- get' ps
  case k of
   1 -> do l <- getNth ps 1
           unsafeEnqueue s l NullClause
           return 1
   _ -> do c <- makeClauseFromStack clsPool ps --  newClauseFromStack True ps
           let lstack = lits c
               findMax :: Int -> Int -> Int -> IO Int -- Pick a second literal to watch:
               findMax ((<= k) -> False) j _ = return j
               findMax i j val = do v <- lit2var <$> getNth lstack i
                                    a <- getNth assigns v
                                    b <- getNth level v
                                    if (a /= LBottom) && (val < b)
                                      then findMax (i + 1) i b
                                      else findMax (i + 1) j val
           swapBetween lstack 2 =<< findMax 1 1 0 -- get the index of the literal with highest level
           -- Bump, enqueue, store clause:
           claBumpActivity s c
           -- Add clause to all managers
           pushTo learnts c
           l1 <- getNth lstack 1
           l2 <- getNth lstack 2
           pushClauseWithKey (getNthWatcher watches (negateLit l1)) c l2
           pushClauseWithKey (getNthWatcher watches (negateLit l2)) c l1
           -- update the solver state by @l@
           unsafeEnqueue s l1 c
           -- Since unsafeEnqueue updates the 1st literal's level, setLBD should be called after unsafeEnqueue
           lbd <- lbdOf s (lits c)
           setRank c lbd
           -- assert (0 < rank c)
           -- set' (protected c) True
           return lbd

-- | __Simplify.__ At the top-level, a constraint may be given the opportunity to
-- simplify its representation (returns @False@) or state that the constraint is
-- satisfied under the current assignment and can be removed (returns @True@).
-- A constraint must /not/ be simplifiable to produce unit information or to be
-- conflicting; in that case the propagation has not been correctly defined.
--
-- MIOS NOTE: the original doesn't update watchers; only checks its satisfiabiliy.
{-# INLINABLE simplify #-}
simplify :: Solver -> Clause -> IO Bool
simplify s c = do
  n <- get' c
  let lstack = lits c
      loop ::Int -> IO Bool
      loop ((<= n) -> False) = return False
      loop i = do v <- valueLit s =<< getNth lstack i
                  if v == 1 then return True else loop (i + 1)
  loop 1

--------------------------------------------------------------------------------
-- MIOS NOTE on Minor methods:
--
-- * no (meaningful) 'newVar' in mios
-- * 'assume' is defined in 'Solver'
-- * `cancelUntil` is defined in 'Solver'

--------------------------------------------------------------------------------
-- Major methods

-- | M114: __Fig. 10. (p.15)__
--
-- analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel :: int&) -> [void]
--
-- __Description:_-
--   Analzye confilct and produce a reason clause.
--
-- __Pre-conditions:__
--   * 'out_learnt' is assumed to be cleared.
--   * Corrent decision level must be greater than root level.
--
-- __Post-conditions:__
--   * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
--   * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
--     rest of literals. There may be others from the same level though.
--
-- @analyze@ is invoked from @search@
analyze :: Solver -> Clause -> IO Int
analyze s@Solver{..} confl = do
  -- litvec
  reset litsLearnt
  pushTo litsLearnt 0 -- reserve the first place for the unassigned literal
  dl <- decisionLevel s
  let loopOnClauseChain :: Clause -> Lit -> Int -> Int -> Int -> IO Int
      loopOnClauseChain c p ti bl pathC = do -- p : literal, ti = trail index, bl = backtrack level
        d <- getRank c
        when (0 /= d) $ claBumpActivity s c
        -- update LBD like #Glucose4.0
        when (2 < d) $ do
          nblevels <- lbdOf s (lits c)
          when (nblevels + 1 < d) $ -- improve the LBD
            -- when (d <= 30) $ set' (protected c) True -- 30 is `lbLBDFrozenClause`
            -- seems to be interesting: keep it fro the next round
            setRank c nblevels     --  Update it
        sc <- get' c
        let lstack = lits c
            loopOnLiterals :: Int -> Int -> Int -> IO (Int, Int)
            loopOnLiterals ((<= sc) -> False) b pc = return (b, pc) -- b = btLevel, pc = pathC
            loopOnLiterals j b pc = do
              (q :: Lit) <- getNth lstack j
              let v = lit2var q
              sn <- getNth an'seen v
              l <- getNth level v
              if sn == 0 && 0 < l
                then do
                    varBumpActivity s v
                    setNth an'seen v 1
                    if dl <= l      -- cancelUntil doesn't clear level of cancelled literals
                      then do
                          -- UPDATEVARACTIVITY: glucose heuristics
                          r <- getNth reason v
                          when (r /= NullClause) $ do
                            ra <- getRank r
                            when (0 /= ra) $ pushTo an'lastDL q
                          -- end of glucose heuristics
                          loopOnLiterals (j + 1) b (pc + 1)
                      else pushTo litsLearnt q >> loopOnLiterals (j + 1) (max b l) pc
                else loopOnLiterals (j + 1) b pc
        (b', pathC') <- loopOnLiterals (if p == bottomLit then 1 else 2) bl pathC
        let nextPickedUpLit :: Int -> IO Int        -- select next clause to look at
            nextPickedUpLit i = do x <- getNth an'seen . lit2var =<< getNth trail i
                                   if x == 0 then nextPickedUpLit (i - 1) else return (i - 1)
        ti' <- nextPickedUpLit (ti + 1)
        nextP <- getNth trail (ti' + 1)
        let nextV = lit2var nextP
        confl' <- getNth reason nextV
        setNth an'seen nextV 0
        if 1 < pathC'
          then loopOnClauseChain confl' nextP (ti' - 1) b' (pathC' - 1)
          else setNth litsLearnt 1 (negateLit nextP) >> return b'
  ti <- subtract 1 <$> get' trail
  levelToReturn <- loopOnClauseChain confl bottomLit ti 0 0
  -- Simplify phase (implemented only @expensive_ccmin@ path)
  n <- get' litsLearnt
  reset an'stack           -- analyze_stack.clear();
  reset an'toClear         -- out_learnt.copyTo(analyze_toclear);
  pushTo an'toClear =<< getNth litsLearnt 1
  let merger :: Int -> Int64 -> IO Int64
      merger ((<= n) -> False) b = return b
      merger i b = do l <- getNth litsLearnt i
                      pushTo an'toClear l
                      -- restrict the search depth (range) to [0 .. 63]
                      merger (i + 1) . setBit b . (63 .&.) =<< getNth level (lit2var l)
  levels <- merger 2 0
  let loopOnLits :: Int -> Int -> IO ()
      loopOnLits ((<= n) -> False) n' = shrinkBy litsLearnt $ n - n' + 1
      loopOnLits i j = do
        l <- getNth litsLearnt i
        c1 <- (NullClause ==) <$> getNth reason (lit2var l)
        if c1
          then setNth litsLearnt j l >> loopOnLits (i + 1) (j + 1)
          else do
             c2 <- not <$> analyzeRemovable s l levels
             if c2
               then setNth litsLearnt j l >> loopOnLits (i + 1) (j + 1)
               else loopOnLits (i + 1) j
  loopOnLits 2 2                -- the first literal is specail
  -- UPDATEVARACTIVITY: glucose heuristics
  nld <- get' an'lastDL
  r <- get' litsLearnt -- this is an estimated LBD value based on the clause size
  let loopOnLastDL :: Int -> IO ()
      loopOnLastDL ((<= nld) -> False) = return ()
      loopOnLastDL i = do v <- lit2var <$> getNth an'lastDL i
                          r' <- get' =<< getNth reason v
                          when (r < r') $ varBumpActivity s v
                          loopOnLastDL $ i + 1
  loopOnLastDL 1
  reset an'lastDL
  -- Clear seen
  k <- get' an'toClear
  let cleaner :: Int -> IO ()
      cleaner ((<= k) -> False) = return ()
      cleaner i = do v <- lit2var <$> getNth an'toClear i
                     setNth an'seen v 0
                     cleaner $ i + 1
  cleaner 1
  return levelToReturn

-- | #M114
-- Check if 'p' can be removed, 'abstract_levels' is used to abort early if the algorithm is
-- visiting literals at levels that cannot be removed later.
--
-- Implementation memo:
--
-- *  @an'toClear@ is initialized by @ps@ in @analyze@ (a copy of 'learnt').
--   This is used only in this function and @analyze@.
--
analyzeRemovable :: Solver -> Lit -> Int64 -> IO Bool
analyzeRemovable Solver{..} p minLevel = do
  -- assert (reason[var(p)] != NullClause);
  reset an'stack      -- analyze_stack.clear()
  pushTo an'stack p   -- analyze_stack.push(p);
  top <- get' an'toClear
  let
    loopOnStack :: IO Bool
    loopOnStack = do
      k <- get' an'stack  -- int top = analyze_toclear.size();
      if 0 == k
        then return True
        else do -- assert(reason[var(analyze_stack.last())] != GClause_NULL);
            sl <- lastOf an'stack
            popFrom an'stack             -- analyze_stack.pop();
            c <- getNth reason (lit2var sl) -- getRoot sl
            nl <- get' c
            let
              lstack = lits c
              loopOnLit :: Int -> IO Bool -- loopOnLit (int i = 1; i < c.size(); i++){
              loopOnLit ((<= nl) -> False) = loopOnStack
              loopOnLit i = do
                p' <- getNth lstack i              -- valid range is [1 .. nl]
                let v' = lit2var p'
                l' <- getNth level v'
                c1 <- (1 /=) <$> getNth an'seen v'
                if c1 && (0 /= l')   -- if (!analyze_seen[var(p)] && level[var(p)] != 0){
                  then do
                      c3 <- (NullClause /=) <$> getNth reason v'
                      if c3 && testBit minLevel (l' .&. 63) -- if (reason[var(p)] != GClause_NULL && ((1 << (level[var(p)] & 31)) & min_level) != 0){
                        then do
                            setNth an'seen v' 1   -- analyze_seen[var(p)] = 1;
                            pushTo an'stack p'    -- analyze_stack.push(p);
                            pushTo an'toClear p'  -- analyze_toclear.push(p);
                            loopOnLit $ i + 1
                        else do
                            -- for (int j = top; j < analyze_toclear.size(); j++) analyze_seen[var(analyze_toclear[j])] = 0;
                            top' <- get' an'toClear
                            let clearAll :: Int -> IO ()
                                clearAll ((<= top') -> False) = return ()
                                clearAll j = do x <- getNth an'toClear j; setNth an'seen (lit2var x) 0; clearAll (j + 1)
                            clearAll $ top + 1
                            -- analyze_toclear.shrink(analyze_toclear.size() - top); note: shrink n == repeat n pop
                            shrinkBy an'toClear $ top' - top
                            return False
                  else loopOnLit $ i + 1
            loopOnLit 2
  loopOnStack

-- | #114
-- analyzeFinal : (confl : Clause *) (skip_first : boot) -> [void]
--
-- __Description:__
--   Specialized analysis proceduce to express the final conflict in terms of assumptions.
--   'root_level' is allowed to point beyond end of trace (useful if called after conflict while
--   making assumptions). If 'skip_first' is TRUE, the first literal of 'confl' is ignored (needed
--   if conflict arose before search even started).
--
analyzeFinal :: Solver -> Clause -> Bool -> IO ()
analyzeFinal Solver{..} confl skipFirst = do
  reset conflicts
  rl <- get' rootLevel
  unless (rl == 0) $ do
    n <- get' confl
    let lstack = lits confl
        loopOnConfl :: Int -> IO ()
        loopOnConfl ((<= n) -> False) = return ()
        loopOnConfl i = do
          (x :: Var) <- lit2var <$> getNth lstack i
          lvl <- getNth level x
          when (0 < lvl) $ setNth an'seen x 1
          loopOnConfl $ i + 1
    loopOnConfl $ if skipFirst then 2 else 1
    tls <- get' trailLim
    trs <- get' trail
    tlz <- getNth trailLim 1
    let loopOnTrail :: Int -> IO ()
        loopOnTrail ((tlz <=) -> False) = return ()
        loopOnTrail i = do
          (l :: Lit) <- getNth trail (i + 1)
          let (x :: Var) = lit2var l
          saw <- getNth an'seen x
          when (saw == 1) $ do
            (r :: Clause) <- getNth reason x
            if r == NullClause
              then pushTo conflicts (negateLit l)
              else do
                  k <- get' r
                  let lstack' = lits r
                      loopOnLits :: Int -> IO ()
                      loopOnLits ((<= k) -> False) = return ()
                      loopOnLits j = do
                        (v :: Var) <- lit2var <$> getNth lstack' j
                        lv <- getNth level v
                        when (0 < lv) $ setNth an'seen v 1
                        loopOnLits $ i + 1
                  loopOnLits 2
          setNth an'seen x 0
          loopOnTrail $ i - 1
    loopOnTrail =<< if tls <= rl then return (trs - 1) else getNth trailLim (rl + 1)

-- | M114:
-- propagate : [void] -> [Clause+]
--
-- __Description:__
--   Porpagates all enqueued facts. If a conflict arises, the conflicting clause is returned.
--   otherwise CRef_undef.
--
-- __Post-conditions:__
--   * the propagation queue is empty, even if there was a conflict.
--
-- memo: @propagate@ is invoked by @search@,`simpleDB` and `solve`
propagate :: Solver -> IO Clause
propagate s@Solver{..} = do
  let
    while :: Clause -> Bool -> IO Clause
    while confl False = return confl
    while confl True = do
      (p :: Lit) <- getNth trail . (1 +) =<< get' qHead
      modify' qHead (+ 1)
      incrementStat s NumOfPropagation 1
      let (ws :: ClauseExtManager) = getNthWatcher watches p
          !falseLit = negateLit p
      end <- get' ws
      cvec <- getClauseVector ws
      bvec <- getKeyVector ws
      let copy :: Int -> Int -> IO ()
          copy ((< end) -> False) _ = return ()
          copy !i' !j' = do setNth cvec j' =<< getNth cvec i'
                            setNth bvec j' =<< getNth bvec i'
                            copy (i' + 1) (j' + 1)
      let forClause :: Int -> Int -> IO Clause
          forClause i@((< end) -> False) !j = shrinkBy ws (i - j) >> return confl
          forClause !i !j = do
            (blocker :: Lit) <- getNth bvec i        -- Try to avoid inspecting the clause:
            bv <- if blocker == 0 then return LiftedF else valueLit s blocker
            if bv == LiftedT
              then do unless (i == j) $ do (c :: Clause) <- getNth cvec i
                                           setNth cvec j c
                                           setNth bvec j blocker
                      forClause (i + 1) (j + 1)
              else do                               -- Make sure the false literal is data[1]:
                  (c :: Clause) <- getNth cvec i
                  let !lstack = lits c
                  tmp <- getNth lstack 1
                  first <- if falseLit == tmp
                           then do l2 <- getNth lstack 2
                                   setNth lstack 2 tmp
                                   setNth lstack 1 l2
                                   return l2
                           else return tmp
                  fv <- valueLit s first
                  if fv == LiftedT
                    then do unless (i == j) $ setNth cvec j c
                            setNth bvec j first
                            forClause (i + 1) (j + 1)
                    else do cs <- get' c           -- Look for new watch:
                            let newWatch :: Int -> IO LiftedBool
                                newWatch ((<= cs) -> False) = do -- Did not find watch
                                  setNth cvec j c
                                  setNth bvec j first
                                  if fv == LiftedF
                                    then do ((== 0) <$> decisionLevel s) >>= (`when` set' ok LiftedF)
                                            set' qHead =<< get' trail
                                            copy (i + 1) (j + 1)
                                            return LiftedF                 -- conflict
                                    else do unsafeEnqueue s first c
                                            return LBottom                 -- unit clause
                                newWatch !k = do (l' :: Lit) <- getNth lstack k
                                                 lv <- valueLit s l'
                                                 if lv /= LiftedF
                                                   then do setNth lstack 2 l'
                                                           setNth lstack k falseLit
                                                           pushClauseWithKey (getNthWatcher watches (negateLit l')) c first
                                                           return LiftedT  -- found another watch
                                                   else newWatch $! k + 1
                            ret <- newWatch 3
                            case ret of
                              LiftedT -> forClause (i + 1) j               -- found another watch
                              LBottom -> forClause (i + 1) (j + 1)         -- unit clause
                              _       -> shrinkBy ws (i - j) >> return c   -- conflict
      c <- forClause 0 0
      while c =<< ((<) <$> get' qHead <*> get' trail)
  while NullClause =<< ((<) <$> get' qHead <*> get' trail)

-- | #M22
-- reduceDB: () -> [void]
--
-- __Description:__
--   Remove half of the learnt clauses, minus the clauses locked by the current assigmnent. Locked
--   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
reduceDB :: Solver -> IO ()
reduceDB s@Solver{..} = do
  n <- nLearnts s
  cvec <- getClauseVector learnts
  n' <- get' trail
  let loop :: Int -> IO ()
      loop ((< n) -> False) = return ()
      loop i = do
        removeWatch s =<< getNth cvec i
        loop $ i + 1
  k <- sortClauses s learnts $ div n 2 -- k is the number of clauses not to be purged
{-
  -- #GLUCOSE3.0 keep more
  t3 <- get' . rank =<< getNth vec (thr -1)
  t5 <- get' . rank =<< getNth vec (lim -1)

  let k = case (t3 <= 3, t5 <= 5) of
            (True, True)   -> min n (thr + 2000)
            (False, False) -> thr
            (_, _)         -> min n (thr + 1000)
  -- let k = div thr 2
-}
  loop k                               -- CAVEAT: `vec` is a zero-based vector
  -- putStrLn $ "reduceDB: purge " ++ show (n - k) ++ " out of " ++ show n
  reset watches
  shrinkBy learnts (n - k)
  incrementStat s NumOfReduction 1

-- constants for sort key layout
rankWidth :: Int
rankWidth = 11
activityWidth :: Int
activityWidth = 51              -- note: the maximum clause activity is 1e20.
rankMax :: Int
rankMax = 2 ^ rankWidth - 1
activityMax :: Int
activityMax = 2 ^ activityWidth - 1

-- | applies a (good to bad) quick semi-sort to the vector in a 'ClauseExtManager'
-- and returns the number of privileged clauses.
-- This function uses the same criteria as reduceDB_lt in glucose 4.0:
-- 1. binary clause
-- 2. smaller LBD
-- 3. larger activity defined as MiniSat
--
-- They are encoded into an "Int64" as the following (11+51 layout):
--
-- * 11 bits for rank (LBD): 'rankWidth'
-- * 51 bits for converted activity: 'activityWidth'
--
sortClauses :: Solver -> ClauseExtManager -> Int -> IO Int
sortClauses s cm limit' = do
  n <- get' cm
  -- assert (n < indexMax)
  vec <- getClauseVector cm
  kvec <- getKeyVector cm
  at <- (0.1 *) . (/ fromIntegral n) <$> get' (claInc s) -- activity threshold
  -- 1: assign keys
  updateNDD s
  cl <- getEMA (emaCDLvl s)
  surface <- if cl == 0 then return 0 else (/ cl) <$> getEMA (emaBDLvl s)  -- 0 <=backjumped level / coflict level < 1.0
  let shiftLBD = activityWidth
      am = fromIntegral activityMax :: Double
      scaleAct :: Double -> Int
      scaleAct x
        | x < 1e-20 = activityMax
        | otherwise = floor $ am * (1 - logBase 10 (x * 1e20) / 40)
      assignKey :: Int -> Int -> IO Int
      assignKey ((< n) -> False) t = return t
      assignKey i t = do
        c <- getNth vec i
        k <- get' c
        if k == 2                  -- Main criteria. Like in MiniSat we keep all binary clauses
          then do setNth kvec i 0
                  assignKey (i + 1) (t + 1)
          else do a <- get' (activity c)                       -- Second one... based on LBD
                  rLBD <- fromIntegral <$> getRank c           -- above the level
                  rNDD <- fromIntegral <$> nddOf s (lits c)    -- under the level
                  let r = if rNDD == 1                         -- this implies rLBD == 1.
                          then 1
                          else ceiling $ rLBD ** surface * rNDD ** (1 - surface)
                  l <- locked s c
                  let d =if | l -> 0
                            | a < at -> rankMax
                            | otherwise ->  min rankMax r                -- rank can be one
                  setNth kvec i $ shiftL d shiftLBD + scaleAct a
                  assignKey (i + 1) $ if l then t + 1 else t
  limit <- max limit' <$> assignKey 0 0
  -- 2: sort keyVector
  let sortOnRange :: Int -> Int -> IO ()
      sortOnRange left right
        | limit < left = return ()
        | left >= right = return ()
        | left + 1 == right = do
            a <- getNth kvec left
            b <- getNth kvec right
            unless (a < b) $ do setNth kvec left b
                                setNth kvec right a
                                swapBetween vec left right
        | otherwise = do
            let p = div (left + right) 2
            pivot <- getNth kvec p
            swapBetween kvec p left -- set a sentinel for r'
            swapBetween vec p left
            let nextL :: Int -> IO Int
                nextL i@((<= right) -> False) = return i
                nextL i = do v <- getNth kvec i; if v < pivot then nextL (i + 1) else return i
                nextR :: Int -> IO Int
                nextR i = do v <- getNth kvec i; if pivot < v then nextR (i - 1) else return i
                divide :: Int -> Int -> IO Int
                divide l r = do
                  l' <- nextL l
                  r' <- nextR r
                  if l' < r'
                    then do swapBetween kvec l' r'
                            swapBetween vec l' r'
                            divide (l' + 1) (r' - 1)
                    else return r'
            m <- divide (left + 1) right
            swapBetween kvec left m
            swapBetween vec left m
            sortOnRange left (m - 1)
            sortOnRange (m + 1) right
  sortOnRange 0 (n - 1)
  return limit

-- | #M22
--
-- simplify : [void] -> [bool]
--
-- __Description:__
--   Simplify the clause database according to the current top-level assigment. Currently, the only
--   thing done here is the removal of satisfied clauses, but more things can be put here.
--
simplifyDB :: Solver -> IO Bool
simplifyDB s@Solver{..} = do
  good <- (LiftedT ==) <$> get' ok
  if good
    then do
      p <- propagate s
      if p /= NullClause
        then set' ok LiftedF >> return False
        else do
            -- Remove satisfied clauses and their watcher lists:
            let
              for :: ClauseExtManager -> IO ()
              for mgr = do
                vec' <- getClauseVector mgr
                n' <- get' mgr
                let
                  loopOnVector :: Int -> Int -> IO ()
                  loopOnVector ((< n') -> False) j = shrinkBy mgr (n' - j)
                  loopOnVector i j = do
                        c <- getNth vec' i
                        l <- locked s c
                        r <- if l then return False else simplify s c
                        if r
                          then removeWatch s c >> loopOnVector (i + 1) j
                          else unless (i == j) (setNth vec' j c) >> loopOnVector (i + 1) (j + 1)
                loopOnVector 0 0
            for clauses
            for learnts
            reset watches
            return True
    else return False

-- | #M22
--
-- search : (nof_conflicts : int) (params : const SearchParams&) -> [lbool]
--
-- __Description:__
--   Search for a model the specified number of conflicts.
--   NOTE: Use negative value for 'nof_conflicts' indicate infinity.
--
-- __Output:__
--   * 'True' if a partial assigment that is consistent with respect to the clause set is found.
--      If all variables are decision variables, that means that the clause set is satisfiable.
--   * 'False' if the clause set is unsatisfiable or some error occured.
search :: Solver -> IO Bool
search s@Solver{..} = do
  -- clear model
  let delta = (sqrt . fromIntegral) nVars
  let loop :: Bool -> IO Bool
      loop restart = do
        confl <- propagate s
        d <- decisionLevel s
        if confl /= NullClause  -- CONFLICT
          then do incrementStat s NumOfBackjump 1
                  r <- get' rootLevel
                  if d == r                       -- Contradiction found:
                    then analyzeFinal s confl False >> return False
                    else do backtrackLevel <- analyze s confl -- 'analyze' resets litsLearnt by itself
                            (s `cancelUntil`) . max backtrackLevel =<< get' rootLevel
                            lbd' <- newLearntClause s litsLearnt
                            k <- get' litsLearnt
                            when (k == 1) $ do
                              (v :: Var) <- lit2var <$> getNth litsLearnt 1
                              setNth level v 0
                            varDecayActivity s
                            claDecayActivity s
                            -- learnt DB Size Adjustment
                            modify' learntSCnt (subtract 1)
                            cnt <- get' learntSCnt
                            when (cnt == 0) $ do
                              t' <- (* 1.5) <$> get' learntSAdj
                              set' learntSAdj t'
                              set' learntSCnt $ floor t'
                              modify' maxLearnts (+ delta)
                            loop =<< checkRestartCondition s lbd' d
          else do when (d == 0) . void $ simplifyDB s -- Simplify the set of problem clauses
                  k1 <- get' learnts
                  k2 <- nAssigns s
                  nl <- floor <$> get' maxLearnts
                  when (nl < k1 - k2) $ do
                    reduceDB s    -- Reduce the set of learnt clauses.
                    when (2 == dumpSolverStatMode config) $ dumpStats DumpCSV s
                  if | k2 == nVars -> return True     -- Model found
                     | restart -> do                  -- Reached bound on number of conflicts
                         (s `cancelUntil`) =<< get' rootLevel -- force a restart
                         -- claRescaleActivityAfterRestart s
{-
                         let toggle :: Int -> Int
                             toggle LiftedT = LiftedF
                             toggle LiftedF = LiftedT
                             toggle x = x
                             nv = nVars
                             toggleAt :: Int -> IO ()
                             toggleAt ((<= nv) -> False) = return ()
                             toggleAt i = modifyNth phases toggle i >> toggleAt (i + 1)
                         rm <- get' restartMode
                         when (rm == 1) $ toggleAt 1
-}
                         loop False
                     | otherwise -> do                -- New variable decision
                         v <- selectVO s
                         -- #phasesaving <<<<  many have heuristic for polarity here
                         oldVal <- getNth phases v
                         unsafeAssume s $ var2lit v (0 < oldVal) -- cannot return @False@
                         -- #phasesaving >>>>
                         loop False
  loop False

-- | __Fig. 16. (p.20)__
-- Main solve method.
--
-- __Pre-condition:__ If assumptions are used, 'simplifyDB' must be
-- called right before using this method. If not, a top-level conflict (resulting in a
-- non-usable internal state) cannot be distinguished from a conflict under assumptions.
solve :: (Foldable t) => Solver -> t Lit -> IO SolverResult
solve s@Solver{..} assumps = do
  -- PUSH INCREMENTAL ASSUMPTIONS:
  let inject :: Lit -> Bool -> IO Bool
      inject _ False = return False
      inject a True = do
        b <- assume s a
        if not b                  -- conflict analyze
          then do (confl :: Clause) <- getNth reason (lit2var a)
                  analyzeFinal s confl True
                  pushTo conflicts (negateLit a)
                  cancelUntil s 0
                  return False
          else do confl <- propagate s
                  if confl /= NullClause
                    then do analyzeFinal s confl True
                            cancelUntil s 0
                            return False
                    else return True
  check_given <- get' ok
  good <- simplifyDB s
  x <- if check_given /= LiftedF && good then foldrM inject True assumps else return False
  if x
    then do set' rootLevel =<< decisionLevel s
            status <- search s
            -- post-proccesing should be done here
            let toInt :: Var -> IO Lit
                toInt v = (\p -> if LiftedT == p then v else negate v) <$> valueVar s v
            asg1 <- mapM toInt [1 .. nVars]
            asg2 <- map lit2int <$> asList conflicts
            when (0 < dumpSolverStatMode config) $ dumpStats DumpCSV s
            cancelUntil s 0     -- reset solver
            flag <- get' ok
            if | status && flag == LiftedT     -> return $ Right (SAT asg1)
               | not status && flag == LiftedF -> return $ Right (UNSAT asg2)
               | otherwise                     -> return $ Left InternalInconsistent
    else return $ Right (UNSAT [])

-- | Though 'enqueue' is defined in 'Solver', most functions in M114 use @unsafeEnqueue@.
{-# INLINABLE unsafeEnqueue #-}
unsafeEnqueue :: Solver -> Lit -> Clause -> IO ()
unsafeEnqueue s@Solver{..} p from = do
  let v = lit2var p
  setNth assigns v $ lit2lbool p
  setNth level v =<< decisionLevel s
  setNth reason v from     -- NOTE: @from@ might be NULL!
  pushTo trail p

-- | __Pre-condition:__ propagation queue is empty.
{-# INLINE unsafeAssume #-}
unsafeAssume :: Solver -> Lit -> IO ()
unsafeAssume s@Solver{..} p = do
  pushTo trailLim =<< get' trail
  unsafeEnqueue s p NullClause
