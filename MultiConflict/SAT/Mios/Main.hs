{-# LANGUAGE
    BangPatterns
  , RecordWildCards
  , ScopedTypeVariables
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | This is a part of MIOS; main heuristics.
module SAT.Mios.Main
       (
         simplifyDB
       , solve
       )
        where

import Control.Monad ((<=<), unless, void, when)
import Data.Bits
import Data.Foldable (foldrM)
-- import Data.List ((\\), nub, sort, sortBy)
-- import Data.Ord (comparing)
import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.ClauseManager
import SAT.Mios.Solver

-- | returns a rank of 'Clause'. Smaller value is better.
{-# INLINE rankOf #-}
rankOf :: Clause -> IO Int
rankOf = get'

-- | #114: __RemoveWatch__
{-# INLINABLE removeWatch #-}
removeWatch :: Solver -> Clause -> IO ()
removeWatch (watches -> w) c = do
  let lstack = lits c
  l1 <- negateLit <$> getNth lstack 1
  markClause (getNthWatcher w l1) c
  l2 <- negateLit <$> getNth lstack 2
  markClause (getNthWatcher w l2) c

--------------------------------------------------------------------------------
-- Operations on 'Clause'
--------------------------------------------------------------------------------

-- | __Fig. 8. (p.12)__ creates a new LEARNT clause and adds it to watcher lists.
-- This is a strippped-down version of 'newClause' in Solver.
-- Note: Clause must be constructed with the following layout:
-- * (lits c)[0] = the number of literals
-- * (lits c)[1] = the resolvent literal, which present level is larger backjump level.
-- * successive literals = reason literals, which levels are smaller than the backjump level.
{-# INLINABLE pushLearntClause #-}
pushLearntClause :: Solver -> Clause -> Bool -> IO ()
pushLearntClause s@Solver{..} c realResolvent = do
  good <- get' ok
  k <- get' c
  case k of
    _ | not good -> return ()
    1 -> do l <- getNth (lits c) 1
            v <- valueLit s l
            when (v == BottomBool) $ unsafeEnqueueFact s l
    _ -> do
      let lstack = lits c
          -- Pick second literal to watch:
          findMax :: Int -> Int -> Int -> IO Int
          findMax ((<= k) -> False) j _ = return j
          findMax i j val = do b <- getNth level . lit2var =<< getNth lstack i
                               -- By starting the loop from i == 1, we can assure there is no 'large' literal.
                               if val < b then findMax (i + 1) i b else findMax (i + 1) j val
      swapBetween lstack 2 =<< findMax 2 2 0 -- Let @max_i@ be the index of the literal with highest decision level
      -- Bump, enqueue, store clause to all managers
      pushTo learnts c
      l1 <- getNth lstack 1
      pushClauseWithKey (getNthWatcher watches (negateLit l1)) c 0
      l2 <- getNth lstack 2
      pushClauseWithKey (getNthWatcher watches (negateLit l2)) c 0
      -- modify' (activity c) (\x -> if x == 0 then 1 {- fromIntegral d -} else x)
      -- new real learnt clauses should be considered as active
      when realResolvent $ set' (protected c) True

-- | __Simplify.__ At the top-level, a constraint may be given the opportunity to
-- simplify its representation (returns @False@) or state that the constraint is
-- satisfied under the current assignment and can be removed (returns @True@).
-- A constraint must /not/ be simplifiable to produce unit information or to be
-- conflicting; in that case the propagation has not been correctly defined.
--
-- MIOS NOTE: the original doesn't update watchers; only checks its satisfiability.
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
{-# INLINABLE analyze #-}
analyze :: Solver -> Clause -> IO Int
analyze s@Solver{..} confl = do
  -- litvec
  reset litsLearnt
  pushTo litsLearnt 0 -- reserve the first place for the unassigned literal
  dl <- decisionLevel s
  let
    loopOnClauseChain :: Clause -> Lit -> Int -> Int -> Int -> IO Int
    loopOnClauseChain c p ti bl pathC = do -- p : literal, ti = trail index, bl = backtrack level
      when (learnt c) $ claBumpActivity s c
{-
        -- update LBD like #Glucose4.0
        d <- get' (lbd c)
        when (2 < d) $ do
          nblevels <- lbdOf s c
          when (nblevels + 1 < d) $ do -- improve the LBD
            when (d <= 30) $ set' (protected c) True -- 30 is `lbLBDFrozenClause`
            -- seems to be interesting: keep it fro the next round
            set' (lbd c) nblevels    -- Update it
-}
      sc <- get' c
      let
        lstack = lits c
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
                      -- glucose heuristics
                      r <- getNth reason v
                      when (r /= NullClause && learnt r) $ pushTo an'lastDL q
                      -- end of glucose heuristics
                      loopOnLiterals (j + 1) b (pc + 1)
                  else pushTo litsLearnt q >> loopOnLiterals (j + 1) (max b l) pc
            else loopOnLiterals (j + 1) b pc
      (b', pathC') <- loopOnLiterals (if p == bottomLit then 1 else 2) bl pathC
      let
        -- select next clause to look at
        nextPickedUpLit :: Int -> IO Int
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
  let
    merger :: Int -> Int -> IO Int
    merger ((<= n) -> False) b = return b
    merger i b = do
      l <- getNth litsLearnt i
      pushTo an'toClear l
      -- restrict the search depth (range) to 32
      merger (i + 1) . setBit b . (31 .&.) =<< getNth level (lit2var l)
  levels <- merger 2 0
  let
    loopOnLits :: Int -> Int -> IO ()
    loopOnLits ((<= n) -> False) n' = shrinkBy litsLearnt $ n - n' + 1
    loopOnLits i j = do
      l <- getNth litsLearnt i
      c1 <- (NullClause ==) <$> getNth reason (lit2var l)
      if c1
        then setNth litsLearnt j l >> loopOnLits (i + 1) (j + 1)
        else do c2 <- not <$> analyzeRemovable s l levels
                if c2
                  then setNth litsLearnt j l >> loopOnLits (i + 1) (j + 1)
                  else loopOnLits (i + 1) j
  loopOnLits 2 2                -- the first literal is specail
  -- glucose heuristics
  nld <- get' an'lastDL
  r <- get' litsLearnt -- this is not the right value
  let loopOnLastDL :: Int -> IO ()
      loopOnLastDL ((<= nld) -> False) = return ()
      loopOnLastDL i = do v <- lit2var <$> getNth an'lastDL i
                          r' <- rankOf =<< getNth reason v
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
  -- #GreedyPropagation :start; analyze should store the results into watches[0] directly
  newClause <- newClauseFromStack True litsLearnt
  pushClauseWithKey newLearnts newClause levelToReturn
  -- #GreedyPropagation :end
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
{-# INLINABLE analyzeRemovable #-}
analyzeRemovable :: Solver -> Lit -> Int -> IO Bool
analyzeRemovable Solver{..} p minLevel = do
  -- assert (reason[var(p)]!= NullClause);
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
                      if c3 && testBit minLevel (l' .&. 31) -- if (reason[var(p)] != GClause_NULL && ((1 << (level[var(p)] & 31)) & min_level) != 0){
                        then do
                            setNth an'seen v' 1   -- analyze_seen[var(p)] = 1;
                            pushTo an'stack p'    -- analyze_stack.push(p);
                            pushTo an'toClear p'  -- analyze_toclear.push(p);
                            loopOnLit $ i + 1
                        else do
                            -- loopOnLit (int j = top; j < analyze_toclear.size(); j++) analyze_seen[var(analyze_toclear[j])] = 0;
                            top' <- get' an'toClear
                            let clearAll :: Int -> IO ()
                                clearAll ((<= top') -> False) = return ()
                                clearAll j = do x <- getNth an'toClear j; setNth an'seen (lit2var x) 0; clearAll (j + 1)
                            clearAll $ top + 1
                            -- analyze_toclear.shrink(analyze_toclear.size() - top); note: shrink n == repeat n pop
                            shrinkBy an'toClear $ top' - top
                            return False
                  else loopOnLit $ i + 1
            loopOnLit 2        -- CHECKIT why 2
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
{-# INLINABLE analyzeFinal #-}
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
    let
      loopOnTrail :: Int -> IO ()
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
-- #GreedyPropagation: returns @True@ if a conflict occured, otherwise @False@
{-# INLINABLE propagate #-}
propagate :: Solver -> IO Bool
-- | an implementation based on the standard algorithm
propagate s@Solver{..} = do
  let
    cnflClsManager = getNthWatcher watches 0
    while :: Clause -> Bool -> IO Bool
    while _ False = {- bumpAllVar >> -} (0 <) <$> get' cnflClsManager
    while conflC True = do
      (p :: Lit) <- getNth trail . (1 +) =<< get' qHead
      let falseLit = negateLit p
      modify' qHead (+ 1)
      let (ws :: ClauseExtManager) = getNthWatcher watches p
      end <- get' ws
      cvec <- getClauseVector ws
      bvec <- getKeyVector ws
      let
        forClause :: Clause -> Int -> Int -> IO Bool
        forClause confl i@((< end) -> False) j = do
          shrinkBy ws (i - j)
          while confl =<< ((<) <$> get' qHead <*> get' trail)
        forClause confl i j = do
          (l :: Lit) <- getNth bvec i
          (c :: Clause) <- getNth cvec i
          bv <- if l == 0 then return LiftedFalse else valueLit s l
          if bv == LiftedTrue
            then do
                 unless (i == j) $ do -- NOTE: if i == j, the path doesn't require accesses to cvec!
                   setNth cvec j c
                   setNth bvec j l
                 forClause confl (i + 1) (j + 1)
            else do
                let lstack = lits c
                -- Make sure the false literal is data[1]
                ((falseLit ==) <$> getNth lstack 1) >>= (`when` swapBetween lstack 1 2)
                -- if 0th watch is true, then clause is already satisfied.
                (first :: Lit) <- getNth lstack 1
                val <- valueLit s first
                if val == LiftedTrue
                  then setNth cvec j c >> setNth bvec j first >> forClause confl (i + 1) (j + 1)
                  else do
                      -- Look for a new watch
                      cs <- get' c
                      let
                        forLit :: Int -> IO Bool
                        forLit ((<= cs) -> False) = do
                          -- Did not find watch; clause is unit under assignment:
                          setNth cvec j c
                          setNth bvec j 0
                          noConflict <- enqueue s first c
                          if noConflict
                            then forClause confl (i + 1) (j + 1)
                            else do
                                ((== 0) <$> decisionLevel s) >>= (`when` set' ok False)
                                pushClauseWithKey cnflClsManager c first
                                set' qHead =<< get' trail
                                -- Copy the remaining watches:
                                let
                                  copy i'@((< end) -> False) j' = forClause c i' j'
                                  copy i' j' = do
                                    setNth cvec j' =<< getNth cvec i'
                                    setNth bvec j' =<< getNth bvec i'
                                    copy (i' + 1) (j' + 1)
                                copy (i + 1) (j + 1)
                        forLit k = do
                          (l' :: Lit) <- getNth lstack k
                          lv <- valueLit s l'
                          if lv == LiftedFalse
                            then forLit $ k + 1
                            else do
                                swapBetween lstack 2 k
                                pushClauseWithKey (getNthWatcher watches (negateLit l')) c l'
                                forClause confl (i + 1) j
                      forLit 3
      forClause conflC 0 0
  reset cnflClsManager
  while NullClause =<< ((<) <$> get' qHead <*> get' trail)

{-
-- | an implementation of greedy propagation
propagate s@Solver{..} gp's gp'i = do
  nAssigns' <- nAssigns s
  -- myVal <- getNth stats (fromEnum NumOfBackjumps)
  -- we use the first element of 'watches' to store all conflicting clauses. So clear it here.
  let cnflClsManager = getNthWatcher watches 0
  reset cnflClsManager
  -- By using enough big value, 'lim < now' is the valid predicate to check the termination condition.
  -- initLimProp <- (5 *) <$> ((+) <$> nClauses s <*> nLearnts s)
  let
    -- the arg is the limit/current propagations
    -- it returts @True@ if a conflict occured
    handleWatch :: Int -> IO Bool
    handleWatch np = do
      qindex <- get' qHead
      tindex <- get' trail
      case () of
        _ | not (qindex < tindex) -> (0 <) <$> get' cnflClsManager
        _ -> do
              (p :: Lit) <- getNth trail (qindex + 1)
              let falseLit = negateLit p
              modify' qHead (+ 1)
              let (ws :: ClauseExtManager) = getNthWatcher watches p
              end <- get' ws
              cvec <- getClauseVector ws
              bvec <- getKeyVector ws
              let
                -- 1st arg is the limit/current propagations
                -- 2nd arg is the source clause index
                -- 3rd arg is the distination clause index
                seekConflict :: Int -> Int -> Int -> IO Bool -- CPS
                seekConflict 0 i j = do                      -- TERMINATION CONDITION
                  unless (i == j) $ do
                    let
                      copy :: Int -> Int -> IO ()
                      copy ((< end) -> False) j' = shrinkBy ws (end - j')
                      copy i' j' = do setNth cvec j' =<< getNth cvec i'
                                      setNth bvec j' =<< getNth bvec i'
                                      copy (i' + 1) (j' + 1)
                    copy i j
                  set' qHead =<< get' trail
                  (0 <) <$> get' cnflClsManager
                seekConflict n ((== end) -> True) j = do     -- end of watch list
                  unless (end == j) $ shrinkBy ws (end - j)
                  handleWatch n
                seekConflict n i j = do                      -- normal case
                  (l :: Lit) <- getNth bvec i
                  (c :: Clause) <- getNth cvec i
                  bv <- if l == 0 || falseLit == l then return LiftedFalse else valueLit s l
                  if bv == LiftedTrue
                    then do unless (i == j) (setNth cvec j c >> setNth bvec j l)
                            seekConflict (n + 1) (i + 1) (j + 1)
                    else do
                        let lstack = lits c
                        -- Make sure the false literal is data[1]
                        ((falseLit ==) <$> getNth lstack 1) >>= (`when` swapBetween lstack 1 2)
                        -- if 0th watch is true, then clause is already satisfied.
                        (first :: Lit) <- getNth lstack 1
                        val <- valueLit s first
                        if val == LiftedTrue || abs val == ConflictBool
                          then do setNth cvec j c
                                  setNth bvec j first
                                  seekConflict (n + 1) (i + 1) (j + 1)
                          else
                          do -- Look for a new watch
                            cs <- get' c
                            let
                              forLit :: Int -> IO Bool -- CPS
                              forLit ((<= cs) -> False) = do
                                -- Did not find watch; clause is unit under assignment:
                                setNth cvec j c
                                setNth bvec j 0
                                noConflict <- enqueue s first c
                                if noConflict
                                  then seekConflict (n + 1) (i + 1) (j + 1)
                                  else do
                                    let v = lit2var first
                                    dl <- decisionLevel s
                                    when (dl == 0) $ set' ok False
                                    pushClauseWithKey cnflClsManager c first
                                    setNth phases v =<< getNth assigns v
                                    lv <- getNth level v
                                    when (lv == dl) $ setNth assigns v ConflictBool
                                    n' <- if 0 < n
                                          then do dn <- subtract nAssigns' <$> nAssigns s -- delta of nAssigns
                                                  let delta :: Double -- that is assign rate against propagation
                                                      delta = gp's * (fromIntegral dn / fromIntegral n) ** gp'i
                                                      -- delta = gp's * fromIntegral dn / fromIntegral n ** gp'i
                                                  return . negate . floor $ delta
                                          else return $ n + 1
                                    seekConflict n' (i + 1) (j + 1)
                              forLit k = do
                                (l' :: Lit) <- getNth lstack k
                                lv <- valueLit s l'
                                if lv == LiftedFalse
                                  then forLit $ k + 1
                                  else do swapBetween lstack 2 k
                                          pushClauseWithKey (getNthWatcher watches (negateLit l')) c l'
                                          seekConflict (n + 1) (i + 1) j
                            forLit 3
              seekConflict np 0 0
  handleWatch 1
-}

-- | #M22
-- reduceDB: () -> [void]
--
-- __Description:__
--   Remove half of the learnt clauses, minus the clauses locked by the current assigmnent. Locked
--   clauses are clauses that are reason to some assignment. Binary clauses are never removed.
{-# INLINABLE reduceDB #-}
reduceDB :: Solver -> IO ()
reduceDB s@Solver{..} = do
  n <- nLearnts s
  vec <- getClauseVector learnts
  let
    loop :: Int -> IO ()
    loop ((< n) -> False) = return ()
    loop i = (removeWatch s =<< getNth vec i) >> loop (i + 1)
  k <- sortClauses s learnts (div n 2) -- k is the number of clauses not to be purged
  loop k                               -- CAVEAT: `vec` is a zero-based vector
  reset watches
  shrinkBy learnts (n - k)

-- | (Good to Bad) Quick sort the key vector based on their activities and returns number of privileged clauses.
-- this function uses the same metrix as reduceDB_lt in glucose 4.0:
-- 1. binary clause
-- 2. smaller rank
-- 3. larger activity defined in MiniSat
-- , where smaller value is better.
--
-- they are coded into an Int as the following layout:
--
-- * 14 bit: LBD or 0 for preserved clauses
-- * 19 bit: converted activity
-- * remain: clauseVector index
--
rankWidth, activityWidth, indexWidth :: Int
(rankWidth, activityWidth, indexWidth) = (l, a, w - (l + a + 1))
  where
    w = finiteBitSize (0:: Int)
    (l, a) = case () of
      _ | 64 <= w -> (8, 25)   -- 30 bit =>   1G clauses
      _ | 60 <= w -> (8, 24)   -- 26 bit =>  64M clauses
      _ | 32 <= w -> (6,  7)   -- 18 bit => 256K clauses
      _ | 29 <= w -> (6,  5)   -- 17 bit => 128K clauses
      _ -> errorWithoutStackTrace "Int on your CPU doesn't have sufficient bit width."

{-# INLINABLE sortClauses #-}
sortClauses :: Solver -> ClauseExtManager -> Int -> IO Int
sortClauses s cm nneeds = do
  -- constants
  let
    rankMax :: Int
    rankMax = 2 ^ rankWidth - 1
    activityMax :: Int
    activityMax = 2 ^ activityWidth - 1
    activityScale :: Double
    activityScale = fromIntegral activityMax
    indexMax :: Int
    indexMax = (2 ^ indexWidth - 1) -- 67,108,863 for 26
  n <- get' cm
  -- when (indexMax < n) $ errorWithoutStackTrace $ "## The number of learnt clauses " ++ show n ++ " exceeds mios's " ++ show indexWidth ++" bit manage capacity"
  vec <- getClauseVector cm
  keys <- getKeyVector cm
  -- 1: assign keys
  let
    assignKey :: Int -> Int -> IO Int
    assignKey ((< n) -> False) m = return m
    assignKey i m = do
      c <- getNth vec i
      k <- (\k -> if k == 2 then return k else fromEnum <$> get' (protected c)) =<< get' c
      case k of
        1 -> set' (protected c) False >> setNth keys i (shiftL 2 indexWidth + i) >> assignKey (i + 1) (m + 1)
        2 -> setNth keys i (shiftL 1 indexWidth + i) >> assignKey (i + 1) (m + 1)
        _ -> do
            l <- locked s c      -- this is expensive
            if l
              then setNth keys i (shiftL 1 indexWidth + i) >> assignKey (i + 1) (m + 1)
              else do
                  d <- rankOf c
                  b <- floor . (activityScale *) . (1 -) . logBase claActivityThreshold . max 1 <$> get' (activity c)
                  setNth keys i $ shiftL (min rankMax d) (activityWidth + indexWidth) + shiftL b indexWidth + i
                  assignKey (i + 1) m
  limit <- min n . (+ nneeds) <$> assignKey 0 0
  -- 2: sort keyVector
  let
    sortOnRange :: Int -> Int -> IO ()
    sortOnRange left right
      | limit < left = return ()
      | left >= right = return ()
      | left + 1 == right = do
          a <- getNth keys left
          b <- getNth keys right
          unless (a < b) $ swapBetween keys left right
      | otherwise = do
          let p = div (left + right) 2
          pivot <- getNth keys p
          swapBetween keys p left -- set a sentinel for r'
          let
            nextL :: Int -> IO Int
            nextL i@((<= right) -> False) = return i
            nextL i = do v <- getNth keys i; if v < pivot then nextL (i + 1) else return i
            nextR :: Int -> IO Int
            nextR i = do v <- getNth keys i; if pivot < v then nextR (i - 1) else return i
            divide :: Int -> Int -> IO Int
            divide l r = do
              l' <- nextL l
              r' <- nextR r
              if l' < r' then swapBetween keys l' r' >> divide (l' + 1) (r' - 1) else return r'
          m <- divide (left + 1) right
          swapBetween keys left m
          sortOnRange left (m - 1)
          sortOnRange (m + 1) right
  sortOnRange 0 (n - 1)
  -- 3: place clauses
  let
    seek :: Int -> IO ()
    seek ((< limit) -> False) = return ()
    seek i = do
      bits <- getNth keys i
      when (indexMax < bits) $ do
        c <- getNth vec i
        let
          sweep k = do
            k' <- (indexMax .&.) <$> getNth keys k
            setNth keys k k
            if k' == i
              then setNth vec k c
              else getNth vec k' >>= setNth vec k >> sweep k'
        sweep i
      seek $ i + 1
  seek 0
  return limit

-- | #M22
--
-- simplify : [void] -> [bool]
--
-- __Description:__
--   Simplify the clause database according to the current top-level assigment. Currently, the only
--   thing done here is the removal of satisfied clauses, but more things can be put here.
--
{-# INLINABLE simplifyDB #-}
simplifyDB :: Solver -> IO Bool
simplifyDB s@Solver{..} = do
  good <- get' ok
  if good
    then do
      conflicting <- propagate s
      if conflicting
        then set' ok False >> return False
        else do
            -- Clear watcher lists:
            n <- get' trail
            let loopOnTrail ((<= n) -> False) = return ()
                loopOnTrail i = do l <- getNth trail i
                                   reset . getNthWatcher watches $ l
                                   reset . getNthWatcher watches $ negateLit l
                                   loopOnTrail $ i + 1
            loopOnTrail 1
            -- Remove satisfied clauses:
            let
              for :: Int -> IO Bool
              for ((< 2) -> False) = return True
              for t = do
                let ptr = if t == 0 then learnts else clauses
                vec' <- getClauseVector ptr
                n' <- get' ptr
                let
                  loopOnVector :: Int -> Int -> IO Bool
                  loopOnVector ((< n') -> False) j = shrinkBy ptr (n' - j) >> return True
                  loopOnVector i j = do
                        c <- getNth vec' i
                        l <- locked s c
                        r <- simplify s c
                        if not l && r
                          then removeWatch s c >> loopOnVector (i + 1) j
                          else setNth vec' j c >> loopOnVector (i + 1) (j + 1)
                loopOnVector 0 0
            ret <- for 0
            reset watches
            return ret
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
--   'l_True' if a partial assigment that is consistent with respect to the clause set is found. If
--   all variables are decision variables, that means that the clause set is satisfiable. 'l_False'
--   if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
{-# INLINABLE search #-}
search :: Solver -> Int -> Int -> IO Int
search s@Solver{..} nOfConflicts nOfLearnts = do
  -- clear model
  let
    loop :: Int -> IO Int
    loop conflictC = do
      conflicting <- propagate s
      d <- decisionLevel s
      if conflicting
        then do confl <- getConflictingClause s
                incrementStat s NumOfBackjumps 1
    --            cp <- return False -- (1000 <) <$> getStat s NumOfBackjumps -- SET CHECK POINT
                r <- get' rootLevel
                if d == r -- Contradiction found:
                  then do analyzeFinal s confl False
                          setStat s SatisfiabilityValue (-1)
                          return LiftedFalse
                  else do
--                      u <- (== 0) . (flip mod 5000) <$> getNth stats (fromEnum NumOfBackjumps)
--                      when u $ do
--                        d <- get' varDecay
--                        when (d < 0.95) $ modify' varDecay (+ 0.01)
                      reset newLearnts
                      let confs = getNthWatcher watches 0
                      conflictCs <- getClauseVector confs
                      n <- get' confs
                      mapM_ (analyze s <=< getNth conflictCs) [0 .. n - 1]
                      dispatchSingleLearnt s
                      -- dispatch s =<< categorizeResolvents s -- (extraParameter3 config) (extraParameter4 config)
                      varDecayActivity s
                      -- claDecayActivity s
                      loop $ conflictC + 1
        else do                 -- NO CONFLICT
            -- Simplify the set of problem clauses:
            when (d == 0) . void $ simplifyDB s -- our simplifier cannot return @False@ here
            k1 <- get' learnts
            k2 <- nAssigns s
            when (k1 - k2 >= nOfLearnts) $ reduceDB s -- Reduce the set of learnt clauses
            case () of
             _ | k2 == nVars -> do
                   -- Model found:
                   let
                     toInt :: Var -> IO Lit
                     toInt v = (\p -> if LiftedTrue == p then v else negate v) <$> valueVar s v
                     setModel :: Int -> IO ()
                     setModel ((<= nVars) -> False) = return ()
                     setModel v = (setNth model v =<< toInt v) >> setModel (v + 1)
                   setModel 1
                   setStat s SatisfiabilityValue 1
                   return LiftedTrue
             _ | conflictC >= nOfConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< get' rootLevel -- force a restart
                   claRescaleActivityAfterRestart s
                   incrementStat s NumOfRestarts 1
                   return BottomBool
             _ -> do
               -- New variable decision:
               v <- select s -- many have heuristic for polarity here
               -- << #phasesaving
               oldVal <- getNth phases v
               unsafeAssume s $ var2lit v (0 < oldVal) -- cannot return @False@
               -- >> #phasesaving
               loop conflictC
  good <- get' ok
  if good then loop 0 else setStat s SatisfiabilityValue (-1) >> return LiftedFalse

-- | __Fig. 16. (p.20)__
-- Main solve method.
--
-- __Pre-condition:__ If assumptions are used, 'simplifyDB' must be
-- called right before using this method. If not, a top-level conflict (resulting in a
-- non-usable internal state) cannot be distinguished from a conflict under assumptions.
{-# INLINABLE solve #-}
solve :: (Foldable t) => Solver -> t Lit -> IO Bool
solve s@Solver{..} assumps = do
  -- PUSH INCREMENTAL ASSUMPTIONS:
  let
    injector :: Lit -> Bool -> IO Bool
    injector _ False = return False
    injector a True = do
      b <- assume s a
      if not b
        then do                 -- conflict analyze
            (confl :: Clause) <- getNth reason (lit2var a)
            analyzeFinal s confl True
            pushTo conflicts (negateLit a)
            cancelUntil s 0
            return False
        else do
            conflicting <- propagate s
            if conflicting
              then do
                  confl <- getConflictingClause s
                  analyzeFinal s confl True
                  cancelUntil s 0
                  return False
              else return True
  good <- simplifyDB s
  x <- if good then foldrM injector True assumps else return False
  if not x
    then setStat s SatisfiabilityValue (-1) >> return False
    else do
        set' rootLevel =<< decisionLevel s
        -- SOLVE:
        nc <- fromIntegral <$> nClauses s
        let
          while :: Double -> Double -> IO Bool
          while nOfConflicts nOfLearnts = do
            status <- search s (floor nOfConflicts) (floor nOfLearnts)
            if status == BottomBool
              then while (1.5 * nOfConflicts) (1.1 * nOfLearnts)
              else cancelUntil s 0 >> return (status == LiftedTrue)
        while 100 (nc / 3.0)

-- | Though 'enqueue' is defined in 'Solver', most functions in M114 use @unsafeEnqueue@.
{-# INLINABLE unsafeEnqueue #-}
unsafeEnqueue :: Solver -> Lit -> Clause -> IO ()
unsafeEnqueue s@Solver{..} p from = do
  let v = lit2var p
  setNth assigns v $! if positiveLit p then LiftedTrue else LiftedFalse
  setNth level v =<< decisionLevel s
  setNth reason v from     -- NOTE: @from@ might be NULL!
  pushTo trail p

-- | Though 'enqueue' is defined in 'Solver', most functions in M114 use @unsafeEnqueue@.
{-# INLINABLE unsafeEnqueueFact #-}
unsafeEnqueueFact :: Solver -> Lit -> IO ()
unsafeEnqueueFact Solver{..} p = do
  let v = lit2var p
  setNth assigns v $! if positiveLit p then LiftedTrue else LiftedFalse
  setNth level v 0
  setNth reason v NullClause
  pushTo trail p

-- | __Pre-condition:__ propagation queue is empty.
{-# INLINE unsafeAssume #-}
unsafeAssume :: Solver -> Lit -> IO ()
unsafeAssume s@Solver{..} p = do
  pushTo trailLim =<< get' trail
  unsafeEnqueue s p NullClause

-- | #GreedyPropagation: selects a conflicting clause from the manager
{-# INLINE getConflictingClause #-}
getConflictingClause :: Solver -> IO Clause
getConflictingClause s = flip getNth 0 =<< getClauseVector (getNthWatcher (watches s) 0)

-- | ((backjump level, clause size, crashing(conflicting) var, source-of-conflict literal), learnt)
type Resolvent = ((Int, Double, Lit, Var), Clause)
type SelectorOutput = (Int, Either Lit [Resolvent], [Resolvent])

-- | the latter part of resolvent categorization
{-# INLINABLE dispatch #-}
dispatch :: Solver -> SelectorOutput -> IO ()
dispatch s@Solver{..} (bj, lowest, clss) = do
  let register :: Resolvent -> IO ()
      register ((k, _, _, _), c) = do pushLearntClause s c (k <= bj)
                                      set' (activity c) $ fromIntegral bj
      implicate :: Resolvent -> IO ()
      implicate ((_, _, _, t), c) = do v <- valueLit s t
                                       when (v == BottomBool) $ unsafeEnqueue s t c
  cancelUntil s bj
  mapM_ register clss
  case lowest of
    Left l   -> unsafeAssume s l
    Right cs -> do mapM_ register cs
                   mapM_ implicate cs

-- | Resolvent Categorization
{-# INLINE categorizeResolvents #-}
categorizeResolvents :: Solver -> {- Int -> Int -> -} IO SelectorOutput
-- an implementation for the normal propagation embedded in resolevent categorization
categorizeResolvents Solver{..} {- 0 0 -} = do
  c <- flip getNth 0 =<< getClauseVector newLearnts
  b <- flip getNth 0 =<< getKeyVector newLearnts
  t <- getNth (lits c) 1
  -- varBumpAll solver 1
  return (b, Right [((b, 0, 0, t), c)], [])

dispatchSingleLearnt :: Solver -> IO ()
dispatchSingleLearnt s@Solver{..} = do
  c <- flip getNth 0 =<< getClauseVector newLearnts
  b <- flip getNth 0 =<< getKeyVector newLearnts
  t <- getNth (lits c) 1
  d <- decisionLevel s
  cancelUntil s b
  -- register ((b, 0, 0, t), c)
  pushLearntClause s c True
  set' (activity c) $ fromIntegral (d - b)
  -- implicate ((b, 0, 0, t), c)
  v <- valueLit s t
  when (v == BottomBool) $ unsafeEnqueue s t c

{-
-- an implementation of resolvent clause categorization
-- * par'3 is used to select a clause evaluator.
-- * par'4 is used whether non-core resolvents are registered.
categorizeResolvents solver@Solver{..} par'3 par'4 = do
  cvec <- getClauseVector newLearnts
  kvec <- getKeyVector newLearnts
  hvec <- getKeyVector (getNthWatcher watches 0)
  void $ subsumeClauses solver    -- DON'T TOUCH; eliminating replicates is crucial.
  n <- get' newLearnts
  let mkResolvent :: Int -> IO Resolvent
      mkResolvent i = do c <- getNth cvec i
                         k <- getNth kvec i
                         s <- getNth hvec i
                         t <- getNth (lits c) 1
                         w <- case par'3 of           -- smaller is better
                                _ | n == 1 -> return 1
                                1 -> fromIntegral <$> get' c
                                2 -> fromIntegral <$> lbdOf solver c
                                3 -> averageActivity solver c
                                _ -> return 1        -- 4 : no valuation
                         return ((k, w, lit2var s, t), c)
      level'  ((k, _, _, _), _) = k
      value'  ((_, w, _, _), _) = w
      crash'  ((_, _, s, _), _) = s
      target' ((_, _, _, t), _) = t
  rsls <- mapM mkResolvent [0 .. n - 1]
  let v = minimum $ map value' rsls
      (cands, ngs) = filter' ((v ==) . value') rsls
      bj = minimum $ map level' cands
      (core', skin) = filter' ((bj ==) . level') {- $ filter ((bj <=) . level') -} cands
      ts = nub $ map target' core'
      core = concatMap (\t -> sortBy (comparing value') (filter ((t ==) . target') core')) ts
  -- mapM_ (\r -> do varBumpActivity solver (crash' r); set' (activity (snd r)) 1) core
  mapM_ (\(target' -> t) -> setNth assigns (lit2var t) (lit2lbool t)) $ skin ++ ngs
  return (bj, Right core, if par'4 == 0 then skin else [])

{-# INLINE filter' #-}
filter' :: (a -> Bool) -> [a] -> ([a], [a])
filter' f l = foldr merger ([], []) l
  where merger x (a,b) = if f x then (x : a, b) else (a, x : b)

-- | note: the target literal's level is going to decrease to the highest level of remains.
-- So we drop the highest one by @init . sort@.
{-# INLINE lbdOf #-}
lbdOf :: Solver -> Clause -> IO Int
lbdOf Solver{..} c = (length . nub . init . sort) <$> (mapM (getNth level . lit2var) . tail =<< asList c)

-- | returns a sort of clause activity; smaller is better.
averageActivity :: Solver -> Clause -> IO Double
averageActivity Solver{..} c = do
  n <- get' c
  let lstack = lits c
      loop :: Int -> Double -> IO Double
      loop ((<= n) -> False) x = return $ fromIntegral n / x
      loop i x = do a <- getNth activities . lit2var =<< getNth lstack i
                    loop (i + 1) (x + a)
  loop 1 0

-- | deletes subsumed clauses from generated learnts
-- Since the number of learnts is very small, we can use list, sort, and so on.
-- And it returns the lowest and second lowest decision level to resolve conflicts
-- Note: also key vector of watches[0] changes to keep the relation between conflict clauses and resolvent clauses
subsumeClauses :: Solver -> IO (Int, Int)
subsumeClauses s@Solver{..} = do
--  cp <- return False -- (1000 <) <$> getStat s NumOfBackjumps
  let manager = newLearnts
  let cnflMgr = getNthWatcher watches 0
  cvec <- getClauseVector manager
  bvec <- getKeyVector manager
  hvec <- getKeyVector cnflMgr
  let
    -- 1st arg @n@ is the index of the last clause; so valid index is [0 .. n]
    loop :: Int -> Int -> Int -> Int -> IO (Int, Int)
    loop n i low high
      | n < i = do
          set' manager i
          return $ if low == 0 then (0, 0) else (low, if n == 0 then low else high)
      | otherwise = do
          c <- getNth cvec i
          let
            removeNth :: Int -> Int -> [Int] -> IO (Int, Int)
            removeNth lastIndex j cls
              | lastIndex < j = do
                  b <- getNth bvec i
                  loop lastIndex (i + 1) (min low b) (max high b)
              | otherwise = do
                  c' <- getNth cvec j
                  cls' <- asList c'
                  if null (cls' \\ cls)                      -- cls' is included in cls completely.
                    then do setNth cvec i c'                 -- So c should be replaced by c'
                            setNth bvec i =<< getNth bvec j
                            setNth hvec i =<< getNth hvec j
                            setNth cvec j =<< getNth cvec lastIndex
                            setNth bvec j =<< getNth bvec lastIndex
                            setNth hvec j =<< getNth hvec lastIndex
                            removeNth (lastIndex - 1) j cls'             -- reexam the new j-th clause
                    else if null (cls \\ cls')                           -- j-th clause should be removed by swapping the last element
                         then do setNth cvec j =<< getNth cvec lastIndex
                                 setNth bvec j =<< getNth bvec lastIndex
                                 setNth hvec j =<< getNth hvec lastIndex
                                 removeNth (lastIndex - 1) j cls
                         else removeNth lastIndex (j + 1) cls
          removeNth n (i + 1) =<< asList c
  -- NOTE: most GP strategies contaminate the current level by ConflictBool
  -- So we have to erase at least the current level.
  d <- subtract 1 <$> decisionLevel s
  n <- subtract 1 <$> get' manager
  loop n 0 d d
-}
