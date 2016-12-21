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

import Control.Monad (unless, void, when)
import Data.Bits
import Data.Foldable (foldrM)
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
  let lvec = asUVector c
  l1 <- negateLit <$> getNth lvec 0
  markClause (getNthWatcher w l1) c
  l2 <- negateLit <$> getNth lvec 1
  markClause (getNthWatcher w l2) c

--------------------------------------------------------------------------------
-- Operations on 'Clause'
--------------------------------------------------------------------------------

-- | __Fig. 8. (p.12)__ creates a new LEARNT clause and adds it to watcher lists.
-- This is a strippped-down version of 'newClause' in Solver.
{-# INLINABLE newLearntClause #-}
newLearntClause :: Solver -> Stack -> IO ()
newLearntClause s@Solver{..} ps = do
  good <- get' ok
  when good $ do
    -- ps is a 'SizedVectorInt'; ps[0] is the number of active literals
    -- Since this solver must generate only healthy learnt clauses, we need not to run misc check in 'newClause'
    k <- get' ps
    case k of
     1 -> do
       l <- getNth ps 1
       unsafeEnqueue s l NullClause
     _ -> do
       -- allocate clause:
       c <- newClauseFromStack True ps
       let vec = asUVector c
       -- Pick a second literal to watch:
       let
         findMax :: Int -> Int -> Int -> IO Int
         findMax ((< k) -> False) j _ = return j
         findMax i j val = do
           v <- lit2var <$> getNth vec i
           a <- getNth assigns v
           b <- getNth level v
           if (a /= LiftedBottom) && (val < b)
             then findMax (i + 1) i b
             else findMax (i + 1) j val
       swapBetween vec 1 =<< findMax 0 0 0 -- Let @max_i@ be the index of the literal with highest decision level
       -- Bump, enqueue, store clause:
       set' (activity c) . fromIntegral =<< decisionLevel s -- newly learnt clauses should be considered active
       -- Add clause to all managers
       pushTo learnts c
       l <- getNth vec 0
       pushClauseWithKey (getNthWatcher watches (negateLit l)) c 0
       l1 <- negateLit <$> getNth vec 1
       pushClauseWithKey (getNthWatcher watches l1) c 0
       -- update the solver state by @l@
       unsafeEnqueue s l c
       -- Since unsafeEnqueue updates the 1st literal's level, setLBD should be called after unsafeEnqueue
       -- setRank s c
       set' (protected c) True

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
  let
    lvec = asUVector c
    loop ::Int -> IO Bool
    loop ((< n) -> False) = return False
    loop i = do
      v <- valueLit s =<< getNth lvec i
      if v == 1 then return True else loop (i + 1)
  loop 0

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
    litsVec = asUVector litsLearnt
    trailVec = asUVector trail
    loopOnClauseChain :: Clause -> Lit -> Int -> Int -> Int -> IO Int
    loopOnClauseChain c p ti bl pathC = do -- p : literal, ti = trail index, bl = backtrack level
      when (learnt c) $ do
        claBumpActivity s c
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
        lvec = asUVector c
        loopOnLiterals :: Int -> Int -> Int -> IO (Int, Int)
        loopOnLiterals ((< sc) -> False) b pc = return (b, pc) -- b = btLevel, pc = pathC
        loopOnLiterals j b pc = do
          (q :: Lit) <- getNth lvec j
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
      (b', pathC') <- loopOnLiterals (if p == bottomLit then 0 else 1) bl pathC
      let
        -- select next clause to look at
        nextPickedUpLit :: Int -> IO Int
        nextPickedUpLit i = do
          x <- getNth an'seen . lit2var =<< getNth trailVec i
          if x == 0 then nextPickedUpLit $ i - 1 else return i
      ti' <- nextPickedUpLit ti
      nextP <- getNth trailVec ti'
      let nextV = lit2var nextP
      confl' <- getNth reason nextV
      setNth an'seen nextV 0
      if 1 < pathC'
        then loopOnClauseChain confl' nextP (ti' - 1) b' (pathC' - 1)
        else setNth litsVec 0 (negateLit nextP) >> return b'
  ti <- subtract 1 <$> get' trail
  levelToReturn <- loopOnClauseChain confl bottomLit ti 0 0
  -- Simplify phase (implemented only @expensive_ccmin@ path)
  n <- get' litsLearnt
  reset an'stack           -- analyze_stack.clear();
  reset an'toClear         -- out_learnt.copyTo(analyze_toclear);
  pushTo an'toClear =<< getNth litsVec 0
  let
    merger :: Int -> Int -> IO Int
    merger ((< n) -> False) b = return b
    merger i b = do
      l <- getNth litsVec i
      pushTo an'toClear l
      -- restrict the search depth (range) to 32
      merger (i + 1) . setBit b . (31 .&.) =<< getNth level (lit2var l)
  levels <- merger 1 0
  let
    loopOnLits :: Int -> Int -> IO ()
    loopOnLits ((< n) -> False) n' = shrinkBy litsLearnt $ n - n'
    loopOnLits i j = do
      l <- getNth litsVec i
      c1 <- (NullClause ==) <$> getNth reason (lit2var l)
      if c1
        then setNth litsVec j l >> loopOnLits (i + 1) (j + 1)
        else do
           c2 <- not <$> analyzeRemovable s l levels
           if c2
             then setNth litsVec j l >> loopOnLits (i + 1) (j + 1)
             else loopOnLits (i + 1) j
  loopOnLits 1 1                -- the first literal is specail
  -- glucose heuristics
  nld <- get' an'lastDL
  r <- get' litsLearnt -- this is not the right value
  let
    vec = asUVector an'lastDL
    loopOnLastDL :: Int -> IO ()
    loopOnLastDL ((< nld) -> False) = return ()
    loopOnLastDL i = do
      v <- lit2var <$> getNth vec i
      r' <- rankOf =<< getNth reason v
      when (r < r') $ varBumpActivity s v
      loopOnLastDL $ i + 1
  loopOnLastDL 0
  reset an'lastDL
  -- Clear seen
  k <- get' an'toClear
  let
    vec' = asUVector an'toClear
    cleaner :: Int -> IO ()
    cleaner ((< k) -> False) = return ()
    cleaner i = do
      v <- lit2var <$> getNth vec' i
      setNth an'seen v 0
      cleaner $ i + 1
  cleaner 0
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
              cvec = asUVector c
              loopOnLit :: Int -> IO Bool -- loopOnLit (int i = 1; i < c.size(); i++){
              loopOnLit ((< nl) -> False) = loopOnStack
              loopOnLit i = do
                p' <- getNth cvec i              -- valid range is [0 .. nl - 1]
                let v' = lit2var p'
                l' <- getNth level v'
                c1 <- (1 /=) <$> getNth an'seen v'
                if c1 && (0 /= l')   -- if (!analyze_seen[var(p)] && level[var(p)] != 0){
                  then do
                      c3 <- (NullClause /=) <$> getNth reason v'
                      if c3 && testBit minLevel (l' .&. 31) -- if (reason[var(p)] != GClause_NULL && ((1 << (level[var(p)] & 31)) & min_level) != 0){
                        then do
                            setNth an'seen v' 1        -- analyze_seen[var(p)] = 1;
                            pushTo an'stack p'    -- analyze_stack.push(p);
                            pushTo an'toClear p'  -- analyze_toclear.push(p);
                            loopOnLit $ i + 1
                        else do
                            -- loopOnLit (int j = top; j < analyze_toclear.size(); j++) analyze_seen[var(analyze_toclear[j])] = 0;
                            top' <- get' an'toClear
                            let
                              vec = asUVector an'toClear
                              clearAll :: Int -> IO ()
                              clearAll ((< top') -> False) = return ()
                              clearAll j = do x <- getNth vec j; setNth an'seen (lit2var x) 0; clearAll (j + 1)
                            clearAll top
                            -- analyze_toclear.shrink(analyze_toclear.size() - top); note: shrink n == repeat n pop
                            shrinkBy an'toClear $ top' - top
                            return False
                  else loopOnLit $ i + 1
            loopOnLit 1
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
    let
      lvec = asUVector confl
      loopOnConfl :: Int -> IO ()
      loopOnConfl ((< n) -> False) = return ()
      loopOnConfl i = do
        (x :: Var) <- lit2var <$> getNth lvec i
        lvl <- getNth level x
        when (0 < lvl) $ setNth an'seen x 1
        loopOnConfl $ i + 1
    loopOnConfl $ if skipFirst then 1 else 0
    tls <- get' trailLim
    trs <- get' trail
    tlz <- getNth (asUVector trailLim) 0
    let
      trailVec = asUVector trail
      loopOnTrail :: Int -> IO ()
      loopOnTrail ((tlz <=) -> False) = return ()
      loopOnTrail i = do
        (l :: Lit) <- getNth trailVec i
        let (x :: Var) = lit2var l
        saw <- getNth an'seen x
        when (saw == 1) $ do
          (r :: Clause) <- getNth reason x
          if r == NullClause
            then pushTo conflicts (negateLit l)
            else do
                k <- get' r
                let
                  cvec = asUVector r
                  loopOnLits :: Int -> IO ()
                  loopOnLits ((< k) -> False) = return ()
                  loopOnLits j = do
                    (v :: Var) <- lit2var <$> getNth cvec j
                    lv <- getNth level v
                    when (0 < lv) $ setNth an'seen v 1
                    loopOnLits $ i + 1
                loopOnLits 1
        setNth an'seen x 0
        loopOnTrail $ i - 1
    loopOnTrail =<< if tls <= rl then return (trs - 1) else getNth (asUVector trailLim) rl

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
{-# INLINABLE propagate #-}
propagate :: Solver -> IO Clause
propagate s@Solver{..} = do
  -- myVal <- getNth stats (fromEnum NumOfBackjump)
  let
{-
    myVal = 0
    bumpAllVar :: IO ()         -- not in use
    bumpAllVar = do
      let
        loop :: Int -> IO ()
        loop ((<= nVars) -> False) = return ()
        loop i = do
          c <- getNth pr'seen i
          when (c == myVal) $ varBumpActivity s i
          loop $ i + 1
      loop 1
-}
    trailVec = asUVector trail
    while :: Clause -> Bool -> IO Clause
    while confl False = {- bumpAllVar >> -} return confl
    while confl True = do
      (p :: Lit) <- getNth trailVec =<< get' qHead
      modify' qHead (+ 1)
      let (ws :: ClauseExtManager) = getNthWatcher watches p
      end <- get' ws
      cvec <- getClauseVector ws
      bvec <- getKeyVector ws
--      rc <- getNth reason $ lit2var p
--      byGlue <- if (rc /= NullClause) && learnt rc then (== 2) <$> get' (lbd rc) else return False
      let
{-
        checkAllLiteralsIn :: Clause -> IO () -- not in use
        checkAllLiteralsIn c = do
          nc <- sizeOfClause c
          let
            vec = asuVector c
            loop :: Int -> IO ()
            loop((< nc) -> False) = return ()
            loop i = do
              (v :: Var) <- lit2var <$> getNth vec i
              setNth pr'seen v myVal
              loop $ i + 1
          loop 0
-}
        forClause :: Clause -> Int -> Int -> IO Clause
        forClause confl i@((< end) -> False) j = do
          shrinkBy ws (i - j)
          while confl =<< ((<) <$> get' qHead <*> get' trail)
        forClause confl i j = do
          (l :: Lit) <- getNth bvec i
          bv <- if l == 0 then return LiftedFalse else valueLit s l
          if bv == LiftedTrue
            then do
                 unless (i == j) $ do -- NOTE: if i == j, the path doesn't require accesses to cvec!
                   (c :: Clause) <- getNth cvec i
                   setNth cvec j c
                   setNth bvec j l
                 forClause confl (i + 1) (j + 1)
            else do
                -- checkAllLiteralsIn c
                (c :: Clause) <- getNth cvec i
                let
                  lits = asUVector c
                  falseLit = negateLit p
                -- Make sure the false literal is data[1]
                ((falseLit ==) <$> getNth lits 0) >>= (`when` swapBetween lits 0 1)
                -- if 0th watch is true, then clause is already satisfied.
                (first :: Lit) <- getNth lits 0
                val <- valueLit s first
                if val == LiftedTrue
                  then setNth cvec j c >> setNth bvec j first >> forClause confl (i + 1) (j + 1)
                  else do
                      -- Look for new watch
                      cs <- get' c
                      let
                        forLit :: Int -> IO Clause
                        forLit ((< cs) -> False) = do
                          -- Did not find watch; clause is unit under assignment:
                          setNth cvec j c
                          setNth bvec j 0
                          result <- enqueue s first c
                          if not result
                            then do
                                ((== 0) <$> decisionLevel s) >>= (`when` set' ok False)
                                -- #BBCP
                                set' qHead =<< get' trail
                                -- Copy the remaining watches:
                                let
                                  copy i'@((< end) -> False) j' = forClause c i' j'
                                  copy i' j' = do
                                    setNth cvec j' =<< getNth cvec i'
                                    setNth bvec j' =<< getNth bvec i'
                                    copy (i' + 1) (j' + 1)
                                copy (i + 1) (j + 1)
                            else forClause confl (i + 1) (j + 1)
                        forLit k = do
                          (l :: Lit) <- getNth lits k
                          lv <- valueLit s l
                          if lv /= LiftedFalse
                            then do
                                swapBetween lits 1 k
                                pushClauseWithKey (getNthWatcher watches (negateLit l)) c l
                                forClause confl (i + 1) j
                            else forLit $ k + 1
                      forLit 2
      forClause confl 0 0
  while NullClause =<< ((<) <$> get' qHead <*> get' trail)

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
(rankWidth :: Int, activityWidth :: Int, indexWidth :: Int) = (l, a, w - (l + a + 1))
  where
    w = finiteBitSize (0:: Int)
    (l, a) = case () of
      _ | 64 <= w -> (8, 25)   -- 30 bit =>   1G clauses
      _ | 60 <= w -> (8, 24)   -- 26 bit =>  64M clauses
      _ | 32 <= w -> (6,  7)   -- 18 bit => 256K clauses
      _ | 29 <= w -> (6,  5)   -- 17 bit => 128K clauses
--      _ -> error "Int on your CPU doesn't have sufficient bit width."

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
  -- when (indexMax < n) $ error $ "## The number of learnt clauses " ++ show n ++ " exceeds mios's " ++ show indexWidth ++" bit manage capacity"
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
      p <- propagate s
      if p /= NullClause
        then set' ok False >> return False
        else do
            -- Clear watcher lists:
            n <- get' trail
            let
              vec = asUVector trail
              loopOnLit ((< n) -> False) = return ()
              loopOnLit i = do
                l <- getNth vec i
                reset . getNthWatcher watches $ l
                reset . getNthWatcher watches $ negateLit l
                loopOnLit $ i + 1
            loopOnLit 0
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
      !confl <- propagate s
      d <- decisionLevel s
      if confl /= NullClause
        then do
            -- CONFLICT
            incrementStat s NumOfBackjump 1
            r <- get' rootLevel
            if d == r
              then do
                  -- Contradiction found:
                  analyzeFinal s confl False
                  return LiftedFalse
              else do
--                  u <- (== 0) . (flip mod 5000) <$> getNth stats (fromEnum NumOfBackjump)
--                  when u $ do
--                    d <- get' varDecay
--                    when (d < 0.95) $ modify' varDecay (+ 0.01)
                  backtrackLevel <- analyze s confl -- 'analyze' resets litsLearnt by itself
                  (s `cancelUntil`) . max backtrackLevel =<< get' rootLevel
                  newLearntClause s litsLearnt
                  k <- get' litsLearnt
                  when (k == 1) $ do
                    (v :: Var) <- lit2var <$> getNth (asUVector litsLearnt) 0
                    setNth level v 0
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
                   return LiftedTrue
             _ | conflictC >= nOfConflicts -> do
                   -- Reached bound on number of conflicts
                   (s `cancelUntil`) =<< get' rootLevel -- force a restart
                   claRescaleActivityAfterRestart s
                   incrementStat s NumOfRestart 1
                   return LiftedBottom
             _ -> do
               -- New variable decision:
               v <- select s -- many have heuristic for polarity here
               -- << #phasesaving
               oldVal <- getNth phases v
               unsafeAssume s $ var2lit v (0 < oldVal) -- cannot return @False@
               -- >> #phasesaving
               loop conflictC
  good <- get' ok
  if good then loop 0 else return LiftedFalse

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
            confl <- propagate s
            if confl /= NullClause
              then do
                  analyzeFinal s confl True
                  cancelUntil s 0
                  return False
              else return True
  good <- simplifyDB s
  x <- if good then foldrM injector True assumps else return False
  if not x
    then return False
    else do
        set' rootLevel =<< decisionLevel s
        -- SOLVE:
        nc <- fromIntegral <$> nClauses s
        let
          while :: Double -> Double -> IO Bool
          while nOfConflicts nOfLearnts = do
            status <- search s (floor nOfConflicts) (floor nOfLearnts)
            if status == LiftedBottom
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

-- | __Pre-condition:__ propagation queue is empty.
{-# INLINE unsafeAssume #-}
unsafeAssume :: Solver -> Lit -> IO ()
unsafeAssume s@Solver{..} p = do
  pushTo trailLim =<< get' trail
  unsafeEnqueue s p NullClause
