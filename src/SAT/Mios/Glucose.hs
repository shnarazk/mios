-- | This is an implementaion of MiniSat 1.14 in Haskell
{-# LANGUAGE
    BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , MagicHash
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

module SAT.Mios.Glucose
       (
         lbdOf
       , setLBD
--       , updateLBD
--       , nextReduction
       )
        where

import SAT.Mios.Types
import SAT.Mios.Clause
import SAT.Mios.Solver

{-# INLINABLE lbdOf #-}
lbdOf :: Solver -> Stack -> IO Int
lbdOf Solver{..} vec = do
  k <- (\k -> if 1000000 < k then 1 else k + 1) <$> get' lbd'key
  set' lbd'key k                -- store the last used value
  nv <- getNth vec 0
  let loop :: Int -> Int -> IO Int
      loop ((<= nv) -> False) n = return n
      loop i n = do l <- getNth level . lit2var =<< getNth vec i
                    x <- getNth lbd'seen l
                    if x /= k
                      then setNth lbd'seen l k >> loop (i + 1) (n + 1)
                      else loop (i + 1) n
  loop 1 0

{-# INLINABLE lbdOf' #-}
lbdOf' :: Solver -> Stack -> IO Int
lbdOf' Solver{..} vec = do
  k <- (\k -> if 1000000 < k then 1 else k + 1) <$> get' lbd'key
  set' lbd'key k                -- store the last used value
  nv <- getNth vec 0
  let loop :: Int -> Int -> IO Int
      loop ((<= nv) -> False) n = putStrLn ("LBD = " ++ show n) >> return n
      loop i n = do l <- getNth vec i
                    let v = lit2var l
                    lv <- getNth level v
                    x <- getNth lbd'seen lv
                    r <- getNth reason v
                    v <- lit2var <$> getNth vec i
                    putStr $ (if r == NullClause then "" else "!") ++ show v ++ "@" ++ show lv ++ ", " 
                    if x /= k
                      then setNth lbd'seen lv k >> loop (i + 1) (n + 1)
                      else loop (i + 1) n
  loop 1 0

{-# INLINE setLBD #-}
setLBD :: Solver -> Clause -> IO ()
setLBD _ NullClause = error "LBD44"
setLBD s c = set' (rank c) =<< lbdOf' s (lits c)

-- | update the lbd field of /c/
{-# INLINE updateLBD #-}
updateLBD :: Solver -> Clause -> IO ()
updateLBD s NullClause = error "LBD71"
updateLBD s c@Clause{..} = do
  k <- get' c
--  o <- getInt lbd
  n <- lbdOf s lits
  case () of
    _ | n == 1 -> set' rank (k - 1)
    -- _ | n < o -> setInt lbd n
    _ -> return ()

-- | 0 based
-- >>> nextReduction 0
-- 20000
-- >>> nextReduction 1
-- 40000 + 200 = 20000 + 20000 + 200
-- >>> nextReduction 2
-- 6000 + 600 = 20000 + 20200 + 20000 + 400
-- >>> nextReduction 3
-- 80000 + 1200 = 20000 + 20200 + 20400 + 20000 + 600
--
nextReduction :: Int -> Int -> Int
-- nextReduction _ n = 30000 + 10000 * n
nextReduction b n = b {- * (n + 1) -} + 300 * n {- * (n + 1) -}
