-- | Basic abstract data types used throughout the code.
{-# LANGUAGE
    TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Trustworthy #-}

module Main where
import Control.Monad
import Data.IORef
import Data.List (sortBy)
import SAT.Solver.Mios.Types

-- | Heap is an alias to 'FixedVecInt'
-- This implementation is identical wtih that in Minisat 1.14
-- But the zero-th element is used for holding the number of elements
data VarOrderHeap = VarOrderHeap
                {
                  heap     :: Vec -- index to var
                , idxs     :: Vec -- var's index
                }

left :: Int -> Int
left = (2 *)

right :: Int -> Int
right = (1 +) . (2 *)

parent :: Int -> Int
parent = (`div` 2)

-- isLargerThan :: Var -> Var -> IO Bool
-- isLargerThan x y = (>) <$> getNthDouble x activity <*> getNthDouble y activity

numElementsInHeap :: VarOrderHeap -> IO Int
numElementsInHeap (heap -> h) = getNthInt 0 h

inHeap :: VarOrderHeap -> Int -> IO Bool
inHeap (idxs -> at) n = (/= 0) <$> getNthInt n at

increase :: (Var -> Var -> IO Bool) -> VarOrderHeap -> Int -> IO ()
increase comp v n = do
  exists <- inHeap v n
  when exists $ percolateUp comp v n

percolateUp :: (Var -> Var -> IO Bool) -> VarOrderHeap -> Int -> IO ()
percolateUp isLargerThan (VarOrderHeap to at) start = do
  x <- getNthInt start to
  let
    loop i = do
      let pi = parent i
      if pi == 0
        then do
            -- putStrLn =<< dump (show x ++ " stored: ") to
            setNthInt i to x >> setNthInt x at i >> return () -- end
        else do
            p <- getNthInt pi to
            -- putStrLn $ show x ++ "'s parent is : " ++ show p ++ " @ " ++ show pi
            outOfOrder <- x `isLargerThan` p -- whether x has larger value
            if outOfOrder
              then setNthInt i to p >> setNthInt p at i >> loop pi -- loop
              else do
                  -- putStrLn =<< dump (show x ++ " stored: ") to
                  setNthInt i to x >> setNthInt x at i >> return () -- end
  loop start

percolateDown :: (Var -> Var -> IO Bool) -> VarOrderHeap -> Int -> IO ()
percolateDown isLargerThan h@(VarOrderHeap to at) start = do
  s <- getNthInt 0 to
  x <- getNthInt start to
  let
    loop i = do
      let li = left i
      if li <= s
        then do
            let ri = right i
            l <- getNthInt li to
            r <- getNthInt ri to
            s <- numElementsInHeap h
            (ci,child) <- if ri <= s
                          then do
                            ordered <- r `isLargerThan` l
                            return $ if ordered then (ri, r) else (li, l)
                          else return (li, l)
            outOfOrder <- child `isLargerThan` i -- whether child has larger value
            if outOfOrder
              then setNthInt i to child >> setNthInt child at i >> loop ci
              else setNthInt i to x >> setNthInt x at i >> return () -- end
        else setNthInt i to x >> setNthInt x at i >> return ()       -- end
  loop start

insert :: (Var -> Var -> IO Bool) -> VarOrderHeap -> Int -> IO ()
insert comp v@(VarOrderHeap to at) n = do
  s <- (1 +) <$> getNthInt 0 to
  setNthInt n at s
  setNthInt s to n
  setNthInt 0 to s
  -- putStrLn $ show n ++ " @ " ++ show s
  percolateUp comp v s

getMin :: (Var -> Var -> IO Bool) -> VarOrderHeap -> IO Int
getMin comp v@(VarOrderHeap to at) = do
  r <- getNthInt 1 to
  l <- flip getNthInt to =<< getNthInt 0 to -- the last element
  setNthInt 1 to l
  setNthInt l at 1
  setNthInt r at 0
  modifyNthInt 0 to $ subtract 1 -- pop
  s <- numElementsInHeap v
  when (1 < s) $ percolateDown comp v 1
  return r

makeVarOrder :: Int -> IO VarOrderHeap
makeVarOrder n = VarOrderHeap <$> newVecWith (n + 1) 0 <*> newVecWith (n + 1) 0

main :: IO ()
main = do
 let comp x y = return $ x >= y
 h <- makeVarOrder 20
 putStrLn "generate a heap"
 let l = [8, 3, 4,18, 13, 12, 17, 2, 1, 7, 11, 5, 9]
 forM_ l $ insert comp h
 putStrLn =<< dump "all stored: " (heap h)
 putStrLn =<< dump "all stored: " (idxs h)
 forM_ (sortBy (flip compare) l) $ \i -> print . (i, ) =<< getMin comp h
 return ()
