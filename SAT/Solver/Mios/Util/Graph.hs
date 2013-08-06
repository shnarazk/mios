{-# LANGUAGE
    TupleSections
  , ViewPatterns
  #-}
{-# LANGUAGE Safe #-}

-- | build a dot file of dependency graph from reason network
module SAT.Solver.Mios.Util.Graph
       (
         makeGraph
       )
       where
import Data.List

header :: String
header = "\n\
\digraph dependency_graph {\n\
\  rankdir =LR;\n\
\  size=\"8,5\";\n\
\"

trailer :: String
trailer = "\n\
\}\n\
\"

-- | returns a string to decorate terminal nodes
decisionVars :: [(Int, [Int])] -> String
decisionVars l = "  node [shape = doublecircle];" ++ intercalate " " (map show l') ++ ";\n" ++ "  node [shape = circle];\n"
  where
    l' = map fst . filter (null . snd) $ l

-- | makes the contents from /assign trail/ and /reasons/
makeGraph :: [Int] -> [(Int, [Int])] -> String
makeGraph trail depends = header ++ decisionVars l ++ toGraph l ++ trailer
  where
    l = deleteIsolated $ requiredAssigns trail depends
    toGraph :: [(Int, [Int])] -> String
    toGraph l = intercalate "\n" $ map f l
      where
        f (_, []) = ""
        f (from, tos) = intercalate "\n" . map (g from) $ nub tos
        g from to = "  " ++ show from ++ " -> " ++ show to ++ ";"

-- | collects data only on active (assigned) variables
requiredAssigns :: [Int] -> [(Int, [Int])] -> [(Int, [Int])]
requiredAssigns l deps = map (\i -> (i, pick i)) l
  where
    pick x = map negate . filter (x /=) . snd $ deps !! (abs x - 1)

-- | deletes isolated nodes
deleteIsolated :: [(Int, [Int])] -> [(Int, [Int])]
deleteIsolated l = filter (flip elem l' . fst) l
  where
    l' = nub $ concatMap snd l ++ map fst (filter (not . null . snd) l)
