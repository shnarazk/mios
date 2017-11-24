{-# LANGUAGE BangPatterns, FlexibleInstances, ViewPatterns, UndecidableInstances #-}
{-# LANGUAGE Safe #-}

-- | Boolean Expression module to build CNF from arbitrary expressions
-- Tseitin translation: http://en.wikipedia.org/wiki/Tseitin_transformation
module SAT.Mios.Util.BoolExp
       (
         -- * Class & Type
         BoolComponent (..)
       , BoolForm (..)
         -- * Expression contructors
       , (-|-)
       , (-&-)
       , (-=-)
       , (-!-)
       , (->-)
       , neg
         -- * List Operation
       , disjunctionOf
       , (-|||-)
       , conjunctionOf
       , (-&&&-)
         -- * Convert function
       , asList
       , asList_
       , asLatex
       , asLatex_
       , numberOfVariables
       , numberOfClauses
       , tseitinBase
       )
       where

import Data.List (foldl', intercalate)

-- | the start index for the generated variables by Tseitin encoding
tseitinBase :: Int
tseitinBase = 1600000

data L = L Int

-- | class of objects that can be interpeted as a bool expression
class BoolComponent a where
  toBF :: a -> BoolForm   -- lift to BoolForm

-- | CNF expression
data BoolForm = Cnf (Int, Int) [[Int]]
    deriving (Eq, Show)

instance BoolComponent Int where
  toBF a = Cnf (abs a, max tseitinBase (abs a)) [[a]]

instance BoolComponent L where
  toBF (L a) = Cnf (abs a, max tseitinBase (abs a)) [[a]]

instance BoolComponent [Char] where
  toBF (read -> a) = Cnf (abs a, max tseitinBase (abs a)) [[a]]

instance BoolComponent BoolForm where
  toBF = id

-- | returns the number of variables in the 'BoolForm'
numberOfVariables :: BoolForm -> Int
numberOfVariables (Cnf (a, b) _) = a + b - tseitinBase

-- | returns the number of clauses in the 'BoolForm'
numberOfClauses :: BoolForm -> Int
numberOfClauses (Cnf _ l) = length l

boolFormTrue :: BoolForm
boolFormTrue = Cnf (-1, 1) []

boolFormFalse :: BoolForm
boolFormFalse = Cnf (-1, -1) []

instance BoolComponent Bool where
  toBF True = boolFormTrue
  toBF False = boolFormFalse

isTrue :: BoolForm -> Bool
isTrue = (== boolFormTrue)

isFalse :: BoolForm -> Bool
isFalse = (== boolFormFalse)

-- | return a 'clause' list only if it contains some real clause (not a literal)
clausesOf :: BoolForm -> [[Int]]
clausesOf cnf@(Cnf _ [[]]) = []
clausesOf cnf@(Cnf _ [[x]]) = []
clausesOf cnf@(Cnf _ l) = l

maxRank :: BoolForm -> Int
maxRank (Cnf (n, _) _) = n

-- | returns the number of valiable used as the output of this expression.
-- and returns itself it the expression is a literal.
-- Otherwise the number is a integer larger than 'tseitinBase'.
-- Therefore @1 + max tseitinBase the-returned-value@ is the next literal variable for future.
tseitinNumber :: BoolForm -> Int
tseitinNumber (Cnf (m, n) [[x]]) = x
tseitinNumber (Cnf (_, n) _) = n

renumber :: Int -> BoolForm -> (BoolForm, Int)
renumber base (Cnf (m, n) l)
  | l == [] = (Cnf (m, n) l, 0)
  | tseitinBase < base = (Cnf (m, n') l', n')
  | otherwise = (Cnf (n', tseitinBase) l', n')
  where
    l' = map (map f) l
    n' = maximum $ map maximum l'
    offset = base - tseitinBase - 1
    f x = if abs x < tseitinBase then x else signum x * (abs x + offset)

instance Ord BoolForm where
  compare (Cnf _ a) (Cnf _ b) = compare a b

-- | disjunction constructor
--
-- >>> asList $ "3" -|- "4"
-- [[3,4,-5],[-3,5],[-4,5]]
--
-- >>> asList (("3" -|- "4") -|- "-1")
-- [[3,4,-5],[-3,5],[-4,5],[5,-1,-6],[-5,6],[1,6]]
--
(-|-) :: (BoolComponent a, BoolComponent b) => a -> b -> BoolForm
(toBF -> e1) -|- (toBF -> e2')
  | isTrue e1 || isTrue e2' = boolFormTrue
  | isFalse e1 && isFalse e2' = boolFormFalse
  | isFalse e1 = e2'
  | isFalse e2' = e1
  | otherwise = Cnf (m, c) $ clausesOf e1 ++ clausesOf e2 ++ [[a, b, - c], [- a, c], [- b, c]]
  where
    a = tseitinNumber e1
    (e2, b) = renumber (1 + max tseitinBase a) e2'
    m = max (maxRank e1) (maxRank e2)
    c = 1 + max tseitinBase (max a b)

-- | conjunction constructor
--
-- >>> asList $ "3" -&- "-2"
-- [[-3,2,4],[3,-4],[-2,-4]]
--
-- >>> asList $ "3" -|- ("1" -&- "2")
-- [[-1,-2,4],[1,-4],[2,-4],[3,4,-5],[-3,5],[-4,5]]
--
(-&-) :: (BoolComponent a, BoolComponent b) => a -> b -> BoolForm
(toBF -> e1) -&- (toBF -> e2')
  | isTrue e1 && isTrue e2' = boolFormTrue
  | isFalse e1 || isFalse e2' = boolFormFalse
  | isTrue e1 = e2'
  | isTrue e2' = e1
  | otherwise = Cnf (m, c) $ clausesOf e1 ++ clausesOf e2 ++ [[- a, - b, c], [a, - c], [b, - c]]
  where
    a = tseitinNumber e1
    (e2, b) = renumber (1 + max tseitinBase a) e2'
    m = max (maxRank e1) (maxRank e2)
    c = 1 + max tseitinBase (max a b)

-- | negate a form
--
-- >>> asList $ neg ("1" -|- "2")
-- [[1,2,-3],[-1,3],[-2,3],[-3,-4],[3,4]]
neg :: (BoolComponent a) => a -> BoolForm
neg (toBF -> e) =
  Cnf (m, c) $ clausesOf e ++ [[- a, - c], [a, c]]
  where
    a = tseitinNumber e
    m = maxRank e
    c = 1 + max tseitinBase a

-- | equal on BoolForm
(-=-) :: (BoolComponent a, BoolComponent b) => a -> b -> BoolForm
(toBF -> e1) -=- (toBF -> e2) = (e1 -&- e2) -|- (neg e1 -&- neg e2)

-- | negation on BoolForm
(-!-) :: (BoolComponent a, BoolComponent b) => a -> b -> BoolForm
(toBF -> e1) -!- (toBF -> e2) = (neg e1 -&- e2) -|- (e1 -&- neg e2)

-- | implication as a short cut
--
-- >>> asList ("1" ->- "2")
-- [[-1,-3],[1,3],[3,2,-4],[-3,4],[-2,4]]
(->-) :: (BoolComponent a, BoolComponent b) => a -> b -> BoolForm
(toBF -> a) ->- (toBF -> b) = (neg a) -|- b

-- | merge [BoolForm] by '(-|-)'
disjunctionOf :: [BoolForm] -> BoolForm
disjunctionOf [] = boolFormFalse
disjunctionOf (x:l) = foldl' (-|-) x l

-- | an alias of 'disjunctionOf'
(-|||-) :: [BoolForm] -> BoolForm
(-|||-) = disjunctionOf

-- | merge [BoolForm] by '(-&-)'
conjunctionOf :: [BoolForm] -> BoolForm
conjunctionOf [] = boolFormTrue
conjunctionOf (x:l) = foldl' (-&-) x l

-- | an alias of 'conjunctionOf'
(-&&&-) :: [BoolForm] -> BoolForm
(-&&&-) = conjunctionOf

-- | converts a BoolForm to "[[Int]]"
asList_ :: BoolForm -> [[Int]]
asList_ cnf@(Cnf (m,_) _)
  | isTrue cnf = []
  | isFalse cnf = [[]]
  | otherwise = l'
  where
    (Cnf _ l', _) = renumber (m + 1) cnf

-- | converts a *satisfied* BoolForm to "[[Int]]"
asList :: BoolForm -> [[Int]]
asList cnf@(Cnf (m,n) l)
  | isTrue cnf = []
  | isFalse cnf = [[]]
  | n <= tseitinBase = l
  | otherwise = [m'] : l'
  where
    (Cnf (m', _) l', _) = renumber (m + 1) cnf

-- | make latex string from CNF, using 'asList_'
--
-- >>> asLatex $ "3" -|- "4"
-- "\\begin{displaymath}\n( x_{3} \\vee x_{4} )\n\\end{displaymath}\n"
--
asLatex_ :: BoolForm -> String
asLatex_ b = beg ++ s ++ end
  where
    beg = "\\begin{displaymath}\n"
    end = "\n\\end{displaymath}\n"
    s = intercalate " \\wedge " [ makeClause c | c <- asList_ b]
    makeClause c = "(" ++ intercalate "\\vee" [makeLiteral l | l <- c] ++ ")"
    makeLiteral l
      | 0 < l = " x_{" ++ show l ++ "} "
      | otherwise = " \\neg " ++ "x_{" ++ show (negate l) ++ "} "

-- | make latex string from CNF, using 'asList'
asLatex :: BoolForm -> String
asLatex b = beg ++ s ++ end
  where
    beg = "\\begin{displaymath}\n"
    end = "\n\\end{displaymath}\n"
    s = intercalate " \\wedge " [ makeClause c | c <- asList b]
    makeClause c = "(" ++ intercalate "\\vee" [makeLiteral l | l <- c] ++ ")"
    makeLiteral l
      | 0 < l = " x_{" ++ show l ++ "} "
      | otherwise = " \\neg " ++ "x_{" ++ show (negate l) ++ "} "
