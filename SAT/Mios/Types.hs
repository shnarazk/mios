{-# LANGUAGE
    BangPatterns
  , PatternSynonyms
  , MultiParamTypeClasses
  #-}
{-# LANGUAGE Safe #-}

-- | Basic data types used throughout mios.
module SAT.Mios.Types
       (
         module SAT.Mios.Vec
         -- *  Variable
       , Var
       , bottomVar
       , int2var
         -- * Internal encoded Literal
       , Lit
       , lit2int
       , int2lit
       , bottomLit
--       , newLit
       , positiveLit
       , lit2var
       , var2lit
       , negateLit
         -- * Assignment on the lifted Bool domain
       , LiftedBool
       , lit2lbool
--       , lbool
       , Int (LiftedFalse, LiftedTrue, BottomBool, ConflictBool)
       , VarOrder (..)
         -- * CNF
       , CNFDescription (..)
         -- * Solver Configuration
       , MiosConfiguration (..)
       , defaultConfiguration
         -- * statistics
       , StatIndex (..)
         -- * dump statistics
       , DumpTag (..)
       , DumpedValue
       , MiosStats (..)
       , QuadLearntC (..)
       , MiosDump (..)
       )
       where

import Data.Bits
import SAT.Mios.Vec

-- | represents "Var". This can be used as index for accessing on Var-indexed Vectors.
type Var = Int

-- | Special constant in 'Var' (p.7)
bottomVar :: Var
bottomVar = 0

-- | converts a usual Int as literal to an internal 'Var' presentation.
--
-- >>> int2var 1
-- 1  -- the first literal is the first variable
-- >>> int2var 2
-- 2  -- literal @2@ is variable 2
-- >>> int2var (-2)
-- 2 -- literal @-2@ (note: its internal representation as 'Lit' is 5) is corresponding to variable 2
--
{-# INLINE int2var #-}
int2var :: Int -> Int
int2var = abs

-- | The literal data has an 'index' method which converts the literal to
-- a "small" integer suitable for array indexing. The 'var'  method returns
-- the underlying variable of the literal, and the 'sign' method if the literal
-- is signed (False for /x/ and True for /-x/).
type Lit = Int

-- | Special constant in 'Lit' (p.7)
bottomLit :: Lit
bottomLit = 0

{-
-- | converts "Var" into 'Lit'
newLit :: Var -> Lit
newLit = errorWithoutStackTrace "newLit undefined"
-}

-- | returns @True@ if the literal is positive
{-# INLINE positiveLit #-}
positiveLit :: Lit -> Bool
positiveLit = even

-- | negates literal
--
-- >>> negateLit 2
-- 3
-- >>> negateLit 3
-- 2
-- >>> negateLit 4
-- 5
-- >>> negateLit 5
-- 4
{-# INLINE negateLit #-}
negateLit :: Lit -> Lit
negateLit l = complementBit l 0 -- if even l then l + 1 else l - 1

----------------------------------------
----------------- Var
----------------------------------------

-- | converts 'Lit' into 'Var'.
--
-- >>> lit2var 2
-- 1
-- >>> lit2var 3
-- 1
-- >>> lit2var 4
-- 2
-- >>> lit2var 5
-- 2
{-# INLINE lit2var #-}
lit2var :: Lit -> Var
lit2var !n = shiftR n 1

-- | converts a 'Var' to the corresponing literal.
--
-- >>> var2lit 1 True
-- 2
-- >>> var2lit 1 False
-- 3
-- >>> var2lit 2 True
-- 4
-- >>> var2lit 2 False
-- 5
{-# INLINE var2lit #-}
var2lit :: Var -> Bool -> Lit
var2lit !v True = shiftL v 1
var2lit !v _ = shiftL v 1 + 1

----------------------------------------
----------------- Int
----------------------------------------

-- | converts 'Int' into 'Lit' as @lit2int . int2lit == id@.
--
-- >>> int2lit 1
-- 2
-- >>> int2lit (-1)
-- 3
-- >>> int2lit 2
-- 4
-- >>> int2lit (-2)
-- 5
--
{-# INLINE int2lit #-}
int2lit :: Int -> Lit
int2lit n
  | 0 < n = 2 * n
  | otherwise = -2 * n + 1

-- | converts `Lit' into 'Int' as @int2lit . lit2int == id@.
--
-- >>> lit2int 2
-- 1
-- >>> lit2int 3
-- -1
-- >>> lit2int 4
-- 2
-- >>> lit2int 5
-- -2
{-# INLINE lit2int #-}
lit2int :: Lit -> Int
lit2int l = case divMod l 2 of
  (i, 0) -> i
  (i, _) -> - i

{-
-- | Lifted Boolean domain (p.7) that extends 'Bool' with "⊥" means /undefined/
-- design note: _|_ should be null = 0; True literals are coded to even numbers. So it should be 2.
data LiftedBool = Bottom | LFalse | LTrue | LConflict
  deriving (Bounded, Eq, Ord, Read, Show)

instance Enum LiftedBool where
  {-# SPECIALIZE INLINE toEnum :: Int -> LiftedBool #-}
  toEnum        1 = LTrue
  toEnum     (-1) = LFalse
  toEnum        _ = Bottom
  {-# SPECIALIZE INLINE fromEnum :: LiftedBool -> Int #-}
  fromEnum Bottom = 0
  fromEnum LFalse = 1
  fromEnum LTrue  = 2

-- | converts 'Bool' into 'LBool'
{-# INLINE lbool #-}
lbool :: Bool -> LiftedBool
lbool True = LTrue
lbool False = LFalse
-}

type LiftedBool = Int

-- | /FALSE/ on the Lifted Bool domain
pattern LiftedFalse :: Int
pattern LiftedFalse = -1

-- | /TRUE/ on the Lifted Bool domain
pattern LiftedTrue :: Int
pattern LiftedTrue = 1

-- | /UNDEFINED/ on the Lifted Bool domain
pattern BottomBool :: Int
pattern BottomBool = 0

-- | /CONFLICT/ on the Lifted Bool domain
pattern ConflictBool :: Int
pattern ConflictBool = 2

{-# INLINE lit2lbool #-}
lit2lbool :: Lit -> LiftedBool
lit2lbool l = if positiveLit l then LiftedTrue else LiftedFalse

-- | Assisting ADT for the dynamic variable ordering of the solver.
-- The constructor takes references to the assignment vector and the activity
-- vector of the solver. The method 'select' will return the unassigned variable
-- with the highest activity.
class VarOrder o where
{-
  -- | constructor
  newVarOrder :: (VecFamily v1 Bool, VecFamily v2 Double) => v1 -> v2 -> IO o
  newVarOrder _ _ = errorWithoutStackTrace "newVarOrder undefined"

  -- | Called when a new variable is created.
  newVar :: o -> IO Var
  newVar = errorWithoutStackTrace "newVar undefined"
-}
  -- | should be called when a variable has increased in activity.
  update :: o -> Var -> IO ()
  update _  = errorWithoutStackTrace "update undefined"
{-
  -- | should be called when all variables have been assigned.
  updateAll :: o -> IO ()
  updateAll = errorWithoutStackTrace "updateAll undefined"
-}
  -- | should be called when a variable becomes unbound (may be selected again).
  undo :: o -> Var -> IO ()
  undo _ _  = errorWithoutStackTrace "undo undefined"

  -- | returns a new, unassigned var as the next decision.
  select :: o -> IO Var
  select    = errorWithoutStackTrace "select undefined"

-- | Misc information on a CNF
data CNFDescription = CNFDescription
  {
    _pathname :: Maybe FilePath          -- ^ given filename
  , _numberOfVariables :: !Int           -- ^ the number of variables
  , _numberOfClauses :: !Int             -- ^ the number of clauses
  }
  deriving (Eq, Ord, Read, Show)

-- | Solver's parameters; random decision rate was dropped.
data MiosConfiguration
  = MiosConfiguration
    {
      variableDecayRate :: !Double  -- ^ decay rate for variable activity
    --, clauseDecayRate :: !Double  -- ^ decay rate for clause activity
    , propagationLimit  :: !Int     -- ^ a resource limit
    , gpParameter1      :: !Double  -- ^ 1st param for greedy propagation
    , gpParameter2      :: !Double  -- ^ 2nd param for greedy propagytion
    , extraParameter3   :: !Int     -- ^ used in mcb experimentation
    , extraParameter4   :: !Int     -- ^ used in mcb experimentation
    }
  deriving (Eq, Ord, Read, Show)

-- | dafault configuration
--
-- * Minisat-1.14 uses @(0.95, 0.999, 0.2 = 20 / 1000)@.
-- * Minisat-2.20 uses @(0.95, 0.999, 0)@.
-- * Gulcose-4.0  uses @(0.8 , 0.999, 0)@.
-- * Mios-1.2     uses @(0.95, 0.999, 0)@.
--
defaultConfiguration :: MiosConfiguration
defaultConfiguration = MiosConfiguration
                         0.95   -- variableDecayRate
                         -- {- 0.999 -} {- 0 -}
                         0      -- propagationLimit
                         0 -- 6.0    -- gpParameter1
                         0 -- 0.35   -- gpParameter2
                         0 -- 1      -- extraParameter3
                         0      -- extraParameter4

-------------------------------------------------------------------------------- statistics

-- | stat index
data StatIndex =
    SatisfiabilityValue          -- ^ { -1 : unsatisfiable, 0 : process aborted, 1 : satisfiable }
  | NumOfBackjumps               -- ^ the number of backjumps
  | NumOfRestarts                -- ^ the number of restarts
  | NumOfPropagations            -- ^ the number of propagations
  | NumOfConflicts               -- ^ the number of conflicts solver found
  | NumOfLearnts                 -- ^ the number of generated learnt clauses
  | NumOfExtra
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

data DumpTag = TerminateS
             | PropagationS
             | ConflictS
             | LearntS
             | BackjumpS
             | RestartS
             | LearningRateS
             | ExtraS
             deriving (Bounded, Enum, Eq, Ord, Read, Show)

type DumpedValue = (DumpTag, Either Double Int)

newtype MiosStats = MiosStats [DumpedValue]
  deriving (Eq, Ord, Read, Show)

data QuadLearntC = QuadLearntC (Double, Double, Double) (Double, Double, Double) (Double, Double, Double) (Double, Double, Double)
  deriving (Eq, Ord, Read, Show)

data MiosDump =
  MiosDump { _dumpedConf ::  (String, MiosConfiguration)
           , _dupmedCNFDesc :: CNFDescription
           , _dumpedStat :: MiosStats
           , _dumpedLCat :: QuadLearntC        -- quad categorization of learnts
           }
  deriving (Eq, Ord, Read, Show)
