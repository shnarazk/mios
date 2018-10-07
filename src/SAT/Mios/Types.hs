-- | (This is a part of MIOS.)
-- Basic data types used throughout mios.
{-# LANGUAGE
    BangPatterns
  , PatternSynonyms
  #-}
{-# LANGUAGE Safe #-}

module SAT.Mios.Types
       (
         -- * Interface to caller
         SolverResult
       , Certificate (..)
       , SolverException (..)
       , CNFDescription (..)
         -- * Solver Configuration
       , MiosConfiguration (..)
       , defaultConfiguration
         -- * internal structure
       ,  module SAT.Mios.Vec
         -- *  Variable
       , Var
       , bottomVar
       , int2var
         -- * Internal encoded Literal
       , Lit
       , lit2int
       , int2lit
       , bottomLit
       , positiveLit
       , lit2var
       , var2lit
       , negateLit
         -- * Assignment on the lifted Bool domain
       , LiftedBool
       , lit2lbool
       , Int (LiftedF, LiftedT, LBottom, Conflict)
       -- a heap
       , VarOrder (..)
       -- Exponential Moving Average, EMA
       , EMA
       , newEMA
       , getEMA
       , updateEMA
         -- * statistics
       , StatIndex (..)
       , DumpMode (..)
{-
         -- * dump statistics
       , DumpTag (..)
       , DumpedValue
       , MiosStats (..)
       , QuadLearntC (..)
       , MiosDump (..)
-}
       )
       where

import Data.Bits
import SAT.Mios.Vec

-- | terminate and find an SAT/UNSAT answer
data Certificate
  = SAT [Int]
  | UNSAT [Int]                 -- FIXME: replace with DRAT
  deriving (Eq, Ord, Read, Show)

-- | abnormal termination flags
data SolverException
  = StateUNSAT                  -- 0
  | StateSAT                    -- 1
  | OutOfMemory                 -- 2
  | TimeOut                     -- 3
  | InternalInconsistent        -- 4
  | UndescribedError            -- 5
  deriving (Bounded, Enum, Eq, Ord, Show)

-- | the type that Mios returns
-- This captures the following three cases:
--  * solved with a satisfiable assigment,
--  * proved that it's an unsatisfiable problem, and
--  * aborted due to Mios specification or an internal error
type SolverResult = Either SolverException Certificate

-- | represents "Var".
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
-- 2 -- literal @-2@ is corresponding to variable 2
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
newLit = error "newLit undefined"
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

-- | Lifted Boolean domain (p.7) that extends 'Bool' with "⊥" means /undefined/
-- design note: _|_ should be null = 0; True literals are coded to even numbers. So it should be 2.
type LiftedBool = Int

-- | /FALSE/ on the Lifted Bool domain
pattern LiftedF :: Int
pattern LiftedF = -1

-- | /TRUE/ on the Lifted Bool domain
pattern LiftedT :: Int
pattern LiftedT = 1

-- | /UNDEFINED/ on the Lifted Bool domain
pattern LBottom :: Int
pattern LBottom = 0

-- | /CONFLICT/ on the Lifted Bool domain
pattern Conflict :: Int
pattern Conflict = 2

-- | returns the value of a literal as a 'LiftedBool'
{-# INLINE lit2lbool #-}
lit2lbool :: Lit -> LiftedBool
lit2lbool l = if positiveLit l then LiftedT else LiftedF

{-
-- | converts 'Bool' into 'LBool'
{-# INLINE lbool #-}
lbool :: Bool -> LiftedBool
lbool True = LTrue
lbool False = LFalse
-}

-- | Assisting ADT for the dynamic variable ordering of the solver.
-- The constructor takes references to the assignment vector and the activity
-- vector of the solver. The method 'select' will return the unassigned variable
-- with the highest activity.
class VarOrder o where
{-
  -- | constructor
  newVarOrder :: (VecFamily v1 Bool, VecFamily v2 Double) => v1 -> v2 -> IO o
  newVarOrder _ _ = error "newVarOrder undefined"

  -- | Called when a new variable is created.
  newVar :: o -> IO Var
  newVar = error "newVar undefined"
-}
  -- | should be called when a variable has increased in activity.
  updateVO :: o -> Var -> IO ()
  updateVO _  = error "update undefined"
{-
  -- | should be called when all variables have been assigned.
  updateAll :: o -> IO ()
  updateAll = error "updateAll undefined"
-}
  -- | should be called when a variable becomes unbound (may be selected again).
  undoVO :: o -> Var -> IO ()
  undoVO _ _  = error "undo undefined"

  -- | returns a new, unassigned var as the next decision.
  selectVO :: o -> IO Var
  selectVO    = error "select undefined"

-------------------------------------------------------------------------------- EMA

-- | Exponential Moving Average, EMA
type EMA = (Double', Maybe Double', Double)

-- | returns a new EMA from a flag (slow or fast) and a window size
{-# INLINE newEMA #-}
newEMA :: Bool -> Int -> IO EMA
newEMA True s = do v <- new' 0.0
                   c <- new' 0.0
                   return (v, Just c, 1 / fromIntegral s)
newEMA False s = do v <- new' 0.0; return (v, Nothing, 1 / fromIntegral s)

-- | returns an EMA value
{-# INLINE getEMA #-}
getEMA :: EMA -> IO Double
getEMA (ema, Just cal, _) = do x <- get' ema
                               c <- get' cal
                               return $ if c == 0 then 0 else x / c
getEMA (ema, Nothing, _)  = get' ema

-- | updates an EMA
{-# INLINE updateEMA #-}
updateEMA :: EMA -> Double -> IO Double
updateEMA (ema, Just cal, cof) x = do e <- ((cof * x) +) . ((1 - cof) *) <$> get' ema
                                      set' ema e
                                      c <- ((cof * 1) +) . ((1 - cof) *) <$> get' cal
                                      set' cal c
                                      return $ e / c
updateEMA (ema, Nothing, cof) x = do e <- ((cof * x) +) . ((1 - cof) *) <$> get' ema; set' ema e; return e

-------------------------------------------------------------------------------- CNF

-- | Misc information on a CNF
data CNFDescription = CNFDescription
  {
    _numberOfVariables :: !Int           -- ^ the number of variables
  , _numberOfClauses :: !Int             -- ^ the number of clauses
  , _pathname :: !FilePath               -- ^ given filename
  }
  deriving (Eq, Ord, Read, Show)

-- | Solver's parameters; random decision rate was dropped.
data MiosConfiguration = MiosConfiguration
                         {
                           variableDecayRate  :: !Double     -- ^ decay rate for variable activity
                         , clauseDecayRate    :: !Double     -- ^ decay rate for clause activity
                         , dumpSolverStatMode :: !Int        -- ^ dump stats data during solving
                         , emaCoeffs          :: !(Int, Int) -- ^ the coefficients for restarts
                         , restartExpansion   :: !Double     -- ^ restart expansion factor
                         , restartStep        :: !Double     -- ^ static Steps between restarts
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
defaultConfiguration = MiosConfiguration 0.95 0.999 0 (ef, es) 1.15 100
  where ef = (2 :: Int) ^ ( 5 :: Int)
        es = (2 :: Int) ^ (14 :: Int)

-------------------------------------------------------------------------------- Statistics

-- | stat index
data StatIndex =
    NumOfBackjump               -- ^ the number of backjump
  | NumOfRestart                -- ^ the number of restart
  | NumOfBlockRestart           -- ^ the number of blacking start
  | NumOfGeometricRestart       -- ^ the number of classic restart
  | NumOfPropagation            -- ^ the number of propagation
  | NumOfReduction              -- ^ the number of reduction
  | NumOfClause                 -- ^ the number of 'alive' given clauses
  | NumOfLearnt                 -- ^ the number of 'alive' learnt clauses
  | NumOfVariable               -- ^ the number of 'alive' variables
  | NumOfAssigned               -- ^ the number of assigned variables
  | EndOfStatIndex              -- ^ Don't use this dummy.
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | formats of state dump
data DumpMode = NoDump | DumpCSVHeader | DumpCSV | DumpJSON
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

data MiosDump =
  MiosDump { _dumpedConf ::  (String, MiosConfiguration)
           , _dupmedCNFDesc :: CNFDescription
           , _dumpedStat :: MiosStats
           }
  deriving (Eq, Ord, Read, Show)
