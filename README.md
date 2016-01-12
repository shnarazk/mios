# mios -- Minisat-based Implementation and Optimization Study
----

`mios` is yet another minisat-based SAT solver implementation in Haskell, as a part of my research
project: 'Study on SAT solver Algorithms in Haskell.'

#### > Features

* based on
  * N. Een and N. Sorensson, *“An extensible SAT-solver [extended version 1.2],”* in 6th Int. Conf. on Theory and Applications of Satisfiability Testing (SAT2003), 2003, pp. 502–518.
  * [MiniSat 1.14](http://minisat.se/downloads/MiniSat_v1.14.2006-Aug-29.src.zip) for the detailed definition of clause activity and strategy to reduce learnt clauses.
* runs in `IO` monad, uses `Data.Vector` and *pointer-based equality* by `reallyUnsafePtrEquality`
* faster (compared with SAT solvers written in Haskell); see below.

##### benchmark results
* [The first 100 problems of uf250-1065 satisfiable set](http://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf250-1065.tar.gz) on [SATLIB](http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)

![](https://docs.google.com/spreadsheets/d/1OYaOTZccjCFrItEb6zOUpXOS9Wbq7Qn22ooWnk95iW4/pubchart?oid=1845809024&format=image)

* Performances on [various 3SAT problems (uf-* series)](http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)

![](https://docs.google.com/spreadsheets/d/1cNltZ4FIu_exSUQMcXe53w4fADr3sOUxpo3L7oM0H_Q/pubchart?oid=297581252&format=image)

#### > Install

* ghc-7.10.2 or upper
* [Stack](http://www.haskellstack.org/) or `cabal-install`

```
stack init --solver nightly
stack install --flag mios:llvm
```

```
cabal install
cabal install -f llvm
cabal install -f profile
```

#### > Usage

##### * As a command

```
$ mios a.cnf
dumps an assignment :: [Int]

$ mios --help
mios version 1.0.0, #hofo
Usage: mios [OPTIONS] target.cnf
  -d 0.95   --variable-decay-rate=0.95  [configuration] variable activity decay rate (0.0 - 1.0)
  -c 0.999  --clause-decay-rate=0.999   [configuration] clause activity decay rate (0.0 - 1.0)
  -r 20     --random-decision-rate=20   [configuration] rate of selecting a decsion variable randomly (0 - 1000)
            --stdin                     [option] read a CNF from STDIN instead of a file
  -v        --verbose                   [option] display misc information
  -X        --hide-solution             [option] hide the solution
  -h        --help                      [misc] display this help message
            --version                   [misc] display program ID
```

##### * In Haskell

```haskell
module Main where -- this is sample.hs in app/

import qualified Data.Vector.Unboxed as U -- used for representing clauses
import SAT.Solver.Mios (CNFDescription (..), solveSAT)

clauses = [[1, 2], [1, 3], [-1, -2], [1, -2, 3], [-3]] :: [Int]
desc = CNFDescription 3 5 Nothing    -- #vars, #clauses, Just pathname or Nothing

main = do
  -- the 0th element of a clause vector is the number of literals in it
  let clausesWithSize = map (\l -> length l : l) clauses
  asg <- solveSAT (desc, map U.fromList clausesWithSize)
  putStrLn $ if null asg then "unsatisfiable" else show asg
```

```
$ stack ghc app/sample.hs
$ app/sample
[1,-2,-3]
```
