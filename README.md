# mios -- Minisat-based Implementation and Optimization Study
----

`mios` is yet another minisat-based SAT solver implementation in Haskell, as a part of my research
project: 'Study on SAT solver Algorithms in Haskell.'

#### > Features

* fundamentally this is a *line-to-line* translation of [MiniSat 1.14](http://minisat.se/downloads/MiniSat_v1.14.2006-Aug-29.src.zip)
(And,  in the early stage of development, it was based on  N. Een and N. Sorensson, *“An extensible SAT-solver [extended version 1.2],”* in 6th Int. Conf. on Theory and Applications of Satisfiability Testing (SAT2003), 2003, pp. 502–518.)
* runs in `IO` monad, uses `Data.Vector` and *pointer-based equality* by `reallyUnsafePtrEquality`
* faster (compared with SAT solvers written in Haskell); see below.

##### benchmark results

* On a subset of SAT-RACE 2015 Application Problems

[under construction]

* Performances on [various 3SAT problems (uf-* series)](http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)

![](https://docs.google.com/spreadsheets/d/1cNltZ4FIu_exSUQMcXe53w4fADr3sOUxpo3L7oM0H_Q/pubchart?oid=297581252&format=image)

#### > Release Note

##### 1.1.0

* Based on [MiniSat 1.14](https://github.com/shnarazk/minisat114/), but lacks the binary clause implementation so far.
* The arguments of `solveSAT`and `validateAssignment` were curried.
* Solver holds a literal set internally in the case of contradicition.

##### 1.0.3

* uses vector-based containers instead of pointer-based clause containers
* adds self checking option (`--validate`), which works only on satisfiable problems
* `stack install` installs `mios`. `stack install --flag mios:devel` installs `mios-1.0.3` for developers.

This is the last version based on *“An extensible SAT-solver [extended version 1.2].”*

##### 1.0.2

* fixs a bug on CNF reader at 1.0.1

##### 1.0.1 => canceled by a bug on CNF reader

* CNF reader was changed from a parser based on 'Parsec' to a simple *reader* based on `Data.ByteString.Char8.readInt`
* uses a true `sortOnActivity` implementation
* phase saving
* provides assignment validation mode (see below)

```
$ mios test/data/uf200-012.cnf | mios -: test/data/uf200-012.cnf      # `-:` is the option for validation.
It's a valid assignment.
$ echo "[1,2,-3,4,-5]" | mios -: test/data/uf200-012.cnf
It's an invalid assignment.
```

#### > Install

* ghc-7.10.2 or upper
* [Stack](http://www.haskellstack.org/) or `cabal-install`

```
stack init --resolver lts-5.5   # or upper
stack install
```

```
cabal install
```

#### > Usage

##### * As a standalone program

```
$ mios a.cnf
dumps an assignment :: [Int]

$ mios --help
mios 1.0.3
Usage: mios [OPTIONS] target.cnf
  -d 0.95   --variable-decay-rate=0.95  [solver] variable activity decay rate (0.0 - 1.0)
  -c 0.999  --clause-decay-rate=0.999   [solver] clause activity decay rate (0.0 - 1.0)
  -r 0      --random-decision-rate=0    [solver] random selection rate (0 - 1000)
            --validate                  [option] self-check the (satisfied) answer
  -v        --verbose                   [option] display misc information
  -X        --hide-solution             [option] hide the solution
  -:        --validate-assignment       [option] read an assignment from STDIN and validate it
  -h        --help                      [misc] display this help message
            --version                   [misc] display program ID
```

##### * In Haskell

```haskell
module Main where -- this is sample.hs in app/
import SAT.Solver.Mios (CNFDescription (..), solveSAT)

clauses = [[1, 2], [1, 3], [-1, -2], [1, -2, 3], [-3]]
desc = CNFDescription 3 5 Nothing    -- #vars, #clauses, Just pathname or Nothing

main = do
  asg <- solveSAT desc clauses    -- solveSAT :: Traversable m => CNFDescription -> m [Int] -> IO [Int]
  putStrLn $ if null asg then "unsatisfiable" else show asg
```

```
$ stack ghc app/sample.hs
$ app/sample
[1,-2,-3]
```
Of cource, you can use mios in ghci similarly.

```
$ stack ghci
...>
```