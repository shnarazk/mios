# mios -- Minisat-based Implementation and Optimization Study
----

**NOTE: This repository will be open in 2016 Jan. And any history before it will be erased (rebased).**

`mios` is yet another SAT solver implemetation as a part of my research project: ***Study on SAT solver Algorithms in Haskell***
and is another imitation of **MINISAT** in Haskell.

#### > Features

* based on
  * N. Een and N. Sorensson, *“An extensible SAT-solver,”* in 6th Int. Conf. on Theory and Applications of Satisfiability Testing (SAT2003), 2003, pp. 502–518.
  * [MiniSat 1.14](http://minisat.se/downloads/MiniSat_v1.14.2006-Aug-29.src.zip) for the detailed definition of clause activity and strategy to reduce learnt clauses.
* runs in `IO` monad, uses `Data.Vector` and *pointer-based equality* by `reallyUnsafePtrEquality`
* faster (compared with SAT solvers written in Haskell); see below.

##### benchmark
* [The first 100 problems of uf250-1065 satisfiable set](http://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf250-1065.tar.gz) on [SATLIB](http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)

![](https://docs.google.com/spreadsheets/d/1OYaOTZccjCFrItEb6zOUpXOS9Wbq7Qn22ooWnk95iW4/pubchart?oid=1845809024&format=image)

#### > Requirement

* ghc-7.10.2 or upper
* `cabal-install` or `stack`


```
cabal install
cabal install -f llvm
cabal install -f profile
```

```
stack init
stack install --flag mios:llvm
```

#### > Usage

```
mios a.cnf

mios --help
mios v0.8 #diveIntoCore
Usage: mios [OPTIONS] target.cnf
  -d 0.95  --variable-decay-rate=0.95  [Option] variable activity decay rate
  -c 0.99  --clause-decay-rate=0.99    [Option] clause activity decay rate
  -v       --verbose                   [Info] display misc information
  -X       --hide-answer               [Info] hide the solution
  -h       --help                      [misc] display this help message
           --version                   [misc] display program ID
           --stdin                     [Option] read from STDIN instead of a file
```
