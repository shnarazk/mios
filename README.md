# Mios -- Minisat-based Implementation and Optimization Study
----

`Mios` is yet another minisat-based SAT solver implementation in Haskell, as
a part of my research theme.

- [ChangeLog](ChangeLog.md)

### > Features

* fundamentally it is developed based on Minisat-1.14 and 2.2.0.
  * Firstly, version 1.0 was based on N. Een and N. Sorensson, *“An extensible SAT-solver [extended version 1.2],”* in 6th Int. Conf. on Theory and Applications of Satisfiability Testing (SAT2003), 2003, pp. 502–518.
  * Version 1.1 was a *line-to-line* translation of [MiniSat 1.14](http://minisat.se/downloads/MiniSat_v1.14.2006-Aug-29.src.zip).
  * Version 1.2 imported some idea used in Glucose 4.0.
  * Version 1.5 uses Literal Block Distance (LBD).
* runs in `IO` monad, uses `Data.Primitive.ByteArray` mainly and `reallyUnsafePtrEquality`.
* very fast, compared with other SAT solvers written in Haskell; see below.

#### benchmark results

- SAT-Competition 2017 Main track, running 3 jobs *in parallel* with a 510 second timeout on Intel Core i7-3930K @ 12x 3.8GHz
  (Therefore results near the threshold should be affected by other threads more or less.)

![Cactus plot with Mios-1.5.3: SAT Competition 2017 main](https://narazaki-lab.github.io/SAT/cactus-1.5.3.png)

- A subset of SAT-Race 2015 Application Problems (timeout: 1200 sec)

This is a result on a subset the problems of which MiniSat-2.2.0 can solve
in 1000 secs. It shows that *mios-1.2.0 is only about 2 times slower than MiniSat-2.2.0*.

![Cactus plot 2:SAT-RACE2015](https://cloud.githubusercontent.com/assets/997855/18457723/e9c6b91c-7995-11e6-8cc5-ecad36259fa7.png)

- Performances on [various 3SAT problems (uf-* series)](http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)

![](https://docs.google.com/spreadsheets/d/1cNltZ4FIu_exSUQMcXe53w4fADr3sOUxpo3L7oM0H_Q/pubchart?oid=297581252&format=image)

### > Install

##### Requirements

- ghc-8.0.1 or upper (By deleting `default-extensions` from mios.cabal, you can use ghc-7.10.x.)
- [Stack](http://www.haskellstack.org/) or `cabal-install`

##### Stack

```
git clone https://github.com/shnarazk/mios
stack init --resolver nightly-2017-XX-XX  # for ghc-8.2.X
stack install
```

##### Cabal

Mios is registered in [hackage](http://hackage.haskell.org/package/mios) now.

```
cabal install mios
```

### > Usage

##### * As a standalone program

```
$ mios a.cnf
an assignment :: [Int]

$ mios --help
mios-1.5.3 -- https://github.com/shnarazk/mios
Usage: mios [OPTIONS] target.cnf
  -d 0.95   --variable-decay-rate=0.95  [solver] variable activity decay rate (0.0 - 1.0)
  -c 0.999  --clause-decay-rate=0.999   [solver] clause activity decay rate (0.0 - 1.0)
            --maxsize=4000000           [solver] limit of the number of variables
  -:        --validate-assignment       [solver] read an assignment from STDIN and validate it
            --validate                  [solver] self-check (satisfiable) assignment
  -o file   --output=file               [option] filename to store result
  -v        --verbose                   [option] display misc information
  -X        --hide-solution             [option] hide solution
            --benchmark=-1/0/N          [devel] No/Exhaustive/N-second timeout benchmark
            --sequence=NUM              [devel] set 2nd field of a CSV generated by benchmark
            --dump=0                    [devel] dump level; 1:solved, 2:reduction, 3:restart
  -h        --help                      [misc] display this message
            --version                   [misc] display program ID
```

If you have GNU parallel, Mios works well with it:

```
parallel "mios --benchmark=0 --sequence={#} {}" ::: *.cnf
```

##### * In Haskell

```haskell
module Main where -- this is sample.hs in app/
import SAT.Mios (CNFDescription (..), solveSAT)

clauses = [[1, 2], [1, 3], [-1, -2], [1, -2, 3], [-3]] :: [[Int]]
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

Of course, you can use Mios in ghci similarly.

```
$ stack ghci
...>
```
