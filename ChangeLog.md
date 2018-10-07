## Release Note

##### 1.6.2

- Mios saves the assignment to a file automatically.
- A bug on a CNF file containing conflicting unit clauses was fixed.
- Restart heuristics was modified slightly (not evaluated well).

##### 1.6.1

- Use CPU clock time in benchmark mode correctly
- Introduce new algorithms:
  - ACIDS (average conflict-index decision score); *Armin Biere and Andreas Fröhlich, "Evaluating CDCL Variable Scoring Schemes", LCSN, vol.9340, pp.405-422, 2015.*
  - An EMA-based restart heuristics (not evaluated well; might be canceled in a future release)
  - A new clause scoring scheme
- The clause sorter doesn't allocate a temporal vector
- Set a maximum heap size as a terminating trigger (default: 7GB)

##### 1.6.0

- switch to hpack
- set a default memory limit in compile-time (fixed in 1.6.0.2)

##### 1.5.4

- 'sortClauses' didn't use clause activity correctly and now uses 2 * Int64 layout.

##### 1.5.3

- implement EMA based Glucose heuristics (Biere 2015) #62
- fix a bug on learnt clause reduction in a marginal situation
- thread-based timeout handling #58
- update command line options
- update the benchmark report format #64
- add a new type to represent a search result #64
- further adaptation to 64-bit CPU

##### 1.5.2

- add options for benchmark, using a timeout thread

##### 1.5.1

- fix a bug in simplifyDB
- revise VARUPDATEACTIVITY (#52)
- revise blockers (#53)
- refactor mios.cabal

##### 1.5.0

- **implement LBD**
- misc micro tuning
- add some utilities
- switch to SAT Competition 2017 main track for benchmark

##### 1.4.1

A maintenance release:

- use `ByteArray`; no performance boost.
- add a copy of a branch: MultiConflict.

##### 1.4.0

- new classes and methods

##### 1.3.0

- replace LBD heuristics with a simpler metrics, inspired by S. Jabbour et al.: “*Revisiting the Learned Clauses Database Reduction Strategies*,” 2013.
- change the module structure

##### 1.2.1

- tiny changes for uploading to [hackage](http://hackage.haskell.org/)
- add a CNF handling library under 'SAT.Util'

Note: Mios requires optimization flag `-O2`; it's crucial.

##### 1.2.0

- use *blocking literals*
- implement *literal block distance (LBD)* (not tested well)
- revise `reduceDB`
- use phase-saving
- remove random literal selection
- remove 'Criterion' from dependency list

##### 1.1.2

- fix a bug in DIMACS CNF parser; only single space between literals was accepted

This would be the last version based on [MiniSat 1.14](https://github.com/shnarazk/minisat114/).

##### 1.1.1

- tiny changes on the output format
- tiny changes on random variable decision rate
- update REDAME.md with a figure on a benchmark run sequentially; the old ones were multi-threaded and got very inaccurate numbers.

##### 1.1.0

- Based on [MiniSat 1.14](https://github.com/shnarazk/minisat114/), but lacks the binary clause implementation so far.
- The arguments of `solveSAT`and `validateAssignment` were curried.
- `Solver` holds a literal set internally in the case of contradiction.
- literals are encoded  to positive integers
- no more queue; `propQ` was merged to `trail`
- added a simple pre-processor
- a new CNF DIMACS parser
- solutions can be saved to a file with `--output` option

##### 1.0.3

- uses vector-based containers instead of pointer-based clause containers
- adds self-checking option (`--validate`), which works only on satisfiable problems
- `stack install` installs `mios`. `stack install --flag mios:devel` installs `mios-1.0.3` for developers.

This is the last version based on *“An extensible SAT-solver [extended version 1.2].”*

##### 1.0.2

- fixes a bug on CNF reader at 1.0.1

##### 1.0.1 => canceled by a bug on CNF reader

- CNF reader was changed from a parser based on 'Parsec' to a simple *reader* based on `Data.ByteString.Char8.readInt`
- uses a true `sortOnActivity` implementation
- phase saving
- provides assignment validation mode (see below)

```
$ mios test/data/uf200-012.cnf | mios -: test/data/uf200-012.cnf      # `-:` is the option for validation.
It's a valid assignment.
$ echo "[1,2,-3,4,-5]" | mios -: test/data/uf200-012.cnf
It's an invalid assignment.
```
