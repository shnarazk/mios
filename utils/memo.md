# My benchmark flow

1. store a lot of CNF files in a dir: bench
1. build SAT solvers: minisat, mios1, mios2 and so on
1. install GNU parallel, R with ggplot2; make sat-benchmark
1. run `sat-benchmark -t bench/* --timeout=200 minisat > r1.csv`
1. run `sat-benchmark -t bench/* --timeout=200 mios1 > r2.csv`
1. run ... (alternatively run `sat-benchmark ... solver1 solver2 solver3 ... > all.csv`)
1. make a file containing a list of filenames with: `ls -1 *.csv > runs`
1. make a cactus with: `mkCactus.R runs`

# A consistency check (only on SAT problems)

Check assignments which mios returns.

1. install GNU parallel
1. change to a directory that contains CNF files
1. run `parallel "mios {} | mios -: -X {}" ::: *.cnf`
1. No parallel? Then run `for f in *.cnf ; do mios $f | mios -: -X $f; done`

Note: Mios with option `-:` checks the assignment without using main module.
I supposed there's no programming error.
