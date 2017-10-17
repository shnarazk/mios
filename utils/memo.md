# my benchmark flow

1. store a lot of CNF files in a dir: bench
1  make sat-benchmark
1. build SAT solvers: minisat, mios1, mios2 and so on
1. run `sat-benchmark -t bench/* --timeout=200 minisat > r1.csv`
1. run `sat-benchmark -t bench/* --timeout=200 mios1 > r2.csv`
1. run ...
1. make a list file with: `ls -1 *.csv > runs`
1. make a cactus with: `./mkCactus runs`
