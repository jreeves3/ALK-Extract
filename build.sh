#!/bin/bash

CORES=1
# if 1 argument is given, use it as the number of cores for parallel build
if [ $# -eq 1 ]; then
    CORES=$1
fi

# build cadical for pure literal elimination
(cd cadical-ple; ./configure && make -j$CORES)

# build the extractor 
(cd extractor; make -j$CORES)

# build cadical for solving 
(cd tools/cadical; sh configure && make -j$CORES)

# build knf2cnf for converting the input formula to CNF
(cd tools/encoders/knf2cnf; make knf2cnf -j$CORES)

(cd tools/encoders/pyencoder/proximity; g++ --std=c++11 main.cpp -o proximity)

# mv executables to scripst/bins
mkdir -p scripts/bins
mv cadical-ple/build/cadical scripts/bins/cadical-ple
mv extractor/cnf2knf scripts/bins/cnf2knf
mv tools/cadical/build/cadical scripts/bins/cadical
mv tools/encoders/knf2cnf/knf2cnf scripts/bins/knf2cnf
mv tools/encoders/pyencoder/proximity/proximity scripts/bins/proximity