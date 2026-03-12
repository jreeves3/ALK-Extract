#!/bin/bash 

touch grid.log hier.log
for f in selected-benchmarks/*; do 
  echo "Running extraction on $f" >> grid.log

  sh scripts/KNF_extract.sh $f grid tmp >> grid.log

  echo "Running extraction on $f" >> hier.log
  sh scripts/KNF_extract.sh $f hier tmp >> hier.log
done