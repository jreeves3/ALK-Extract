#!bin/bash

INFORM=$1
ENCODER=$2
CADICAL=scripts/bins/cadical
KNF2CNF=scripts/bins/knf2cnf
PYENCODER=tools/encoders/pyencoder/order_and_encode.py
PROXIMITY=scripts/bins/proximity

SOLVETIMEOUT=5000

INFORM_BASE=$(basename -- "$INFORM" .knf) 
TMP=tmp/$INFORM_BASE-solve

mkdir -p $TMP

echo "CCC encode "$INFORM_BASE" with "$ENCODER
if [ "$ENCODER" == "optimized-seqCnt" ]; then
  time ./$KNF2CNF $INFORM > $TMP/encoded.cnf
elif [ "$ENCODER" == "proximity-kmtotalizer" ]; then 
  time python3 $PYENCODER -d $PROXIMITY -v proximity -e kmtotalizer -k $INFORM -c $TMP/encoded.cnf
else 
  echo "Invalid encoder: $ENCODER. Must be 'optimized-seqCnt' or 'proximity-kmtotalizer'."
  exit 1
fi

echo "CCC Solve problem "$INFORM_BASE" with cadical"
time ./$CADICAL $TMP/encoded.cnf -t $SOLVETIMEOUT 

