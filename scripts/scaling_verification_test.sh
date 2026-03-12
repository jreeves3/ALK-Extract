#!bin/bash

CADICALPLE=scripts/bins/cadical-ple
Extractor=scripts/bins/cnf2knf
PYENCODER=tools/encoders/pyencoder/order_and_encode.py

ple=1
size=$1
bound=$2
encoding=$3
verification_type=$4
timeout=1000

# size > 0 
# bound > 0 and < size
# encoding in {sequential-counter, totalizer, kmtotalizer, cardnetwrk}
# verification_type in {0, 1, 2, 3}
if [ $size -le 0 ]; then
    echo "Size must be greater than 0"
    exit 1
fi
if [ $bound -le 0 ] || [ $bound -ge $size ]; then
    echo "Bound must be greater than 0 and less than size"
    exit 1
fi
if [[ "$encoding" != "seqcounter" && "$encoding" != "totalizer" && "$encoding" != "kmtotalizer" && "$encoding" != "cardnetwrk" ]]; then
    echo "Encoding must be one of seqcounter, totalizer, kmtotalizer, cardnetwrk"
    exit 1 
fi
if [[ "$verification_type" != "0" && "$verification_type" != "1" && "$verification_type" != "2" && "$verification_type" != "3" ]]; then
    echo "Verification type must be one of 0, 1, 2, 3"
    exit 1
fi

TMP=tmp/scaling_${size}_${bound}_${encoding}_${verification_type}
mkdir -p $TMP


CNF_FILE=$TMP/encoded_${size}_${bound}_${encoding}.cnf
KNF_FILE=$TMP/${size}_${bound}_${encoding}.knf
CONSTRAINT_VARS_FILE=$TMP/card_${size}_${bound}_${encoding}_${verification_type}_constraint_vars.txt

# Generate KNF file with header and clauses
{
    echo "p knf $size 2"
    # Clause 1: all positive literals
    for ((i=1; i<=size; i++)); do
        printf "%s " "$i"
    done
    printf "0\n"
    # Clause 2: 'k' (bound) and all negative literals
    printf "k %s " "$bound"
    for ((i=1; i<=size; i++)); do
        printf "%s " "-$i"
    done
    printf "0\n"
} > "$KNF_FILE"

{
    echo "d "
    # Clause 1: all positive literals
    for ((i=1; i<=size; i++)); do
        printf "%s " "$i"
    done
} > "$CONSTRAINT_VARS_FILE"

python3 $PYENCODER  -k $KNF_FILE -e $encoding -v natural -c $CNF_FILE

# perform unit propagation with CaDiCaL
if [ $ple -gt 0 ]
then
  time ./$CADICALPLE $CNF_FILE -o $TMP/ple.cnf -c 0 --ple > /dev/null
  mv $TMP/ple.cnf $CNF_FILE
fi

# perform extraction
total_arg="false"
# if encoding in totalizer, kmtotalizer, or cardnetwrk
if [[ "$encoding" == "totalizer"  || "$encoding" == "kmtotalizer" || "$encoding" == "cardnetwrk" ]]; then
    total_arg="true"
fi


time timeout $timeout's' ./$Extractor --grid=$total_arg -verification_type $verification_type -ver_only_file $CONSTRAINT_VARS_FILE $CNF_FILE > $TMP/out.log

FOUND=$(grep "c k" "$TMP/out.log")
# check that the consrtaint without leading 'c ' appears in the KNF file
FOUND_KNF=$(grep "^k " "$KNF_FILE")

# Compare by removing 'c' and 'k', then sorting integers
FOUND_SORTED=$(echo "$FOUND" | tr -d 'ck' | tr -s ' ' '\n' | sort -n | tr '\n' ' ' | xargs)
FOUND_KNF_SORTED=$(echo "$FOUND_KNF" | tr -d 'ck' | tr -s ' ' '\n' | sort -n | tr '\n' ' ' | xargs)

# echo "Found in log: $FOUND_SORTED"
# echo "Found in KNF: $FOUND_KNF_SORTED"

EQUAL=$([[ "$FOUND_SORTED" == "$FOUND_KNF_SORTED" ]] && echo "true" || echo "false")

VTIME=$(grep "c Verification time" "$TMP/out.log" | awk '{print $4}')

NCONFLICTS=$(grep "c conflicts:" "$TMP/out.log" | awk '{print $3}')

tail -n 30 "$TMP/out.log" 
# if grep above is successful, then run the extraction script
if [ "$EQUAL" = "true" ]; then
    echo "v SUCCESS"
    grep "^c k " "$TMP/out.log"
else
    echo "v FAILURE"
fi

# if nconflicts is empty, set to 0
if [ -z "$NCONFLICTS" ]; then
    NCONFLICTS=0
fi

echo "Success,Runtime,Size,Bound,Encoding,VerificationType,SATConflicts"
echo "CSV $EQUAL,$VTIME,$size,$bound,$encoding,$verification_type,$NCONFLICTS"
