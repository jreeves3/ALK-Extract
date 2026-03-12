#!bin/bash
CHILD_PID=""

killtree() {
  local _pid=$1
  local _sig=${2:-TERM}
  local _child
  for _child in $(pgrep -P "${_pid}" 2>/dev/null); do
    killtree "${_child}" "${_sig}"
  done
  kill -s "${_sig}" "${_pid}" 2>/dev/null
}

cleanup() {
  trap - INT TERM QUIT EXIT
  if [ -n "${CHILD_PID}" ]; then
    killtree "$CHILD_PID" TERM
    sleep 1
    killtree "$CHILD_PID" KILL
  fi
}

trap 'cleanup; exit 130' INT TERM QUIT
trap cleanup EXIT

INFORM=$1
INFORM_BASE=$(basename -- "$INFORM" .cnf)
OUTPUT_DIR=$3
GUESSING_TYPE=$2
ple=1
totalizer_arg="false"
write_knf=1
verification_type=3

if [ $GUESSING_TYPE == "grid" ]
then
  totalizer_arg="false"
elif [ $GUESSING_TYPE == "hier" ]
then
  totalizer_arg="true"
else 
  echo "Invalid guessing type: $GUESSING_TYPE. Must be 'grid' or 'hier'."
  exit 1
fi


CADICALPLE=scripts/bins/cadical-ple
Extractor=scripts/bins/cnf2knf

TIMEOUT=1000

OUTPUT_KNF=$OUTPUT_DIR/$INFORM_BASE.knf

# Directory for temporary files
TMP=tmp/$INFORM_BASE-extract
mkdir -p $TMP

cp $INFORM $TMP/input.cnf
INPUT_CNF=$TMP/input.cnf

# perform unit propagation with CaDiCaL
if [ $ple -gt 0 ]
then
  time ./$CADICALPLE $INPUT_CNF -o $TMP/input-ple.cnf -c 0 --ple > /dev/null
  INPUT_CNF=$TMP/input-ple.cnf
fi

write_knf_arg=$OUTPUT_KNF

timeout "${TIMEOUT}s" ./$Extractor -Write_KNF "$write_knf_arg" --grid="$totalizer_arg" -verification_type "$verification_type" "$INPUT_CNF" &
CHILD_PID=$!
wait "$CHILD_PID"
status=$?
CHILD_PID=""
exit "$status"
