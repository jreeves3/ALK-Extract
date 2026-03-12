# CNF to KNF Extraction

## Build

```bash
sh build.sh
```

Binaries are placed in `scripts/bins/`.

Several scripts require the python-sat module (https://pysathq.github.io/installation/)
 
To clean:

```bash
sh clean.sh
```

---

## General Usage

```bash
./scripts/bins/cnf2knf <options> <form.cnf>
```

Default extraction uses ALK extraction with the **grid expansion** strategy, the random-testing prefilter, and SAT-based verification.

| Option | Description |
|---|---|
| `--grid=true` | Use hierarchical strategy |
| `-verification_type 0` | Random-testing prefilter |
| `-verification_type 1` | SAT-based verification |
| `-verification_type 2` | BDD-based verification |
| `-verification_type 3` *(default)* | Random-testing prefilter + SAT-based verification |
| `-Write_KNF <output.knf>` | write extracted KNF formula |

---

## Selected Benchmarks

A selection of benchmarks from the SAT Competition Anniversary Track are included in the selected-benchmarks directory. 

Expected results:

| Benchmark     | Grid cons | Hier cons | Orig sole time (s) | Reencoded solve time (s) |
| baseball      | 15        | 13        | 67    | 4 |
| edit_distance | 0         | 1         | 111   | >5000 |
| ktf           | 0         | 4         | >5000 | >5000 |
| timetable     | 752       | 753       | 81    | 67 *(using optimized sequential counter)* |


## Scripts

Temporary files will be placed in the folder 'tmp'. Scripts should be run from the main directory. 

**Extract KNF** — runs pure literal elimination and extraction (grid or hier) with random-testing and SAT-based verification, storing the result in `<output_directory>`:

```bash
sh scripts/KNF_extract.sh <input.cnf> <grid|hier> <output_directory>
```

**Scaling verification test** — checks random-testing or verification runtime for a given configuration:

```bash
sh scripts/scaling_verification_test.sh <size> <bound> <encoding_type> <verification_type>
```

| Parameter | Values |
|---|---|
| `encoding_type` | `seqcounter`, `totalizer`, `kmtotalizer`, `cardnetwrk` |
| `verification_type` | `0` random-testing, `1` SAT, `2` BDD, `3` random-testing + SAT |

Example — SAT-based verification for the `kmtotalizer` encoding with 100 data literals and bound 25:

```bash
sh scripts/scaling_verification_test.sh 100 25 kmtotalizer 2
```

**KNF solving** — solve an extracted KNF constraint:

```bash
sh scripts/KNF_solve.sh <input.knf> <encoder>
```
| Parameter | Values |
|---|---|
| `encoder` | `optimized-seqCnt`, `proximity-kmtotalizer` |


**Compare with CaDiCaL** — run CaDiCaL on the original CNF formula:

```bash
./scripts/bins/cadical <input.cnf>
```

---

## Data

Show tables:

```bash
python3 scripts/get_data.py -t <solve|extract>
```

Show plots:

```bash
python3 scripts/get_data.py -p -t <solve|scale>
```

The files marked 'sizes' show the list ```[(<size>,<bound>):<count>]``` for each formula with recovered constraints. For example (90,85):158 means the tool recovered 158 constraints each with 90 data literals and a bound of 85. 