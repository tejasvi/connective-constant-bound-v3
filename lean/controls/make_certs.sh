#!/bin/bash
# make_certs.sh SAW_CPP INDEPENDENT_DIR: rebuild the control certificates (certs/) and the reference runs of the C++
# checker (logs/chk_*.out). SAW_CPP is the construction program (builder/saw.cpp of the supplement); INDEPENDENT_DIR
# holds check38a.cpp, mutate_cert.py, gaploop_guard_removed.patch and generated_SHA256SUMS (independent/ of the
# supplement). Needs g++ with OpenMP, patch and python3. Exit code 0 only if every certificate file has the sha256 in
# generated_SHA256SUMS (where listed) and every C++ run has the expected exit code (0 for the good certificates, 5 for
# the controls that must fail).
set -euo pipefail
cd "$(dirname "$0")"
SAW=$(readlink -f "$1"); IND=$(readlink -f "$2")
if env | grep -q '^SAW_'; then echo "unset the SAW_* environment variables first"; exit 1; fi
mkdir -p bin certs logs
cp "$SAW" bin/saw.cpp
cp "$SAW" bin/saw_gaploop.cpp
patch -s bin/saw_gaploop.cpp "$IND/gaploop_guard_removed.patch"
g++ -O2 -fopenmp -o bin/saw bin/saw.cpp
g++ -O2 -fopenmp -o bin/saw_gaploop bin/saw_gaploop.cpp
g++ -O2 -march=native -fopenmp -o bin/check38a "$IND/check38a.cpp"
bad=0
: > logs/chk_summary.txt
run() {   # run NAME EXPECTED_EXIT_CODE CMD...: stdout to logs/chk_NAME.out; exit code and time to logs/chk_summary.txt
  local name=$1 exp=$2 rc=0 t0 t1
  shift 2
  t0=$(date +%s%N)
  "$@" > "../logs/chk_$name.out" || rc=$?
  t1=$(date +%s%N)
  echo "$name exit=$rc expected=$exp time_ms=$(( (t1 - t0) / 1000000 ))" >> ../logs/chk_summary.txt
  if [ "$rc" != "$exp" ]; then echo "UNEXPECTED exit code $rc for $name"; bad=1; fi
}
cd certs
for K in 12 14 16; do
  ../bin/saw $K PBXbSTU72q ok_k$K 1 22 > "../logs/build_ok_k$K.out" 2> "../logs/build_ok_k$K.err"
  ../bin/saw_gaploop $K PBXbSTU72q gap_k$K 1 22 > "../logs/build_gap_k$K.out" 2> "../logs/build_gap_k$K.err"
  run ok_k$K 0 ../bin/check38a ok_k$K $K 1
  LAM=$(sed -n 's/.*max ratio LAM = \([0-9]*\) \/ \([0-9]*\) .*/\1\/\2/p' "../logs/chk_ok_k$K.out")
  ST=$(sed -n 's/.*first state attaining it: \([0-9]*\).*/\1/p' "../logs/chk_ok_k$K.out")
  NUM=${LAM%/*}; DEN=${LAM#*/}
  python3 -I "$IND/mutate_cert.py" ok_k$K mut_k$K "$ST" > /dev/null
  run ok_k${K}_claim 0 ../bin/check38a ok_k$K $K 1 "$LAM"
  run ok_k${K}_lamm1 5 ../bin/check38a ok_k$K $K 1 "$((NUM - 1))/$DEN"
  run mut_k${K}_M1_dropchild 5 ../bin/check38a mut_k$K/mut_M1_dropchild $K 1
  run mut_k${K}_M2_redirect 5 ../bin/check38a mut_k$K/mut_M2_redirect $K 1
  run mut_k${K}_M3_lowv 5 ../bin/check38a mut_k$K/mut_M3_lowv $K 1 "$LAM"
  run gap_k$K 5 ../bin/check38a gap_k$K $K 1
done
# sha256 of the certificate files against the supplement's list (mut/ there = mut_k16/ here; ok_k10 is not used)
while read -r h f; do
  case $f in ok_k10.*) continue ;; esac
  g=${f/#mut\//mut_k16/}
  if [ "$(sha256sum "$g" | cut -d' ' -f1)" = "$h" ]; then echo "MATCH $g"; else echo "DIFF $g"; bad=1; fi
done < "$IND/generated_SHA256SUMS" > ../logs/cert_sha_check.txt
grep -c MATCH ../logs/cert_sha_check.txt | sed 's/^/certificate files matching generated_SHA256SUMS: /'
cat ../logs/chk_summary.txt
exit $bad
