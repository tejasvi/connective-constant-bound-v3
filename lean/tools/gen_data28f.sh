#!/bin/bash
# gen_data28f.sh [PREFIX]: check the sha256 of PREFIX.{keys,chosen,v} (the certificate of order 28, file prefix k28f; default
# PREFIX ~/l38/cert/k28f), convert it into 2676 chunk files data/cNNNN.s7 (31 chars per state) and write
# L38Data/ChunkNNNN.lean, L38Data/All.lean and the root L38Data.lean.
set -euo pipefail
cd "$(dirname "$0")/.."
P=${1:-$HOME/l38/cert/k28f}; B=2164802; NCH=2676; N=5792114594
sha256sum -c - <<SUMS
b73d1cccf9790daf2560025d804661976c27e81dea99b9444cf8fc362522309c  $P.keys
64c49e61c481539fd658b66b788052634863f3f2e15d6f5e56ee31934caeda3e  $P.chosen
e0142296de5bce853d3c4e80d1189e7647647b74462dcdd397fd2a305cdbfb94  $P.v
SUMS
mkdir -p data L38Data pins
seq 0 $((NCH - 1)) | xargs -P 200 -I{} bash -c 'i={}; f=$(printf "%04d" $i); python3 -I tools/mkchunk28f.py '"$P"' $((i * '"$B"')) '"$B"' data/c$f.s7 > pins/$f.txt'
for i in $(seq 0 $((NCH - 1))); do
  f=$(printf "%04d" $i); read -r len h < pins/$f.txt
  printf 'import L38Loader\n\n/-! Chunk %d of the k28f certificate (%s characters, 31 per state). -/\n\nload_cert_chunk L38.Data.chunk%s "data/c%s.s7" %s\n' $i $len $f $f $h > L38Data/Chunk$f.lean
done
{
  for i in $(seq 0 $((NCH - 1))); do printf 'import L38Data.Chunk%04d\n' $i; done
  printf '\nset_option maxRecDepth 100000\n\nnamespace L38.Data\n\n/-- States per chunk. -/\ndef chunkStates : Nat := %d\n\n/-- The number of states. -/\ndef numStates : Nat := %d\n\n/-- The chunks of the k28f certificate, in order. -/\ndef chunks : Array String := #[\n' $B $N
  for i in $(seq 0 $((NCH - 1))); do sep=","; [ $i -eq $((NCH - 1)) ] && sep=""; printf '  chunk%04d%s\n' $i "$sep"; done
  printf ']\n\nend L38.Data\n'
} > L38Data/All.lean
printf 'import L38Data.All\n' > L38Data.lean
cat pins/*.txt | awk '{s += $1} END {print "chars", s}'
