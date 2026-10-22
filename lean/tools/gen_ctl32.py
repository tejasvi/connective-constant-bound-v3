#!/usr/bin/env python3
"""gen_ctl32.py PREFIX OUT: native controls of the k28f checker at states above 2^32 (positive and negative):
a window of 1000 states from index 2^32 must pass; the decoded child index of a state above 2^32 must equal the
uint64 value in the certificate file (and must differ from that value minus 2^32); the same window must fail with
N = 2^32 (children above 2^32 out of range) and with a misaligned record layout (chunk size + 1)."""
import os, struct, sys
P, OUT = sys.argv[1], sys.argv[2]
N = os.path.getsize(P + ".keys") // 8
W = os.path.getsize(P + ".chosen") // (3 * N); assert W == 8
LO = 1 << 32
f = open(P + ".chosen", "rb")
pick = None
for i in range(LO, LO + 100000):
    f.seek(24 * i); c = struct.unpack("<3Q", f.read(24))
    for j in range(3):
        if c[j] != (1 << 64) - 1 and c[j] >= LO:
            pick = (i, j, c[j]); break
    if pick: break
assert pick, "no child above 2^32 found"
i, j, v = pick
fld = ["c0", "c1", "c2"][j]
NUM, DEN = 5100683462145913, 1917628724674902
open(OUT, "w").write(f"""import Saw38aCore
import L38Data.All

/-! Native controls at states above 2^32 (k28f). -/

namespace L38.Ctl32

/-- Positive: the 1000 states from index 2^32 pass the check. -/
theorem window_ok : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates L38.Data.numStates {NUM} {DEN}
    {LO} {LO + 1000} = true := by native_decide

/-- Positive: state {i} has child index {v} (> 2^32) in slot {j}, as in the certificate file. -/
theorem child_ok : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates {i}).{fld} = {v} := by native_decide

/-- Negative: the same child index read without its high bit would be {v - LO}; it is not. -/
theorem child_high_bit : decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates {i}).{fld} = {v - LO}) = false :=
  by native_decide

/-- Negative: with N = 2^32 the window fails (children above 2^32 are out of range). -/
theorem window_bound_fails : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates {LO} {NUM} {DEN}
    {LO} {LO + 1000} = false := by native_decide

/-- Negative: with a misaligned record layout (chunk size + 1) the window fails. -/
theorem window_misaligned_fails : Saw38aCore.checkRange L38.Data.chunks (L38.Data.chunkStates + 1) L38.Data.numStates
    {NUM} {DEN} {LO} {LO + 1000} = false := by native_decide

end L38.Ctl32
""")
print("state", i, "slot", j, "child", v)
