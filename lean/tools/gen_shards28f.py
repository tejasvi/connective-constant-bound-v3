#!/usr/bin/env python3
"""Write L38Shard/Defs.lean, the shard modules L38Shard/SNNN.lean (one native_decide each), L38Shard/Start.lean and
L38Shard/All.lean (shards_ok : ∀ k < M, shardP k) for the k28f certificate."""
import os, sys
root = sys.argv[1] if len(sys.argv) > 1 else "."
N, CS, NCH = 5792114594, 2164802, 2676
PER = 16                      # data chunks per shard
B = PER * CS                  # states per shard
M = -(-N // B)                # number of shards
NUM, DEN, TASKS = 5100683462145913, 1917628724674902, 4000
d = os.path.join(root, "L38Shard"); os.makedirs(d, exist_ok=True)
open(os.path.join(d, "Defs.lean"), "w").write(f"""import Saw38aCore
import L38Data.All

/-!
# Shards of the k28f check

Shard `k` checks the records `[k B, min N ((k + 1) B))` with `B = {B}` ({PER} data chunks), in {TASKS} tasks.
-/

namespace L38.Shard

/-- States per shard. -/
def B : Nat := {B}

/-- The number of shards. -/
def M : Nat := {M}

/-- Shard `k` passes the check (ratio at most {NUM} / {DEN}). -/
def shardP (k : Nat) : Prop :=
  Saw38aCore.checkRangePar L38.Data.chunks L38.Data.chunkStates L38.Data.numStates {NUM} {DEN}
    (k * {B}) (min L38.Data.numStates ((k + 1) * {B})) {TASKS} = true

end L38.Shard
""")
for k in range(M):
    open(os.path.join(d, f"S{k:03d}.lean"), "w").write(f"""import L38Shard.Defs

/-- Shard {k} of {M}. -/
theorem L38.Shard.shard{k:03d} : L38.Shard.shardP {k} := by
  unfold L38.Shard.shardP
  native_decide
""")
open(os.path.join(d, "Start.lean"), "w").write("""import Saw38aCore
import L38Data.All

/-- Record 0 is the start state of order 28 (15 cells, turn code 0). -/
theorem L38.Shard.start_ok :
    (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 0).n = 15 ∧
      (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 0).T = 0 := by
  native_decide
""")
L = ["import L38Shard.Start\n"] + [f"import L38Shard.S{k:03d}\n" for k in range(M)]
L.append("\nset_option maxRecDepth 100000\n\nnamespace L38.Shard\n\n")
L.append("/-- Every shard in the list passes. -/\ndef AllK : List Nat → Prop\n  | [] => True\n  | k :: ks => shardP k ∧ AllK ks\n\n")
L.append("theorem AllK.mem : ∀ {l : List Nat}, AllK l → ∀ k ∈ l, shardP k\n"
         "  | [], _, k, hk => by simp at hk\n"
         "  | b :: l, h, k, hk => by\n"
         "    simp only [List.mem_cons] at hk\n"
         "    rcases hk with rfl | hk\n"
         "    · exact h.1\n"
         "    · exact AllK.mem h.2 k hk\n\n")
L.append(f"theorem allK : AllK (List.range {M}) :=\n  ⟨" +
         ", ".join(f"shard{k:03d}" for k in range(M)) + ", trivial⟩\n\n")
L.append(f"theorem shards_ok : ∀ k < {M}, shardP k :=\n  fun k hk => AllK.mem allK k (List.mem_range.2 hk)\n\n")
L.append("end L38.Shard\n")
open(os.path.join(d, "All.lean"), "w").write("".join(L))
print("shards", M, "B", B, "last range", (M - 1) * B, min(N, M * B))
