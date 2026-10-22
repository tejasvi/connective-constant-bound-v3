import Saw38aCore
import L38Data.All

/-! Native controls at states above 2^32 (k28f). -/

namespace L38.Ctl32

/-- Positive: the 1000 states from index 2^32 pass the check. -/
theorem window_ok : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates L38.Data.numStates 5100683462145913 1917628724674902
    4294967296 4294968296 = true := by native_decide

/-- Positive: state 4294967297 has child index 5071223956 (> 2^32) in slot 0, as in the certificate file. -/
theorem child_ok : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 4294967297).c0 = 5071223956 := by native_decide

/-- Negative: the same child index read without its high bit would be 776256660; it is not. -/
theorem child_high_bit : decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 4294967297).c0 = 776256660) = false :=
  by native_decide

/-- Negative: with N = 2^32 the window fails (children above 2^32 are out of range). -/
theorem window_bound_fails : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates 4294967296 5100683462145913 1917628724674902
    4294967296 4294968296 = false := by native_decide

/-- Negative: with a misaligned record layout (chunk size + 1) the window fails. -/
theorem window_misaligned_fails : Saw38aCore.checkRange L38.Data.chunks (L38.Data.chunkStates + 1) L38.Data.numStates
    5100683462145913 1917628724674902 4294967296 4294968296 = false := by native_decide

end L38.Ctl32
