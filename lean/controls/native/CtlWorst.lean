import Saw38aCore
import L38Data.All

/-! Native controls at the worst state 326522321 of the k28f certificate, where the first C++ checker
(checker/check_saw.cpp of the supplement) attains the largest ratio: the exact ratio passes, and num - 1 fails. -/

namespace L38.CtlWorst

/-- Positive: states 326521821 .. 326522820 (1000 states around the worst state) pass with the exact ratio. -/
theorem window_ok : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    5100683462145913 1917628724674902 326521821 326522821 = true := by native_decide

/-- Positive: the worst state alone passes with the exact ratio. -/
theorem worst_ok : Saw38aCore.checkState L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    5100683462145913 1917628724674902 326522321 = true := by native_decide

/-- Negative: the worst state fails with num - 1, so the ratio is attained exactly there. -/
theorem worst_num_minus_one : Saw38aCore.checkState L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    5100683462145912 1917628724674902 326522321 = false := by native_decide

end L38.CtlWorst
