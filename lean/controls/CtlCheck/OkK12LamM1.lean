import Saw38aCore
import CtlData.D_ok_k12

/-- Control OkK12LamM1: (e) ok_k12, num - 1. -/
theorem Ctl.Check.OkK12LamM1 : Saw38aCore.checkRange #[Ctl.Data.ok_k12] 2924 2924 9538444858171517 3540745356779801 0 2924 = false := by
  native_decide
