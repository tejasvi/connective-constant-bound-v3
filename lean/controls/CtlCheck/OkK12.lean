import Saw38aCore
import CtlData.D_ok_k12

/-- Control OkK12: ok_k12, exact ratio. -/
theorem Ctl.Check.OkK12 : Saw38aCore.checkRange #[Ctl.Data.ok_k12] 2924 2924 9538444858171518 3540745356779801 0 2924 = true := by
  native_decide
