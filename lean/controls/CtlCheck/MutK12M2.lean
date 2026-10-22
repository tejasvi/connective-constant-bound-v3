import Saw38aCore
import CtlData.D_mut_k12_mut_M2_redirect

/-- Control MutK12M2: (b) ok_k12, children redirected. -/
theorem Ctl.Check.MutK12M2 : Saw38aCore.checkRange #[Ctl.Data.mut_k12_mut_M2_redirect] 2924 2924 9538444858171518 3540745356779801 0 2924 = false := by
  native_decide
