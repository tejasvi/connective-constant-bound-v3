import Saw38aCore
import CtlData.D_mut_k12_mut_M3_lowv

/-- Control MutK12M3: (c) ok_k12, one weight halved. -/
theorem Ctl.Check.MutK12M3 : Saw38aCore.checkRange #[Ctl.Data.mut_k12_mut_M3_lowv] 2924 2924 9538444858171518 3540745356779801 0 2924 = false := by
  native_decide
