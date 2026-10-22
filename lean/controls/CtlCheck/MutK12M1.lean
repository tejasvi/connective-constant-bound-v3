import Saw38aCore
import CtlData.D_mut_k12_mut_M1_dropchild

/-- Control MutK12M1: (a) ok_k12, first child removed. -/
theorem Ctl.Check.MutK12M1 : Saw38aCore.checkRange #[Ctl.Data.mut_k12_mut_M1_dropchild] 2924 2924 9538444858171518 3540745356779801 0 2924 = false := by
  native_decide
