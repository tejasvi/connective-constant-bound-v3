import Saw38aCore
import CtlData.D_mut_k16_mut_M2_redirect

/-- Control MutK16M2: (b) ok_k16, children redirected. -/
theorem Ctl.Check.MutK16M2 : Saw38aCore.checkRange #[Ctl.Data.mut_k16_mut_M2_redirect] 67280 67280 5838240731654091 2177607514009156 0 67280 = false := by
  native_decide
