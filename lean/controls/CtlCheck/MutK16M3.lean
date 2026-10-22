import Saw38aCore
import CtlData.D_mut_k16_mut_M3_lowv

/-- Control MutK16M3: (c) ok_k16, one weight halved. -/
theorem Ctl.Check.MutK16M3 : Saw38aCore.checkRange #[Ctl.Data.mut_k16_mut_M3_lowv] 67280 67280 5838240731654091 2177607514009156 0 67280 = false := by
  native_decide
