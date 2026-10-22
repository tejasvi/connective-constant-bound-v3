import Saw38aCore
import CtlData.D_mut_k16_mut_M1_dropchild

/-- Control MutK16M1: (a) ok_k16, first child removed. -/
theorem Ctl.Check.MutK16M1 : Saw38aCore.checkRange #[Ctl.Data.mut_k16_mut_M1_dropchild] 67280 67280 5838240731654091 2177607514009156 0 67280 = false := by
  native_decide
