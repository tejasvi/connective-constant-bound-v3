import Saw38aCore
import CtlData.D_ok_k16

/-- Control OkK16LamM1: (e) ok_k16, num - 1. -/
theorem Ctl.Check.OkK16LamM1 : Saw38aCore.checkRange #[Ctl.Data.ok_k16] 67280 67280 5838240731654090 2177607514009156 0 67280 = false := by
  native_decide
