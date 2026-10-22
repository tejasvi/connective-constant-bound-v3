import Saw38aCore
import CtlData.D_ok_k16

/-- Control OkK16: ok_k16, exact ratio. -/
theorem Ctl.Check.OkK16 : Saw38aCore.checkRange #[Ctl.Data.ok_k16] 67280 67280 5838240731654091 2177607514009156 0 67280 = true := by
  native_decide
