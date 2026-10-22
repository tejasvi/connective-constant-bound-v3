import Saw38aCore
import CtlData.D_ok_k14

/-- Control OkK14: ok_k14, exact ratio. -/
theorem Ctl.Check.OkK14 : Saw38aCore.checkRange #[Ctl.Data.ok_k14] 13650 13650 19286821624401396 7178537576273569 0 13650 = true := by
  native_decide
