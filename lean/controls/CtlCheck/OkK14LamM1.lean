import Saw38aCore
import CtlData.D_ok_k14

/-- Control OkK14LamM1: (e) ok_k14, num - 1. -/
theorem Ctl.Check.OkK14LamM1 : Saw38aCore.checkRange #[Ctl.Data.ok_k14] 13650 13650 19286821624401395 7178537576273569 0 13650 = false := by
  native_decide
