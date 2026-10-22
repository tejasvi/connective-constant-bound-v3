import Saw38aCore
import CtlData.D_mut_k14_mut_M3_lowv

/-- Control MutK14M3: (c) ok_k14, one weight halved. -/
theorem Ctl.Check.MutK14M3 : Saw38aCore.checkRange #[Ctl.Data.mut_k14_mut_M3_lowv] 13650 13650 19286821624401396 7178537576273569 0 13650 = false := by
  native_decide
