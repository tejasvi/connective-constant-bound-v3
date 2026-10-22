import Saw38aCore
import CtlData.D_mut_k14_mut_M2_redirect

/-- Control MutK14M2: (b) ok_k14, children redirected. -/
theorem Ctl.Check.MutK14M2 : Saw38aCore.checkRange #[Ctl.Data.mut_k14_mut_M2_redirect] 13650 13650 19286821624401396 7178537576273569 0 13650 = false := by
  native_decide
