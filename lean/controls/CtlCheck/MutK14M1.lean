import Saw38aCore
import CtlData.D_mut_k14_mut_M1_dropchild

/-- Control MutK14M1: (a) ok_k14, first child removed. -/
theorem Ctl.Check.MutK14M1 : Saw38aCore.checkRange #[Ctl.Data.mut_k14_mut_M1_dropchild] 13650 13650 19286821624401396 7178537576273569 0 13650 = false := by
  native_decide
