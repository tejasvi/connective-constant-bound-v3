import Saw38aCore
import CtlData.D_gap_k14

/-- Control GapK14: (d) gap_k14, its own exact ratio. -/
theorem Ctl.Check.GapK14 : Saw38aCore.checkRange #[Ctl.Data.gap_k14] 13158 13158 7886375692179181 2935472799381404 0 13158 = false := by
  native_decide
