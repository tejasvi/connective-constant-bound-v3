import Saw38aCore
import CtlData.D_gap_k16

/-- Control GapK16: (d) gap_k16, its own exact ratio. -/
theorem Ctl.Check.GapK16 : Saw38aCore.checkRange #[Ctl.Data.gap_k16] 64854 64854 14496392835318946 5407284821498573 0 64854 = false := by
  native_decide
