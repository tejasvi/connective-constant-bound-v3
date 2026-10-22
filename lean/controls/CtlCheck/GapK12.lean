import Saw38aCore
import CtlData.D_gap_k12

/-- Control GapK12: (d) gap_k12, its own exact ratio. -/
theorem Ctl.Check.GapK12 : Saw38aCore.checkRange #[Ctl.Data.gap_k12] 2826 2826 18238581991091836 6770765732755619 0 2826 = false := by
  native_decide
