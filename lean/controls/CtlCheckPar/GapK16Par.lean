import Saw38aCore
import CtlData.P_gap_k16_c00
import CtlData.P_gap_k16_c01
import CtlData.P_gap_k16_c02
import CtlData.P_gap_k16_c03
import CtlData.P_gap_k16_c04
import CtlData.P_gap_k16_c05
import CtlData.P_gap_k16_c06

/-- Control GapK16 with 7 chunks of 10000 states (Par). -/
theorem Ctl.CheckPar.GapK16Par :
    Saw38aCore.checkRangePar #[Ctl.DataPar.gap_k16_c00, Ctl.DataPar.gap_k16_c01, Ctl.DataPar.gap_k16_c02, Ctl.DataPar.gap_k16_c03, Ctl.DataPar.gap_k16_c04, Ctl.DataPar.gap_k16_c05, Ctl.DataPar.gap_k16_c06] 10000 64854 14496392835318946 5407284821498573 0 64854 16 = false := by
  native_decide
