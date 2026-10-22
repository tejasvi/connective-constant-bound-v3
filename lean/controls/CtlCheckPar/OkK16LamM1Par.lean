import Saw38aCore
import CtlData.P_ok_k16_c00
import CtlData.P_ok_k16_c01
import CtlData.P_ok_k16_c02
import CtlData.P_ok_k16_c03
import CtlData.P_ok_k16_c04
import CtlData.P_ok_k16_c05
import CtlData.P_ok_k16_c06

/-- Control OkK16LamM1 with 7 chunks of 10000 states (Par). -/
theorem Ctl.CheckPar.OkK16LamM1Par :
    Saw38aCore.checkRangePar #[Ctl.DataPar.ok_k16_c00, Ctl.DataPar.ok_k16_c01, Ctl.DataPar.ok_k16_c02, Ctl.DataPar.ok_k16_c03, Ctl.DataPar.ok_k16_c04, Ctl.DataPar.ok_k16_c05, Ctl.DataPar.ok_k16_c06] 10000 67280 5838240731654090 2177607514009156 0 67280 16 = false := by
  native_decide
