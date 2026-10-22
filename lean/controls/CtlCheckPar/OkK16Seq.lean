import Saw38aCore
import CtlData.P_ok_k16_c00
import CtlData.P_ok_k16_c01
import CtlData.P_ok_k16_c02
import CtlData.P_ok_k16_c03
import CtlData.P_ok_k16_c04
import CtlData.P_ok_k16_c05
import CtlData.P_ok_k16_c06

/-- Control OkK16 with 7 chunks of 10000 states (Seq). -/
theorem Ctl.CheckPar.OkK16Seq :
    Saw38aCore.checkRange #[Ctl.DataPar.ok_k16_c00, Ctl.DataPar.ok_k16_c01, Ctl.DataPar.ok_k16_c02, Ctl.DataPar.ok_k16_c03, Ctl.DataPar.ok_k16_c04, Ctl.DataPar.ok_k16_c05, Ctl.DataPar.ok_k16_c06] 10000 67280 5838240731654091 2177607514009156 0 67280 = true := by
  native_decide
