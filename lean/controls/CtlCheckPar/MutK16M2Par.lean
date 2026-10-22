import Saw38aCore
import CtlData.P_mut_k16_mut_M2_redirect_c00
import CtlData.P_mut_k16_mut_M2_redirect_c01
import CtlData.P_mut_k16_mut_M2_redirect_c02
import CtlData.P_mut_k16_mut_M2_redirect_c03
import CtlData.P_mut_k16_mut_M2_redirect_c04
import CtlData.P_mut_k16_mut_M2_redirect_c05
import CtlData.P_mut_k16_mut_M2_redirect_c06

/-- Control MutK16M2 with 7 chunks of 10000 states (Par). -/
theorem Ctl.CheckPar.MutK16M2Par :
    Saw38aCore.checkRangePar #[Ctl.DataPar.mut_k16_mut_M2_redirect_c00, Ctl.DataPar.mut_k16_mut_M2_redirect_c01, Ctl.DataPar.mut_k16_mut_M2_redirect_c02, Ctl.DataPar.mut_k16_mut_M2_redirect_c03, Ctl.DataPar.mut_k16_mut_M2_redirect_c04, Ctl.DataPar.mut_k16_mut_M2_redirect_c05, Ctl.DataPar.mut_k16_mut_M2_redirect_c06] 10000 67280 5838240731654091 2177607514009156 0 67280 16 = false := by
  native_decide
