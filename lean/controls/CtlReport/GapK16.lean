import Saw38aCore
import CtlData.D_gap_k16

def Ctl.Report.GapK16 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.gap_k16] 64854 64854 14496392835318946 5407284821498573 0 64854
  let t1 ← IO.monoNanosNow
  let fails := (List.range 64854).filter fun i => !Saw38aCore.checkState #[Ctl.Data.gap_k16] 64854 64854 14496392835318946 5407284821498573 i
  IO.println s!"CTL GapK16: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.GapK16
