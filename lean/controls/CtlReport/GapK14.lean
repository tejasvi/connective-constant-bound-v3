import Saw38aCore
import CtlData.D_gap_k14

def Ctl.Report.GapK14 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.gap_k14] 13158 13158 7886375692179181 2935472799381404 0 13158
  let t1 ← IO.monoNanosNow
  let fails := (List.range 13158).filter fun i => !Saw38aCore.checkState #[Ctl.Data.gap_k14] 13158 13158 7886375692179181 2935472799381404 i
  IO.println s!"CTL GapK14: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.GapK14
