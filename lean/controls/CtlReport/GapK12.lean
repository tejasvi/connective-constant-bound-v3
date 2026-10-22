import Saw38aCore
import CtlData.D_gap_k12

def Ctl.Report.GapK12 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.gap_k12] 2826 2826 18238581991091836 6770765732755619 0 2826
  let t1 ← IO.monoNanosNow
  let fails := (List.range 2826).filter fun i => !Saw38aCore.checkState #[Ctl.Data.gap_k12] 2826 2826 18238581991091836 6770765732755619 i
  IO.println s!"CTL GapK12: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.GapK12
