import Saw38aCore
import CtlData.D_ok_k12

def Ctl.Report.OkK12 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.ok_k12] 2924 2924 9538444858171518 3540745356779801 0 2924
  let t1 ← IO.monoNanosNow
  let fails := (List.range 2924).filter fun i => !Saw38aCore.checkState #[Ctl.Data.ok_k12] 2924 2924 9538444858171518 3540745356779801 i
  IO.println s!"CTL OkK12: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.OkK12
