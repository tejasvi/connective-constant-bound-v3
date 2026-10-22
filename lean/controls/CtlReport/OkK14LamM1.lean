import Saw38aCore
import CtlData.D_ok_k14

def Ctl.Report.OkK14LamM1 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.ok_k14] 13650 13650 19286821624401395 7178537576273569 0 13650
  let t1 ← IO.monoNanosNow
  let fails := (List.range 13650).filter fun i => !Saw38aCore.checkState #[Ctl.Data.ok_k14] 13650 13650 19286821624401395 7178537576273569 i
  IO.println s!"CTL OkK14LamM1: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.OkK14LamM1
