import Saw38aCore
import CtlData.D_mut_k14_mut_M3_lowv

def Ctl.Report.MutK14M3 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.mut_k14_mut_M3_lowv] 13650 13650 19286821624401396 7178537576273569 0 13650
  let t1 ← IO.monoNanosNow
  let fails := (List.range 13650).filter fun i => !Saw38aCore.checkState #[Ctl.Data.mut_k14_mut_M3_lowv] 13650 13650 19286821624401396 7178537576273569 i
  IO.println s!"CTL MutK14M3: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.MutK14M3
