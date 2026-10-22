import Saw38aCore
import CtlData.D_mut_k12_mut_M1_dropchild

def Ctl.Report.MutK12M1 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.mut_k12_mut_M1_dropchild] 2924 2924 9538444858171518 3540745356779801 0 2924
  let t1 ← IO.monoNanosNow
  let fails := (List.range 2924).filter fun i => !Saw38aCore.checkState #[Ctl.Data.mut_k12_mut_M1_dropchild] 2924 2924 9538444858171518 3540745356779801 i
  IO.println s!"CTL MutK12M1: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.MutK12M1
