import Saw38aCore
import CtlData.D_mut_k16_mut_M1_dropchild

def Ctl.Report.MutK16M1 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.mut_k16_mut_M1_dropchild] 67280 67280 5838240731654091 2177607514009156 0 67280
  let t1 ← IO.monoNanosNow
  let fails := (List.range 67280).filter fun i => !Saw38aCore.checkState #[Ctl.Data.mut_k16_mut_M1_dropchild] 67280 67280 5838240731654091 2177607514009156 i
  IO.println s!"CTL MutK16M1: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.MutK16M1
