import Saw38aCore
import CtlData.D_ok_k16

def Ctl.Report.OkK16LamM1 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => Saw38aCore.checkRange #[Ctl.Data.ok_k16] 67280 67280 5838240731654090 2177607514009156 0 67280
  let t1 ← IO.monoNanosNow
  let fails := (List.range 67280).filter fun i => !Saw38aCore.checkState #[Ctl.Data.ok_k16] 67280 67280 5838240731654090 2177607514009156 i
  IO.println s!"CTL OkK16LamM1: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, first {fails.head?}"

#eval Ctl.Report.OkK16LamM1
