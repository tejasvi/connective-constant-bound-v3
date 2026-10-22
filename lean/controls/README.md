# Controls of the native checker

Positive and negative controls of `Saw38aCore.checkRange` (../Saw38aCore/Check.lean: records of 31 characters, child
indices of 33 bits) on small certificates built by the paper's construction program. ctl_table.txt lists them; logs/
holds the reference runs of the independent C++ checker (chk_*.out; exit codes and times in chk_summary.txt) and the
Lean build logs (lake_*.log).

The certificates (not included; regenerate them):
- ok_k12, ok_k14, ok_k16: the construction program at orders 12, 14 and 16 with rules PBXbSTU72q and default tables.
- gap_k12, gap_k14, gap_k16: separate builds by the variant of the program without the guard for loops with a gap cell
  (independent/gaploop_guard_removed.patch of the supplement).
- mut_kK/mut_M1_dropchild, mut_M2_redirect, mut_M3_lowv: independent/mutate_cert.py from the supplement applied to
  ok_kK. The states are 1249, 5512 and 17751 for K = 12, 14 and 16 (the state on each certificate's LAM line).
  - M1 empties the +x slot of state 0.
  - M2 redirects children.
  - M3 halves one weight.
- `./make_certs.sh SAW_CPP INDEPENDENT_DIR`, with SAW_CPP the construction program (builder/saw.cpp of the supplement)
  and INDEPENDENT_DIR the supplement's independent/ directory, builds them under certs/, compares their sha256 with
  independent/generated_SHA256SUMS (logs/cert_sha_check.txt: all 27 files match with GCC 14.2 on x86-64) and writes
  the C++ checker's outputs to logs/chk_NAME.out.
- The `chosen` files of these certificates hold 32-bit indices; tools/mkchunk28f.py writes their "no child" value as
  2^33 - 1, the value that the checker expects.

Run:
1. Copy ../Saw38aCore, ../Saw38aCore.lean, ../L38Loader.lean and ../tools here, and lean-toolchain from ../.
2. `./make_certs.sh SAW_CPP INDEPENDENT_DIR` (see above).
3. `python3 gen_ctl.py`: writes data/, CtlData/, CtlCheck/ and CtlReport/. It uses tools/mkchunk28f.py.
4. `lake build CtlCheck`: 18 `native_decide` theorems. The 3 good certificates give `checkRange ... = true`; all
   others give `= false`.
5. `lake build CtlReport`: for each control, `#eval` prints the verdict, the number of failing states and the first
   failing state.
6. Optional: `python3 gen_ctl_par.py` and `lake build CtlCheckPar` run the order-16 controls split into 7 chunks of
   10000 states (the last one partial), with checkRange and checkRangePar.

Expected: for the certificates that violate (C1) or (C2), the number of failing states and the first failing state
equal those of the C++ checker (logs/chk_*.out). In the ratio controls (weight halved, num - 1), the C++ checker
reports a global ratio mismatch with 0 failing states. Lean flags the state or states where that checker attains the
largest ratio.
