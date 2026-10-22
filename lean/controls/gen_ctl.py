#!/usr/bin/env python3
"""gen_ctl.py: positive and negative controls of the native checker Saw38aCore.checkRange on small certificates.

Run in this directory after the certificates (certs/) and the C++ checker logs (logs/chk_*.out) exist. Writes
data/NAME.s7 (one chunk, 31 characters per state, by tools/mkchunk28f.py), CtlData/NAME.lean (the chunk, as in
tools/gen_data28f.sh), CtlCheck/NAME.lean (one native_decide theorem: checkRange ... = expected) and
CtlReport/NAME.lean (#eval: verdict, number and first of the failing states, time).
"""
import os, re, subprocess

ROOT = os.path.dirname(os.path.abspath(__file__))
os.chdir(ROOT)


def lam(log):
    m = re.search(r"max ratio LAM = (\d+) / (\d+)", open(os.path.join("logs", log)).read())
    return int(m.group(1)), int(m.group(2))


# (module name, certificate prefix, num, den, expected verdict, description)
CTL = []
for K in (12, 14, 16):
    a, b = lam("chk_ok_k%d.out" % K)
    g1, g2 = lam("chk_gap_k%d.out" % K)
    CTL += [
        ("OkK%d" % K, "certs/ok_k%d" % K, a, b, True, "ok_k%d, exact ratio" % K),
        ("OkK%dLamM1" % K, "certs/ok_k%d" % K, a - 1, b, False, "(e) ok_k%d, num - 1" % K),
        ("MutK%dM1" % K, "certs/mut_k%d/mut_M1_dropchild" % K, a, b, False, "(a) ok_k%d, first child removed" % K),
        ("MutK%dM2" % K, "certs/mut_k%d/mut_M2_redirect" % K, a, b, False, "(b) ok_k%d, children redirected" % K),
        ("MutK%dM3" % K, "certs/mut_k%d/mut_M3_lowv" % K, a, b, False, "(c) ok_k%d, one weight halved" % K),
        ("GapK%d" % K, "certs/gap_k%d" % K, g1, g2, False, "(d) gap_k%d, its own exact ratio" % K),
    ]

for d in ("data", "CtlData", "CtlCheck", "CtlReport"):
    os.makedirs(d, exist_ok=True)

done = {}
rows = []
for name, pre, num, den, exp, desc in CTL:
    N = os.path.getsize(pre + ".keys") // 8
    dname = pre.replace("certs/", "").replace("/", "_")
    if dname not in done:
        out = subprocess.run(["python3", "-I", "tools/mkchunk28f.py", pre, "0", str(N), "data/%s.s7" % dname],
                             check=True, capture_output=True, text=True).stdout.split()
        ln, h = int(out[0]), int(out[1])
        assert ln == 31 * N
        dmod = "D_" + dname
        open("CtlData/%s.lean" % dmod, "w").write(
            "import L38Loader\n\n/-! Control certificate %s (%d characters, 31 per state). -/\n\n"
            "load_cert_chunk Ctl.Data.%s \"data/%s.s7\" %d\n" % (dname, ln, dname, dname, h))
        done[dname] = (dmod, ln, h)
    dmod, ln, h = done[dname]
    call = "Saw38aCore.checkRange #[Ctl.Data.%s] %d %d %d %d 0 %d" % (dname, N, N, num, den, N)
    open("CtlCheck/%s.lean" % name, "w").write(
        "import Saw38aCore\nimport CtlData.%s\n\n/-- Control %s: %s. -/\n"
        "theorem Ctl.Check.%s : %s = %s := by\n  native_decide\n"
        % (dmod, name, desc, name, call, "true" if exp else "false"))
    open("CtlReport/%s.lean" % name, "w").write(
        "import Saw38aCore\nimport CtlData.%s\n\n"
        "def Ctl.Report.%s : IO Unit := do\n"
        "  let t0 ← IO.monoNanosNow\n"
        "  let r ← IO.lazyPure fun _ => %s\n"
        "  let t1 ← IO.monoNanosNow\n"
        "  let fails := (List.range %d).filter fun i => !Saw38aCore.checkState #[Ctl.Data.%s] %d %d %d %d i\n"
        "  IO.println s!\"CTL %s: checkRange = {r} in {(t1 - t0) / 1000000} ms; failing states {fails.length}, "
        "first {fails.head?}\"\n\n#eval Ctl.Report.%s\n"
        % (dmod, name, call, N, dname, N, N, num, den, name, name))
    rows.append((name, dname, N, num, den, exp, h))

open("CtlData.lean", "w").write("".join("import CtlData.%s\n" % v[0] for v in done.values()))
with open("ctl_table.txt", "w") as f:
    for r in rows:
        f.write("%s data=%s N=%d num=%d den=%d expected=%s fnv=%d\n" % r)
print("controls", len(rows), "data files", len(done))
