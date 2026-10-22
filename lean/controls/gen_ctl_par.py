#!/usr/bin/env python3
"""gen_ctl_par.py: extra controls with several chunks (CS states each, the last one partial) and with checkRangePar.

Run in this directory after gen_ctl.py. Writes data/NAME_cJJ.s7, CtlData/P_NAME_cJJ.lean, CtlCheckPar/NAME{Seq,Par}.lean
(native_decide: checkRange / checkRangePar ... = expected) and rewrites the root CtlData.lean.
"""
import os, re, subprocess

ROOT = os.path.dirname(os.path.abspath(__file__))
os.chdir(ROOT)
CS, TASKS = 10000, 16


def lam(log):
    m = re.search(r"max ratio LAM = (\d+) / (\d+)", open(os.path.join("logs", log)).read())
    return int(m.group(1)), int(m.group(2))


a, b = lam("chk_ok_k16.out")
g1, g2 = lam("chk_gap_k16.out")
CTL = [("OkK16", "certs/ok_k16", a, b, True), ("OkK16LamM1", "certs/ok_k16", a - 1, b, False),
       ("MutK16M1", "certs/mut_k16/mut_M1_dropchild", a, b, False),
       ("MutK16M2", "certs/mut_k16/mut_M2_redirect", a, b, False),
       ("MutK16M3", "certs/mut_k16/mut_M3_lowv", a, b, False), ("GapK16", "certs/gap_k16", g1, g2, False)]
os.makedirs("CtlCheckPar", exist_ok=True)
done = {}
for name, pre, num, den, exp in CTL:
    N = os.path.getsize(pre + ".keys") // 8
    dname = pre.replace("certs/", "").replace("/", "_")
    if dname not in done:
        names = []
        for j, lo in enumerate(range(0, N, CS)):
            cn = "%s_c%02d" % (dname, j)
            out = subprocess.run(["python3", "-I", "tools/mkchunk28f.py", pre, str(lo), str(CS), "data/%s.s7" % cn],
                                 check=True, capture_output=True, text=True).stdout.split()
            ln, h = int(out[0]), int(out[1])
            assert ln == 31 * min(CS, N - lo)
            open("CtlData/P_%s.lean" % cn, "w").write(
                "import L38Loader\n\n/-! Chunk %d of the control certificate %s (%d characters, 31 per state). -/\n\n"
                "load_cert_chunk Ctl.DataPar.%s \"data/%s.s7\" %d\n" % (j, dname, ln, cn, cn, h))
            names.append(cn)
        done[dname] = names
    names = done[dname]
    imports = "".join("import CtlData.P_%s\n" % cn for cn in names)
    arr = "#[" + ", ".join("Ctl.DataPar.%s" % cn for cn in names) + "]"
    for kind, call in (("Seq", "Saw38aCore.checkRange %s %d %d %d %d 0 %d" % (arr, CS, N, num, den, N)),
                       ("Par", "Saw38aCore.checkRangePar %s %d %d %d %d 0 %d %d" % (arr, CS, N, num, den, N, TASKS))):
        open("CtlCheckPar/%s%s.lean" % (name, kind), "w").write(
            "import Saw38aCore\n%s\n/-- Control %s with %d chunks of %d states (%s). -/\n"
            "theorem Ctl.CheckPar.%s%s :\n    %s = %s := by\n  native_decide\n"
            % (imports, name, len(names), CS, kind, name, kind, call, "true" if exp else "false"))
mods = sorted(f[:-5] for f in os.listdir("CtlData") if f.endswith(".lean"))
open("CtlData.lean", "w").write("".join("import CtlData.%s\n" % m for m in mods))
print("par controls", 2 * len(CTL), "chunk files", sum(len(v) for v in done.values()))
