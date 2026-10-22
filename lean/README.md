# A Lean proof that the connective constant of Z^2 is at most 2.6598911

Lean 4 (v4.35.0-rc3) with Mathlib at commit c55e6e786f49 (see lake-manifest.json).

## Main theorem
`Saw38a.K28F.connective_constant_le_unconditional` (Saw38a/Final.lean):

    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (5100683462145913 : ℝ) / 1917628724674902 ∧ μ < 2.6598911

`sawCount n` is the number of n-step self-avoiding walks on Z^2 that start at the origin, counted as step sequences
(Saw38a/Spec.lean). The theorem has no hypotheses. `#print axioms` gives propext, Classical.choice and Quot.sound,
plus 169 `native_decide` axioms: 168 for the shards `L38.Shard.shard000` to `L38.Shard.shard167`, and one for
`L38.Shard.start_ok`.

Statement files:
- `Saw38a/Statements28f.lean` holds the statements of this proof with `sorry` bodies. `probe/CheckFinal.lean` checks
  by `rfl` that the proved theorems have exactly these types.
- `Saw38a/Statements.lean` is the same file for a certificate of order 26; the proof does not use it.
- Final.lean imports neither statement file. Their `sorry` bodies make `lake build Saw38a` print "declaration uses
  `sorry`" warnings for these two files only.

## Contents
- Saw38a/Spec.lean: definitions.
  - Walks, `sawCount`, `bridgeCount`.
  - The Hammersley-Welsh bound `HW` in a weak form (a subexponential factor).
  - States, dead cells and certificates (Definitions 3.1 and 3.2 of the paper).
  - The number of paths of the automaton graph.
- Saw38aCore/Check.lean: the certificate checker, core Lean only, compiled to native code.
  - Records are 31 characters per state; child indices have 33 bits, and 2^33 - 1 stands for "no child".
  - It checks (C1), (C2), positive weights and `den · Σ V(children) ≤ num · V` for every state.
  - Every claim that a cell cannot escape is re-checked by a closure test of the flood-fill result.
- Saw38a/CheckGrid.lean, CheckConf.lean, CheckDead.lean, CheckDecode.lean, CheckMain.lean: if the checker accepts
  every record, the records form a valid certificate (`valid_of_check`, `checkState_of_shards`).
- Saw38a/Bridge.lean: Theorem 4.1, b_n ≤ the number of automaton paths of length n.
- Saw38a/Count.lean: Lemma 5.1, the number of paths of length n is at most V_st · λ^n.
- Saw38a/Fekete.lean: c_{m+n} ≤ c_m c_n, and the limit μ exists.
- Saw38a/Mu.lean: `HW` and b_n ≤ C λ^n give μ ≤ λ.
- Saw38a/HW.lean: `hw' : HW`, with c_n ≤ (n+1)^(2⌊√(2n)⌋+1) b_(n+1).
- Saw38a/Final.lean: the assembly for the certificate of order 28 (file prefix k28f).
- L38Loader.lean: the build-time loader.
  - `load_cert_chunk name "path" hash` defines `name : String` from a data file after checking its 64-bit FNV-1a hash.
  - The definition is compiled and not inlined.
- tools/mkchunk28f.py and tools/gen_data28f.sh convert the certificate files into 2676 chunk files of 31 seven-bit
  characters per state: 2,164,802 states each, the last has 1,269,244. They write the modules L38Data/ChunkNNNN.lean
  and L38Data/All.lean. DATA_PINS.txt lists the length and FNV-1a hash of every chunk.
- tools/gen_shards28f.py writes L38Shard/Defs.lean, the 168 shard modules (34,636,832 states each; the last has
  7,763,650), L38Shard/Start.lean and L38Shard/All.lean.
- tools/gen_ctl32.py writes the native controls above 2^32 (controls/native/).

## Data
The certificate of order 28 (files k28f.keys, k28f.chosen, k28f.v) in the paper's supplement:
- doi:10.5281/zenodo.23551536 holds k28f.keys.xz and k28f.v.xz;
- doi:10.5281/zenodo.23551538 holds k28f.chosen.xz.
The sha256 values of the xz files are:
- keys.xz 0e320435432cb5909de4f4474ade0b68a385aa9078350f7123efc3c1431a6d7e
- chosen.xz 634a82630e4bfc6d82778286411b31dcebdf1a8e7a4d3548cb772413ac646ce3
- v.xz ffaf8ab83f22ae09c4dcc851127be78790fd4b802faff130b4dcbae39bbb7f35
After decompression, the files have these sha256 values (checked by tools/gen_data28f.sh):
- keys b73d1cccf9790daf2560025d804661976c27e81dea99b9444cf8fc362522309c
- chosen 64c49e61c481539fd658b66b788052634863f3f2e15d6f5e56ee31934caeda3e (64-bit indices)
- v e0142296de5bce853d3c4e80d1189e7647647b74462dcdd397fd2a305cdbfb94
The certificate has 5,792,114,594 states, which become 179,555,552,414 characters of chunk data. The soundness of the
checker does not depend on the data; the data only determine which certificate is checked.

## Build
1. Download the three xz files and decompress them (`xz -d`; 231.7 GB after decompression).
2. Run `tools/gen_data28f.sh PREFIX`, where PREFIX is the absolute path of the files without the extension (default
   ~/l38/cert/k28f). The script checks the sha256 of the three files, converts them in parallel, and writes data/
   (179.6 GB of chunk data), pins/ and L38Data/. Compare pins/ with DATA_PINS.txt. The certificate files are not needed
   after this step.
3. `lake build L38Data L38Data:shared`. This writes about 1.1 TB (C, objects, oleans, and a 180 GB shared library).
   Linking the shared library reached about 330 GB of resident memory, mostly file pages of the linker's inputs and
   output (on a machine with 384 GB of RAM). With data/, the build needs about 1.2 TB of disk space.
4. `python3 tools/gen_shards28f.py .`, then `lake build L38Shard.SNNN` for NNNN = 000 to 167.
   - Each shard is one `native_decide` that uses all cores.
   - The machine needs enough RAM to keep the 180 GB library in the page cache.
   - On one machine with 128 threads and 512 GB of RAM, the shards took 239,456 CPU-seconds and about 40 minutes in
     total: 9-52 s per shard, at most 37 GB of memory per shard.
5. `lake build Saw38a.Final`, then `lake env lean probe/CheckFinal.lean` (statements and axioms).
The proof modules without the data, `lake build Saw38a`, build in a few minutes.

## Controls
- controls/ (see controls/README.md) reruns the small-certificate controls with this checker.
  - It accepts certificates of order 12, 14 and 16 built by the same program.
  - It rejects every corrupted variant: a child removed, children redirected, a weight halved, a claimed ratio below
    the true one, and builds of a variant of the program without the guard for loops with a gap cell (separate
    builds, not modifications).
  - For the certificates that violate (C1) or (C2), it reports the same number of failing states and the same first
    failing state as the independent C++ checker. In the ratio controls, its first failing state is the state where
    that checker attains the largest ratio.
- controls/native/ holds controls on the full certificate.
  - Above 2^32 (Ctl32.lean, written by tools/gen_ctl32.py), these pass:
    - the 1000 states from index 2^32;
    - the decoded child index 5,071,223,956 of state 4,294,967,297, which equals the 64-bit value in k28f.chosen.
  - Above 2^32, these fail:
    - that value minus 2^32;
    - the bound N = 2^32;
    - a misaligned record layout.
  - At state 326522321, where the first C++ checker (checker/check_saw.cpp of the supplement) attains the largest
    ratio (CtlWorst.lean): the exact ratio passes, and num - 1 fails.
  - To run them, copy the files into L38Shard/ and `lake build L38Shard.Ctl32 L38Shard.CtlWorst`.
