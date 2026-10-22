# An upper bound for the connective constant of the square lattice

Programs, certificate hashes and the Lean formalization for the paper *An upper bound for the connective constant of
the square lattice* by Tejasvi Singh Tomar (doi:10.5281/zenodo.23551535). The programs, the Lean files and two of the
three certificate files, `k28f.keys.xz` and `k28f.v.xz`, are archived at doi:10.5281/zenodo.23551536. The third file,
`k28f.chosen.xz`, is archived at doi:10.5281/zenodo.23551538. Two other certificates, with larger ratios, are archived
at doi:10.5281/zenodo.23548806 (see "Other certificates" below).

## Theorem

Let `c_n` be the number of `n`-step self-avoiding walks on the square lattice `Z^2` that start at the origin, and let
`mu = lim c_n^(1/n)` be the connective constant. Then

    mu <= 5100683462145913/1917628724674902 = 2.65989103965400719... < 2.6598911.

The previous best upper bound was `mu <= 2.662342426` (O. Couronné, J. Stat. Phys. 192 (2025), 153; arXiv:2211.16146).
This is constant 38a of the repository of optimization constants (https://teorth.github.io/optimizationproblems/).

## Proof outline

1. **Bridges** (Section 2 of the paper). A bridge is a walk `w_0, ..., w_n` with `x(w_0) < x(w_i) <= x(w_n)` for
   `i >= 1`. By Hammersley and Welsh (1962), `mu = lim b_n^(1/n)`, where `b_n` is the number of `n`-step bridges from
   the origin. A bridge from the origin, preceded by the half-line `H = {(x,0) : x <= 0}`, is part of a two-sided
   infinite self-avoiding path.
2. **Dead cells** (Section 3). A cell is dead if no infinite self-avoiding continuation of the current past can visit
   it. Three tests that look only at the state and the step recognize dead cells: (a) at least three neighbours of
   the cell belong to the state; (b) the cell is not connected to infinity; (c) one free cell separates it from
   infinity and from the free neighbours of the new position.
3. **Certificate** (Sections 3-5). A state is a lattice path ending at the origin with last step `+x`. A certificate
   lists states, gives for each state and each of the steps `+x`, `+y`, `-y` either no child (only if the step goes
   into a cell of the state or into a finite region) or a child state, and gives a nonnegative integer weight `V` for
   each state. Every cell of a child, placed at the new position by one of the 8 lattice symmetries, must be a cell
   of the old state, the new position, or a dead cell. Along every bridge, all cells of the current state are then
   visited or dead (Theorem 4.1), so distinct bridges give distinct paths in the automaton. If no weight is 0, the
   number of paths of length `n` is at most `V_start lambda^n`, where `lambda` is the largest ratio
   `sum_children V / V` (Lemma 5.1). Hence `mu <= lambda`.
4. **The certificate of the theorem** (Section 6) has order 28 and 5,792,114,594 states, all with `V > 0`. Two
   checkers, written independently, verify it and compute `lambda` exactly in 128-bit integer arithmetic. Both
   checkers also accept the two other certificates.
5. **Lean proof** (Section 7). `lean/` holds a Lean 4 proof of the theorem without hypotheses,
   `Saw38a.K28F.connective_constant_le_unconditional`. It also proves the Hammersley-Welsh inequality, in the form
   `c_n <= (n+1)^(2 floor(sqrt(2n))+1) b_(n+1)`. The certificate is checked by a checker written in Lean, in 168
   `native_decide` steps that execute compiled code (and one more for the start state), so the Lean compiler is part
   of the trusted base; the soundness of the checker is proved in Lean. See the section "Lean proof" below and
   `lean/README.md`.

## Files

- `checker/check_saw.cpp`: the checker (C++ with OpenMP). Its header states the checked claim and the certificate
  format with 32-bit entries; for the 64-bit entries see "Certificate format".
- `independent/`: a second checker, `check38a.cpp`. Its checking logic was written from the description of the checked
  conditions before its author read the first checker. The directory also holds a Python version, `check38a_py.py`,
  for small certificates, the generators of the negative controls (`mutate_cert.py`, `gaploop_guard_removed.patch`) and
  its own README.
- `builder/saw.cpp`: the program that built the certificates (see "Provenance notes"). It is not needed to check
  them.
- `certificate/SHA256SUMS`: sha256 of the certificate files and of their compressed copies in the records listed
  above, for the certificate of the theorem and for the two other certificates.
- `lean/`: the Lean proof (sources only), with its own README, `SHA256SUMS` and `DATA_PINS.txt`.
- `SHA256SUMS`: sha256 of all other files in this repository.

## Certificate format

The certificate of order `K = 28` consists of three binary files (little-endian):

- `k28f.keys`: `N` strictly increasing 64-bit unsigned integers, one per state. A key encodes a lattice path
  `c_0, ..., c_{n-1}`: `n = key >> 58` is the number of cells, and the low 58 bits hold
  `T = sum_{i=1}^{n-2} t_i 3^(n-2-i)`, where `t_i` is the turn at `c_i` (0 straight, 1 left, 2 right). The last step
  `c_{n-2} -> c_{n-1}` is `+x` and `c_{n-1} = (0,0)`.
- `k28f.chosen`: `N x 3` 64-bit unsigned integers. Entry `3s + j` is the index of the child of state `s` for the step
  `+x`, `+y`, `-y` (`j = 0, 1, 2`), or `0xFFFFFFFFFFFFFFFF` for no child.
- `k28f.v`: `N` doubles in `[0,1]`; the weight of state `s` is `V_s = floor(2^60 v_s)`.

Here `N = 5792114594`. The start state is the straight path of `K/2 + 1 = 15` cells, with key `15 << 58`.

The entries are 64-bit because `N >= 2^32 - 1`. The two other certificates have fewer states, and their entries are
32-bit unsigned integers, with `0xFFFFFFFF` for no child. `independent/check38a.cpp` reads 32-bit entries if
`N < 2^32 - 1` and 64-bit entries otherwise, and requires the `.chosen` file to have `12 N` or `24 N` bytes
accordingly. `checker/check_saw.cpp` takes the width from the size of the `.chosen` file: 32-bit entries if it has
`12 N` bytes, 64-bit entries if it has `24 N` bytes.

## Checking the certificate

The record doi:10.5281/zenodo.23551536 contains `k28f.keys.xz` (3,684,462,840 bytes) and `k28f.v.xz`
(27,412,437,612 bytes), and the record doi:10.5281/zenodo.23551538 contains `k28f.chosen.xz` (18,593,405,052 bytes).
They were made with XZ Utils 5.4.1 as `xz -9 -T0 -k`, and their sha256 are in `certificate/SHA256SUMS`. Decompress them
with `xz -dk` (65 MiB of memory) and check the results:

    sha256sum k28f.keys k28f.chosen k28f.v

must print

    b73d1cccf9790daf2560025d804661976c27e81dea99b9444cf8fc362522309c  k28f.keys
    64c49e61c481539fd658b66b788052634863f3f2e15d6f5e56ee31934caeda3e  k28f.chosen
    e0142296de5bce853d3c4e80d1189e7647647b74462dcdd397fd2a305cdbfb94  k28f.v

The uncompressed files take 231.7 GB (46,336,916,752, 139,010,750,256 and 46,336,916,752 bytes).

Build and run the checker:

    g++ -O2 -march=native -fopenmp -o check_saw checker/check_saw.cpp
    ./check_saw 28 k28f 176

The arguments are the order `K`, the file prefix and the number of threads. It prints, with exit code 0,

    CERTIFIED k=28 states=5792114594 Vzero=0 forbidden(occupied=2438258843 trapped=646976096) children(subset=12260547298) dead cells(3nb=1795496418 enclosed=346701725 cut=595009424)
    LAM = 2.659891039655 (exact ratio 5100683462145913 / 1917628724674902 at state 326522321)  =>  mu(Z^2) <= 2.659891039655

In the first line, `occupied` and `trapped` count the entries without a child for the two cases of condition (C1) of the
paper, `subset` counts the children that need no dead cell, and `3nb`, `enclosed` and `cut` count the dead cells, by the
first of the tests (a), (b), (c) that they pass. The exact ratio is the largest `sum_children V / V`, printed as a
fraction that need not be reduced, and the decimal is rounded up. Several states may attain the maximum, so the printed
state and fraction may differ from run to run; the reduced fraction is always `5100683462145913/1917628724674902`, the
form printed by the run above.
On a failed check the checker prints a line starting with `FAIL` and exits with a nonzero code. The run took 1,178 s on
176 threads; the checker holds about 52 bytes per state in memory (about 301 GB here).

The second checker takes the claimed ratio as an argument and compares it exactly:

    g++ -O2 -march=native -fopenmp -o check38a independent/check38a.cpp
    ./check38a k28f 28 96 5100683462145913/1917628724674902

See `independent/README.md` for its output, its exit codes, the small certificates and the negative controls.

## Other certificates

The record doi:10.5281/zenodo.23548806 contains two other certificates, made by the same program with other
parameters (see "Building the certificates"): `k28e`, of order 28, with 4,124,965,633 states, and `k26f`, of order 26,
with 960,470,402 states. Their compressed sizes are

| file | bytes | file | bytes |
|---|---|---|---|
| `k28e.keys.xz` | 2,924,191,244 | `k26f.keys.xz` | 608,516,272 |
| `k28e.chosen.xz` | 12,765,591,564 | `k26f.chosen.xz` | 2,982,188,008 |
| `k28e.v.xz` | 18,694,447,344 | `k26f.v.xz` | 4,519,899,776 |

After decompression,

    sha256sum k28e.keys k28e.chosen k28e.v k26f.keys k26f.chosen k26f.v

must print

    ae2fc2a3ed12239868fb9f711ae16e7a5554792b6ed49e068b86abf461a87753  k28e.keys
    71e3e45b9f5e08dedcbfc78316eb7fbef97357c3df699aa0e4213c5603e5602d  k28e.chosen
    8062f90eb09348c27a7e11deabecd7cb4f4f8565bc743db78be8dd3063ca0069  k28e.v
    1fcb4b076db689a9d9a044cc0e2a920c0eb5296c68b44bd4b5a5b083984291e0  k26f.keys
    3a3bbe57756025029032e012953809526e4d072398a023a38831a3d0298822e9  k26f.chosen
    8e89d9f25cb73384bb2c1bf41be46e93e86e4eb5578e6065f74f7233d40818ca  k26f.v

Then `./check_saw 28 k28e 176` prints, with exit code 0,

    CERTIFIED k=28 states=4124965633 Vzero=0 forbidden(occupied=1837522690 trapped=558549870) children(subset=8528323731) dead cells(3nb=1255135841 enclosed=312989071 cut=475332839)
    LAM = 2.660075548827 (exact ratio 30613031269641620 / 11508331514550308 at state 3315780989)  =>  mu(Z^2) <= 2.660075548827

so that `mu <= 7653257817410405/2877082878637577 = 2.66007554882623093...`; that run took 846 s on 176 threads. And
`./check_saw 26 k26f 44` prints, with exit code 0,

    CERTIFIED k=26 states=960470402 Vzero=0 forbidden(occupied=398483209 trapped=101832727) children(subset=2040865274) dead cells(3nb=298688271 enclosed=64135060 cut=106262887)
    LAM = 2.661472061273 (exact ratio 2725816588621027200 / 1024176292618053632 at state 1062168)  =>  mu(Z^2) <= 2.661472061273

so that `mu <= 21295442098601775/8001377286078544 = 2.66147206127291875...`; that run took 703 s on 44 threads.
`independent/README.md` gives the output of the second checker for both.

## Building the certificates

The certificate of the theorem was built by `builder/saw.cpp` with the command

    SAW_ROUNDS=8 SAW_TOL=1e-12 SAW_GT=8,8,8,8,6,6,6,6,6,6,4,4,4,2,0 SAW_GT2=8,8,6,6,6,6,6,6,4,2,0 OMP_NUM_THREADS=176 \
      ./saw 28 PBXbSTU72q k28f 176 34

which took 18,937 s on 176 threads. The two other certificates were built with

    SAW_ROUNDS=9 SAW_TOL=1e-12 SAW_GT=8,8,8,6,6,6,6,6,6,6,4,4,4,2,0 SAW_GT2=8,6,6,6,6,6,6,4,2,0 OMP_NUM_THREADS=176 \
      ./saw 28 PBXbSTU72q k28e 176 33
    SAW_ROUNDS=10 SAW_TOL=1e-12 SAW_GT=8,8,8,8,6,6,6,6,6,4,4,4,2,0 SAW_GT2=8,8,6,6,6,6,6,4,2,0 OMP_NUM_THREADS=44 \
      ./saw 26 PBXbSTU72q k26f 44 31

which took 9,603 s on 176 threads and 4,703 s on 44 threads. The builder can be compiled with

    g++ -O2 -march=native -fopenmp -o saw builder/saw.cpp

as for the small certificates described in `independent/README.md`. The checkers do not depend on how the builder chose
the children. At orders 10 to 16 the builder gave byte-identical files with 1 and 2 threads and on two machines (GCC
15.2, x86-64). The certificates of orders 26 and 28 were not rebuilt, so we do not claim that rebuilding them gives the
same files.

## Provenance notes

- The certificates were built from a copy of `builder/saw.cpp` with sha256
  `16e76bc08659548b217dcdbde9686b4f03dd452bea8649606a0acfa04e330322`, which differs from `builder/saw.cpp` only in the
  wording of four comment lines (1, 7, 15 and 152); with the same compiler and flags, both copies compile to the same
  binary.
- The comment at line 132 of `checker/check_saw.cpp` gives the rule by which the builder chooses the width of the
  entries (the rule of the second checker); the code of `check_saw.cpp` accepts either width.
- The first version of the record doi:10.5281/zenodo.23548806, doi:10.5281/zenodo.23540769, contains the same files of
  the two other certificates.

## Lean proof

`lean/README.md` states the theorem, lists the files and gives the build steps. The build reads the three certificate
files of the theorem (decompressed from the two records), converts them into 2,676 Lean data files (179.6 GB) of at most
2,164,802 states, compiles them (about 1.1 TB of build files, including a 180 GB shared library; linking the library
uses about 330 GB of memory), and then runs the 168 checking steps of at most 34,636,832 states, which took about
2.4 × 10^5 CPU-seconds, or about 40 minutes on one machine with 128 threads and 512 GB of memory. The theorem depends on
the standard axioms `propext`, `Classical.choice` and `Quot.sound` and on 169 `native_decide` axioms, one for each
checking step and one for the start state. The toolchain is Lean v4.35.0-rc3 with Mathlib commit c55e6e786f49.
`lean/controls/` holds the harness that runs the Lean checker on the certificates of orders 12, 14 and 16 and on
certificates that must fail, with its logs and a README on regenerating these certificates; `lean/controls/native/`
holds checks on the certificate of the theorem at indices above 2^32 and at a state where the largest ratio is attained.

## License

Apache-2.0 (see `LICENSE`).
