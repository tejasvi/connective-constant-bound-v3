# check38a: independent check of the certificates k28f, k28e (K = 28) and k26f (K = 26) for the connective constant of Z^2

## Files

- `check38a.cpp`: the checker (C++ with OpenMP). Its header gives the usage, the certificate format and the checked claim.
- `check38a_py.py`: a second implementation in Python 3 (standard library only, plain set-based searches), for small
  memory parameters (K = 10, 12, 14).
- `mutate_cert.py`: generator of the mutation negative controls.
- `gaploop_guard_removed.patch`: generator of the gap-loop negative control (a patch to the builder source `saw.cpp`).
- `generated_SHA256SUMS`: sha256 of the small certificates generated for the checks below, in our build.
- `SHA256SUMS`: sha256 of the files above.

## Build

    g++ -O2 -march=native -fopenmp -o check38a check38a.cpp

A 64-bit GCC or Clang with OpenMP and `unsigned __int128` is needed (tested with GCC 14.2 and 15.2 on x86-64 Linux).

## Usage and exit codes

    ./check38a PREFIX K [THREADS] [NUM/DEN]
    python3 check38a_py.py PREFIX K [NUM/DEN]

Both read `PREFIX.keys`, `PREFIX.chosen`, `PREFIX.v`. K is the memory parameter (the start state is the straight line of
K/2+1 cells). THREADS defaults to the OpenMP default; the output does not depend on it. NUM/DEN is the claimed exact
ratio, reduced or not; if it is given, PASS also requires the computed ratio to equal it.

The child indices in `PREFIX.chosen` are 32-bit unsigned integers when the number of states N is below 2^32 - 1, as for
k28e and k26f, and 64-bit unsigned integers when N >= 2^32 - 1, as for k28f; the all-ones value means "no child". Both
programs take the width from N.

The exit code is 0 only on PASS, and the last line is then `VERDICT: PASS`. Otherwise the last line is `VERDICT: FAIL` and
the exit code is

| code | meaning |
|---|---|
| 1 | malformed arguments |
| 2 | a file is missing, unreadable, empty or not a regular file |
| 3 | inconsistent file sizes (keys not a multiple of 8 bytes, chosen not 12 N bytes for N < 2^32 - 1 or not 24 N bytes for N >= 2^32 - 1, v not 8 N bytes), N = 0, or N > 2^56 (C++ program only) |
| 4 | keys not strictly increasing, a v outside [0, 1] or NaN, a child index >= N, start state missing or with V = 0 |
| 5 | a state fails the check, a V = 0 condition fails, no positive ratio, or the computed ratio differs from NUM/DEN |

Neither program uses assertions, so `-DNDEBUG` or `python3 -O` does not change the result.

## Certificate k28f (mu(Z^2) <= 2.6598911)

    sha256sum k28f.keys k28f.chosen k28f.v

must print

    b73d1cccf9790daf2560025d804661976c27e81dea99b9444cf8fc362522309c  k28f.keys
    64c49e61c481539fd658b66b788052634863f3f2e15d6f5e56ee31934caeda3e  k28f.chosen
    e0142296de5bce853d3c4e80d1189e7647647b74462dcdd397fd2a305cdbfb94  k28f.v

Then

    ./check38a k28f 28 96 5100683462145913/1917628724674902

prints, with exit code 0,

    check38a: N=5792114594 K=28 start=0 Vzero=0 (children of V=0 states with V>0: 0; V=0 subgraph acyclic: 1)
      no-child slots: occupied 2438258843, trapped 646976096; children verified 14291108843; child cells in E 355761635395, dead (a) 1795496418, (b) 346701725, (c) 595009424
      failing states 0
      max ratio LAM = 5100683462145913 / 1917628724674902 ~ 2.659891039654007 (first state attaining it: 326522321)
      claimed ratio 5100683462145913/1917628724674902 equals the computed ratio: 1
    VERDICT: PASS

So LAM = 5100683462145913/1917628724674902 = 2.659891039654007194... and mu(Z^2) <= 2.6598911.
Run time: 1 h 01 min 20 s wall on 96 hardware threads (48 cores), 97.4 hours of CPU time;
peak resident memory 231.6 GB, almost all of it the memory-mapped certificate files (231.7 GB).

## Certificate k26f (mu(Z^2) <= 2.6614721)

    sha256sum k26f.keys k26f.chosen k26f.v

must print

    1fcb4b076db689a9d9a044cc0e2a920c0eb5296c68b44bd4b5a5b083984291e0  k26f.keys
    3a3bbe57756025029032e012953809526e4d072398a023a38831a3d0298822e9  k26f.chosen
    8e89d9f25cb73384bb2c1bf41be46e93e86e4eb5578e6065f74f7233d40818ca  k26f.v

Then

    ./check38a k26f 26 96 2725816588621027200/1024176292618053632

prints, with exit code 0,

    check38a: N=960470402 K=26 start=0 Vzero=0 (children of V=0 states with V>0: 0; V=0 subgraph acyclic: 1)
      no-child slots: occupied 398483209, trapped 101832727; children verified 2381095270; child cells in E 54734060289, dead (a) 298688271, (b) 64135060, (c) 106262887
      failing states 0
      max ratio LAM = 21295442098601775 / 8001377286078544 ~ 2.661472061272919 (first state attaining it: 325078)
      claimed ratio 2725816588621027200/1024176292618053632 equals the computed ratio: 1
    VERDICT: PASS

So LAM = 21295442098601775/8001377286078544 = 2.661472061272918750... and mu(Z^2) <= 2.6614721.
Run time: 5 min 48 s wall on 96 hardware threads (48 cores), 9.3 hours of CPU time;
peak resident memory 26.9 GB, almost all of it the memory-mapped certificate files (26.9 GB).

## Certificate k28e (mu(Z^2) <= 2.6600756)

    sha256sum k28e.keys k28e.chosen k28e.v

must print

    ae2fc2a3ed12239868fb9f711ae16e7a5554792b6ed49e068b86abf461a87753  k28e.keys
    71e3e45b9f5e08dedcbfc78316eb7fbef97357c3df699aa0e4213c5603e5602d  k28e.chosen
    8062f90eb09348c27a7e11deabecd7cb4f4f8565bc743db78be8dd3063ca0069  k28e.v

Then

    ./check38a k28e 28 48 30613031269641620/11508331514550308

prints, with exit code 0,

    check38a: N=4124965633 K=28 start=0 Vzero=0 (children of V=0 states with V>0: 0; V=0 subgraph acyclic: 1)
      no-child slots: occupied 1837522690, trapped 558549870; children verified 9978824339; child cells in E 248320670214, dead (a) 1255135841, (b) 312989071, (c) 475332839
      failing states 0
      max ratio LAM = 7653257817410405 / 2877082878637577 ~ 2.660075548826231 (first state attaining it: 3315780989)
      claimed ratio 30613031269641620/11508331514550308 equals the computed ratio: 1
    VERDICT: PASS

So LAM = 7653257817410405/2877082878637577 = 2.660075548826230932... and mu(Z^2) <= 2.6600756.
Run time: 1 h 50 min 57 s wall on 48 hardware threads (24 cores), 88.7 hours of CPU time;
peak resident memory 115.5 GB, almost all of it the memory-mapped certificate files (115.5 GB).

## Small-order check in Python (K = 10, 12, 14)

The small certificates come from the builder `saw.cpp` (sha256
`16e76bc08659548b217dcdbde9686b4f03dd452bea8649606a0acfa04e330322`), built with the same flags as above and run with no
`SAW_*` environment variables set:

    ./saw K PBXbSTU72q ok_kK 1 22
    python3 check38a_py.py ok_kK K
    ./check38a ok_kK K 1

| K | states | LAM (both programs) | Python time, one core |
|---|---|---|---|
| 10 | 662 | 7586028738440393/2805785315054258 | 0.4 s |
| 12 | 2924 | 9538444858171518/3540745356779801 | 1.9 s |
| 14 | 13650 | 19286821624401396/7178537576273569 | 10.7 s |

All three PASS in both programs. The Python program is not practical for K = 26.

## Negative controls

1. Gap-loop variant. The builder may close a gap-sealed small loop at the current endpoint A only when no free neighbour
   of A lies in the interior of the loop. The patch removes this guard:

        cp saw.cpp saw_gaploop.cpp && patch saw_gaploop.cpp gaploop_guard_removed.patch
        g++ -O2 -march=native -fopenmp -o saw_gaploop saw_gaploop.cpp
        ./saw_gaploop K PBXbSTU72q gap_kK 1 22        (K = 12, 14, 16)
        ./check38a gap_kK K 1

   Result: FAIL (exit code 5) with 47, 257 and 1357 failing states for K = 12, 14, 16 (first failing states 517, 1289,
   3202). `check38a_py.py` also fails them, with 47 and 257 failing states at K = 12 and 14. The unmodified builder, run
   in the same way, gives certificates that PASS (K = 12, 14, 16; K = 16 has LAM = 5838240731654091/2177607514009156).

2. Mutations of the K = 16 certificate `ok_k16` built by the unmodified builder:

        python3 mutate_cert.py ok_k16 mut 17751
        ./check38a mut/mut_M1_dropchild 16 1
        ./check38a mut/mut_M2_redirect 16 1
        ./check38a mut/mut_M3_lowv 16 1 5838240731654091/2177607514009156

   Results: M1 (one child removed) FAIL with 1 failing state; M2 (random children redirected) FAIL with 16 failing
   states; M3 (v of state 17751 halved) has no failing state, but its computed ratio
   5838240731654091/1088803757004578 differs from the claim, so FAIL. All three exit with code 5. State 17751 is the state
   printed on the LAM line for `ok_k16`.

`generated_SHA256SUMS` lists the sha256 of all these small certificates in our build (GCC 15.2, x86-64). Another
compiler or CPU may round the builder's floating-point eigenvector iteration differently, which can change the
certificates and the counts above but should not change any verdict.
