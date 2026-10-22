// check38a.cpp: independent checker for a memory-automaton certificate of an upper bound on the connective constant
// mu(Z^2) of self-avoiding walks on the square lattice.
//
// usage:  check38a PREFIX K [THREADS] [NUM/DEN]
//   reads PREFIX.keys, PREFIX.chosen, PREFIX.v; K = memory parameter (even, 4..60); THREADS = OpenMP threads;
//   NUM/DEN = claimed exact ratio. If given, PASS also requires the computed exact ratio to equal NUM/DEN.
//   Exit code 0 only on PASS. Any failing check, any missing, truncated or size-inconsistent file, N = 0, a missing
//   start state, a malformed argument or a claimed ratio that differs from the computed one gives a nonzero code.
//   No assert() is used, so the result does not depend on -DNDEBUG.
//
// Certificate format.
//   keys   : N uint64, strictly increasing. A key encodes a lattice path c_0, ..., c_{n-1}: n = key >> 58 cells; the low
//            58 bits are T = sum_{i=1}^{n-2} t_i 3^{n-2-i} with t_i in {0 straight, 1 left (counter-clockwise), 2 right}
//            the turn at c_i; the last step c_{n-2} -> c_{n-1} is +x and c_{n-1} = (0,0) =: A.
//   chosen : N x 3 child indices, uint32 (uint64 when N >= 2^32 - 1); slot j is the move of A by +x, +y, -y; the
//            all-ones value means "no child".
//   v      : N doubles in [0,1]; V_s := floor(v_s 2^60).
//
// Checked claim (every state S, every slot j, target t = A + e_j):
//   1. "no child" only if t is a cell of S, or t cannot reach the outside of the bounding box of S by a 4-connected
//      path avoiding S;
//   2. otherwise the child path C satisfies: for some g among the 8 lattice symmetries, every cell of g(C) + t lies in
//      E = S + {t} or is dead for E:
//        (a) it has at least 3 neighbours in E other than t; or
//        (b) it is not connected to infinity in Z^2 \ E; or
//        (c) for some cell g' not in E, its component in Z^2 \ (E + {g'}) is finite and contains no neighbour of t
//            outside E + {g'};
//   3. every state with V_s > 0 has sum over its children of V_child <= LAM V_s, where LAM is the exact maximum ratio
//      (printed as a reduced fraction); states with V_s = 0 have only children with V = 0 and contain no cycle; the
//      start state (the straight line of K/2+1 cells, key (K/2+1) << 58) has V > 0.
//   Also: keys strictly increasing; every key decodes (no excess digits) to a self-avoiding path in the coordinate
//   range [-28, 28]; child indices < N; every v in [0,1].
// The searches in 2(c) use a restricted candidate set (cells within Chebyshev distance 1 of E, in the cell's component)
// and bounded boxes; a restriction can only turn a valid certificate into a FAIL, never an invalid one into a PASS.
//
// Build:  g++ -O2 -march=native -fopenmp -o check38a check38a.cpp
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cerrno>
#include <cstdarg>
#include <vector>
#include <string>
#include <algorithm>
#include <atomic>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <omp.h>

typedef unsigned __int128 u128;
static const int OFF = 32;          // grid offset: coordinate x in [-32,31] -> bit x+32, row y+32
static const uint64_t NONE32 = 0xffffffffull;

enum { EXIT_PASS = 0, EXIT_USAGE = 1, EXIT_FILE = 2, EXIT_FORMAT = 3, EXIT_GLOBAL = 4, EXIT_FAIL = 5 };

static void fail_exit(int code, const char *fmt, ...) {      // print "FAIL: <reason>" and the verdict, exit nonzero
    va_list ap; va_start(ap, fmt);
    printf("FAIL: "); vprintf(fmt, ap); printf("\nVERDICT: FAIL\n");
    va_end(ap); fflush(stdout); exit(code);
}

struct Grid { uint64_t r[64]; };
static inline void gclear(Grid &g) { memset(g.r, 0, sizeof g.r); }
static inline bool gget(const Grid &g, int x, int y) { return (g.r[y + OFF] >> (x + OFF)) & 1ull; }
static inline void gset(Grid &g, int x, int y) { g.r[y + OFF] |= 1ull << (x + OFF); }

static const void *map_file(const std::string &p, size_t &sz) {
    int fd = open(p.c_str(), O_RDONLY);
    if (fd < 0) fail_exit(EXIT_FILE, "cannot open %s: %s", p.c_str(), strerror(errno));
    struct stat st;
    if (fstat(fd, &st) != 0) fail_exit(EXIT_FILE, "cannot stat %s", p.c_str());
    if (!S_ISREG(st.st_mode)) fail_exit(EXIT_FILE, "not a regular file: %s", p.c_str());
    sz = (size_t)st.st_size;
    if (sz == 0) fail_exit(EXIT_FILE, "empty file %s", p.c_str());
    void *m = mmap(nullptr, sz, PROT_READ, MAP_SHARED, fd, 0);
    if (m == MAP_FAILED) fail_exit(EXIT_FILE, "cannot map %s", p.c_str());
    close(fd);
    return m;
}

static bool parse_u64(const char *s, uint64_t &out) {
    if (!s || !*s) return false;
    errno = 0; char *e = nullptr;
    unsigned long long v = strtoull(s, &e, 10);
    if (errno || *e || s[0] == '-') return false;
    out = (uint64_t)v; return true;
}

// decode key -> cells (x,y); returns n, or -1 if invalid (n < 2 or > 40, excess digits, not self-avoiding, out of range)
static int decode(uint64_t key, int *xs, int *ys) {
    int n = (int)(key >> 58);
    uint64_t T = key & ((1ull << 58) - 1);
    if (n < 2 || n > 40) return -1;
    int t[64];
    for (int i = n - 2; i >= 1; i--) { t[i] = (int)(T % 3); T /= 3; }
    if (T != 0) return -1;
    int dx = 1, dy = 0;                       // d_{n-2}: step c_{n-2} -> c_{n-1} = +x
    xs[n - 1] = 0; ys[n - 1] = 0;
    xs[n - 2] = -1; ys[n - 2] = 0;
    for (int i = n - 2; i >= 1; i--) {         // turn t_i at c_i relates d_{i-1} and d_i
        int ndx, ndy;
        if (t[i] == 0) { ndx = dx; ndy = dy; }
        else if (t[i] == 1) { ndx = dy; ndy = -dx; }      // left: d_i = rotL(d_{i-1}), so d_{i-1} = rotR(d_i)
        else { ndx = -dy; ndy = dx; }                      // right: d_{i-1} = rotL(d_i)
        dx = ndx; dy = ndy;
        xs[i - 1] = xs[i] - dx; ys[i - 1] = ys[i] - dy;
    }
    for (int i = 0; i < n; i++) {
        if (xs[i] < -28 || xs[i] > 28 || ys[i] < -28 || ys[i] > 28) return -1;
        for (int j = 0; j < i; j++) if (xs[i] == xs[j] && ys[i] == ys[j]) return -1;
    }
    return n;
}

static const int GX[8][4] = {   // g(x,y) = (a x + b y, c x + d y): the 8 symmetries of Z^2 fixing the origin
    {1, 0, 0, 1}, {0, -1, 1, 0}, {-1, 0, 0, -1}, {0, 1, -1, 0},
    {1, 0, 0, -1}, {-1, 0, 0, 1}, {0, 1, 1, 0}, {0, -1, -1, 0}};

struct Box { int x0, x1, y0, y1; };          // inclusive
static inline uint64_t rowmask(int x0, int x1) {   // bits for coordinates x0..x1
    int b0 = x0 + OFF, b1 = x1 + OFF;
    uint64_t hi = (b1 >= 63) ? ~0ull : ((1ull << (b1 + 1)) - 1);
    uint64_t lo = (b0 <= 0) ? 0ull : ((1ull << b0) - 1);
    return hi & ~lo;
}

// 4-connected flood fill from (sx,sy) over the cells of the box that are not blocked
static void flood(const Grid &blocked, const Box &bx, int sx, int sy, Grid &out) {
    uint64_t m = rowmask(bx.x0, bx.x1);
    int r0 = bx.y0 + OFF, r1 = bx.y1 + OFF;
    uint64_t freer[64];
    for (int r = r0; r <= r1; r++) { freer[r] = m & ~blocked.r[r]; out.r[r] = 0; }
    if (!((freer[sy + OFF] >> (sx + OFF)) & 1ull)) return;
    out.r[sy + OFF] = 1ull << (sx + OFF);
    bool ch = true;
    while (ch) {
        ch = false;
        for (int r = r0; r <= r1; r++) {             // downward sweep
            uint64_t v = out.r[r];
            uint64_t nv = v | (v << 1) | (v >> 1);
            if (r > r0) nv |= out.r[r - 1];
            if (r < r1) nv |= out.r[r + 1];
            nv &= freer[r];
            if (nv != v) { out.r[r] = nv; ch = true; }
        }
        for (int r = r1; r >= r0; r--) {             // upward sweep
            uint64_t v = out.r[r];
            uint64_t nv = v | (v << 1) | (v >> 1);
            if (r > r0) nv |= out.r[r - 1];
            if (r < r1) nv |= out.r[r + 1];
            nv &= freer[r];
            if (nv != v) { out.r[r] = nv; ch = true; }
        }
    }
}
static bool touches_ring(const Grid &f, const Box &bx) {      // filled region meets the outermost ring of the box
    uint64_t m = rowmask(bx.x0, bx.x1);
    uint64_t edges = (1ull << (bx.x0 + OFF)) | (1ull << (bx.x1 + OFF));
    if (f.r[bx.y0 + OFF] & m) return true;
    if (f.r[bx.y1 + OFF] & m) return true;
    for (int r = bx.y0 + OFF + 1; r < bx.y1 + OFF; r++) if (f.r[r] & edges) return true;
    return false;
}

static std::string u128s(u128 v) {
    if (v == 0) return "0";
    char buf[64]; int p = 63; buf[p] = 0;
    while (v) { buf[--p] = (char)('0' + (int)(v % 10)); v /= 10; }
    return std::string(buf + p);
}

struct Stats {
    uint64_t nochild_occ = 0, nochild_trap = 0, child_ok = 0, cell_inE = 0, dead_a = 0, dead_b = 0, dead_c = 0;
    uint64_t fails = 0;
};

int main(int argc, char **argv) {
    if (argc < 3 || argc > 5) fail_exit(EXIT_USAGE, "usage: check38a PREFIX K [THREADS] [NUM/DEN]");
    std::string P = argv[1];
    uint64_t K64;
    if (!parse_u64(argv[2], K64) || K64 < 4 || K64 > 60 || (K64 & 1)) fail_exit(EXIT_USAGE, "bad K (even, 4..60)");
    int K = (int)K64;
    int th = omp_get_max_threads();
    if (argc > 3) { uint64_t t64; if (!parse_u64(argv[3], t64) || t64 < 1 || t64 > 4096) fail_exit(EXIT_USAGE, "bad THREADS (1..4096)"); th = (int)t64; }
    omp_set_num_threads(th);
    bool haveclaim = false; u128 cnum = 0, cden = 1;
    if (argc > 4) {
        std::string c = argv[4]; size_t sl = c.find('/');
        uint64_t a, b;
        if (sl == std::string::npos || !parse_u64(c.substr(0, sl).c_str(), a) || !parse_u64(c.substr(sl + 1).c_str(), b) || b == 0)
            fail_exit(EXIT_USAGE, "bad claimed ratio (expected NUM/DEN)");
        haveclaim = true; cnum = a; cden = b;
    }
    size_t szk, szc, szv;
    const uint64_t *keys = (const uint64_t *)map_file(P + ".keys", szk);
    const void *chosen = map_file(P + ".chosen", szc);
    const double *vv = (const double *)map_file(P + ".v", szv);
    if (szk % 8 != 0) fail_exit(EXIT_FORMAT, "keys file size not a multiple of 8");
    uint64_t N = szk / 8;
    if (N == 0) fail_exit(EXIT_FORMAT, "N = 0");
    if (N > (1ull << 56)) fail_exit(EXIT_FORMAT, "N too large");
    if (szv != N * 8) fail_exit(EXIT_FORMAT, "v file size %zu, expected %llu", szv, (unsigned long long)(N * 8));
    bool wide = N >= 0xffffffffull;
    if (szc != N * 3 * (wide ? 8 : 4)) fail_exit(EXIT_FORMAT, "chosen file size %zu, expected %llu", szc, (unsigned long long)(N * 3 * (wide ? 8 : 4)));
    const uint32_t *ch32 = (const uint32_t *)chosen; const uint64_t *ch64 = (const uint64_t *)chosen;
    auto child = [&](uint64_t s, int j) -> uint64_t {
        if (wide) return ch64[3 * s + j];
        uint32_t c = ch32[3 * s + j]; return c == NONE32 ? ~0ull : (uint64_t)c;
    };
    auto V = [&](uint64_t s) -> uint64_t { return (uint64_t)(vv[s] * 0x1p60); };   // exact: v in [0,1] checked first
    std::atomic<uint64_t> bad_order(0), bad_v(0), bad_idx(0);
    #pragma omp parallel for schedule(static)
    for (uint64_t s = 0; s < N; s++) {
        if (s + 1 < N && !(keys[s] < keys[s + 1])) bad_order++;
        double v = vv[s];
        if (!(v >= 0.0 && v <= 1.0)) bad_v++;
        for (int j = 0; j < 3; j++) { uint64_t c = child(s, j); if (c != ~0ull && c >= N) bad_idx++; }
    }
    if (bad_order || bad_v || bad_idx)
        fail_exit(EXIT_GLOBAL, "keys not increasing %llu, v outside [0,1] %llu, child index out of range %llu", (unsigned long long)bad_order.load(),
                  (unsigned long long)bad_v.load(), (unsigned long long)bad_idx.load());
    uint64_t startkey = (uint64_t)(K / 2 + 1) << 58;
    const uint64_t *sp = std::lower_bound(keys, keys + N, startkey);
    if (sp == keys + N || *sp != startkey) fail_exit(EXIT_GLOBAL, "start state missing");
    uint64_t start = (uint64_t)(sp - keys);
    if (V(start) == 0) fail_exit(EXIT_GLOBAL, "start state has V = 0");

    std::vector<Stats> st(th);
    std::vector<u128> bestnum(th, 0), bestden(th, 1);
    std::vector<uint64_t> bests(th, 0);
    std::atomic<uint64_t> vzero(0), vzero_badchild(0), firstfail(~0ull);
    auto note_fail = [&](uint64_t s) {          // keep the smallest failing index (deterministic output)
        uint64_t e = firstfail.load();
        while (s < e && !firstfail.compare_exchange_weak(e, s)) {}
    };
    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        Stats &S_ = st[tid];
        int xs[64], ys[64], cx[64], cy[64];
        Grid Sg, Eg, fl, blk;
        #pragma omp for schedule(dynamic, 4096)
        for (uint64_t s = 0; s < N; s++) {
            int n = decode(keys[s], xs, ys);
            if (n < 0) { S_.fails++; note_fail(s); continue; }
            gclear(Sg);
            Box sb = {xs[0], xs[0], ys[0], ys[0]};
            for (int i = 0; i < n; i++) {
                gset(Sg, xs[i], ys[i]);
                sb.x0 = std::min(sb.x0, xs[i]); sb.x1 = std::max(sb.x1, xs[i]);
                sb.y0 = std::min(sb.y0, ys[i]); sb.y1 = std::max(sb.y1, ys[i]);
            }
            static const int EX[3] = {1, 0, 0}, EY[3] = {0, 1, -1};
            bool okstate = true;
            u128 sum = 0;
            for (int j = 0; j < 3 && okstate; j++) {
                int tx = EX[j], ty = EY[j];
                uint64_t c = child(s, j);
                if (c == ~0ull) {
                    if (gget(Sg, tx, ty)) { S_.nochild_occ++; continue; }
                    if (tx < sb.x0 || tx > sb.x1 || ty < sb.y0 || ty > sb.y1) { okstate = false; break; }
                    Box b1 = {sb.x0 - 1, sb.x1 + 1, sb.y0 - 1, sb.y1 + 1};
                    flood(Sg, b1, tx, ty, fl);
                    if (touches_ring(fl, b1)) { okstate = false; break; }
                    S_.nochild_trap++;
                    continue;
                }
                sum += V(c);
                // (a child for an occupied target is allowed: no walk takes that slot; it only adds to the count)
                int m = decode(keys[c], cx, cy);
                if (m < 0) { okstate = false; break; }
                Eg = Sg; gset(Eg, tx, ty);
                Box eb = {std::min(sb.x0, tx), std::max(sb.x1, tx), std::min(sb.y0, ty), std::max(sb.y1, ty)};
                Box bigb = {eb.x0 - 3, eb.x1 + 3, eb.y0 - 3, eb.y1 + 3};
                int fnx[4], fny[4], nfn = 0;
                static const int NX[4] = {1, -1, 0, 0}, NY[4] = {0, 0, 1, -1};
                for (int q = 0; q < 4; q++) { int ax = tx + NX[q], ay = ty + NY[q]; if (!gget(Eg, ax, ay)) { fnx[nfn] = ax; fny[nfn] = ay; nfn++; } }
                int memo_x[256], memo_y[256], memo_v[256], nmemo = 0;
                auto dead = [&](int x, int y) -> int {        // 0 not dead, 1 (a), 2 (b), 3 (c)
                    for (int q = 0; q < nmemo; q++) if (memo_x[q] == x && memo_y[q] == y) return memo_v[q];
                    int res = 0;
                    int cnt = 0;
                    for (int q = 0; q < 4; q++) { int ax = x + NX[q], ay = y + NY[q]; if (!(ax == tx && ay == ty) && gget(Eg, ax, ay)) cnt++; }
                    if (cnt >= 3) res = 1;
                    if (!res && x >= bigb.x0 + 1 && x <= bigb.x1 - 1 && y >= bigb.y0 + 1 && y <= bigb.y1 - 1) {
                        flood(Eg, bigb, x, y, fl);
                        if (!touches_ring(fl, bigb)) res = 2;
                        else {
                            int gxv[512], gyv[512], gd[512], ng = 0;
                            for (int yy = eb.y0 - 1; yy <= eb.y1 + 1; yy++)
                                for (int xx = eb.x0 - 1; xx <= eb.x1 + 1; xx++) {
                                    if (ng >= 512) break;                         // capacity: can only cause a FAIL
                                    if (gget(Eg, xx, yy) || (xx == x && yy == y)) continue;
                                    bool nearE = false;
                                    for (int ddy = -1; ddy <= 1 && !nearE; ddy++) for (int ddx = -1; ddx <= 1; ddx++) if (gget(Eg, xx + ddx, yy + ddy)) { nearE = true; break; }
                                    if (!nearE) continue;
                                    if (!((fl.r[yy + OFF] >> (xx + OFF)) & 1ull)) continue;   // must lie in the cell's component
                                    gxv[ng] = xx; gyv[ng] = yy; gd[ng] = abs(xx - x) + abs(yy - y); ng++;
                                }
                            for (int a = 1; a < ng; a++) { int k2 = a; while (k2 > 0 && gd[k2 - 1] > gd[k2]) { std::swap(gd[k2 - 1], gd[k2]); std::swap(gxv[k2 - 1], gxv[k2]); std::swap(gyv[k2 - 1], gyv[k2]); k2--; } }
                            Grid f2;
                            for (int a = 0; a < ng && !res; a++) {
                                blk = Eg; gset(blk, gxv[a], gyv[a]);
                                flood(blk, bigb, x, y, f2);
                                if (touches_ring(f2, bigb)) continue;
                                bool tn = false;
                                for (int q = 0; q < nfn; q++) if (!(fnx[q] == gxv[a] && fny[q] == gyv[a]) && ((f2.r[fny[q] + OFF] >> (fnx[q] + OFF)) & 1ull)) { tn = true; break; }
                                if (!tn) res = 3;
                            }
                        }
                    }
                    if (nmemo < 256) { memo_x[nmemo] = x; memo_y[nmemo] = y; memo_v[nmemo] = res; nmemo++; }
                    return res;
                };
                bool found = false;
                uint64_t la = 0, lb = 0, lc = 0, le = 0;
                for (int g = 0; g < 8 && !found; g++) {
                    bool ok = true; uint64_t a1 = 0, b1c = 0, c1 = 0, e1 = 0;
                    for (int i = 0; i < m && ok; i++) {
                        int x = GX[g][0] * cx[i] + GX[g][1] * cy[i] + tx;
                        int y = GX[g][2] * cx[i] + GX[g][3] * cy[i] + ty;
                        if (gget(Eg, x, y)) { e1++; continue; }
                        int d = dead(x, y);
                        if (d == 1) a1++; else if (d == 2) b1c++; else if (d == 3) c1++; else ok = false;
                    }
                    if (ok) { found = true; la = a1; lb = b1c; lc = c1; le = e1; }
                }
                if (!found) { okstate = false; break; }
                S_.child_ok++; S_.cell_inE += le; S_.dead_a += la; S_.dead_b += lb; S_.dead_c += lc;
            }
            if (!okstate) { S_.fails++; note_fail(s); continue; }
            uint64_t Vs = V(s);
            if (Vs == 0) {
                vzero++;
                for (int j = 0; j < 3; j++) { uint64_t c = child(s, j); if (c != ~0ull && V(c) != 0) vzero_badchild++; }
            } else {
                u128 l = sum * (u128)bestden[tid], r = bestnum[tid] * (u128)Vs;
                if (l > r || (l == r && sum > 0 && s < bests[tid])) { bestnum[tid] = sum; bestden[tid] = Vs; bests[tid] = s; }
            }
        }
    }
    Stats tot;
    u128 bn = 0, bd = 1; uint64_t bs = 0;
    for (int t = 0; t < th; t++) {
        tot.nochild_occ += st[t].nochild_occ; tot.nochild_trap += st[t].nochild_trap; tot.child_ok += st[t].child_ok;
        tot.cell_inE += st[t].cell_inE; tot.dead_a += st[t].dead_a; tot.dead_b += st[t].dead_b; tot.dead_c += st[t].dead_c;
        tot.fails += st[t].fails;
        u128 l = bestnum[t] * bd, r = bn * bestden[t];           // ties: smallest state index
        if (l > r || (l == r && bestnum[t] > 0 && bests[t] < bs)) { bn = bestnum[t]; bd = bestden[t]; bs = bests[t]; }
    }
    bool acyclic = true;                         // V = 0 subgraph acyclicity (Kahn's algorithm)
    if (vzero.load() > 0) {
        std::vector<uint32_t> indeg(N, 0);
        for (uint64_t s = 0; s < N; s++) if (V(s) == 0) for (int j = 0; j < 3; j++) {
            uint64_t c = child(s, j);
            if (c != ~0ull && V(c) == 0) { if (indeg[c] == 0xffffffffu) fail_exit(EXIT_FAIL, "in-degree overflow"); indeg[c]++; }
        }
        std::vector<uint64_t> q; uint64_t seen = 0;
        for (uint64_t s = 0; s < N; s++) if (V(s) == 0 && indeg[s] == 0) q.push_back(s);
        while (!q.empty()) { uint64_t s = q.back(); q.pop_back(); seen++; for (int j = 0; j < 3; j++) { uint64_t c = child(s, j); if (c != ~0ull && V(c) == 0 && --indeg[c] == 0) q.push_back(c); } }
        acyclic = (seen == vzero.load());
    }
    bool ratio_ok = bn > 0;                      // at least one state with a child and V > 0
    u128 rn = 0, rd = 1;
    if (ratio_ok) { u128 a = bn, b = bd; while (b) { u128 t2 = a % b; a = b; b = t2; } rn = bn / a; rd = bd / a; }
    printf("check38a: N=%llu K=%d start=%llu Vzero=%llu (children of V=0 states with V>0: %llu; V=0 subgraph acyclic: %d)\n",
           (unsigned long long)N, K, (unsigned long long)start, (unsigned long long)vzero.load(), (unsigned long long)vzero_badchild.load(), (int)acyclic);
    printf("  no-child slots: occupied %llu, trapped %llu; children verified %llu; child cells in E %llu, dead (a) %llu, (b) %llu, (c) %llu\n",
           (unsigned long long)tot.nochild_occ, (unsigned long long)tot.nochild_trap, (unsigned long long)tot.child_ok,
           (unsigned long long)tot.cell_inE, (unsigned long long)tot.dead_a, (unsigned long long)tot.dead_b, (unsigned long long)tot.dead_c);
    if (tot.fails) printf("  failing states %llu (first: %llu)\n", (unsigned long long)tot.fails, (unsigned long long)firstfail.load());
    else printf("  failing states 0\n");
    if (ratio_ok) printf("  max ratio LAM = %s / %s ~ %.15f (first state attaining it: %llu)\n", u128s(rn).c_str(), u128s(rd).c_str(), (double)rn / (double)rd, (unsigned long long)bs);
    else printf("  max ratio: none (no state with V > 0 and a child)\n");
    bool claim_ok = true;
    if (haveclaim) { claim_ok = ratio_ok && (rn * cden == cnum * rd); printf("  claimed ratio %s/%s equals the computed ratio: %d\n", u128s(cnum).c_str(), u128s(cden).c_str(), (int)claim_ok); }
    bool ok = tot.fails == 0 && vzero_badchild.load() == 0 && acyclic && ratio_ok && claim_ok;
    printf("VERDICT: %s\n", ok ? "PASS" : "FAIL");
    return ok ? EXIT_PASS : EXIT_FAIL;
}
