// check_saw.cpp: independent checker for a memory-automaton upper bound on the square-lattice connective constant.
//
// Certificate (files PREFIX.keys, PREFIX.chosen, PREFIX.v):
//   keys   : N strictly increasing uint64. Key -> lattice path: n = key >> 58 cells c_0..c_{n-1}; the low 58 bits hold
//            T = sum_{i=1}^{n-2} t_i 3^{n-2-i}, t_i in {0 straight, 1 left turn, 2 right turn} at c_i; the last step
//            c_{n-2} -> c_{n-1} is +x and c_{n-1} = (0,0) (the current endpoint A).
//   chosen : N x 3 uint32; slot 0/1/2 = move of A by +x / +y / -y; value = index of the child state, or 0xFFFFFFFF.
//   v      : N doubles >= 0.
// Claim checked: for every state s and every slot, either the move is impossible or leads to a bounded tail
// (0xFFFFFFFF with: target cell occupied, or target cannot reach infinity avoiding the cells of s), or the child's cells,
// under one of the 8 lattice symmetries placing the child's endpoint on the target cell, are cells of s, the target, or
// dead cells of E = s + target: (a) >= 3 neighbours in E, (b) not connected to infinity in Z^2 \ E, or (c) separated
// from infinity and from every free neighbour of the target by one free cell g. With V_s = floor(v_s 2^60), the states
// with V > 0 satisfy sum_children V <= LAM V_s with LAM = max ratio (exact rational, printed), states with V = 0 have
// only V = 0 children and form no cycle, and the start state (straight line of K/2+1 cells) has V > 0.
// Then every n-step bridge in the +x direction (x_0 < x_i <= x_n), preceded by the fake history (the cells of the start
// state, x <= 0, y = 0), is a prefix of an infinite self-avoiding bridge; along it the states only contain visited or
// dead cells (cells no infinite continuation can visit, by induction), so every step is an automaton transition and
// b_n <= C LAM^n; with Hammersley-Welsh, mu(Z^2) = lim b_n^(1/n) <= LAM.
//
// usage: check_saw K PREFIX [THREADS]
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <algorithm>
#include <atomic>
#include <omp.h>
#include <sys/stat.h>

typedef unsigned __int128 u128;
static void fail(const char *m, uint64_t i) { fprintf(stderr, "FAIL: %s (state %llu)\n", m, (unsigned long long)i); exit(2); }

struct Pt { int x, y; };
static const int MX = 64;
static const int SX[4] = {1, 0, -1, 0}, SY[4] = {0, 1, 0, -1};

static bool path_of(uint64_t key, Pt *c, int &n) {
    n = (int)(key >> 58);
    if (n < 2 || n > 60) return false;
    uint64_t T = key & ((1ULL << 58) - 1);
    int t[MX];
    for (int i = n - 2; i >= 1; i--) { t[i] = (int)(T % 3); T /= 3; }
    if (T != 0) return false;                       // no excess digits
    int dir[MX]; dir[n - 1] = 0;                     // dir[i] = step c_{i-1} -> c_i
    for (int i = n - 2; i >= 1; i--) dir[i] = (dir[i + 1] - (t[i] == 0 ? 0 : (t[i] == 1 ? 1 : -1)) + 4) % 4;
    c[n - 1] = {0, 0};
    for (int i = n - 1; i >= 1; i--) c[i - 1] = {c[i].x - SX[dir[i]], c[i].y - SY[dir[i]]};
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (c[i].x == c[j].x && c[i].y == c[j].y) return false;
    return true;
}

// local occupancy grid around the origin
static const int W = 200, H0 = 100;
struct Box {
    std::vector<uint32_t> occ, vis; uint32_t og = 1, vg = 1; std::vector<int> q;
    Box() : occ(W * W, 0), vis(W * W, 0), q(W * W) {}
    void newocc() { if (++og == 0) { std::fill(occ.begin(), occ.end(), 0); og = 1; } }
    void newvis() { if (++vg == 0) { std::fill(vis.begin(), vis.end(), 0); vg = 1; } }
    static int id(int x, int y) { return (y + H0) * W + (x + H0); }
    bool isocc(int x, int y) const { return occ[id(x, y)] == og; }
    void put(int x, int y) { occ[id(x, y)] = og; }
};

// flood from s avoiding occupied cells (and the extra blocked cell bx,by if hasb) inside [x0,x1]x[y0,y1];
// returns true if the border of that rectangle is reached; 'stopcells' reached also counts as success when given
static bool reach_out(Box &b, int sx, int sy, int x0, int x1, int y0, int y1, bool hasb, int bx, int by,
                      const Pt *stop, int nstop) {
    if (b.isocc(sx, sy) || (hasb && sx == bx && sy == by)) return false;
    b.newvis(); int h = 0, t = 0; b.q[t++] = Box::id(sx, sy); b.vis[Box::id(sx, sy)] = b.vg;
    while (h < t) {
        int cur = b.q[h++]; int x = cur % W - H0, y = cur / W - H0;
        if (x <= x0 || x >= x1 || y <= y0 || y >= y1) return true;
        for (int k = 0; k < nstop; k++) if (stop[k].x == x && stop[k].y == y) return true;
        for (int d = 0; d < 4; d++) {
            int nx = x + SX[d], ny = y + SY[d]; int j = Box::id(nx, ny);
            if (b.vis[j] == b.vg || b.occ[j] == b.og || (hasb && nx == bx && ny == by)) continue;
            b.vis[j] = b.vg; b.q[t++] = j;
        }
    }
    return false;
}

struct Stats { uint64_t forb_occ = 0, forb_trap = 0, sub = 0, deadA = 0, deadB = 0, deadC = 0; };

static bool cell_dead(Box &b, Pt x, const Pt *E, int nE, Pt nA, int x0, int x1, int y0, int y1, Stats &st) {
    // (a) >= 3 neighbours in E other than the target nA: a continuation from nA cannot pass through x
    int cnt = 0;
    for (int d = 0; d < 4; d++) { int ax = x.x + SX[d], ay = x.y + SY[d]; if (b.isocc(ax, ay) && !(ax == nA.x && ay == nA.y)) cnt++; }
    if (cnt >= 3) { st.deadA++; return true; }
    if (!reach_out(b, x.x, x.y, x0, x1, y0, y1, false, 0, 0, nullptr, 0)) { st.deadB++; return true; }
    // candidate cut cells: the cells of one shortest path from x to the border
    Pt fn[4]; int nf = 0;
    for (int d = 0; d < 4; d++) { int ax = nA.x + SX[d], ay = nA.y + SY[d]; if (!b.isocc(ax, ay)) fn[nf++] = {ax, ay}; }
    std::vector<int> par(0);
    b.newvis(); int h = 0, t = 0; std::vector<int> prev; prev.assign(W * W, -1);
    b.q[t++] = Box::id(x.x, x.y); b.vis[Box::id(x.x, x.y)] = b.vg; int end = -1;
    while (h < t && end < 0) {
        int cur = b.q[h++]; int cx = cur % W - H0, cy = cur / W - H0;
        if (cx <= x0 || cx >= x1 || cy <= y0 || cy >= y1) { end = cur; break; }
        for (int d = 0; d < 4; d++) {
            int nx = cx + SX[d], ny = cy + SY[d]; int j = Box::id(nx, ny);
            if (b.vis[j] == b.vg || b.occ[j] == b.og) continue;
            b.vis[j] = b.vg; prev[j] = cur; b.q[t++] = j;
        }
    }
    if (end < 0) return false;
    std::vector<int> pathc;
    for (int cur = end; cur >= 0; cur = prev[cur]) pathc.push_back(cur);
    for (int cur : pathc) {
        int gx = cur % W - H0, gy = cur / W - H0;
        if (gx == x.x && gy == x.y) continue;
        if (!reach_out(b, x.x, x.y, x0, x1, y0, y1, true, gx, gy, fn, nf)) { st.deadC++; return true; }
    }
    (void)E; (void)nE; (void)par;
    return false;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: check_saw K PREFIX [THREADS]\n"); return 1; }
    int K = atoi(argv[1]); std::string P = argv[2];
    if (argc > 3) omp_set_num_threads(atoi(argv[3]));
    auto fsz = [](const std::string &f) { struct stat s; if (stat(f.c_str(), &s)) { fprintf(stderr, "missing %s\n", f.c_str()); exit(1); } return (uint64_t)s.st_size; };
    uint64_t N = fsz(P + ".keys") / 8;
    uint64_t csz = fsz(P + ".chosen");
    if ((csz != N * 12 && csz != N * 24) || fsz(P + ".v") != N * 8) { fprintf(stderr, "FAIL: file sizes\n"); return 2; }
    const uint64_t NONE = ~0ULL;
    std::vector<uint64_t> key(N); std::vector<uint64_t> ch(N * 3); std::vector<double> v(N);
    { FILE *f = fopen((P + ".keys").c_str(), "rb"); if (fread(key.data(), 8, N, f) != N) return 3; fclose(f); }
    {   // chosen: uint32 (0xFFFFFFFF = none) when N < 2^32 - 1, else uint64 (all ones = none)
        FILE *f = fopen((P + ".chosen").c_str(), "rb");
        if (csz == N * 12) {
            std::vector<uint32_t> c32(N * 3); if (fread(c32.data(), 4, N * 3, f) != N * 3) return 3;
            for (uint64_t i = 0; i < N * 3; i++) ch[i] = c32[i] == 0xFFFFFFFFu ? NONE : c32[i];
        } else if (fread(ch.data(), 8, N * 3, f) != N * 3) return 3;
        fclose(f);
    }
    { FILE *f = fopen((P + ".v").c_str(), "rb"); if (fread(v.data(), 8, N, f) != N) return 3; fclose(f); }
    for (uint64_t i = 1; i < N; i++) if (key[i] <= key[i - 1]) fail("keys not strictly increasing", i);
    std::vector<uint64_t> V(N);
    for (uint64_t i = 0; i < N; i++) {
        if (!(v[i] >= 0 && v[i] <= 1)) fail("v outside [0,1]", i);
        V[i] = (uint64_t)(v[i] * 1152921504606846976.0);      // floor(v 2^60)
    }
    uint64_t start = ((uint64_t)(K / 2 + 1)) << 58;
    uint64_t si = std::lower_bound(key.begin(), key.end(), start) - key.begin();
    if (si >= N || key[si] != start) { fprintf(stderr, "FAIL: start state missing\n"); return 2; }
    if (V[si] == 0) { fprintf(stderr, "FAIL: start state has V = 0\n"); return 2; }
    Stats tot; uint64_t bad = 0;
    // best ratio (num, den) over V > 0 states
    u128 bn = 0, bd = 1; uint64_t bi = 0;
#pragma omp parallel
    {
        Box b; Stats st; u128 ln = 0, ld = 1; uint64_t li = 0;
        Pt c[MX], cc[MX], E[MX + 1];
#pragma omp for schedule(dynamic, 1024)
        for (uint64_t i = 0; i < N; i++) {
            int n; if (!path_of(key[i], c, n)) fail("key does not decode to a self-avoiding path", i);
            int x0 = 0, x1 = 0, y0 = 0, y1 = 0;
            for (int t = 0; t < n; t++) { x0 = std::min(x0, c[t].x); x1 = std::max(x1, c[t].x); y0 = std::min(y0, c[t].y); y1 = std::max(y1, c[t].y); }
            u128 sum = 0;
            const int mdir[3] = {0, 1, 3};
            for (int sl = 0; sl < 3; sl++) {
                Pt nA = {SX[mdir[sl]], SY[mdir[sl]]};
                uint64_t cid = ch[i * 3 + sl];
                b.newocc(); for (int t = 0; t < n; t++) b.put(c[t].x, c[t].y);
                if (cid == NONE) {
                    if (b.isocc(nA.x, nA.y)) { st.forb_occ++; continue; }
                    if (!reach_out(b, nA.x, nA.y, x0 - 1, x1 + 1, y0 - 1, y1 + 1, false, 0, 0, nullptr, 0)) { st.forb_trap++; continue; }
                    fail("move without child is neither occupied nor trapped", i);
                }
                if (cid >= N) fail("child index out of range", i);
                int m; if (!path_of(key[cid], cc, m)) fail("child key invalid", cid);
                // E = cells + nA
                int nE = 0; for (int t = 0; t < n; t++) E[nE++] = c[t]; E[nE++] = nA;
                b.put(nA.x, nA.y);
                int ex0 = std::min(x0, nA.x) - 1, ex1 = std::max(x1, nA.x) + 1, ey0 = std::min(y0, nA.y) - 1, ey1 = std::max(y1, nA.y) + 1;
                bool okany = false;
                for (int g = 0; g < 8 && !okany; g++) {
                    bool ok = true; bool usedDead = false;
                    Stats st2;
                    for (int t = 0; t < m && ok; t++) {
                        int px = cc[t].x, py = cc[t].y, qx, qy;
                        switch (g) {
                            case 0: qx = px; qy = py; break;       case 1: qx = -py; qy = px; break;
                            case 2: qx = -px; qy = -py; break;     case 3: qx = py; qy = -px; break;
                            case 4: qx = px; qy = -py; break;      case 5: qx = py; qy = px; break;
                            case 6: qx = -px; qy = py; break;      default: qx = -py; qy = -px; break;
                        }
                        qx += nA.x; qy += nA.y;
                        if (b.isocc(qx, qy)) continue;
                        if (qx < -90 || qx > 90 || qy < -90 || qy > 90) { ok = false; break; }
                        usedDead = true;
                        if (!cell_dead(b, {qx, qy}, E, nE, nA, ex0, ex1, ey0, ey1, st2)) ok = false;
                    }
                    if (ok) { okany = true; if (!usedDead) st.sub++; st.deadA += st2.deadA; st.deadB += st2.deadB; st.deadC += st2.deadC; }
                }
                if (!okany) fail("child is not a valid reduction of state + move", i);
                sum += V[cid];
            }
            if (V[i] > 0) {
                if (sum * ld > ln * (u128)V[i]) { ln = sum; ld = V[i]; li = i; }
            } else if (sum != 0) fail("V = 0 state has a child with V > 0", i);
        }
#pragma omp critical
        {
            tot.forb_occ += st.forb_occ; tot.forb_trap += st.forb_trap; tot.sub += st.sub;
            tot.deadA += st.deadA; tot.deadB += st.deadB; tot.deadC += st.deadC;
            if (ln * bd > bn * ld) { bn = ln; bd = ld; bi = li; }
        }
    }
    (void)bad;
    // V = 0 states: no cycle among them (Kahn's algorithm on the subgraph)
    std::vector<uint32_t> indeg(N, 0); uint64_t nz = 0;
    (void)NONE;
    for (uint64_t i = 0; i < N; i++) if (V[i] == 0) { nz++; for (int sl = 0; sl < 3; sl++) { uint64_t c2 = ch[i * 3 + sl]; if (c2 != NONE) indeg[c2]++; } }
    std::vector<uint64_t> stk; for (uint64_t i = 0; i < N; i++) if (V[i] == 0 && indeg[i] == 0) stk.push_back(i);
    uint64_t removed = 0;
    while (!stk.empty()) {
        uint64_t i = stk.back(); stk.pop_back(); removed++;
        for (int sl = 0; sl < 3; sl++) { uint64_t c2 = ch[i * 3 + sl]; if (c2 != NONE && V[c2] == 0 && --indeg[c2] == 0) stk.push_back(c2); }
    }
    if (removed != nz) { fprintf(stderr, "FAIL: cycle among V = 0 states\n"); return 2; }
    // exact ratio bn/bd -> decimal, rounded up at 1e-12
    u128 scale = 1000000000000ULL; u128 q = (bn * scale + bd - 1) / bd;
    uint64_t ip = (uint64_t)(q / scale), fp = (uint64_t)(q % scale);
    printf("CERTIFIED k=%d states=%llu Vzero=%llu forbidden(occupied=%llu trapped=%llu) children(subset=%llu) dead cells(3nb=%llu enclosed=%llu cut=%llu)\n",
           K, (unsigned long long)N, (unsigned long long)nz, (unsigned long long)tot.forb_occ, (unsigned long long)tot.forb_trap,
           (unsigned long long)tot.sub, (unsigned long long)tot.deadA, (unsigned long long)tot.deadB, (unsigned long long)tot.deadC);
    printf("LAM = %llu.%012llu (exact ratio %llu / %llu at state %llu)  =>  mu(Z^2) <= %llu.%012llu\n",
           (unsigned long long)ip, (unsigned long long)fp, (unsigned long long)bn, (unsigned long long)bd,
           (unsigned long long)bi, (unsigned long long)ip, (unsigned long long)fp);
    return 0;
}
