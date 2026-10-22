// saw.cpp: memory automaton for half-plane self-avoiding walks on Z^2, with rules of the kind of Ponitz-Tittmann and Couronne.
//
// State = lattice path of cells c_0 (= B, oldest) .. c_{n-1} (= A, current endpoint); cells are visited vertices or dead
// cells (large-bridge / small-loop cells). Key = canonical turn sequence under the 8 lattice symmetries:
//   key = n << 58 | min(T, mirror(T)),  T = sum_{i=1}^{n-2} t_i 3^{n-2-i},  t_i in {0 straight, 1 left, 2 right}.
// Moves: the 3 non-reversing directions. Forbidden: revisit; 'P' nA cannot reach infinity avoiding the cells (bounded tail);
// 'e' enclosure of the oldest cell B with all newer cells as walls (rule 4.2 of Couronne); option not used for the certificate.
// Children of E = cells + nA: E when allowed; else gradual drop of the oldest cells, plus each simplification
// ('B' small bridge, 'X' large bridge with dead cell, 'b' large bridge with 1 = B, 'S' sealed small loop push-in, 'T' with
// runs >= 2) followed by the same reduction, recursion depth <= DEPTH (default 2).
// Allowed: size-loop = n + |A-B|_1 - 1 <= k (+ bonus: '3' line-like 2/4, '4' no bridge in the older half and a free
// monotone path from A to B: 2).
//
// usage: saw K RULES OUT [THREADS] [LOG2CAP]
//   writes OUT.keys (sorted uint64 keys), OUT.alive, OUT.chosen and OUT.v, prints lambda rounds.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <vector>
#include <string>
#include <algorithm>
#include <atomic>
#include <omp.h>
#include <parallel/algorithm>
#include <sys/time.h>

static double now() { struct timeval t; gettimeofday(&t, 0); return t.tv_sec + 1e-6 * t.tv_usec; }
static void die(const char *m) { fprintf(stderr, "FATAL: %s\n", m); exit(1); }

static int K = 0, DEPTH = 2, LMIN = 3, B44 = 2, EXTT = -1, GT[64], NGT = 0, GT2[64], NGT2 = 0;
static bool rP, rB, rX, rb, rS, r3, r4, re, r5, r6, r2, r7, r8, rU;
static const int DX[4] = {1, 0, -1, 0}, DY[4] = {0, 1, 0, -1};   // E N W S

struct C { int x, y; };
static const int MAXN = 64;
struct Path { int n; C c[MAXN]; };

static inline uint64_t pow3(int e) { uint64_t r = 1; while (e-- > 0) r *= 3; return r; }
static uint64_t P3[64];

static inline int dir_of(C a, C b) {      // b - a unit step
    int dx = b.x - a.x, dy = b.y - a.y;
    if (dx == 1) return 0; if (dy == 1) return 1; if (dx == -1) return 2; return 3;
}
static uint64_t encode(const Path &p) {
    int n = p.n; uint64_t T = 0, M = 0;
    int dprev = dir_of(p.c[0], p.c[1]);
    for (int i = 1; i <= n - 2; i++) {
        int d = dir_of(p.c[i], p.c[i + 1]);
        int tv = (d - dprev) & 3;                 // 0 straight, 1 left, 3 right
        int t = tv == 0 ? 0 : (tv == 1 ? 1 : 2), m = t == 0 ? 0 : 3 - t;
        T += (uint64_t)t * P3[n - 2 - i]; M += (uint64_t)m * P3[n - 2 - i];
        dprev = d;
    }
    return ((uint64_t)n << 58) | std::min(T, M);
}
static void decode(uint64_t key, Path &p) {
    int n = (int)(key >> 58); uint64_t T = key & ((1ULL << 58) - 1);
    int t[MAXN];
    for (int i = n - 2; i >= 1; i--) { t[i] = (int)(T % 3); T /= 3; }
    int d[MAXN]; d[n - 1] = 0;
    for (int i = n - 2; i >= 1; i--) { int tv = t[i] == 0 ? 0 : (t[i] == 1 ? 1 : 3); d[i] = (d[i + 1] - tv) & 3; }
    p.n = n; p.c[n - 1] = {0, 0};
    for (int i = n - 1; i >= 1; i--) { p.c[i - 1].x = p.c[i].x - DX[d[i]]; p.c[i - 1].y = p.c[i].y - DY[d[i]]; }
}
static inline int size_loop(const Path &p) { return p.n + abs(p.c[p.n - 1].x - p.c[0].x) + abs(p.c[p.n - 1].y - p.c[0].y) - 1; }
static inline bool adj(C a, C b) { return abs(a.x - b.x) + abs(a.y - b.y) == 1; }

// ---- small grid (per thread): cells within +-80 of A
static const int G = 192, OFF = 96;
struct Grid {
    uint32_t mark[G * G]; uint32_t gen = 1;
    uint32_t seen[G * G]; uint32_t sgen = 1;
    int qx[G * G], qy[G * G];
    void clear() { if (++gen == 0) { memset(mark, 0, sizeof mark); gen = 1; } }
    inline void set(C a) { mark[(a.y + OFF) * G + a.x + OFF] = gen; }
    inline bool has(C a) const { return mark[(a.y + OFF) * G + a.x + OFF] == gen; }
    inline bool hasxy(int x, int y) const { return mark[(y + OFF) * G + x + OFF] == gen; }
    void newseen() { if (++sgen == 0) { memset(seen, 0, sizeof seen); sgen = 1; } }
};
static thread_local Grid *TG = nullptr;
static Grid &grid() { if (!TG) TG = new Grid(); return *TG; }

// does s reach outside the bounding box (+1) of the marked cells listed in w[0..nw) without touching them?
static bool escapes(Grid &g, C s, const C *w, int nw) {
    if (nw == 0) return true;
    int x0 = w[0].x, x1 = w[0].x, y0 = w[0].y, y1 = w[0].y;
    for (int i = 1; i < nw; i++) { x0 = std::min(x0, w[i].x); x1 = std::max(x1, w[i].x); y0 = std::min(y0, w[i].y); y1 = std::max(y1, w[i].y); }
    x0--; x1++; y0--; y1++;
    if (!(x0 < s.x && s.x < x1 && y0 < s.y && s.y < y1)) return true;
    g.newseen(); int h = 0, tl = 0;
    g.qx[tl] = s.x; g.qy[tl] = s.y; tl++; g.seen[(s.y + OFF) * G + s.x + OFF] = g.sgen;
    while (h < tl) {
        int x = g.qx[h], y = g.qy[h]; h++;
        if (x <= x0 || x >= x1 || y <= y0 || y >= y1) return true;
        for (int k = 0; k < 4; k++) {
            int nx = x + DX[k], ny = y + DY[k]; int id = (ny + OFF) * G + nx + OFF;
            if (g.mark[id] == g.gen || g.seen[id] == g.sgen) continue;
            g.seen[id] = g.sgen; g.qx[tl] = nx; g.qy[tl] = ny; tl++;
        }
    }
    return false;
}

// ---- simplifications (cells removed only inside [lo, hi))
static void bridges(const Path &c, int lo, int hi, std::vector<Path> &out) {
    int n = c.n;
    if (rB) for (int i = 0; i + 3 <= n - 1; i++) {
        if (lo <= i + 1 && i + 2 < hi && adj(c.c[i], c.c[i + 3])) {
            Path s; s.n = 0;
            for (int t = 0; t <= i; t++) s.c[s.n++] = c.c[t];
            for (int t = i + 3; t < n; t++) s.c[s.n++] = c.c[t];
            out.push_back(s);
        }
    }
    if (rX) for (int i = rb ? 0 : 1; i < n - 5; i++) {
        if (!(lo <= i + 1 && i + 3 < hi)) continue;
        C a = c.c[i], e = c.c[i + 4];
        if (!((a.x == e.x && abs(a.y - e.y) == 2) || (a.y == e.y && abs(a.x - e.x) == 2))) continue;
        C m = {(a.x + e.x) / 2, (a.y + e.y) / 2};
        if (!adj(c.c[i + 2], m)) continue;
        bool in = false; for (int t = 0; t < n; t++) if (c.c[t].x == m.x && c.c[t].y == m.y) { in = true; break; }
        if (in) continue;
        Path s; s.n = 0;
        for (int t = 0; t <= i; t++) s.c[s.n++] = c.c[t];
        s.c[s.n++] = m;
        for (int t = i + 4; t < n; t++) s.c[s.n++] = c.c[t];
        out.push_back(s);
    }
}

// sealed loops: c[i..j] (j - i >= 9) closed by at most one free gap cell g (ends adjacent/diagonal: no gap; (2,0) and
// (2,2): the middle cell; knight (2,1) with 'U': either of the two middle cells, one interior per choice). Interior I =
// cells not reachable from the box border avoiding the loop and g; a walk can enter I only through g and is then trapped,
// so I is dead when nA is not in I. A straight run of >= LMIN cells between two inward corners is pushed into I.
static void small_loops(const Path &c, std::vector<Path> &out) {
    int n = c.n; Grid &g = grid();
    C nA = c.c[n - 1];
    for (int i = 0; i < n; i++) for (int j = i + 9; j < n; j++) {
        int dx = abs(c.c[i].x - c.c[j].x), dy = abs(c.c[i].y - c.c[j].y);
        C gaps[2]; int ng = 0; bool nogap = false;
        if (std::max(dx, dy) == 1) nogap = true;
        else if ((dx == 2 && dy == 0) || (dx == 0 && dy == 2) || (rU && dx == 2 && dy == 2)) gaps[ng++] = {(c.c[i].x + c.c[j].x) / 2, (c.c[i].y + c.c[j].y) / 2};
        else if (rU && ((dx == 2 && dy == 1) || (dx == 1 && dy == 2))) {
            int sx = c.c[j].x > c.c[i].x ? 1 : -1, sy = c.c[j].y > c.c[i].y ? 1 : -1;
            if (dx == 2) { gaps[ng++] = {c.c[i].x + sx, c.c[i].y}; gaps[ng++] = {c.c[i].x + sx, c.c[i].y + sy}; }
            else { gaps[ng++] = {c.c[i].x, c.c[i].y + sy}; gaps[ng++] = {c.c[i].x + sx, c.c[i].y + sy}; }
        } else continue;
        // with a gap, the loop end D = c_j must not be the endpoint A: a walk standing on the loop could enter the
        // interior directly and leave through the gap (Couronne, Section 3.4, asks both ends to differ from A at distance 2)
        bool Dend = (!nogap && j == n - 1);     // allowed only when no free neighbour of A lies in the interior
        for (int opt = 0; opt < (nogap ? 1 : ng); opt++) {
            C w[MAXN + 1]; int nw = 0;
            for (int t = i; t <= j; t++) w[nw++] = c.c[t];
            if (!nogap) {
                bool gin = false; for (int t = 0; t < n; t++) if (c.c[t].x == gaps[opt].x && c.c[t].y == gaps[opt].y) gin = true;
                if (gin) continue;           // gap cell occupied: covered by another (i, j) pair
                w[nw++] = gaps[opt];
            }
            int x0 = w[0].x, x1 = w[0].x, y0 = w[0].y, y1 = w[0].y;
            for (int t = 1; t < nw; t++) { x0 = std::min(x0, w[t].x); x1 = std::max(x1, w[t].x); y0 = std::min(y0, w[t].y); y1 = std::max(y1, w[t].y); }
            x0--; x1++; y0--; y1++;
            g.clear(); for (int t = 0; t < nw; t++) g.set(w[t]);
            g.newseen(); int h = 0, tl = 0;
            g.qx[tl] = x0; g.qy[tl] = y0; tl++; g.seen[(y0 + OFF) * G + x0 + OFF] = g.sgen;
            while (h < tl) {
                int x = g.qx[h], y = g.qy[h]; h++;
                for (int k = 0; k < 4; k++) {
                    int nx = x + DX[k], ny = y + DY[k];
                    if (nx < x0 || nx > x1 || ny < y0 || ny > y1) continue;
                    int id = (ny + OFF) * G + nx + OFF;
                    if (g.mark[id] == g.gen || g.seen[id] == g.sgen) continue;
                    g.seen[id] = g.sgen; g.qx[tl] = nx; g.qy[tl] = ny; tl++;
                }
            }
            auto inbox = [&](C q) { return x0 <= q.x && q.x <= x1 && y0 <= q.y && q.y <= y1; };
            auto interior = [&](C q) { return inbox(q) && !g.has(q) && g.seen[(q.y + OFF) * G + q.x + OFF] != g.sgen; };
            if (interior(nA)) continue;      // the walk is inside
            if (Dend) {
                bool touch = false;
                for (int k = 0; k < 4; k++) { C q = {nA.x + DX[k], nA.y + DY[k]}; if (interior(q)) touch = true; }
                if (touch) continue;
            }
            for (int a = i + 1; a < j; a++) {
                int nx = c.c[a - 1].x - c.c[a].x, ny = c.c[a - 1].y - c.c[a].y;
                int ddx = c.c[a + 1].x - c.c[a].x, ddy = c.c[a + 1].y - c.c[a].y;
                if (nx * ddx + ny * ddy != 0) continue;
                int b = a + 1;
                while (b < j && c.c[b + 1].x - c.c[b].x == ddx && c.c[b + 1].y - c.c[b].y == ddy) b++;
                if (b >= j || b - a - 1 < LMIN) continue;
                if (!(c.c[b + 1].x - c.c[b].x == nx && c.c[b + 1].y - c.c[b].y == ny)) continue;
                bool okp = true;
                for (int t = a + 1; t < b && okp; t++) {
                    C q = {c.c[t].x + nx, c.c[t].y + ny};
                    if (!interior(q)) okp = false;
                    for (int u = 0; u < n && okp; u++) if (c.c[u].x == q.x && c.c[u].y == q.y) okp = false;
                }
                if (!okp) continue;
                Path s; s.n = 0;
                for (int t = 0; t < a; t++) s.c[s.n++] = c.c[t];
                for (int t = a + 1; t < b; t++) s.c[s.n++] = {c.c[t].x + nx, c.c[t].y + ny};
                for (int t = b + 1; t < n; t++) s.c[s.n++] = c.c[t];
                out.push_back(s);
            }
        }
    }
}

static bool rl = false, rq = false;
static bool direct_path(const Path &c) {
    Grid &g = grid(); g.clear(); for (int t = 0; t < c.n; t++) g.set(c.c[t]);
    C B = c.c[0], A = c.c[c.n - 1];
    if (rl) {                // 'l': an L-shaped (or straight) free path from A to B
        int sx = B.x > A.x ? 1 : (B.x < A.x ? -1 : 0), sy = B.y > A.y ? 1 : (B.y < A.y ? -1 : 0);
        bool p1 = true, p2 = true;
        for (int x = A.x + sx, y = A.y; sx && x != B.x + sx; x += sx) if (!(x == B.x && y == B.y) && g.hasxy(x, y)) { p1 = false; break; }
        if (p1) for (int y = A.y + sy, x = B.x; sy && y != B.y + sy; y += sy) if (!(x == B.x && y == B.y) && g.hasxy(x, y)) { p1 = false; break; }
        for (int y = A.y + sy, x = A.x; sy && y != B.y + sy; y += sy) if (!(x == B.x && y == B.y) && g.hasxy(x, y)) { p2 = false; break; }
        if (p2) for (int x = A.x + sx, y = B.y; sx && x != B.x + sx; x += sx) if (!(x == B.x && y == B.y) && g.hasxy(x, y)) { p2 = false; break; }
        return p1 || p2;
    }
    int sx = B.x > A.x ? 1 : -1, sy = B.y > A.y ? 1 : -1, nx = abs(B.x - A.x), ny = abs(B.y - A.y);
    static thread_local std::vector<char> ok; ok.assign((nx + 1) * (ny + 1), 0);
    ok[0] = 1;
    for (int i = 0; i <= nx; i++) for (int j = 0; j <= ny; j++) {
        if (i == 0 && j == 0) continue;
        if (!(i == nx && j == ny) && g.hasxy(A.x + sx * i, A.y + sy * j)) continue;
        ok[i * (ny + 1) + j] = (i > 0 && ok[(i - 1) * (ny + 1) + j]) || (j > 0 && ok[i * (ny + 1) + j - 1]);
    }
    return ok[nx * (ny + 1) + ny];
}

static bool r9 = false; static int LCLOSE = 3;
static int line_bonus(const Path &c) {
    int L = K / 2;
    if (r9) {                // '9': the first L cells from B form a geodesic (monotone) path; +4 when the last step
        if (c.n < L + 1) return 0;   //       moved A toward B and |A-B|_1 >= LCLOSE
        if (abs(c.c[L - 1].x - c.c[0].x) + abs(c.c[L - 1].y - c.c[0].y) != L - 1) return 0;
        int dA = abs(c.c[c.n - 1].x - c.c[0].x) + abs(c.c[c.n - 1].y - c.c[0].y);
        int dP = abs(c.c[c.n - 2].x - c.c[0].x) + abs(c.c[c.n - 2].y - c.c[0].y);
        return (dA < dP && dA >= LCLOSE) ? 4 : 2;
    }
    if (c.n < L + 1) return 0;
    int ux = c.c[1].x - c.c[0].x, uy = c.c[1].y - c.c[0].y;
    for (int t = 1; t < L - 1; t++) if (c.c[t + 1].x - c.c[t].x != ux || c.c[t + 1].y - c.c[t].y != uy) return 0;
    int ax = c.c[c.n - 1].x - c.c[0].x, ay = c.c[c.n - 1].y - c.c[0].y;
    int pr = ax * ux + ay * uy, off = abs(ax * uy - ay * ux);
    if (off >= 1 && 1 <= pr && pr <= L - 1) return 4;
    return 2;
}

static bool allowed(const Path &c) {
    int s = size_loop(c);
    if (s <= K) return true;
    if (r3 && s <= K + line_bonus(c)) return true;
    if (s > K + 2 || !r4) return false;
    std::vector<Path> tmp; bridges(c, 0, c.n / 2, tmp);
    return tmp.empty() && direct_path(c);
}

static const uint64_t *SF = nullptr; static uint64_t SFN = 0;     // frozen state set of the previous pass (sorted keys)
struct KeyIndex; static bool in_frozen_idx(uint64_t k2);
static inline bool in_frozen(const Path &c) {
    if (!SF) return false;
    return in_frozen_idx(encode(c));
}
static inline bool okc(const Path &c, int bonus) {
    return allowed(c) || size_loop(c) <= K + bonus || in_frozen(c);
}
static bool rZ = false, rW = false;
static void reduce(const Path &c, int depth, int bonus, std::vector<Path> &out) {
    if (okc(c, bonus)) { out.push_back(c); return; }
    Path d = c; int off = 0;
    while (true) {
        Path t; t.n = d.n - off; for (int i = 0; i < t.n; i++) t.c[i] = d.c[off + i];
        // 'Z': truncations stop only at base size or at a state of the previous pass (no own bonus)
        if (rZ ? (size_loop(t) <= K + bonus || in_frozen(t)) : okc(t, bonus)) { out.push_back(t); break; }
        off++;
    }
    if (depth < DEPTH) {
        std::vector<Path> sims; bridges(c, 0, c.n, sims);
        if (rS) small_loops(c, sims);
        for (auto &s : sims) reduce(s, depth + 1, bonus, out);
    }
}
static bool lacks_simpl(const Path &c) {        // no bridge removable in the older half, free monotone path A -> B
    std::vector<Path> tmp; bridges(c, 0, c.n / 2, tmp);
    if (!tmp.empty()) return false;
    if (rq) { small_loops(c, tmp); if (!tmp.empty()) return false; }   // 'q': and no small-loop simplification
    return direct_path(c);
}

// children of a state: for each of the 3 moves, either forbidden (empty) or the deduplicated candidate keys in order
static void expand(uint64_t key, std::vector<uint64_t> ch[3], bool ok[3]) {
    Path p; decode(key, p);
    Grid &g = grid();
    C A = p.c[p.n - 1], prev = p.c[p.n - 2];
    int mi = 0;
    int pbonus = (r5 && lacks_simpl(p)) ? 2 : 0;
    for (int d = 0; d < 4; d++) {
        C nA = {A.x + DX[d], A.y + DY[d]};
        if (nA.x == prev.x && nA.y == prev.y) continue;
        int slot = mi++;
        ch[slot].clear(); ok[slot] = false;
        g.clear(); for (int t = 0; t < p.n; t++) g.set(p.c[t]);
        if (g.has(nA)) continue;
        if (rP && !escapes(g, nA, p.c, p.n)) continue;
        if (re) {
            g.clear(); for (int t = 1; t < p.n; t++) g.set(p.c[t]); g.set(nA);
            C w[MAXN + 1]; int nw = 0; for (int t = 1; t < p.n; t++) w[nw++] = p.c[t]; w[nw++] = nA;
            if (!escapes(g, p.c[0], w, nw)) continue;
        }
        Path E = p; E.c[E.n++] = nA;
        if (E.n >= MAXN) die("path too long");
        int bonus = pbonus;
        if (r6 && lacks_simpl(E)) bonus = 2;
        int dbonus = 0;                                   // bonus for the direct child E only ('7': 4.4, '8': 4.3)
        if (r7 && NGT2 && !lacks_simpl(E)) {   // SAW_GT2: bonus by slack for E that HAS simplifications
            int dAB = abs(E.c[E.n - 1].x - E.c[0].x) + abs(E.c[E.n - 1].y - E.c[0].y);
            int sl = (E.n - 1 - dAB) / 2; dbonus = GT2[std::min(sl, NGT2 - 1)];
        } else
        if (r7 && lacks_simpl(E)) {
            dbonus = B44;
            if (EXTT >= 0) {     // SAW_EXT=t: bonus B44 only for nearly monotone E (|A-B|_1 >= n-1-2t), else 2
                int dAB = abs(E.c[E.n - 1].x - E.c[0].x) + abs(E.c[E.n - 1].y - E.c[0].y);
                if (dAB < E.n - 1 - 2 * EXTT) dbonus = 2;
            }
            if (NGT) {           // SAW_GT=g0,g1,...: bonus by slack index ((n-1) - |A-B|_1)/2, last value repeats
                int dAB = abs(E.c[E.n - 1].x - E.c[0].x) + abs(E.c[E.n - 1].y - E.c[0].y);
                int sl = (E.n - 1 - dAB) / 2; dbonus = GT[std::min(sl, NGT - 1)];
            }
        }
        if (r8) dbonus = std::max(dbonus, line_bonus(E));
        std::vector<Path> cands;
        if (dbonus && size_loop(E) <= K + dbonus) { cands.push_back(E); if (rW) reduce(E, 0, 0, cands); }
        else reduce(E, 0, bonus, cands);
        for (auto &c : cands) {
            uint64_t k2 = encode(c);
            if (std::find(ch[slot].begin(), ch[slot].end(), k2) == ch[slot].end()) ch[slot].push_back(k2);
        }
        ok[slot] = true;
    }
}

// ---- concurrent hash set of keys
struct HSet {
    uint64_t *t = nullptr; uint64_t mask = 0;
    void init(int lg) { size_t n = 1ULL << lg; t = (uint64_t *)calloc(n, 8); if (!t) die("calloc hash"); mask = n - 1; }
    static inline uint64_t h(uint64_t x) { x ^= x >> 31; x *= 0x7fb5d329728ea185ULL; x ^= x >> 27; x *= 0x81dadef4bc2dd44dULL; x ^= x >> 33; return x; }
    bool insert(uint64_t k) {      // true if newly inserted
        uint64_t i = h(k) & mask;
        while (true) {
            uint64_t cur = __atomic_load_n(&t[i], __ATOMIC_RELAXED);
            if (cur == k) return false;
            if (cur == 0) {
                uint64_t z = 0;
                if (__atomic_compare_exchange_n(&t[i], &z, k, false, __ATOMIC_ACQ_REL, __ATOMIC_RELAXED)) return true;
                if (z == k) return false;
                continue;
            }
            i = (i + 1) & mask;
        }
    }
};

// ---- sorted-key index: sample every 256th key; lookup = binary search in the samples, then in one block
struct KeyIndex {
    const uint64_t *k = nullptr; uint64_t n = 0; std::vector<uint64_t> smp;
    void build(const uint64_t *keys, uint64_t N) {
        k = keys; n = N; smp.resize((N + 255) / 256);
#pragma omp parallel for schedule(static)
        for (uint64_t i = 0; i < smp.size(); i++) smp[i] = keys[i * 256];
    }
    inline uint64_t find(uint64_t key) const {         // index of key, or n if absent
        if (n == 0) return n;
        uint64_t b = std::upper_bound(smp.begin(), smp.end(), key) - smp.begin();
        if (b == 0) return n;
        uint64_t lo = (b - 1) * 256, hi = std::min(n, lo + 256);
        const uint64_t *q = std::lower_bound(k + lo, k + hi, key);
        return (q != k + hi && *q == key) ? (uint64_t)(q - k) : n;
    }
};
static KeyIndex SFI;
static bool in_frozen_idx(uint64_t k2) { return SFI.find(k2) < SFI.n; }

template <typename IdT>
static void rows_and_solve(uint64_t *keys, uint64_t N, const std::string &out, const std::string &R, double t0) {
    const IdT NONE = (IdT)~(IdT)0;
    KeyIndex KI; KI.build(keys, N);
    // phase A: candidate counts per move (0 = forbidden)
    std::vector<uint8_t> cnt(N * 3, 0);
    std::vector<uint64_t> soff(N + 1, 0);
#pragma omp parallel
    {
        std::vector<uint64_t> ch[3]; bool okm[3];
#pragma omp for schedule(dynamic, 1024)
        for (uint64_t i = 0; i < N; i++) {
            expand(keys[i], ch, okm);
            uint64_t tot = 0;
            for (int m = 0; m < 3; m++) {
                size_t c = okm[m] ? ch[m].size() : 0;
                if (c > 255) die("more than 255 candidates");
                cnt[i * 3 + m] = (uint8_t)c; tot += c;
            }
            soff[i + 1] = tot;
        }
    }
    for (uint64_t i = 0; i < N; i++) soff[i + 1] += soff[i];
    IdT *cand = (IdT *)malloc(soff[N] * sizeof(IdT) + 8); if (!cand) die("malloc cand");
    fprintf(stderr, "rows: %llu candidate entries, %zu-byte ids (%.1fs)\n", (unsigned long long)soff[N], sizeof(IdT), now() - t0);
    // phase B: fill candidate ids
#pragma omp parallel
    {
        std::vector<uint64_t> ch[3]; bool okm[3];
#pragma omp for schedule(dynamic, 1024)
        for (uint64_t i = 0; i < N; i++) {
            expand(keys[i], ch, okm);
            uint64_t q = soff[i];
            for (int m = 0; m < 3; m++) {
                size_t c = okm[m] ? ch[m].size() : 0;
                if (c != cnt[i * 3 + m]) die("nondeterministic expansion");
                for (size_t t = 0; t < c; t++) {
                    uint64_t id = KI.find(ch[m][t]);
                    if (id >= N) die("closure failure");
                    cand[q++] = (IdT)id;
                }
            }
        }
    }
    fprintf(stderr, "rows filled (%.1fs)\n", now() - t0);
    auto mstart = [&](uint64_t i, int m) { uint64_t q = soff[i]; for (int t = 0; t < m; t++) q += cnt[i * 3 + t]; return q; };
    // ---- prune dead states (no move with an alive candidate)
    std::vector<uint8_t> alive(N, 1);
    for (bool chg = true; chg;) {
        chg = false;
#pragma omp parallel for schedule(static) reduction(||:chg)
        for (uint64_t i = 0; i < N; i++) {
            if (!alive[i]) continue;
            bool any = false;
            for (uint64_t q = soff[i]; q < soff[i + 1]; q++) if (alive[cand[q]]) { any = true; break; }
            if (!any) { alive[i] = 0; chg = true; }
        }
    }
    uint64_t NA = 0; for (uint64_t i = 0; i < N; i++) NA += alive[i];
    fprintf(stderr, "live states %llu (%.1fs)\n", (unsigned long long)NA, now() - t0);
    // ---- chosen candidate index per move (255 = forbidden): first alive candidate, else the first (dead) one
    std::vector<uint8_t> cho(N * 3, 255);
#pragma omp parallel for schedule(static)
    for (uint64_t i = 0; i < N; i++) for (int m = 0; m < 3; m++) {
        uint64_t q0 = mstart(i, m); int c = cnt[i * 3 + m]; if (!c) continue;
        int pick = 0; for (int t = 0; t < c; t++) if (alive[cand[q0 + t]]) { pick = t; break; }
        cho[i * 3 + m] = (uint8_t)pick;
    }
    std::vector<double> v(N, 0.0), w(N, 0.0);
    for (uint64_t i = 0; i < N; i++) v[i] = alive[i] ? 1.0 : 0.0;
    double lam_hi = 0, lam_lo = 0;
    int rounds = getenv("SAW_ROUNDS") ? atoi(getenv("SAW_ROUNDS")) : 12;
    double tol = getenv("SAW_TOL") ? atof(getenv("SAW_TOL")) : 1e-13;
    for (int rd = 0; rd < rounds; rd++) {
        int it;
        for (it = 0; it < 100000; it++) {
            double mx = 0, rlo = 1e300, rhi = 0;
#pragma omp parallel for schedule(static) reduction(max:mx) reduction(min:rlo) reduction(max:rhi)
            for (uint64_t i = 0; i < N; i++) {
                if (!alive[i]) continue;
                double s = 0; uint64_t q = soff[i];
                for (int m = 0; m < 3; m++) { int c = cnt[i * 3 + m]; if (c) s += v[cand[q + cho[i * 3 + m]]]; q += c; }
                w[i] = s; double r = s / v[i];
                if (s > mx) mx = s; if (r < rlo) rlo = r; if (r > rhi) rhi = r;
            }
            double inv = 1.0 / mx;
#pragma omp parallel for schedule(static)
            for (uint64_t i = 0; i < N; i++) v[i] = w[i] * inv;
            lam_lo = rlo; lam_hi = rhi;
            if (rhi / rlo - 1 < tol) break;
        }
        uint64_t changed = 0;
#pragma omp parallel for schedule(static) reduction(+:changed)
        for (uint64_t i = 0; i < N; i++) {
            uint64_t q = soff[i];
            for (int m = 0; m < 3; m++) {
                int c = cnt[i * 3 + m];
                if (c) {
                    int best = -1; double bv = 1e300;
                    for (int t = 0; t < c; t++) { uint64_t cc = cand[q + t]; if (alive[cc] && v[cc] < bv) { bv = v[cc]; best = t; } }
                    if (best >= 0 && best != cho[i * 3 + m]) { cho[i * 3 + m] = (uint8_t)best; changed++; }
                }
                q += c;
            }
        }
        fprintf(stderr, "   round %d: lambda in [%.12f, %.12f] (%d its), %llu choices changed (%.1fs)\n", rd, lam_lo, lam_hi, it,
                (unsigned long long)changed, now() - t0);
        if (!changed) break;
    }
    { double vmin = 1e300; for (uint64_t i = 0; i < N; i++) if (alive[i]) vmin = std::min(vmin, v[i]);
      fprintf(stderr, "min v over live states: %.3e\n", vmin); }
    printf("RESULT k=%d rules=%s states=%llu live=%llu lambda<=%.12f\n", K, R.c_str(), (unsigned long long)N, (unsigned long long)NA, lam_hi);
    fflush(stdout);
    // ---- outputs: keys, alive, chosen child ids (IdT per move, all ones = forbidden), v
    FILE *f = fopen((out + ".keys").c_str(), "wb"); fwrite(keys, 8, N, f); fclose(f);
    f = fopen((out + ".alive").c_str(), "wb"); fwrite(alive.data(), 1, N, f); fclose(f);
    {
        const uint64_t B = 1 << 20; std::vector<IdT> buf(3 * B);
        f = fopen((out + ".chosen").c_str(), "wb");
        for (uint64_t lo = 0; lo < N; lo += B) {
            uint64_t hi = std::min(N, lo + B);
#pragma omp parallel for schedule(static)
            for (uint64_t i = lo; i < hi; i++) {
                uint64_t q = soff[i];
                for (int m = 0; m < 3; m++) { int c = cnt[i * 3 + m]; buf[(i - lo) * 3 + m] = c ? cand[q + cho[i * 3 + m]] : NONE; q += c; }
            }
            fwrite(buf.data(), sizeof(IdT), (hi - lo) * 3, f);
        }
        fclose(f);
    }
    f = fopen((out + ".v").c_str(), "wb"); fwrite(v.data(), 8, N, f); fclose(f);
    fprintf(stderr, "outputs written (%.1fs)\n", now() - t0);
    free(cand);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: saw K RULES OUT [THREADS] [LOG2CAP]\n"); return 1; }
    for (int i = 0; i < 64; i++) P3[i] = pow3(i);
    K = atoi(argv[1]); std::string R = argv[2]; std::string out = argv[3];
    int th = argc > 4 ? atoi(argv[4]) : omp_get_max_threads(); omp_set_num_threads(th);
    int lg = argc > 5 ? atoi(argv[5]) : 24;
    auto has = [&](char ch) { return R.find(ch) != std::string::npos; };
    rP = has('P'); rB = has('B'); rX = has('X'); rb = has('b'); rS = has('S'); r3 = has('3'); r4 = has('4'); re = has('e');
    r5 = has('5'); r6 = has('6'); r2 = has('2'); r7 = has('7'); r8 = has('8'); rU = has('U'); rl = has('l'); rq = has('q'); r9 = has('9'); rZ = has('Z'); rW = has('W'); if (getenv("SAW_LCLOSE")) LCLOSE = atoi(getenv("SAW_LCLOSE"));
    if (has('T')) LMIN = 2;
    if (getenv("SAW_DEPTH")) DEPTH = atoi(getenv("SAW_DEPTH"));
    if (getenv("SAW_B44")) B44 = atoi(getenv("SAW_B44"));
    if (getenv("SAW_EXT")) EXTT = atoi(getenv("SAW_EXT"));
    if (getenv("SAW_GT2")) { char *q = getenv("SAW_GT2"); while (*q && NGT2 < 64) { GT2[NGT2++] = (int)strtol(q, &q, 10); if (*q == ',') q++; } }
    if (getenv("SAW_GT")) { char *q = getenv("SAW_GT"); while (*q && NGT < 64) { GT[NGT++] = (int)strtol(q, &q, 10); if (*q == ',') q++; } }
    double t0 = now();
    // ---- discovery (pass 1; with '2' a second discovery whose reductions may stop at any pass-1 state)
    size_t cap = (size_t)(0.75 * (1ULL << lg));
    uint64_t *keys = (uint64_t *)malloc(cap * 8); if (!keys) die("malloc keys");
    uint64_t *keys1 = nullptr; uint64_t N1 = 0;
    Path s0; s0.n = K / 2 + 1; for (int i = 0; i < s0.n; i++) s0.c[i] = {i - s0.n + 1, 0};
    uint64_t N = 0;
    int npass = r2 ? (getenv("SAW_PASSES") ? atoi(getenv("SAW_PASSES")) : 2) : 1;
    for (int pass = 1; pass <= npass; pass++) {
        HSet hs; hs.init(lg);
        keys[0] = encode(s0); hs.insert(keys[0]);
        std::atomic<uint64_t> cnt(1);
        uint64_t lo = 0; int wave = 0;
        while (lo < cnt.load()) {
            uint64_t hi = cnt.load();
#pragma omp parallel
            {
                std::vector<uint64_t> ch[3]; bool okm[3];
#pragma omp for schedule(dynamic, 256)
                for (uint64_t i = lo; i < hi; i++) {
                    expand(keys[i], ch, okm);
                    for (int m = 0; m < 3; m++) if (okm[m]) for (uint64_t k2 : ch[m]) if (hs.insert(k2)) {
                        uint64_t id = cnt.fetch_add(1);
                        if (id >= cap) die("hash capacity exceeded: raise LOG2CAP");
                        keys[id] = k2;
                    }
                }
            }
            lo = hi; wave++;
        }
        N = cnt.load();
        free(hs.t);
        __gnu_parallel::sort(keys, keys + N);
        fprintf(stderr, "k=%d rules=%s pass %d: %llu states, %d waves (%.1fs)\n", K, R.c_str(), pass, (unsigned long long)N, wave, now() - t0);
        if (pass < npass) {
            if (keys1) free(keys1);
            keys1 = (uint64_t *)malloc(N * 8); memcpy(keys1, keys, N * 8); N1 = N;
            SF = keys1; SFN = N1; SFI.build(keys1, N1);
        }
    }
    if (N < 0xFFFFFFFFULL) rows_and_solve<uint32_t>(keys, N, out, R, t0);
    else rows_and_solve<uint64_t>(keys, N, out, R, t0);
    return 0;
}
