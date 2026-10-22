#!/usr/bin/env python3
"""check38a_py.py: second, slower implementation of the check in check38a.cpp, for small memory parameters (K <= 14).

usage:  python3 check38a_py.py PREFIX K [NUM/DEN]
  Reads PREFIX.keys, PREFIX.chosen, PREFIX.v (format as in check38a.cpp). NUM/DEN = claimed exact ratio; if given, PASS
  also requires the computed exact ratio to equal it. Exit code 0 only on PASS; any failing check, missing, truncated or
  size-inconsistent file, N = 0, missing start state, malformed argument or differing claimed ratio gives a nonzero code.
  No assert statements are used, so the result does not depend on python -O.

Checks (same claim as check38a.cpp): keys strictly increasing and decoding (no excess digits) to self-avoiding paths ending
at (0,0) with last step +x; child indices < N; v in [0,1]; start state (K/2+1) << 58 present with V > 0, where
V = floor(v 2^60); for every state and slot (moves +x, +y, -y from A = (0,0)):
  no child -> target occupied, or no 4-path from the target to the outside of the state's bounding box avoiding the state;
  child    -> under some lattice symmetry placing the child's endpoint on the target, every child cell is in
              E = state + target or is dead for E: (a) >= 3 neighbours in E other than the target, (b) not connected to
              infinity in Z^2 \\ E, or (c) for some cell g not in E, its component in Z^2 \\ (E + {g}) is finite and
              contains no neighbour of the target outside E + {g} (every cell of the box around E is tried as g);
exact maximum ratio sum V_child / V_s over V_s > 0 (Fractions); V = 0 states have only V = 0 children and no cycle.
Plain breadth-first searches on sets; independent of the bitboard code of check38a.cpp.
"""
import sys
import os
import struct
from fractions import Fraction
from collections import deque


def fail(msg, code=5):
    print('FAIL:', msg)
    print('VERDICT: FAIL')
    sys.exit(code)


if len(sys.argv) not in (3, 4):
    fail('usage: python3 check38a_py.py PREFIX K [NUM/DEN]', 1)
pre = sys.argv[1]
try:
    K = int(sys.argv[2])
except ValueError:
    fail('bad K', 1)
if K < 4 or K % 2 or K > 60:
    fail('bad K', 1)
claim = None
if len(sys.argv) == 4:
    try:
        a, b = sys.argv[3].split('/')
        claim = Fraction(int(a), int(b))
        if int(a) < 0 or int(b) <= 0:
            raise ValueError
    except (ValueError, ZeroDivisionError):
        fail('bad claimed ratio (expected NUM/DEN)', 1)


def read(name):
    p = pre + name
    if not os.path.isfile(p):
        fail('missing or not a regular file: ' + p, 2)
    try:
        with open(p, 'rb') as fh:
            data = fh.read()
    except OSError as e:
        fail('cannot read %s: %s' % (p, e), 2)
    if len(data) == 0:
        fail('empty file ' + p, 2)
    return data


kb, cb, vb = read('.keys'), read('.chosen'), read('.v')
if len(kb) % 8:
    fail('keys file size not a multiple of 8', 3)
N = len(kb) // 8
if N == 0:
    fail('N = 0', 3)
wide = N >= 0xffffffff
if len(cb) != 3 * N * (8 if wide else 4) or len(vb) != 8 * N:
    fail('chosen or v file size inconsistent with N', 3)
keys = struct.unpack('<%dQ' % N, kb)
ch = struct.unpack('<%d%s' % (3 * N, 'Q' if wide else 'I'), cb)
NONE = 0xffffffffffffffff if wide else 0xffffffff
vv = struct.unpack('<%dd' % N, vb)
for i in range(N - 1):
    if not keys[i] < keys[i + 1]:
        fail('keys not strictly increasing at %d' % i, 4)
for i, v in enumerate(vv):
    if not (0.0 <= v <= 1.0):
        fail('v outside [0,1] at %d' % i, 4)
for c in ch:
    if c != NONE and c >= N:
        fail('child index out of range', 4)
V = [int(v * 2 ** 60) for v in vv]          # exact: v * 2^60 is an exact double and int() truncates (v >= 0)


def decode(key):
    """cells of the path encoded by key, or None if invalid"""
    n = key >> 58
    T = key & ((1 << 58) - 1)
    if n < 2 or n > 40:
        return None
    t = {}
    for i in range(n - 2, 0, -1):
        t[i] = T % 3
        T //= 3
    if T != 0:
        return None
    d = (1, 0)
    cells = [None] * n
    cells[n - 1] = (0, 0)
    cells[n - 2] = (-1, 0)
    for i in range(n - 2, 0, -1):
        if t[i] == 1:          # left (counter-clockwise): d_i = rotL(d_{i-1}), so d_{i-1} = rotR(d_i)
            d = (d[1], -d[0])
        elif t[i] == 2:        # right
            d = (-d[1], d[0])
        cells[i - 1] = (cells[i][0] - d[0], cells[i][1] - d[1])
    if len(set(cells)) != n:
        return None
    return cells


NB = ((1, 0), (-1, 0), (0, 1), (0, -1))


def component(start, blocked, box):
    """BFS from start over cells not in blocked; returns (set, reaches_outside_box)."""
    if start in blocked:
        return set(), False
    seen = {start}
    dq = deque([start])
    out = False
    x0, x1, y0, y1 = box
    while dq:
        x, y = dq.popleft()
        if not (x0 <= x <= x1 and y0 <= y <= y1):
            out = True
            continue
        for dx, dy in NB:
            q = (x + dx, y + dy)
            if q not in blocked and q not in seen:
                seen.add(q)
                dq.append(q)
    return seen, out


def bbox(cells):
    xs = [c[0] for c in cells]
    ys = [c[1] for c in cells]
    return min(xs), max(xs), min(ys), max(ys)


G8 = [lambda x, y: (x, y), lambda x, y: (-y, x), lambda x, y: (-x, -y), lambda x, y: (y, -x),
      lambda x, y: (x, -y), lambda x, y: (-x, y), lambda x, y: (y, x), lambda x, y: (-y, -x)]

start_key = (K // 2 + 1) << 58
if start_key not in set(keys):
    fail('start state missing', 4)
if V[keys.index(start_key)] == 0:
    fail('start state has V = 0', 4)

nfail = 0
best = None
for s in range(N):
    S = decode(keys[s])
    if S is None:
        nfail += 1
        continue
    Sset = set(S)
    bS = bbox(S)
    ok = True
    tot = 0
    for j, (tx, ty) in enumerate(((1, 0), (0, 1), (0, -1))):
        t = (tx, ty)
        c = ch[3 * s + j]
        if c == NONE:
            if t in Sset:
                continue
            comp, out = component(t, Sset, bS)
            if out:
                ok = False
                break
            continue
        tot += V[c]
        E = Sset | {t}
        bE = bbox(list(E))
        box = (bE[0] - 1, bE[1] + 1, bE[2] - 1, bE[3] + 1)
        free_t = [(tx + dx, ty + dy) for dx, dy in NB if (tx + dx, ty + dy) not in E]
        memo = {}

        def dead(p):
            if p in memo:
                return memo[p]
            r = 0
            if sum(1 for dx, dy in NB if (p[0] + dx, p[1] + dy) in E and (p[0] + dx, p[1] + dy) != t) >= 3:
                r = 1
            else:
                comp, out = component(p, E, box)
                if not out:
                    r = 2
                else:
                    for gx in range(box[0], box[1] + 1):
                        for gy in range(box[2], box[3] + 1):
                            g = (gx, gy)
                            if g in E or g == p:
                                continue
                            comp2, out2 = component(p, E | {g}, box)
                            if out2 or any(f in comp2 for f in free_t if f != g):
                                continue
                            r = 3
                            break
                        if r:
                            break
            memo[p] = r
            return r

        C = decode(keys[c])
        if C is None:
            ok = False
            break
        found = False
        for g in G8:
            good = True
            for (x, y) in C:
                gx, gy = g(x, y)
                q = (gx + tx, gy + ty)
                if q not in E and not dead(q):
                    good = False
                    break
            if good:
                found = True
                break
        if not found:
            ok = False
            break
    if not ok:
        nfail += 1
        continue
    if V[s] > 0:
        r = Fraction(tot, V[s])
        if best is None or r > best:
            best = r
    elif any(ch[3 * s + j] != NONE and V[ch[3 * s + j]] != 0 for j in range(3)):
        nfail += 1
# V = 0 subgraph acyclicity
zero = [i for i in range(N) if V[i] == 0]
indeg = {i: 0 for i in zero}
for i in zero:
    for j in range(3):
        c = ch[3 * i + j]
        if c != NONE and V[c] == 0:
            indeg[c] += 1
stack = [i for i in zero if indeg[i] == 0]
removed = 0
while stack:
    i = stack.pop()
    removed += 1
    for j in range(3):
        c = ch[3 * i + j]
        if c != NONE and V[c] == 0:
            indeg[c] -= 1
            if indeg[c] == 0:
                stack.append(c)
acyclic = removed == len(zero)
print('check38a_py: N=%d K=%d failing states %d; V=0 states %d (acyclic %s)' % (N, K, nfail, len(zero), acyclic))
if best is not None:
    print('  max ratio LAM = %d / %d ~ %.15f' % (best.numerator, best.denominator, float(best)))
claim_ok = claim is None or (best is not None and best == claim)
if claim is not None:
    print('  claimed ratio %d/%d equals the computed ratio: %s' % (claim.numerator, claim.denominator, claim_ok))
ok = nfail == 0 and acyclic and best is not None and best > 0 and claim_ok
print('VERDICT:', 'PASS' if ok else 'FAIL')
sys.exit(0 if ok else 5)
