#!/usr/bin/env python3
"""mutate_cert.py: negative-control mutations of a small certificate (uint32 child indices).

usage:  python3 mutate_cert.py PREFIX OUTDIR STATE
  Reads PREFIX.keys, PREFIX.chosen, PREFIX.v and writes three mutated copies into OUTDIR:
    mut_M1_dropchild : the first slot (in state order) that has a child is set to "no child";
    mut_M2_redirect  : 20 random draws (seed 7) of a slot; a slot with a child is redirected to a random state;
    mut_M3_lowv      : v of state STATE is halved (STATE = the state attaining the maximum ratio, as printed by check38a),
                       so the computed ratio no longer equals the claimed one.
  Each copy must be rejected by check38a (M3 when run with the claimed ratio of the unmutated certificate).
"""
import os
import random
import struct
import sys

if len(sys.argv) != 4:
    print('usage: python3 mutate_cert.py PREFIX OUTDIR STATE')
    sys.exit(1)
P, out, st = sys.argv[1], sys.argv[2], int(sys.argv[3])
random.seed(7)
keys = open(P + '.keys', 'rb').read()
ch = open(P + '.chosen', 'rb').read()
v = open(P + '.v', 'rb').read()
N = len(keys) // 8
if len(keys) != 8 * N or len(ch) != 12 * N or len(v) != 8 * N or not 0 <= st < N:
    print('unexpected file sizes or STATE out of range')
    sys.exit(1)
os.makedirs(out, exist_ok=True)
C = list(struct.unpack('<%dI' % (3 * N), ch))


def write(name, C2=None, v2=None):
    p = os.path.join(out, name)
    open(p + '.keys', 'wb').write(keys)
    open(p + '.chosen', 'wb').write(struct.pack('<%dI' % (3 * N), *(C2 if C2 is not None else C)))
    open(p + '.v', 'wb').write(v2 if v2 is not None else v)


C1 = list(C)                                   # M1
for i in range(N):
    for j in range(3):
        if C1[3 * i + j] != 0xffffffff:
            C1[3 * i + j] = 0xffffffff
            break
    else:
        continue
    break
write('mut_M1_dropchild', C2=C1)
C2 = list(C)                                   # M2
for _ in range(20):
    i = random.randrange(N)
    j = random.randrange(3)
    if C2[3 * i + j] != 0xffffffff:
        C2[3 * i + j] = random.randrange(N)
write('mut_M2_redirect', C2=C2)
vv = list(struct.unpack('<%dd' % N, v))        # M3
vv[st] *= 0.5
write('mut_M3_lowv', v2=struct.pack('<%dd' % N, *vv))
print('mutations written to', out)
