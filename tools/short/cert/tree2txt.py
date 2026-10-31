#!/usr/bin/env python3
"""Convert the generator's binary tree dump (cert4 tree=PREFIX) to text for the Lean encoder.
Output: "nT nF", then nT lines "type dec sc k1 q2 k2 sp w", then nF lines "c0 c[0..7]"."""
import struct, sys
src, dst = sys.argv[1], sys.argv[2]
b = open(src, 'rb').read()
o = 0
nT, = struct.unpack_from('<Q', b, o); o += 8
nodes = []
for _ in range(nT):
    ty, dec, sc, k1, q2, k2, p0, p1, sp, w = struct.unpack_from('<8BqQ', b, o); o += 24
    nodes.append((ty, dec, sc, k1, q2, k2, sp, w))
nF, = struct.unpack_from('<Q', b, o); o += 8
forms = []
for _ in range(nF):
    vals = struct.unpack_from('<q8i', b, o); o += 40
    forms.append(vals)
assert o == len(b), (o, len(b))
with open(dst, 'w') as f:
    f.write(f'{nT} {nF}\n')
    for n in nodes: f.write(' '.join(map(str, n)) + '\n')
    for v in forms: f.write(' '.join(map(str, v)) + '\n')
