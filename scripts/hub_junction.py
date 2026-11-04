#!/usr/bin/env python3
"""hub_junction.py [N]: one junction shared by all the shells? Uncertified numerics; CI does not run it.

The orbit Gram matrix `G(m, n) = √(mn)·K_H(m/n)` of `docs/ball-conjecture.md` (computed from the primes by
`ball_orbit.gram`) is cut into dyadic shells `[2^k, 2^{k+1})`. The `positivity-search` branch found that the coupling
between shells has no low-rank common junction (about twelve directions carry 95% of its energy, at every size). This
script tests the next version of the idea: a hub `H`, a set of indices shared by every shell, through which all the
coupling might pass. Conditioning on the hub replaces the form on the shells by the Schur complement
`S = G_SS − G_SH G_HH⁻¹ G_HS`, the form on the orthogonal complement of the hub's vectors, and the question is whether
the shells decouple in `S`. For each hub it prints `λ_min(S)`; the contraction norm `‖A^{−1/2}BC^{−1/2}‖` of each pair
of shells (below `1` exactly when the pair is positive definite, and the junction margin of the branch is `1` minus it)
as its maximum, its mean and its values on adjacent shells; the share of the off-shell energy `‖S − blockdiag S‖_F²`
left relative to no hub; and the number of singular directions of the off-shell part that carry 95% and 99% of its
energy. Hubs: the first `h` integers, `h` random integers below the first shell (a control), and the smallest primes.
`docs/research-opportunities.md` §6.1 records what it shows. Needs numpy and scipy.
"""
import os
import sys

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ball_orbit as bo  # noqa: E402

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2047
G = bo.gram(N)                                             # index i <-> n = i + 1
FIRST = 64                                                 # the shells start here; hubs stay below
shells = [(2 ** k, min(2 ** (k + 1) - 1, N)) for k in range(6, N.bit_length())]
idx = lambda a, b: np.arange(a - 1, b)                     # the indices of n in [a, b]
S_idx = np.concatenate([idx(a, b) for a, b in shells])
offsets = np.cumsum([0] + [b - a + 1 for a, b in shells])


def schur(H):
    if len(H) == 0:
        return G[np.ix_(S_idx, S_idx)]
    GHH, GSH = G[np.ix_(H, H)], G[np.ix_(S_idx, H)]
    return G[np.ix_(S_idx, S_idx)] - GSH @ np.linalg.solve(GHH, GSH.T)


def block(S, i, j):
    return S[offsets[i]:offsets[i + 1], offsets[j]:offsets[j + 1]]


def contraction(S, i, j):
    La, Lc = np.linalg.cholesky(block(S, i, i)), np.linalg.cholesky(block(S, j, j))
    T = sl.solve_triangular(La, sl.solve_triangular(Lc, block(S, i, j).T, lower=True).T, lower=True)
    return sl.svdvals(T)[0]


def offshell(S):
    O = S.copy()
    for i in range(len(shells)):
        O[offsets[i]:offsets[i + 1], offsets[i]:offsets[i + 1]] = 0
    return O


def report(name, H, base):
    S = schur(H)
    lam = sl.eigh(S, eigvals_only=True, subset_by_index=[0, 0])[0]
    pairs = [contraction(S, i, j) for i in range(len(shells)) for j in range(i + 1, len(shells))]
    adjacent = [contraction(S, i, i + 1) for i in range(len(shells) - 1)]
    left = np.linalg.norm(offshell(S)) ** 2 / base
    sv = sl.svdvals(offshell(S))
    c = np.cumsum(sv ** 2) / np.sum(sv ** 2)
    k95, k99 = np.searchsorted(c, 0.95) + 1, np.searchsorted(c, 0.99) + 1
    print(f"{name:28s} lambda_min {lam:8.2e}  contraction max {max(pairs):.4f} mean {np.mean(pairs):.4f} "
          f"adjacent {' '.join(f'{x:.3f}' for x in adjacent)}  off-shell energy left {left:.3f}  "
          f"k95 {k95:3d}  k99 {k99:3d}", flush=True)


print(f"N = {N}; shells {shells}; hubs below {FIRST}")
base = np.linalg.norm(offshell(G[np.ix_(S_idx, S_idx)])) ** 2
report("no hub", np.array([], dtype=int), base)
for h in (4, 8, 16, 32, FIRST - 1):
    report(f"first {h} integers", idx(1, h), base)
rng = np.random.default_rng(1)
for h in (16, 32):
    report(f"{h} random integers < {FIRST}", np.sort(rng.choice(np.arange(FIRST - 1), size=h, replace=False)), base)
primes = [p for p in bo.primes_upto(FIRST - 1)]
report(f"the {len(primes)} primes < {FIRST}", np.array(primes) - 1, base)
