#!/usr/bin/env python3
"""tree_cert.py W1 W2 a/b [--h 0.005] [--depth 8] [--stats]: search for a tree of SieveAdDefs.lean that passes
`SieveAd.ok` with the tests `SieveAd.mixTests`, in exact integers.

The route is L = a/b with the window [W1, W2]/10^5 (the grid's U1 = ceil(W1 DEN/10^5), U2 = floor(W2 DEN/10^5), as
in mirror8.py), and the tests are the Lean definitions read line by line:

  * `vanishOK`, `dropOK`, `dropCost`, `dropBOK`, `dropBCost` (SieveAdDefs.lean), with `omKw` of
    SieveCertDefs.lean;
  * `okIW`, `okJW` (SieveAdWinDefs.lean): a box surely evaluable, and a box that the bilinear rule `ibOK` passes
    at the floor V = U2 - U1;
  * `okI2`, `okJ2` (SieveAdTwoDefs.lean): the estimate in two variables on Zone7d, for a box and for the
    comparison at a floor.

A box is a list of cells (lo, hi), the newest prime first, in units of 1/DEN of exponents of x. The search is the
decomposition of harman_sieve.py without role reversal: a term is evaluated if a test passes; otherwise Buchstab's
identity at the largest floor at which the comparison is evaluated, the new prime's range cut into cells of side
h (coarser from the fifth prime on); a term of the sign + may be dropped instead, at `dropCost`, or at
`dropBCost` if its box has no term but the products n = r themselves. A term of the sign - whose box passes
nothing is cut in two, down to a least width.

It prints the tree's cost over K (the loss: below 1, the tree gives the theorem by `SieveAd.linnik_tree`) and its
size, and checks the tree with a mirror of `SieveAd.ok`. It writes nothing: the Lean files of a tree are not
generated yet.

One box is dropped at `dropBCost`: the corner where the first two primes are both near x^{1/2}, whose only terms
are the products n = p1 p2 in (x, 2x]. Its cost is the width of the first prime's top cell, up to a constant, so
the search makes that cell thin.

Values (11 November 2026; the window is the one harman_sieve.py prints for the exponent):

    219/100,   window [44260, 46717], --h 0.005:  cost/K 0.925, 849000 nodes, 25 s
    219/100,   window [44260, 46717], --h 0.004:  cost/K 0.889, 2.0 10^6 nodes
    2195/1000, window [43859, 46838], --h 0.005:  cost/K 0.841, 725000 nodes
"""
import argparse
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mirror8 as m8  # noqa: E402

DEN, K, SC = m8.DEN, m8.K, m8.SC
INF = float('inf')
cdiv, tsub, omKw = m8.cdiv, m8.tsub, m8.omKw


class Tests:
    """`SieveAd.mixTests` on the grid of the window and `IBPar ⟨Ln, Ld⟩`."""

    def __init__(self, W1, W2, Ln, Ld):
        self.U1, self.U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
        self.V = self.U2 - self.U1
        self.Ln, self.Ld = Ln, Ld
        m8.G.update(U1=self.U1, U2=self.U2, Lnum=Ln, Lden=Ld)

    # SieveAdWinDefs.lean
    def cellsIn(self, lo, bl):
        return all(lo <= c[0] <= DEN and c[1] <= DEN for c in bl)

    def okIW(self, bl):
        return len(bl) <= 13 and self.cellsIn(self.V, bl) and m8.surelyEval(bl[::-1])

    def ibOK(self, xs):
        T = m8.tstar(xs)
        if T is None:
            return False
        hs = m8.hiSum(xs)
        return any(m8.condIB(s[1] + T, hs - s[1]) or m8.condIB(s[1], hs - s[1] + T) for s in m8.subsetSums(xs))

    def okJW(self, bl, f):
        return f == self.V and len(bl) <= 13 and self.cellsIn(self.V, bl) and self.ibOK(bl[::-1])

    # SieveAdTwoDefs.lean
    def uOf(self, r1):
        Ln, Ld = self.Ln, self.Ld
        return max(cdiv(2 * Ld * DEN, 3 * Ln),
                   cdiv(tsub(62505 * Ld * DEN + 27637 * Ln, 27637 * Ln * r1), 62500 * Ln))

    def vOf(self, r2):
        Ln, Ld = self.Ln, self.Ld
        return min(tsub(tsub(3 * Ln * DEN, 2 * Ld * DEN) // (3 * Ln), r2 + 1),
                   tsub(tsub(62500 * Ln * DEN, 62505 * Ld * DEN), 34863 * Ln * (r2 + 1)) // (62500 * Ln))

    def zone(self, r1, r2, u, v):
        """The region's six inequalities of `chkJ2`, for the rests [r1 - 1, r2 + 1] and the window [u, v]."""
        Ln, Ld = self.Ln, self.Ld
        return (Ld * DEN + 2000 * Ln <= 2000 * Ln * r1 and 2 * Ld * DEN <= 3 * Ln * u
                and 2 * Ld * DEN + 3 * Ln * (r2 + 1 + v) <= 3 * Ln * DEN
                and 62505 * Ld * DEN + 27637 * Ln <= 62500 * Ln * u + 27637 * Ln * r1
                and 62505 * Ld * DEN + 62500 * Ln * v + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN
                and 125005 * Ld * DEN + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN)

    def leaves(self, D1, D2):
        Ln, Ld = self.Ln, self.Ld
        return (Ln * D1 + Ld * DEN < Ln * DEN and 2 * Ln * (D1 + D2) + Ld * DEN < 2 * Ln * DEN
                and Ln * (D1 + 2 * D2) + 2 * Ld * DEN < 2 * Ln * DEN)

    def chkJ2(self, bl, f, s0, sr, s1, e, u, v, t):
        r1, r2 = mSum(0, bl, sr), mSum(1, bl, sr)
        D1 = mSum(1, bl, s1) + (t if e else 0)
        D2 = tsub(hiSum(bl), mSum(1, bl, s1)) + (0 if e else t)
        return (0 < f and len(bl) <= 13 and all(f <= c[0] <= c[1] <= DEN for c in bl) and s0 & sr == 0
                and self.zone(r1, r2, u, v) and u + f < v and u <= t + mSum(0, bl, s0) and mSum(1, bl, s0) < v
                and self.leaves(D1, D2))

    def okJ2(self, bl, f, cfg):
        _, s0, sr, s1, e = cfg
        u, v = self.uOf(mSum(0, bl, sr)), self.vOf(mSum(1, bl, sr))
        return self.chkJ2(bl, f, s0, sr, s1, e, u, v, tsub(u, mSum(0, bl, s0)))

    def chkI2(self, bl, s0, sr):
        Ln, Ld = self.Ln, self.Ld
        r1, r2, u, v = mSum(0, bl, sr), mSum(1, bl, sr), mSum(0, bl, s0), mSum(1, bl, s0)
        return (len(bl) <= 13 and all(1 <= c[0] <= c[1] <= DEN for c in bl) and s0 & sr == 0
                and Ld * DEN + 2000 * Ln <= 2000 * Ln * r1 and 2 * Ld * DEN + 3 * Ln <= 3 * Ln * u
                and 2 * Ld * DEN + 3 * Ln * (r2 + 1 + v) <= 3 * Ln * DEN
                and 62505 * Ld * DEN + 90137 * Ln <= 62500 * Ln * u + 27637 * Ln * r1
                and 62505 * Ld * DEN + 62500 * Ln * v + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN
                and 125005 * Ld * DEN + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN)

    # SieveAdMixDefs.lean
    def okI(self, bl, cfg):
        return self.okIW(bl) if cfg[0] == 0 else self.chkI2(bl, cfg[1], cfg[2])

    def okJ(self, bl, f, cfg):
        return self.okJW(bl, f) if cfg[0] == 0 else self.okJ2(bl, f, cfg)


# SieveAdDefs.lean

def mSum(j, bl, m):
    return sum(c[j] for t, c in enumerate(bl) if m >> t & 1)


def loSum(bl):
    return sum(c[0] for c in bl)


def hiSum(bl):
    return sum(c[1] for c in bl)


def vanishOK(bl):
    if not bl:
        return False
    c, b = bl[0], bl[1:]
    return c[1] + hiSum(b) + 1 <= DEN and DEN + 1 <= c[0] + loSum(b) + c[0]


def dropOK(bl):
    return bool(bl) and all(0 < c[0] < c[1] for c in bl) and hiSum(bl) <= DEN


def trF(a, w):
    return cdiv(SC * (w * (2 * a + w)), 2 * a * (a + w))


def exF(a, w):
    return cdiv(SC * (DEN * w), a * (a + w))


def dropCost(bl):
    if not bl:
        return 0
    c, b = bl[0], bl[1:]
    tr = 1
    for d in b:
        tr *= trF(d[0], d[1] - d[0])
    return cdiv(omKw(loSum(b), c[0], tsub(c[1] + hiSum(b), c[0] + loSum(b)), c[1] - c[0])
                * (exF(c[0], c[1] - c[0]) * tr), SC ** (len(b) + 1))


def dropBOK(bl):
    """`dropBOK`: two primes at least and no term with a cofactor (the product of the primes times the last
    exceeds 2x), and the primes but the last have their product below x."""
    return (len(bl) >= 2 and all(0 < c[0] < c[1] for c in bl) and DEN + 1 <= loSum(bl) + bl[0][0]
            and hiSum(bl[1:]) < DEN)


def dropBCost(bl):
    """`dropBCost`: a bound, in units of 1/K, for the products n = r of the box in (x, 2x]: the last prime is then
    a prime of (x/r', 2x/r'], r' the product of the others, at most x/(r' log(x/r')) of them, and log(x/r') is at
    least (1 - the others' upper sum) log x."""
    b = bl[1:]
    tr = 1
    for d in b:
        tr *= trF(d[0], d[1] - d[0])
    return cdiv(K * DEN * tr, (DEN - hiSum(b)) * SC ** len(b))


def ok(T, tree, bl, par):
    """`SieveAd.ok`, on a tree as nested tuples: ('V',), ('D',), ('DB',), ('E', cfg), ('S', t, c, l, r),
    ('B', f, cfg, ch)."""
    tag = tree[0]
    if tag == 'V':
        return vanishOK(bl)
    if tag == 'D':
        return par and dropOK(bl)
    if tag == 'DB':
        return par and dropBOK(bl)
    if tag == 'E':
        return len(bl) > 0 and T.okI(bl, tree[1])
    if tag == 'S':
        _, t, c, l, r = tree
        if not (t < len(bl) and bl[t][0] < c < bl[t][1]):
            return False
        lo = bl[:t] + [(bl[t][0], c)] + bl[t + 1:]
        hi = bl[:t] + [(c, bl[t][1])] + bl[t + 1:]
        return ok(T, l, lo, par) and ok(T, r, hi, par)
    _, f, cfg, ch = tree
    return bool(bl) and 0 < f <= bl[0][0] and T.okJ(bl, f, cfg) and ok(T, ch, [(f, bl[0][1])] + bl, not par)


def cost(tree, bl):
    tag = tree[0]
    if tag == 'D':
        return dropCost(bl)
    if tag == 'DB':
        return dropBCost(bl)
    if tag == 'S':
        _, t, c, l, r = tree
        return (cost(l, bl[:t] + [(bl[t][0], c)] + bl[t + 1:]) + cost(r, bl[:t] + [(c, bl[t][1])] + bl[t + 1:]))
    if tag == 'B':
        return cost(tree[3], [(tree[1], bl[0][1])] + bl)
    return 0


# the search

def sums(j, bl):
    """The sums of the cells' ends over the sets of positions, by their masks."""
    S = [0]
    for c in bl:
        S += [x + c[j] for x in S]
    return S


class Search:
    def __init__(self, T, h, depth, wmin):
        self.T, self.depth = T, depth
        hI = int(round(h * DEN))
        self.step = {d: hI * (1 if d <= 4 else 1 + (d - 3) // 2) for d in range(1, 16)}
        self.wmin = int(round(wmin * DEN))
        self.nodes = {}
        Ln, Ld = T.Ln, T.Ld
        self.Ln, self.Ld = Ln, Ld
        self.D1max = ((Ln - Ld) * DEN - 1) // Ln
        self.T5 = (2 * Ln * DEN - Ld * DEN - 1) // (2 * Ln)
        self.T6 = (2 * Ln * DEN - 2 * Ld * DEN - 1) // Ln
        self.u2 = cdiv(2 * Ld * DEN + 3 * Ln, 3 * Ln)

    def count(self, tag):
        self.nodes[tag] = self.nodes.get(tag, 0) + 1

    def rests(self, Slo, Shi, full):
        """The sets that may be the rest: those that pass the region's two inequalities on the rest alone."""
        Ln, Ld = self.Ln, self.Ld
        out = []
        for sr in range(1, full + 1):
            if (Ld * DEN + 2000 * Ln <= 2000 * Ln * Slo[sr]
                    and 125005 * Ld * DEN + 34863 * Ln * (Shi[sr] + 1) <= 62500 * Ln * DEN):
                out.append(sr)
        return out

    def direct(self, bl, Slo, Shi, full, rests):
        """A configuration that evaluates the box outright, or None."""
        T = self.T
        if T.okIW(bl):
            return (0, 0, 0, 0, False)
        Ln, Ld = self.Ln, self.Ld
        for sr in rests:
            umin = max(self.u2, cdiv(tsub(62505 * Ld * DEN + 90137 * Ln, 27637 * Ln * Slo[sr]), 62500 * Ln))
            vmax = T.vOf(Shi[sr])
            comp = full ^ sr
            s0 = comp
            while s0:
                if Slo[s0] >= umin and Shi[s0] <= vmax and T.chkI2(bl, s0, sr):
                    return (1, s0, sr, 0, False)
                s0 = (s0 - 1) & comp
        return None

    def split_leaves(self, Shi, order, hs, t):
        """A split (s1, e) of the leaves that passes, or None: D1 in [2(hs + t) - T6, D1max], hs + t <= T5."""
        if hs + t > self.T5:
            return None
        lo, hi = 2 * (hs + t) - self.T6, self.D1max
        for e, sh in ((True, t), (False, 0)):
            # the largest sum with Shi[s1] + sh <= hi
            a, b = 0, len(order)
            while a < b:
                mid = (a + b) // 2
                if Shi[order[mid]] + sh <= hi:
                    a = mid + 1
                else:
                    b = mid
            if a and Shi[order[a - 1]] + sh >= lo:
                return order[a - 1], e
        return None

    def floor(self, bl, Slo, Shi, full, rests):
        """The largest floor at which the comparison passes the box, with its configuration; (0, None) if none."""
        T = self.T
        best, cfg = 0, None
        lomin = min((c[0] for c in bl), default=DEN)
        hs = Shi[full]
        order = sorted(range(full + 1), key=lambda m: Shi[m])
        for sr in rests:
            u, v = T.uOf(Slo[sr]), T.vOf(Shi[sr])
            f = min(lomin, v - u - 1)
            if f <= best:
                continue
            comp = full ^ sr
            s0 = comp
            while True:
                if Shi[s0] < v:
                    t = tsub(u, Slo[s0])
                    sp = self.split_leaves(Shi, order, hs, t)
                    if sp and T.chkJ2(bl, f, s0, sr, sp[0], sp[1], u, v, t):
                        best, cfg = f, (1, s0, sr, sp[0], sp[1])
                        break
                if not s0:
                    break
                s0 = (s0 - 1) & comp
        if best < T.V <= lomin and T.okJW(bl, T.V):
            best, cfg = T.V, (0, 0, 0, 0, False)
        return best, cfg

    def solve(self, bl, par, limit=INF):
        """The least cost found for the term of the box, and its tree; (INF, None) if none."""
        if vanishOK(bl):
            self.count('V')
            return 0, ('V',)
        k = len(bl)
        full = (1 << k) - 1
        Slo, Shi = sums(0, bl), sums(1, bl)
        rests = self.rests(Slo, Shi, full)
        cfg = self.direct(bl, Slo, Shi, full, rests)
        if cfg is not None:
            self.count('E')
            return 0, ('E', cfg)
        best, tree = INF, None
        if par and dropOK(bl):
            best, tree = dropCost(bl), ('D',)
        elif par and dropBOK(bl):
            best, tree = dropBCost(bl), ('DB',)
        if k < self.depth:
            f, cfgJ = self.floor(bl, Slo, Shi, full, rests)
            if cfgJ is not None:
                c, ch = self.children(bl, f, not par, min(best, limit))
                if c < best:
                    best, tree = c, ('B', f, cfgJ, ch)
        if tree is None and bl[0][1] - bl[0][0] > self.wmin:
            mid = (bl[0][0] + bl[0][1]) // 2
            c1, t1 = self.solve([(bl[0][0], mid)] + bl[1:], par)
            if c1 < INF:
                c2, t2 = self.solve([(mid, bl[0][1])] + bl[1:], par)
                if c2 < INF:
                    self.count('S')
                    return c1 + c2, ('S', 0, mid, t1, t2)
            return INF, None
        if tree is None:
            return INF, None
        self.count(tree[0])
        return best, tree

    def children(self, bl, f, par, limit):
        """The cells of the new prime in [f, hi) below the box: their total cost and the tree of cuts."""
        top = bl[0][1]
        lo_all = loSum(bl)
        # above `reg` the new prime's square is too large for a term with a cofactor
        reg = min(top, tsub(DEN, lo_all) // 2 + 2)
        cuts = [f]
        if reg > f:
            n = max(1, -(-(reg - f) // self.step[len(bl) + 1]))
            cuts += [f + (reg - f) * j // n for j in range(1, n + 1)]
        if cuts[-1] < top:
            # where the product of all the primes stays below x, a box above `reg` has no term
            b = tsub(DEN - 1, hiSum(bl))
            if cuts[-1] < b < top:
                cuts.append(b)
            cuts.append(top)
        cuts = sorted(set(cuts))
        total, trees = 0, []
        for a, b in zip(cuts, cuts[1:]):
            c, t = self.solve([(a, b)] + bl, par, limit - total)
            if c == INF:
                return INF, None
            total += c
            trees.append(t)
            if total >= limit:
                return INF, None
        # the cuts, as a chain: below cuts[i] the cell i - 1
        tree = trees[-1]
        for i in range(len(trees) - 2, -1, -1):
            self.count('S')
            tree = ('S', 0, cuts[i + 1], trees[i], tree)
        return total, tree


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('W1', type=int)
    ap.add_argument('W2', type=int)
    ap.add_argument('L', help='the exponent, as a fraction a/b')
    ap.add_argument('--h', type=float, default=0.005, help='side of the cells of the first four primes')
    ap.add_argument('--depth', type=int, default=8, help='primes in a term')
    ap.add_argument('--wmin', type=float, default=0.0005, help='least width of a cell cut for want of a test')
    a = ap.parse_args()
    Ln, Ld = map(int, a.L.split('/'))
    T = Tests(a.W1, a.W2, Ln, Ld)
    S = Search(T, a.h, a.depth, a.wmin)
    t0 = time.time()
    cfg0 = (0, 0, 0, 0, False)
    assert T.okJ([], T.V, cfg0), 'the root is not evaluated at the floor V'
    root = [(T.V, DEN // 2 + 1)]
    sys.setrecursionlimit(100000)
    # the cells of the first prime
    n = max(1, -(-(root[0][1] - T.V) // S.step[1]))
    # the window's ends, and a thin cell at the top: the corner where two primes are near x^{1/2} costs its width
    cuts = sorted({T.V + (root[0][1] - T.V) * j // n for j in range(n + 1)}
                  | {T.U1 + 1, T.U2 - 1, DEN // 2 - S.wmin})
    total, trees = 0, []
    for lo, hi in zip(cuts, cuts[1:]):
        c, t = S.solve([(lo, hi)], False)
        if c == INF:
            print(f'no tree for the first prime in [{lo / DEN:.5f}, {hi / DEN:.5f})')
            return 1
        total += c
        trees.append(t)
    tree = trees[-1]
    for i in range(len(trees) - 2, -1, -1):
        tree = ('S', 0, cuts[i + 1], trees[i], tree)
    assert ok(T, tree, root, False) and cost(tree, root) == total
    size = sum(S.nodes.values()) + len(trees) - 1
    print(f'L = {a.L}, window [{a.W1}, {a.W2}]/10^5, h = {a.h}: cost/K = {total / K:.5f}; {size} nodes '
          f'({", ".join(f"{k} {v}" for k, v in sorted(S.nodes.items()))}); checked by the mirror of SieveAd.ok; '
          f'{time.time() - t0:.0f} s')
    return 0


if __name__ == '__main__':
    sys.exit(main())
