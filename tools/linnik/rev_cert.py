#!/usr/bin/env python3
"""rev_cert.py --try H DEPTH KAPPA DEPTHR HR HQ [W1 W2 a/b] [--norev]: the search with role reversal, and the base
of the searches of `fill_cert.py`, `flip_cert.py` and `hint_cert.py`.

The search of `tree_cert.py` (a tree of Buchstab steps with the window's tests and those of the estimate in two
variables) has here one more node, **role reversal** (`lib/pnt/SieveAdRevDefs.lean`): a term of three primes
p1 > p2 > p3 of the sign −, whose numbers are n = p1 p2 p3 m with m a prime or a product of two, is bounded by the
sums over r' = n/p1 of the n that are rough at p3's least value, each a term of the usual kind for the atoms of r'
under a condition on their product, with its own tree. `SieveAd.solveG` is `tree_cert.py`'s search with the tests
of its nodes as parameters (`SieveAd.Ops`), and `SieveAd.revCost` the cost of a reversal. This script is the search
in Python:

  * `tree_cert.py`'s tests, proposals and costs (`Tests`, `Search`);
  * `Ops`, `nodeG`, `solveG` (with `stepG`); `vanishK`, `dropK`, `opsK`; `rootJ`, `famCost`, `cellQ`, `revOK`,
    `revCost` (SieveAdRevDefs.lean), definition by definition;
  * the reversal as the node `alt` of the first prime's tree, and a strategy whose cells shrink with the exponent,
    whose Lean, that of the theorem at L = 218/100, is in the git history at commit 76abe3c.

The search treats a box as `tree_cert.py`'s does, with the new prime's range cut into cells of side at most H and at
most the exponent over KAPPA, and for a box of three primes of the sign − it takes the reversal's cost if that is
below the cost of Buchstab's identity. A reversal's trees have chains of fewer than DEPTHR primes, in cells of side
at most HR (twice that from the second prime of a chain on), and the smaller prime of a cofactor of two primes is in
cells of side at most HQ. `pred` predicts the kernel's time on a part of the search from the search's work in it.
`cell`, `box`, `bool_` and `chain` write Lean text for `hint_cert.py`.

What is here is what the other scripts import, and `--try`, which runs the search with the given parameters, on
the window [W1, W2]/10^5 at L = a/b (by default [45073, 46472]/10^5 at 218/100; without the reversal, with
`--norev`), and prints its cost.

Values (11 November 2026), at 218/100: `--try 0.006 6 10 3 0.012 0.02`: 0.91849 K on 1063672 boxes, with 3664
reversals taken of 8185 tried; with `--norev`, 1.16057 K. `--try 0.006 6 10 4 0.006 0.006`: 0.90043, 1309777 boxes;
`--try 0.007 6 10 3 0.009 0.012`: 1.01637; `--try 0.006 5 10 3 0.009 0.012`: 2.10153; `--try 0.006 6 10 2 0.012
0.02`: 1.05710; `--try 0.006 6 10 4 0.006 0.006 45481 46349 2175/1000`: 1.05257;
`--try 0.005 6 10 4 0.006 0.006 45481 46349 2175/1000`: 0.98482, 2631876 boxes;
`--try 0.006 6 10 4 0.006 0.006 45892 46226 217/100`: 1.26965;
`--try 0.005 6 10 4 0.006 0.006 45892 46226 217/100`: 1.18333;
`--try 0.004 7 12 4 0.005 0.005 45892 46226 217/100`: 1.03938, 10140441 boxes.

Needs Python 3 only. Two minutes.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
from tree_cert import (DEN, K, SC, BIG, cdiv, tsub, omKw, loSum, hiSum, vanishOK, dropC, trF, exF, wrap,  # noqa: E402
                       nat)

# the route of `--try` when none is given, the least width of a cell that is cut for want of a test, and the fuel
LNUM, LDEN, W1, W2 = 218, 100, 45073, 46472
WMIN, FUEL = round(0.0005 * DEN), 200
CAPK = 64 * K



# SieveAdRevDefs.lean, definition by definition, and the strategy's cuts (`geoCuts`, `cutsQ`)

def cellsOK(bl):
    return all(0 < c[0] < c[1] for c in bl)


def trProd(bl):
    r = 1
    for c in bl:
        r *= trF(c[0], tsub(c[1], c[0]))
    return r


def chainOf(na, bl):
    return bl[:tsub(len(bl), na)]


def vanishK(ctx, ch):
    if not ch:
        return False
    c, b = ch[0], ch[1:]
    return c[1] + hiSum(b) + 1 <= ctx[0] and ctx[1] + 1 <= c[0] + loSum(b) + c[0]


def dropK(ctx, ch, par):
    if not ch:
        return None
    c, b = ch[0], ch[1:]
    if par and cellsOK(ch) and c[1] + hiSum(b) + 1 <= ctx[0]:
        return cdiv(omKw(loSum(b) + tsub(DEN, ctx[1]), c[0],
                         tsub(c[1] + hiSum(b), c[0] + loSum(b)) + (tsub(ctx[1], ctx[0]) + 1), tsub(c[1], c[0]))
                    * (exF(c[0], tsub(c[1], c[0])) * trProd(b)), SC ** (len(b) + 1))
    return None


def emptyBox(bl):
    if not bl:
        return False
    c, b = bl[0], bl[1:]
    if c[1] <= c[0]:
        return True
    if not b:
        return False
    return b[0][1] <= c[0] or emptyBox(b)


def trBut(i, bl):
    if not bl:
        return 1
    if i == 0:
        return trProd(bl[1:])
    return trF(bl[0][0], tsub(bl[0][1], bl[0][0])) * trBut(i - 1, bl[1:])


def penK(ctx, y):
    return tsub(cdiv(omKw(tsub(tsub(DEN, ctx[1]), y), y, tsub(ctx[1], ctx[0]), 1) * DEN, y), K * DEN // ctx[1])


def bdK(ctx, y):
    return cdiv(omKw(tsub(tsub(tsub(DEN, ctx[1]), y), 1), y, tsub(ctx[1], ctx[0]) + 2, 1) * DEN, y)


def addL(c1, rest, lim):
    return c1 if lim <= c1 else c1 + rest(lim - c1)


def revOK(bl):
    if len(bl) != 3:
        return False
    c3, c2, c1 = bl
    return (cellsOK(bl) and c2[1] <= c1[0] and c1[1] + c2[1] + c3[1] <= DEN
            and tsub(DEN + 1, c1[0] + c2[0] + c3[0]) <= 3 * c3[0] and c3[0] <= c1[0])


def geoCuts(kappa, st, reg, n, c):
    out = []
    while n > 0 and c < reg:
        c = c + max(1, min(st, c // kappa))
        out.append(min(c, reg))
        n -= 1
    return out


def cutsQ(hQ, a, top):
    n = max(1, cdiv(tsub(top, a), hQ))
    return [a + tsub(top, a) * j // n for j in range(1, n + 1)]


class Strat:
    def __init__(self, depth, wmin, cuts):
        self.depth, self.wmin, self.cuts = depth, wmin, cuts


class Ops:
    def __init__(self, grd, van, drp, alt):
        self.grd, self.van, self.drp, self.alt = grd, van, drp, alt


class RevSearch(tc.Search):
    """`SieveAd.solveG` with the reversal as the node `alt` (`altR`) and a strategy whose cells shrink with the
    exponent (κ, hI, depth); the reversals' trees with the nodes `opsK` and cells of side at most hR (κ, depthR), the
    smaller prime of a cofactor of two primes in cells of side at most hQ; with counts of its work."""

    def __init__(self, T, hI, depth, wmin, kappa, hR, depthR, hQ, fuel, rev=True):
        super().__init__(T, hI, depth, wmin)
        self.kappa, self.hR, self.depthR, self.hQ, self.fuel, self.rev = kappa, hR, depthR, hQ, fuel, rev
        self.minfuel = fuel
        self.W.update(kcalls=0, kdfs=0, fams=0)
        self.stat = dict.fromkeys(('revtry', 'revwin', 'fams', 'rootfail'), 0)
        self.SG = Strat(depth, wmin, self.cutsOfG)
        self.OR = Ops(lambda bl: True, vanishOK, dropC, self.altR)

    # the strategies
    def cutsOfG(self, bl, f):
        if not bl:
            return []
        reg = min(bl[0][1], tsub(DEN, loSum(bl)) // 2 + 2)
        last = tsub(DEN - 1, hiSum(bl))
        if f < reg:
            return geoCuts(self.kappa, self.stepOf(len(bl) + 1), reg, 4096, f) + [last]
        return [last]

    def cutsK(self, ctx, ch, top, f):
        reg = min(top, tsub(ctx[1] + 1, loSum(ch)) // 2 + 2)
        last = tsub(tsub(ctx[0], 1), hiSum(ch))
        if f < reg:
            return geoCuts(self.kappa, self.hR if len(ch) < 2 else 2 * self.hR, reg, 4096, f) + [last]
        return [last]

    def stratK(self, ctx, na):
        def cuts(bl, f):
            ch = chainOf(na, bl)
            return self.cutsK(ctx, ch, ch[0][1] if ch else bl[0][0], f)
        return Strat(self.depthR + na, self.wmin, cuts)

    def opsK(self, ctx, na):
        return Ops(lambda bl: na < len(bl) <= 12, lambda bl: vanishK(ctx, chainOf(na, bl)),
                   lambda bl, par: dropK(ctx, chainOf(na, bl), par), lambda bl, par, l: l)

    # the search with its nodes' tests as parameters
    def kidsG(self, rec, top, bl, par, cs, a, lim):
        """`kids rec top bl par cs a lim`."""
        for i, c in enumerate(cs):
            if a < c < top:
                c1 = rec([(a, c)] + bl, par, lim)
                if lim <= c1:
                    return c1
                return c1 + self.kidsG(rec, top, bl, par, cs[i + 1:], c, tsub(lim, c1))
        return rec([(a, top)] + bl, par, lim)

    def buchG(self, S, rec, x, bl, par, lim):
        if len(bl) < S.depth:
            fj = self.firstJ(bl, x[0], self.propJ(bl))
            if fj is not None:
                self.W['cuts'] += 1
                return self.kidsG(rec, x[1], bl, not par, S.cuts(bl, fj[0]), fj[0], lim)
        return lim + BIG

    def splitG(self, S, rec, x, bl, par, lim):
        mid = (x[0] + x[1]) // 2
        if S.wmin < tsub(x[1], x[0]) and x[0] < mid < x[1]:
            c1 = rec([(x[0], mid)] + bl[1:], par, lim)
            if lim <= c1:
                return c1
            return c1 + rec([(mid, x[1])] + bl[1:], par, tsub(lim, c1))
        return lim + BIG

    def nodeG(self, O, S, rec, x, bl, par, lim):
        dc = O.drp(bl, par)
        if dc is not None:
            bc = self.buchG(S, rec, x, bl, par, dc if dc <= lim else lim)
            return dc if dc <= bc else bc
        bc = self.buchG(S, rec, x, bl, par, lim)
        l2 = bc if bc <= lim else lim
        rc = O.alt(bl, par, l2)
        if rc < l2:
            return rc
        if bc < BIG:
            return bc
        return self.splitG(S, rec, x, bl, par, lim)

    def solveG(self, O, S, n, bl, par, lim):
        """`solveG O τ S n bl par lim`, with this search's tests for τ."""
        self.minfuel = min(self.minfuel, n)
        if n == 0 or not bl or not O.grd(bl):
            return lim
        self.W['calls'] += 1
        if O.van(bl) or self.anyI(bl):
            return 0
        return self.nodeG(O, S, lambda b, p, l: self.solveG(O, S, n - 1, b, p, l), bl[0], bl, par, lim)

    # the reversal
    def rootJ(self, S, ctx, beta, lim):
        if not beta:
            return lim
        c = beta[0]
        fj = self.firstJ(beta, c[0], self.propJ(beta))
        if fj is None:
            return lim
        if c[0] <= fj[0]:
            return 0
        O = self.opsK(ctx, len(beta))
        w0 = (self.W['calls'], self.W['dfs'])
        r = self.kidsG(lambda b, p, l: self.solveG(O, S, self.fuel, b, p, l), c[0], beta, True,
                       S.cuts(beta, fj[0]), fj[0], lim)
        self.W['kcalls'] += self.W['calls'] - w0[0]
        self.W['kdfs'] += self.W['dfs'] - w0[1]
        return r

    def famCost(self, ctx, beta, iq, lim):
        if emptyBox(beta):
            return 0
        self.stat['fams'] += 1
        self.W['fams'] += 1
        C = self.rootJ(self.stratK(ctx, len(beta)), ctx, beta, CAPK)
        if CAPK <= C:
            self.stat['rootfail'] += 1
            return lim
        y, q, tr, sc = beta[0][0], beta[iq][0], trBut(iq, beta), SC ** len(beta)
        return (cdiv(trF(q, tsub(tsub(ctx[1], ctx[0]), 1)) * tr * (C + penK(ctx, y)), sc)
                + cdiv(2 * trF(q, 1) * tr * (C + bdK(ctx, y)), sc))

    def cellQ(self, c1, c2, c3, mlo, mhi, bl, par, lim):
        if len(bl) != 1:
            return lim
        d = bl[0]
        iq2 = (max(tsub(mlo, d[1]), d[0]), tsub(mhi, d[0]) + 1)
        return addL(self.famCost(c1, [c3, d, iq2, c2], 2, lim),
                    lambda l1: addL(self.famCost(c1, [c3, d, c2, iq2], 3, l1),
                                    lambda l2: self.famCost(c1, [c3, c2, d, iq2], 3, l2), l1), lim)

    def revCost(self, bl, lim):
        if len(bl) != 3:
            return lim
        c3, c2, c1 = bl
        mlo, mhi = tsub(DEN, c1[1] + c2[1] + c3[1]), tsub(DEN + 1, c1[0] + c2[0] + c3[0])
        iq1, top = (max(mlo, c3[0]), mhi), (mhi + 1) // 2
        return addL(self.famCost(c1, [c3, c2, iq1], 2, lim),
                    lambda l1: addL(self.famCost(c1, [c3, iq1, c2], 1, l1),
                                    lambda l2: self.kidsG(lambda b, p, l: self.cellQ(c1, c2, c3, mlo, mhi, b, p, l),
                                                          top, [], False, cutsQ(self.hQ, c3[0], top), c3[0], l2),
                                    l1), lim)

    def altR(self, bl, par, l):
        if self.rev and not par and revOK(bl):
            self.stat['revtry'] += 1
            r = self.revCost(bl, l)
            self.stat['revwin'] += r < l
            return r
        return l

    def solveR(self, bl, par, lim):
        """`solveG` with the nodes `OR` (the reversal as `alt`) and the strategy `SG`, at the fuel `fuel`."""
        return self.solveG(self.OR, self.SG, self.fuel, bl, par, lim)

    def kidsR(self, top, bl, par, cs, a, lim):
        """`kids` with `solveR` for `rec`."""
        return self.kidsG(self.solveR, top, bl, par, cs, a, lim)


def rowCuts(S):
    """The ends of the cells of the first prime: steps of at most hI and at most the exponent over κ from V to
    DEN/2 + 1, the window's ends, and a thin cell at the top."""
    T = S.T
    return sorted(set([T.V] + geoCuts(S.kappa, S.hI, DEN // 2 + 1, 4096, T.V))
                  | {T.U1 + 1, T.U2 - 1, DEN // 2 - S.wmin})


def search_only(h, depth, kappa, depthR, hR, hQ, w1, w2, ln, ld, rev=True):
    """The cost of the search with other parameters, the number of boxes searched and the reversals' counts; with
    `rev` false, the search without the reversal (its node `alt` returns its limit)."""
    T = tc.Tests(w1, w2, ln, ld)
    S = RevSearch(T, round(h * DEN), depth, WMIN, kappa, round(hR * DEN), depthR, round(hQ * DEN), FUEL, rev)
    sys.setrecursionlimit(100000)
    cuts = rowCuts(S)
    return S.kidsR(DEN // 2 + 1, [], False, cuts[1:-1], cuts[0], 4 * K), S.W['calls'], S.stat


def pred(w):
    """The kernel's time on a part, in seconds, from the search's work in it: `tree_cert.pred` for the work outside
    the reversals' trees, and 3.3e-4 seconds for each step of the searches over the sets of a box's cells inside them
    (their boxes have more cells; the kernel's checks of thirty-one parts with reversals, of 1 to 81 seconds, took
    1.8e-4 to 3.2e-4 seconds a step). The kernel's memory in a part grows with its time, about 0.9 GB and 105 MB a
    second, so a part of 22 seconds needs about 3.2 GB."""
    return tc.pred(dict(w, dfs=w['dfs'] - w['kdfs'])) + 3.3e-4 * w['kdfs']


# the Lean text, as `hint_cert.py` writes it

def cell(c):
    return f'({c[0]}, {nat(c[1]).strip("()")})'


def box(bl):
    return '[' + ', '.join(cell(c) for c in bl) + ']'


def bool_(b):
    return 'true' if b else 'false'


def chain(items):
    """`pr_split` over the pieces `items` (Lean terms), nested to the right, one piece a line."""
    if len(items) == 1:
        return f'    {items[0]}'
    lines = [f'    pr_split (by decide) (by decide) ({x}) (' for x in items[:-1]]
    return '\n'.join(lines) + f'\n    {items[-1]}' + ')' * (len(items) - 1)


def main():
    if '--try' in sys.argv:
        a = [x for x in sys.argv[sys.argv.index('--try') + 1:] if x != '--norev']
        w1, w2, (ln, ld) = (int(a[6]), int(a[7]), map(int, a[8].split('/'))) if len(a) >= 9 else (W1, W2, (LNUM, LDEN))
        c, n, st = search_only(float(a[0]), int(a[1]), int(a[2]), int(a[3]), float(a[4]), float(a[5]), w1, w2, ln, ld,
                               '--norev' not in sys.argv)
        print(f'L = {ln}/{ld}, window [{w1}, {w2}]/10^5, cells of side {a[0]} and exponent/{a[2]}, depth {a[1]}; '
              f'reversals: chains below {a[3]} primes, cells {a[4]}, cofactor cells {a[5]}: cost/K = {c / K:.5f}; '
              f'{n} boxes searched; {st}')
        return 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main())
