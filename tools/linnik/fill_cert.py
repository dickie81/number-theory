#!/usr/bin/env python3
"""fill_cert.py --try H DEPTH KAPPA DEPTHR HR HQ [a/b] [--norev]: the search with no Type II window, as the kernel
searched it for the theorem at L = 2165/1000, and the base of the searches of `flip_cert.py` and `hint_cert.py`.

Below 13/6 the Type II estimate in one variable has no window, and a decomposition has the estimate in two
variables alone. Its rest is a product of primes of exponent between 1/2000 and about (L − 2)/0.558 in base q, and
a term whose primes are all larger has none among them. For such a term at a floor, the comparison takes its rest
from the primes of its own tree of Buchstab steps below the floor (`SieveFillComp.prop6_fill`): the first of them
join the first variable until its product enters the window, and the next ones are the rest until their product
reaches q^(1/2000). The tests are `SieveAd.fillTests` (`lib/pnt/SieveAdFillDefs.lean`): `okI2` for a box, and at a
floor `okJ2` (the rest among the box's primes) or, for a configuration of kind 2, `okJ3` (the rest among the
tree's); they are sound (`lib/pnt/SieveAdFill.lean`). The search is `rev_cert.py`'s, with role reversal
(`SieveAd.solveG`, with the cost `SieveAd.revCost` of the reversal of a box of the sign `−` that `SieveAd.revOK`
accepts as one more bound), and its strategy proposes no window and the floors of `okJ3`, counted down from
`SieveAd.fmax3` (`lib/pnt/SieveAdFillSearchDefs.lean`). This script is that search in Python, on
top of `rev_cert.py` and `tree_cert.py`:

  * `TestsF`: `fillTests` (`chkJ3`, `okJ3`), definition by definition;
  * `FillSearch`: `rev_cert.RevSearch` with `propJ3` and `propJF` for `propJ`, and `propI2` alone for the boxes.

The root is the comparison of the empty box at the floor that `propJ3` gives, x^0.0489 at 2165/1000, and the first
prime's cells run from there to x^(1/2).

The theorem at 2165/1000 (`Linnik21650.linnik_21650`, 11 November 2026) was this search with the parameters
`0.005 6 10 3 0.012 0.02`, run by the kernel in 2353 parts; the theorem at 2150/1000 superseded it, and it was removed on 16 November 2026
with its files, with the Lean definitions of this strategy (`tryJ3`, `propJ3`, `propJF`, `stratGF`, `stratKF`) and
with the part of this script that wrote the files. They are in the git history, at commit `faaa2d1`. What is left
here is what `flip_cert.py`, `flip_proto.py`, `hint_cert.py` and `hint_probe.py` build on, and `--try`, which runs
the search with given parameters (at another exponent, if given; without the reversal, with `--norev`) and prints
its cost.

Values (11 November 2026): the search costs 0.95109 K on 3607561 boxes, with 8720 reversals taken of 18611 tried
(`--try 0.005 6 10 3 0.012 0.02`). `--try 0.006 6 10 3 0.012 0.02`: 1.05186, 2272818 boxes.

Needs Python 3 only. Five minutes.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import rev_cert as rc  # noqa: E402
from tree_cert import DEN, K, cdiv, tsub, loSum, hiSum, mSum  # noqa: E402
from rev_cert import geoCuts, bool_  # noqa: E402

# the exponent of `--try` when none is given; the least width of a cell that is cut for want of a test, and the
# fuel of a reversal's trees
LNUM, LDEN = 2165, 1000
WMIN, FUEL = round(0.0005 * DEN), 200


class TestsF(tc.Tests):
    """`SieveAd.fillTests` at `IBPar ⟨Ln, Ld⟩` (SieveAdFillDefs.lean)."""

    def __init__(self, Ln, Ld):
        self.Ln, self.Ld = Ln, Ld
        self.U1 = self.U2 = self.V = 0
        self.fillLo = cdiv(Ld * DEN + 2000 * Ln, 2000 * Ln)

    def chkJ3(self, bl, f, s0, s1, e, u, v, t, r1, r2):
        D1 = mSum(1, bl, s1) + (t + r2 if e else 0)
        D2 = tsub(hiSum(bl), mSum(1, bl, s1)) + (0 if e else t + r2)
        return (0 < f and len(bl) <= 13 and all(f <= c[0] <= c[1] <= DEN for c in bl)
                and self.zone(r1, r2, u, v) and r1 + f < r2 and u + f < v and u <= t + mSum(0, bl, s0)
                and mSum(1, bl, s0) < v and (self.leaves(D1, D2) or (self.energy and self.leavesE(D1, D2))))

    def okJ3(self, bl, f, cfg):
        _, s0, _, s1, e = cfg
        r1, r2 = self.fillLo, self.fillLo + f + 1
        u, v = self.uOf(r1), self.vOf(r2)
        return self.chkJ3(bl, f, s0, s1, e, u, v, tsub(u, mSum(0, bl, s0)), r1, r2)

    def okI(self, bl, cfg):
        return self.chkI2(bl, cfg[1], cfg[2])

    def okJ(self, bl, f, cfg):
        return self.okJ3(bl, f, cfg) if cfg[0] == 2 else self.okJ2(bl, f, cfg)


class FillSearch(rc.RevSearch):
    """`SieveAd.solveG (opsR fillTests (stratKF κ hR depthR wmin) fuel (cutsQ hQ)) fillTests (stratGF κ hI depth wmin)`,
    with counts of its work (SieveAdFillSearchDefs.lean)."""

    def __init__(self, T, hI, depth, wmin, kappa, hR, depthR, hQ, fuel, rev=True):
        super().__init__(T, hI, depth, wmin, kappa, hR, depthR, hQ, fuel, rev)
        self.W.update(okJ3=0)
        self.u3 = self.uOfF(self.restLo)
        self.fmax3 = min(tsub(self.vA, self.restLo + 3 + self.u3) // 2,
                         tsub(self.vB, self.vC * (self.restLo + 2) + (self.u3 + 1) * self.uC) // (self.uC + self.vC))

    def anyI(self, bl):
        for cfg in self.propI2(bl, loSum(bl)):
            self.W['okI2'] += 1
            if self.T.okI(bl, cfg):
                return True
        return False

    def tryJ3(self, bl, ls, hs, f):
        r2 = self.restLo + f + 1
        b = self.bestSub(self.vOfF(r2), 0, bl, 1, 0, 0, 0, ls, (0, 0))
        sp = self.leavesOfJ2(bl, hs, tsub(self.u3, b[0]) + r2)
        return None if sp is None else (f, (2, b[1], 0, sp[0], sp[1]))

    def propJ3(self, bl, ls, hs, n, f):
        for _ in range(n):
            r = self.tryJ3(bl, ls, hs, f)
            if r is not None:
                return r
            f = 3 * f // 4
        return None

    def propJ(self, bl):
        """`propJF bl`."""
        lomin, ls, hs = min([DEN] + [c[0] for c in bl]), loSum(bl), hiSum(bl)
        if self.t5J() < hs:
            return []
        r = self.propJ2(bl, lomin, ls, hs)
        out = []
        if r[0] < lomin:
            r3 = self.propJ3(bl, ls, hs, 8, min(lomin, self.fmax3))
            if r3 is not None and r[0] < r3[0]:
                out.append(r3)
        if r[1] is not None:
            out.append(r)
        return out

    def firstJ(self, bl, lo0, ps):
        for f, cfg in ps:
            self.W['okJ3' if cfg[0] == 2 else 'okJ2'] += 1
            if 0 < f <= lo0 and self.T.okJ(bl, f, cfg):
                return f, cfg
        return None


def root_of(S):
    """The floor and the configuration of the root: the first proposal for the empty box."""
    fj = S.firstJ([], DEN, S.propJ([]))
    assert fj is not None and fj[0] <= DEN // 2 + 1
    return fj


def rowCuts(S, f0):
    """The ends of the cells of the first prime: steps of at most hI and at most the exponent over κ from the
    root's floor to DEN/2 + 1, and a thin cell at the top."""
    return sorted(set([f0] + geoCuts(S.kappa, S.hI, DEN // 2 + 1, 4096, f0)) | {DEN // 2 - S.wmin})


def search_only(h, depth, kappa, depthR, hR, hQ, ln, ld, rev=True):
    """The cost of the search with other parameters, the number of boxes searched and the reversals' counts; with
    `rev` false, the search without the reversal."""
    S = FillSearch(TestsF(ln, ld), round(h * DEN), depth, WMIN, kappa, round(hR * DEN), depthR, round(hQ * DEN),
                   FUEL, rev)
    sys.setrecursionlimit(100000)
    f0, _ = root_of(S)
    cuts = rowCuts(S, f0)
    return S.kidsR(DEN // 2 + 1, [], False, cuts[1:-1], cuts[0], 4 * K), S.W['calls'], S.stat, f0


def pred(w):
    """The kernel's time on a part, in seconds, from the search's work in it: `rev_cert.pred`, with the tests of the
    comparison with the rest among the tree's primes counted with the others."""
    return rc.pred(dict(w, okJ2=w['okJ2'] + w['okJ3']))


def cfg_(cfg):
    return f'⟨{cfg[0]}, {cfg[1]}, {cfg[2]}, {cfg[3]}, {bool_(cfg[4])}⟩'


def main():
    if '--try' in sys.argv:
        a = [x for x in sys.argv[sys.argv.index('--try') + 1:] if x != '--norev']
        ln, ld = map(int, a[6].split('/')) if len(a) >= 7 else (LNUM, LDEN)
        c, n, st, f0 = search_only(float(a[0]), int(a[1]), int(a[2]), int(a[3]), float(a[4]), float(a[5]), ln, ld,
                                   '--norev' not in sys.argv)
        print(f'L = {ln}/{ld}, no window, root floor {f0 / DEN:.5f}, cells of side {a[0]} and exponent/{a[2]}, '
              f'depth {a[1]}; reversals: chains below {a[3]} primes, cells {a[4]}, cofactor cells {a[5]}: '
              f'cost/K = {c / K:.5f}; {n} boxes searched; {st}')
        return 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main())
