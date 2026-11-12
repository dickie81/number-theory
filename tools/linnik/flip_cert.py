#!/usr/bin/env python3
"""flip_cert.py --try H DEPTH KAPPA DEPTHR HR HQ HF DEPTHF MAXLEN [a/b] [--loose] | --box L1 H1 L2 H2: the search
with the reversal of a box through its largest prime, searched as the kernel searches it.

The search is `fill_cert.py`'s with one more bound for a box of the sign − (`SieveAd.opsF`,
`lib/pnt/SieveAdFlipDefs.lean`): the box `β ++ [ctx]` of two to MAXLEN primes, the cell `ctx = (l₁, h₁)` of its
largest prime at least one unit above the next prime's cell, is reversed through that prime. The frozen part is
the numbers `R = ∏a·m`, `a` in the cells `β` and `m` rough at the least prime of `a`, with `R` between
`x^{(DEN−h₁)/DEN}` and `x^{(DEN−l₁+1)/DEN}`; the term of the box is at most the terms of `n/R` at the level
`t = ⌈h₁/2⌉` over it, and those are a tree of Buchstab steps on the chain of primes of `n/R` from a floor to `t`,
searched with the tests `SieveAd.frozTests` (`lib/pnt/SieveAdFrozDefs.lean`) by the strategy `SieveAd.stratFF`
(`lib/pnt/SieveAdFlipStratDefs.lean`). With the tree's cost `c`, the cost of the box is
`⌈(c·(h₁·D₀ + E) + bdK·E)/(DEN·K)⌉` (`SieveAd.flipCost`), and the tree is searched with the limit past which that
is not below the box's other bound. The main strategy is `SieveAd.stratGFF`: `stratGF` with one more cut, one unit
below the largest prime's cell. This script is that search in Python, definition by definition, on top of
`fill_cert.py`:

  * `loR`, `hiR`, `hiRc`, `coreI2`, `coreJ3`, `coreJ2`, `okIF`, `okJF3`, `okJF2`: `frozTests`;
  * `vboxF`, `widen`, `anyI`, `propJFl`, `propJ`, `stratF`, `cutsKh`: `stratFF`; `insCut`, `cutsOfG`: `stratGFF`;
  * `flipT`, `flipOK`, `flipTree`, `flipCost`, `altF`: `opsF`.

A box of the sign − has an odd number of primes, so MAXLEN = 4 reverses the boxes of three primes, and 6 those of
five too.

With `--try`, the search is run with the given parameters (cells of side H, boxes of fewer than DEPTH primes
decomposed, cells at most the exponent over KAPPA; the three-prime reversal of `rev_cert.py`: chains below DEPTHR
primes in cells HR, its cofactor's cells HQ; the reversal through the largest prime: chains below DEPTHF primes in
cells HF, on boxes of at most MAXLEN primes), and its cost is printed; `--loose` searches every tree with the
limit `CAPK` (the same cost, more boxes). With `--box`, the search at 2165/1000 with the parameters of the theorem
there (`fill_cert.py`'s) and `0.012 3 4` for the new reversal is run on the box of the second prime in
`(L2, H2)` under the first in `(L1, H1)` (integers, in units of 1/DEN), of the sign +, and the part's statement is
printed, with the cost of the theorem's search on the box: `lib/pnt/SieveFlipPart21650.lean` has the part
`--box 465911610850 471409168989 295487308541 300984866680`, which the kernel checks in nineteen seconds
(`Linnik21650.flip_box_21650`).

Checked against the kernel (12 November 2026): four values of `flipCost` and a row of the first prime with
`0.02 6 10 3 0.012 0.02 0.012 3 4`, as equalities by `decide +kernel`, and that part. The kernel takes about
13 ms a box over a frozen part and 4 ms a box elsewhere (`fill_cert.pred` is right for both), and its memory
grows with a part's time (13 GB for a part of two minutes). `--try 0.02 6 10 3 0.012 0.02 0.012 3 4`: 1.71328 K on
468212 boxes, 218818 of them over frozen parts (356628 with `--loose`), in twenty seconds.
`--try 0.005 6 10 3 0.012 0.02 0.012 3 4`: 0.90810 K at 2165/1000 on 6.9·10^6 boxes, 3.0·10^6 of them over frozen
parts, and 0.97731 K at 2160/1000 on 7.4·10^6: each about twenty-three hours of the kernel as this search. With
boxes of five primes too (`… 0.012 3 6`, H = 0.01, 2165/1000): 1.206 K; chains' cells of side 0.006 make it
1.187 K, and chains of one more prime change nothing. `hint_cert.py` is this search as a plan that the kernel
follows.

Needs Python 3 only.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import rev_cert as rc  # noqa: E402
import fill_cert as fc  # noqa: E402
from tree_cert import DEN, K, cdiv, tsub, loSum, hiSum, vanishOK, dropC, mSum, dropCost  # noqa: E402
from rev_cert import Ops, Strat, cellsOK, bdK, revOK, chainOf, CAPK  # noqa: E402


def flipT(ctx):
    return (ctx[1] + 1) // 2


def flipOK(maxlen, bl):
    """`flipOK maxlen bl`."""
    if not (2 <= len(bl) <= maxlen <= 11):
        return False
    ctx, t = bl[-1], flipT(bl[-1])
    return (cellsOK(bl) and hiSum(bl) + 2 <= DEN and bl[-2][1] + 1 <= ctx[0] and 3 <= ctx[0] and t <= ctx[0]
            and ctx[1] + t + 1 <= DEN)


def insCut(c, cs):
    """`insCut c cs`."""
    for i, x in enumerate(cs):
        if c < x:
            return cs[:i] + [c] + cs[i:]
        if c == x:
            return cs
    return cs + [c]


def widen(Kb, bl):
    return [(max(1, tsub(a, Kb)), b + Kb) for a, b in bl]


def vboxF(ctx, beta, bl):
    """`vboxF ctx β bl`."""
    hi = tsub(tsub(DEN, ctx[0]) + 1, loSum(beta))
    if hi < 2:
        return bl
    return bl + [(max(1, tsub(tsub(DEN, ctx[1]), hiSum(beta))), hi)]


class FlipSearch(fc.FillSearch):
    """`SieveAd.solveG (opsF fillTests (stratKF κ hR depthR wmin) fuel (cutsQ hQ) (stratFF κ hF depthF wmin) fuel
    maxlen) fillTests (stratGFF κ hI depth wmin)`, with counts of its work."""

    def __init__(self, T, hI, depth, wmin, kappa, hR, depthR, hQ, fuel, hF, depthF, maxlen, rev=True, flip=True):
        super().__init__(T, hI, depth, wmin, kappa, hR, depthR, hQ, fuel, rev)
        self.hF, self.depthF, self.maxlen, self.flip = hF, depthF, maxlen, flip
        self.tight = True
        self.frz = None
        self.stat.update(fliptry=0, flipwin=0, fliproot=0, flipcap=0)
        self.W.update(fcalls=0, fdfs=0, flips=0)
        self.OR = Ops(lambda bl: True, vanishOK, dropC, self.altF)

    # frozTests (SieveAdFrozDefs.lean): the exponents of a set of bits over ch ++ β ++ [cofactor]
    def loR(self, e1, beta, ch, m):
        mA = m >> len(ch)
        a = tsub(e1, tsub(hiSum(beta), mSum(1, beta, mA))) if mA >> len(beta) & 1 else mSum(0, beta, mA)
        return a + mSum(0, ch, m)

    def hiR(self, e2, beta, ch, m):
        mA = m >> len(ch)
        a = tsub(e2, tsub(loSum(beta), mSum(0, beta, mA))) if mA >> len(beta) & 1 else mSum(1, beta, mA)
        return a + mSum(1, ch, m)

    def hiRc(self, e2, beta, ch, m):
        mA = m >> len(ch)
        a = tsub(hiSum(beta), mSum(1, beta, mA)) if mA >> len(beta) & 1 else tsub(e2, mSum(0, beta, mA))
        return a + tsub(hiSum(ch), mSum(1, ch, m))

    def coreI2(self, u, v, r1, r2):
        Ln, Ld = self.T.Ln, self.T.Ld
        return (Ld * DEN + 2000 * Ln <= 2000 * Ln * r1 and 2 * Ld * DEN + 3 * Ln <= 3 * Ln * u
                and 2 * Ld * DEN + 3 * Ln * (r2 + 1 + v) <= 3 * Ln * DEN
                and 62505 * Ld * DEN + 90137 * Ln <= 62500 * Ln * u + 27637 * Ln * r1
                and 62505 * Ld * DEN + 62500 * Ln * v + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN
                and 125005 * Ld * DEN + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN)

    def coreJ3(self, f, e, u, v, t, r1, r2, c0lo, c0hi, h1s, h2s):
        T = self.T
        D1, D2 = h1s + (t + r2 if e else 0), h2s + (0 if e else t + r2)
        return (0 < f and T.zone(r1, r2, u, v) and r1 + f < r2 and u + f < v and u <= t + c0lo and c0hi < v
                and T.leaves(D1, D2))

    def coreJ2(self, f, e, u, v, t, r1, r2, c0lo, c0hi, h1s, h2s):
        T = self.T
        D1, D2 = h1s + (t if e else 0), h2s + (0 if e else t)
        return (0 < f and T.zone(r1, r2, u, v) and u + f < v and u <= t + c0lo and c0hi < v and T.leaves(D1, D2))

    def okIF(self, bl, cfg):
        e1, e2, Kb, beta = self.frz
        ch = chainOf(len(beta), bl)
        _, s0, sr, _, _ = cfg
        return (all(1 <= c[0] <= c[1] <= DEN for c in bl) and s0 & sr == 0 and 0 < self.loR(e1, beta, ch, sr)
                and self.coreI2(self.loR(e1, beta, ch, s0), self.hiR(e2, beta, ch, s0),
                                self.loR(e1, beta, ch, sr), self.hiR(e2, beta, ch, sr)))

    def okJF3(self, bl, f, cfg):
        e1, e2, Kb, beta = self.frz
        ch = chainOf(len(beta), bl)
        _, s0, _, s1, e = cfg
        T = self.T
        r1, r2 = T.fillLo, T.fillLo + f + 1
        u, c0lo = T.uOf(r1), tsub(self.loR(e1, beta, ch, s0), Kb)
        return (0 < f and all(f <= c[0] <= c[1] <= DEN for c in bl)
                and self.coreJ3(f, e, u, T.vOf(r2), tsub(u, c0lo), r1, r2, c0lo, self.hiR(e2, beta, ch, s0) + Kb,
                                self.hiR(e2, beta, ch, s1) + Kb, self.hiRc(e2, beta, ch, s1) + Kb))

    def okJF2(self, bl, f, cfg):
        e1, e2, Kb, beta = self.frz
        ch = chainOf(len(beta), bl)
        _, s0, sr, s1, e = cfg
        T = self.T
        r1, r2 = tsub(self.loR(e1, beta, ch, sr), Kb), self.hiR(e2, beta, ch, sr) + Kb
        u, c0lo = T.uOf(r1), tsub(self.loR(e1, beta, ch, s0), Kb)
        return (0 < f and all(f <= c[0] <= c[1] <= DEN for c in bl) and s0 & sr == 0
                and 0 < self.loR(e1, beta, ch, sr)
                and self.coreJ2(f, e, u, T.vOf(r2), tsub(u, c0lo), r1, r2, c0lo, self.hiR(e2, beta, ch, s0) + Kb,
                                self.hiR(e2, beta, ch, s1) + Kb, self.hiRc(e2, beta, ch, s1) + Kb))

    # stratFF (SieveAdFlipStratDefs.lean); `self.frz` is set inside a tree over a frozen part
    def anyI(self, bl):
        if self.frz is None:
            return super().anyI(bl)
        blv = vboxF(self.fctx, self.frz[3], bl)
        for cfg in self.propI2(blv, loSum(blv)):
            self.W['okI2'] += 1
            if self.okIF(bl, cfg):
                return True
        return False

    def propJFl(self, bl, lomin):
        ls, hs = loSum(bl), hiSum(bl)
        if self.T5 < hs:
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

    def propJ(self, bl):
        if self.frz is None:
            return super().propJ(bl)
        Kb, beta = self.frz[2], self.frz[3]
        return self.propJFl(widen(Kb, vboxF(self.fctx, beta, bl)), min([DEN] + [c[0] for c in widen(Kb, bl)]))

    def firstJ(self, bl, lo0, ps):
        if self.frz is None:
            return super().firstJ(bl, lo0, ps)
        for f, cfg in ps:
            self.W['okJ3' if cfg[0] == 2 else 'okJ2'] += 1
            if 0 < f <= lo0 and (self.okJF3(bl, f, cfg) if cfg[0] == 2 else self.okJF2(bl, f, cfg)):
                return f, cfg
        return None

    def stratF(self, ctx, beta):
        def cuts(bl, f):
            ch = chainOf(len(beta), bl)
            return self.cutsKh(self.hF, ctx, ch, ch[0][1] if ch else flipT(ctx), f)
        return Strat(self.depthF + len(beta), self.wmin, cuts)

    def cutsKh(self, hR, ctx, ch, top, f):
        """`cutsK κ hR ctx ch top f`."""
        reg = min(top, tsub(ctx[1] + 1, loSum(ch)) // 2 + 2)
        last = tsub(tsub(ctx[0], 1), hiSum(ch))
        if f < reg:
            return rc.geoCuts(self.kappa, hR if len(ch) < 2 else 2 * hR, reg, 4096, f) + [last]
        return [last]

    # stratGFF
    def cutsOfG(self, bl, f):
        cs = super().cutsOfG(bl, f)
        if not self.flip:
            return cs
        c = tsub(bl[-1][0], 1) if bl else 0
        return insCut(c, cs) if f < c else cs

    # opsF (SieveAdFlipDefs.lean)
    def flipTree(self, ctx, beta, lim):
        """`flipTree stratFF fuel ctx β lim`."""
        if not beta:
            return lim
        c, t = beta[0], flipT(ctx)
        self.frz, self.fctx = (tsub(DEN, ctx[1]), tsub(DEN, ctx[0]) + 1, 12 + DEN // c[0], beta), ctx
        w0 = (self.W['calls'], self.W['dfs'])
        try:
            S = self.stratF(ctx, beta)
            fj = self.firstJ(beta, min(c[0], t), self.propJ(beta))
            if fj is None:
                self.stat['fliproot'] += 1
                return lim
            O = self.opsK(ctx, len(beta))
            return self.kidsG(lambda b, p, l: self.solveG(O, S, self.fuel, b, p, l), t, beta, True,
                              S.cuts(beta, fj[0]), fj[0], lim)
        finally:
            self.frz = None
            self.W['fcalls'] += self.W['calls'] - w0[0]
            self.W['fdfs'] += self.W['dfs'] - w0[1]

    def flipCost(self, bl, lim):
        """`flipCost stratFF fuel bl lim`: the tree is searched with the limit past which the cost is not below
        `lim`."""
        ctx, beta = bl[-1], bl[:-1]
        self.W['flips'] += 1
        E = ((ctx[1] + 1) * dropCost(beta + [(tsub(ctx[1], 1), ctx[1] + 1)])
             + (ctx[0] + 1) * dropCost(beta + [(tsub(ctx[0], 1), ctx[0] + 1)]))
        A, B = ctx[1] * dropCost(bl) + E, bdK(ctx, flipT(ctx)) * E
        cl = min(CAPK, tsub(tsub(lim, 1) * (DEN * K), B) // A + 1) if self.tight else CAPK
        c = self.flipTree(ctx, beta, cl)
        if cl <= c:
            self.stat['flipcap'] += 1
            return lim
        return cdiv(c * A + B, DEN * K)

    def altF(self, bl, par, l):
        """`(opsF …).alt bl par l`."""
        r = l
        if not par and revOK(bl):
            if self.rev:
                self.stat['revtry'] += 1
                r = self.revCost(bl, l)
                self.stat['revwin'] += r < l
        if self.flip and not par and flipOK(self.maxlen, bl):
            self.stat['fliptry'] += 1
            c = self.flipCost(bl, r)
            if c < r:
                self.stat['flipwin'] += 1
                return c
        return r


def search_only(h, depth, kappa, depthR, hR, hQ, hF, depthF, maxlen, ln, ld, rev=True, flip=True):
    """The cost of the search with the given parameters, the boxes searched (and those in the trees over the frozen
    parts), the counts and the root's floor."""
    S = FlipSearch(fc.TestsF(ln, ld), round(h * DEN), depth, fc.WMIN, kappa, round(hR * DEN), depthR,
                   round(hQ * DEN), fc.FUEL, round(hF * DEN), depthF, maxlen, rev, flip)
    S.tight = '--loose' not in sys.argv
    sys.setrecursionlimit(100000)
    f0, _ = fc.root_of(S)
    cuts = fc.rowCuts(S, f0)
    c = S.kidsR(DEN // 2 + 1, [], False, cuts[1:-1], cuts[0], 4 * K)
    return c, S.W, S.stat, f0


def main():
    if '--try' in sys.argv:
        import time
        a = [x for x in sys.argv[sys.argv.index('--try') + 1:] if not x.startswith('--')]
        ln, ld = map(int, a[9].split('/')) if len(a) >= 10 else (2165, 1000)
        t0 = time.time()
        c, W, st, f0 = search_only(float(a[0]), int(a[1]), int(a[2]), int(a[3]), float(a[4]), float(a[5]),
                                   float(a[6]), int(a[7]), int(a[8]), ln, ld, '--norev' not in sys.argv,
                                   '--noflip' not in sys.argv)
        print(f'L = {ln}/{ld}, root floor {f0 / DEN:.5f}, cells {a[0]} and exponent/{a[2]}, depth {a[1]}; '
              f'three-prime reversal: chains below {a[3]}, cells {a[4]}, cofactor cells {a[5]}; reversal through '
              f'the largest prime: boxes of at most {a[8]} primes, chains below {a[7]}, cells {a[6]}: '
              f'cost/K = {c / K:.5f}; {W["calls"]} boxes searched ({W["fcalls"]} over frozen parts), predicted '
              f'{fc.pred(W):.0f} s of the kernel; {st}; {time.time() - t0:.0f} s', flush=True)
        return 0
    if '--box' in sys.argv:
        a = [int(x) for x in sys.argv[sys.argv.index('--box') + 1:][:4]]
        S = FlipSearch(fc.TestsF(fc.LNUM, fc.LDEN), fc.HI, fc.DEPTH, fc.WMIN, fc.KAPPA, fc.HR, fc.DEPTHR, fc.HQ,
                       fc.FUEL, round(0.012 * DEN), 3, 4)
        S0 = fc.FillSearch(fc.TestsF(fc.LNUM, fc.LDEN), fc.HI, fc.DEPTH, fc.WMIN, fc.KAPPA, fc.HR, fc.DEPTHR,
                           fc.HQ, fc.FUEL)
        sys.setrecursionlimit(100000)
        bl = [(a[2], a[3]), (a[0], a[1])]
        c, w = S.work(lambda: S.solveR(bl, True, K))
        c0 = S0.solveR(bl, True, K)
        print(f'theorem flipPart{fc.TAG} : kids (solveG opsFl{fc.TAG} fillTests stratFl{fc.TAG} {fc.FUEL}) {a[3]} '
              f'[({a[0]}, {a[1]})] true [] {a[2]} K ≤ {c} := by decide +kernel')
        print(f'cost/K = {c / K:.6f}; the search of the theorem: {c0} ({c0 / K:.6f} K); {S.stat}; '
              f'{w["calls"]} boxes ({w["fcalls"]} over frozen parts), predicted {fc.pred(w):.0f} s of the kernel')
        return 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main())
