#!/usr/bin/env python3
"""flip_proto.py H DEPTH KAPPA DEPTHR HR HQ LN/LD [--noflip] [--neg] [--norev] [--maxlen N] [--minc X] [--cap X]: the
exact search of fill_cert.py with one more bound for a box: its reversal through its largest prime, as
`lib/pnt/SieveAdFlipSum.lean` and `lib/pnt/SieveAdFrozTests.lean` have it. A measurement, not a certificate: the
Lean search does not call this rule yet.

The rule. A box `bl = β ++ [ctx]` of two primes or more, the cell `ctx = (l₁, h₁)` of its largest prime at least
one unit above the next prime's cell. The frozen part is the numbers `R = ∏a·m`, `a` in the cells `β` and `m`
rough at the least prime of `a`, with `R` in the slab `(x^{1−h₁}, x^{1−l₁}]` (exponents in units of 1/DEN; one
unit narrower at each end for a term of the sign +). The term of the box is the terms of `n/R` at the level
`t = ⌈h₁/2⌉` over the frozen part, up to the `R` within one unit of the slab's ends (`bd_flip_neg`,
`bd_flip_pos`), and those are a tree of Buchstab steps on the chain of primes of `n/R` from a floor `f` to `t`,
searched as `rev_cert.py` searches the tree of a reversed term, with the tests `frozTests` (`okIF`, `okJF3`,
`okJF2` of `lib/pnt/SieveAdFrozDefs.lean`: the cofactor is one more bit of a set, and the comparisons at a floor
have `Kb = 12 + DEN/lo_s` cells of room). With the tree's cost `c` in units of `1/K` of the sum of `1/R`, the cost
of the box is

    (c·(h₁·D₀ + E) + bdK·E)/(DEN·K)    for the sign −,        (c·h₁·D₀ + bdK·E)/(DEN·K)    for the sign +,

`D₀ = dropCost bl` the share of the box, `E = (h₁ + 1)·dropCost(β ++ [(h₁ − 1, h₁ + 1)]) +
(l₁ + 1)·dropCost(β ++ [(l₁ − 1, l₁ + 1)])` the shares of the two ends, and `bdK ctx t` Buchstab's bound at the
level. The strategy proposes the sets of the tests with the cofactor as one more cell (widened by `Kb`, for the
room of the tests), and cuts the range of the second prime one unit below the first prime's cell. A term of the
sign + is reversed only where its other bound exceeds `--minc` (in units of `K`); `--neg` reverses the terms of the
sign − only, `--norev` drops the reversal of rev_cert.py, `--maxlen` bounds the primes of a reversed box.

Values (12 November 2026; `H 6 10 3 0.012 0.02`, boxes of at most four primes): at 2165/1000 with H = 0.005 the
search costs 0.897 K on 1.1·10^7 boxes (0.911 without the reversal of rev_cert.py; that reversal alone, the
theorem's search, 0.951; none, 1.221), and at 2160/1000, 0.967 K on 1.2·10^7 boxes (1.018 without this rule).
With H = 0.01 at 2165/1000: 1.438 with no reversal, 1.306 with rev_cert.py's, 1.286 with this one, 1.276 with
both; and with `--maxlen 5 --norev`, 1.213 on 5.6·10^6 boxes (thirteen minutes). With H = 0.005 and `--maxlen 5`
at 2165/1000: 0.829 K on 2.7·10^7 boxes, 2.4·10^7 of them over frozen parts (an hour). The model (`harman_sieve.py cells 2165/1000 --no-window --fill --shrink 0.0015 --h 0.005 --flips 4 --nest 1
--rev first,floor,offdiag`) has 0.781 where this search has 0.897, as it has 0.851 for the shapes of rev_cert.py
where the search has 0.951.

It prints the reversals' attempts by number of primes, sign and outcome (`len`: a box of one prime or of more
than `--maxlen`; `sep`: the second prime's cell not below the first's; `fit`: no room for the ends; `try`, `win`
and `gain`, the cost saved in units of `K`), then the cost, the boxes searched and the counts.

Needs Python 3 only. Seven minutes at H = 0.005.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import rev_cert as rc  # noqa: E402
import fill_cert as fc  # noqa: E402
from tree_cert import DEN, K, cdiv, tsub, loSum, hiSum, vanishOK, dropC, mSum, dropCost  # noqa: E402
from rev_cert import Ops, cellsOK, bdK, revOK  # noqa: E402


class FlipSearch(fc.FillSearch):
    def __init__(self, *a, flip=True, pos=True, maxlen=4, minc=1e-5, cap=64, **kw):
        super().__init__(*a, **kw)
        self.flip, self.pos, self.maxlen, self.minc, self.cap = flip, pos, maxlen, round(minc * K), cap * K
        self.frz = None
        self.reasons = {}
        self.stat.update(fliptry=0, flipwin=0, fliproot=0, flipcap=0, postry=0, poswin=0)
        self.W.update(fcalls=0)
        self.OR = Ops(lambda bl: True, vanishOK, dropC, self.altF)

    # the exponents of a set of bits over ch ++ beta ++ [cofactor]
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

    # the tests of the tree over the frozen part (SieveAdFrozDefs.lean)
    def coreI2(self, u, v, r1, r2):
        Ln, Ld = self.T.Ln, self.T.Ld
        return (Ld * DEN + 2000 * Ln <= 2000 * Ln * r1 and 2 * Ld * DEN + 3 * Ln <= 3 * Ln * u
                and 2 * Ld * DEN + 3 * Ln * (r2 + 1 + v) <= 3 * Ln * DEN
                and 62505 * Ld * DEN + 90137 * Ln <= 62500 * Ln * u + 27637 * Ln * r1
                and 62505 * Ld * DEN + 62500 * Ln * v + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN
                and 125005 * Ld * DEN + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN)

    def okIF(self, bl, cfg):
        e1, e2, Kb, beta = self.frz
        ch = bl[:len(bl) - len(beta)]
        _, s0, sr, _, _ = cfg
        return (all(1 <= c[0] <= c[1] <= DEN for c in bl) and s0 & sr == 0 and 0 < self.loR(e1, beta, ch, sr)
                and self.coreI2(self.loR(e1, beta, ch, s0), self.hiR(e2, beta, ch, s0),
                                self.loR(e1, beta, ch, sr), self.hiR(e2, beta, ch, sr)))

    def okJF3(self, bl, f, cfg):
        e1, e2, Kb, beta = self.frz
        ch = bl[:len(bl) - len(beta)]
        _, s0, _, s1, e = cfg
        T = self.T
        r1, r2 = T.fillLo, T.fillLo + f + 1
        u, v = T.uOf(r1), T.vOf(r2)
        c0lo = tsub(self.loR(e1, beta, ch, s0), Kb)
        t = tsub(u, c0lo)
        D1 = self.hiR(e2, beta, ch, s1) + Kb + (t + r2 if e else 0)
        D2 = self.hiRc(e2, beta, ch, s1) + Kb + (0 if e else t + r2)
        return (0 < f and all(f <= c[0] <= c[1] <= DEN for c in bl) and T.zone(r1, r2, u, v) and r1 + f < r2
                and u + f < v and u <= t + c0lo and self.hiR(e2, beta, ch, s0) + Kb < v and T.leaves(D1, D2))

    def okJF2(self, bl, f, cfg):
        e1, e2, Kb, beta = self.frz
        ch = bl[:len(bl) - len(beta)]
        _, s0, sr, s1, e = cfg
        T = self.T
        r1, r2 = tsub(self.loR(e1, beta, ch, sr), Kb), self.hiR(e2, beta, ch, sr) + Kb
        u, v = T.uOf(r1), T.vOf(r2)
        c0lo = tsub(self.loR(e1, beta, ch, s0), Kb)
        t = tsub(u, c0lo)
        D1 = self.hiR(e2, beta, ch, s1) + Kb + (t if e else 0)
        D2 = self.hiRc(e2, beta, ch, s1) + Kb + (0 if e else t)
        return (0 < f and all(f <= c[0] <= c[1] <= DEN for c in bl) and s0 & sr == 0
                and 0 < self.loR(e1, beta, ch, sr) and T.zone(r1, r2, u, v) and u + f < v and u <= t + c0lo
                and self.hiR(e2, beta, ch, s0) + Kb < v and T.leaves(D1, D2))

    # proposals for the boxes over the frozen part: the cofactor as one more cell
    def vbox(self, bl):
        e1, e2, Kb, beta = self.frz
        hi = tsub(e2, loSum(beta))
        if hi < 2:
            return bl
        return bl + [(max(1, tsub(e1, hiSum(beta))), hi)]

    def anyI(self, bl):
        if self.frz is None:
            return super().anyI(bl)
        blv = self.vbox(bl)
        for cfg in self.propI2(blv, loSum(blv)):
            self.W['okI2'] += 1
            if self.okIF(bl, cfg):
                return True
        return False

    def propJ(self, bl):
        if self.frz is None:
            return super().propJ(bl)
        Kb = self.frz[2]
        blv = [(max(1, a - Kb), b + Kb) for a, b in self.vbox(bl)]
        lomin, ls, hs = min([DEN] + [c[0] for c in blv[:len(bl)]]), loSum(blv), hiSum(blv)
        if self.T5 < hs:
            return []
        r = self.propJ2(blv, lomin, ls, hs)
        out = []
        if r[0] < lomin:
            r3 = self.propJ3(blv, ls, hs, 8, min(lomin, self.fmax3))
            if r3 is not None and r[0] < r3[0]:
                out.append(r3)
        if r[1] is not None:
            out.append(r)
        return out

    def firstJ(self, bl, lo0, ps):
        if self.frz is None:
            return super().firstJ(bl, lo0, ps)
        for f, cfg in ps:
            if 0 < f <= lo0 and (self.okJF3(bl, f, cfg) if cfg[0] == 2 else self.okJF2(bl, f, cfg)):
                return f, cfg
        return None

    # the main strategy: one more cut, just below the first prime's cell
    def cutsOfG(self, bl, f):
        cs = super().cutsOfG(bl, f)
        if self.flip and bl:
            c = bl[-1][0] - 1
            if f < c and c not in cs:
                cs = sorted(cs + [c])
        return cs

    # the tree over the frozen part
    def flipTree(self, ctx, beta, t, par, e1, e2, lim):
        los = beta[0][0]
        Kb = 12 + DEN // los
        self.frz = (e1, e2, Kb, beta)
        w0 = self.W['calls']
        try:
            fj = self.firstJ(beta, min(los, t), self.propJ(beta))
            if fj is None:
                self.stat['fliproot'] += 1
                return lim
            f = fj[0]
            O = self.opsK(ctx, len(beta))
            S = self.stratK(ctx, len(beta))
            return self.kidsG(lambda b, p, l: self.solveG(O, S, self.fuel, b, p, l), t, beta, par,
                              self.cutsK(ctx, [], t, f), f, lim)
        finally:
            self.frz = None
            self.W['fcalls'] += self.W['calls'] - w0

    def flipCost(self, bl, par, lim):
        R = self.reasons
        key = (len(bl), par)
        if not 2 <= len(bl) <= self.maxlen:
            R[key + ('len',)] = R.get(key + ('len',), 0) + 1
            return lim
        ctx, beta = bl[-1], bl[:-1]
        l1, h1 = ctx
        t = (h1 + 1) // 2
        if not (cellsOK(bl) and hiSum(bl) + 2 <= DEN and beta[-1][1] + 1 <= l1 and 3 <= l1 and t <= l1
                and h1 + t + 1 <= DEN):
            why = 'sep' if not beta[-1][1] + 1 <= l1 else ('fit' if not hiSum(bl) + 2 <= DEN else 'other')
            R[key + (why,)] = R.get(key + (why,), 0) + 1
            return lim
        R[key + ('try',)] = R.get(key + ('try',), 0) + 1
        D0 = dropCost(bl)
        endw = (h1 + 1) * dropCost(beta + [(h1 - 1, h1 + 1)]) + (l1 + 1) * dropCost(beta + [(l1 - 1, l1 + 1)])
        bd = bdK(ctx, t)
        if not par:
            c = self.flipTree(ctx, beta, t, True, DEN - h1, DEN - l1 + 1, self.cap)
            if self.cap <= c:
                self.stat['flipcap'] += 1
                return lim
            return cdiv(c * (h1 * D0 + endw) + bd * endw, DEN * K)
        c = self.flipTree(ctx, beta, t, False, DEN - h1 + 1, DEN - l1, self.cap)
        if self.cap <= c:
            self.stat['flipcap'] += 1
            return lim
        return cdiv(c * h1 * D0 + bd * endw, DEN * K)

    def altF(self, bl, par, l):
        r = l
        if self.rev and not par and revOK(bl):
            self.stat['revtry'] += 1
            c = self.revCost(bl, r)
            if c < r:
                self.stat['revwin'] += 1
                r = c
        if self.flip and self.frz is None and (not par or self.pos):
            self.stat['postry' if par else 'fliptry'] += 1
            c = self.flipCost(bl, par, r)
            if c < r:
                self.stat['poswin' if par else 'flipwin'] += 1
                key = (len(bl), par, 'win')
                self.reasons[key] = self.reasons.get(key, 0) + 1
                key = (len(bl), par, 'gain')
                self.reasons[key] = self.reasons.get(key, 0) + (r - c) / K if r < 10 * K else self.reasons.get(key, 0)
                r = c
        return r

    def nodeG(self, O, S, rec, x, bl, par, lim):
        dc = O.drp(bl, par)
        if dc is not None:
            bc = self.buchG(S, rec, x, bl, par, dc if dc <= lim else lim)
            m = dc if dc <= bc else bc
            if self.pos and O is self.OR and self.minc < m:
                rc = O.alt(bl, par, m if m <= lim else lim)
                if rc < m:
                    return rc
            return m
        return super().nodeG(O, S, rec, x, bl, par, lim)


def run(h, depth, kappa, depthR, hR, hQ, ln, ld, **kw):
    S = FlipSearch(fc.TestsF(ln, ld), round(h * DEN), depth, fc.WMIN, kappa, round(hR * DEN), depthR,
                   round(hQ * DEN), fc.FUEL, **kw)
    sys.setrecursionlimit(100000)
    f0, _ = fc.root_of(S)
    cuts = fc.rowCuts(S, f0)
    c = S.kidsR(DEN // 2 + 1, [], False, cuts[1:-1], cuts[0], 4 * K)
    print(sorted(S.reasons.items()), flush=True)
    return c / K, S.W['calls'], S.W['fcalls'], S.stat, f0 / DEN


if __name__ == '__main__':
    a = sys.argv[1:]
    kw = {}
    if '--noflip' in a:
        kw['flip'] = False
    if '--neg' in a:
        kw['pos'] = False
    if '--norev' in a:
        kw['rev'] = False
    for name, key, conv in (('--maxlen', 'maxlen', int), ('--minc', 'minc', float), ('--cap', 'cap', int)):
        if name in a:
            kw[key] = conv(a[a.index(name) + 1])
    ln, ld = (int(v) for v in a[6].split('/'))
    import time
    t0 = time.time()
    r = run(float(a[0]), int(a[1]), int(a[2]), int(a[3]), float(a[4]), float(a[5]), ln, ld, **kw)
    print(' '.join(a), '->', 'cost %.5f boxes %d (frozen %d) floor %.4f' % (r[0], r[1], r[2], r[4]), r[3],
          '%.0fs' % (time.time() - t0), flush=True)
