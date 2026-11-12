#!/usr/bin/env python3
"""Measurements on the plan of `hint_cert.py`, the search of the theorem at `L = 2150/1000`: where its cost is,
and what variants of the search would give. Not a certificate, and nothing here is in Lean beyond what the notes
say (`docs/research-opportunities.md` §3.1).

    python3 tools/linnik/hint_probe.py LNUM/LDEN H HF MAXLEN STEP PROCS mode [mode ...]

plans the cells of the first prime of index `0, STEP, 2 STEP, …` with cells of side at most `H`, chains' cells of
side at most `HF` over the frozen parts and boxes of at most `MAXLEN` primes reversed (the theorem: `2150/1000
0.004 0.006 6`), once for each `mode`, a comma-separated list of:

  * `base`: the planner as it is (without its merging of cells, which changes no cost but the dropped cells').
  * `break`: the plan's cost by what is done: dropped boxes of the main tree by their number of primes, reversed
    boxes by theirs and, inside, the dropped boxes of the chain by its length.
  * `mI`, `mJ`, `fI`, `fJ`: the tests of a term (`I`) or of the terms at a floor (`J`), in the main tree (`m`) or
    over the frozen parts (`f`), taken at the midpoints of the cells, which is no certificate: what the cells
    cost. `fIc`, `fIb`, `fIs`: for the term tests over the frozen parts, only the chain's cells, the frozen
    primes' cells, or the slab of the frozen number at the midpoint.
  * `cm`, `cf`: when no configuration evaluates a box, its newest cell is cut at the ends of the largest part
    that one configuration evaluates (found from those that pass at the cell's ends and middle), and only the
    rest is searched, in the main tree or over the frozen parts. Sound with the rules that are proved
    (`SieveAd.Rules.split` at any cut); the search led by hints has no step that reads such a cut.
  * `pos`: a box of the sign `+` may be reversed through its largest prime too, the chain's first boxes then
    needing upper bounds (`SieveAd.bd_flip_pos_at`, with the wider frozen part's tests; the search's rule is not
    written).
  * `l2`: a second level. Inside the tree over the frozen part of a box reversed through `p₁`, a chain's box of
    the sign `−` is reversed again through `p₂`, the largest prime of the frozen number `R = p₂R₂`: the frozen
    numbers of the second level are `R' = R₂N`, `N = n/R` the chain's primes and their cofactor, with `N` in the
    cell of `p₁` and `x/R'` in the cell of `p₂`, and the tree is on a chain of primes of `n/R'` below
    `x^{t₂}`. Its cost is at most `(h₂/DEN)(D₁/K)` times the first level's weight, `D₁` the drop bound of the
    chain's box. The tests read the sums of the roles (primes of `R₂`, its cofactor, the first chain's primes,
    their cofactor, the second chain's primes) from the cells and the two slabs. A prototype: the ends of the
    second slab are not costed, and none of it is proved. `one`: also when `R` has one prime, its cofactor then
    taken free of primes below the lower end of that prime's cell, with a rough penalty (`penN`: `N` times the
    cell's relative width times `D₁`; default `3`).
  * `any`: a box of the sign `−` may be reversed through a prime that is neither its largest nor its least.
  * `lamN`: the planner chooses by cost plus `N·10⁻⁶ K` for each second that `hint_cert.SEC` predicts of the
    kernel: a box of the sign `+` is decomposed further only if that saves more than its time is worth, and a
    box of the sign `−` is reversed or decomposed by the same count. The plan is one that the kernel follows as
    it is; the line gives the predicted seconds and the steps. Alone in its mode (with the planner's merging).

Each line gives the cost on the cells planned, in units of `K`, the boxes searched and the counts of the
variants. On twenty of the 115 cells of the first prime (`STEP = 6`) at the theorem's parameters, 12 November
2026: `base` 0.15403; `mI` 0.14513, `mJ` 0.14506, `fI` 0.13538, `fJ` 0.14775, all four 0.11621; `fIc` 0.14785,
`fIb` 0.14595, `fIs` 0.15219; `cm` 0.15175, `cm,cf` 0.14703 (212529 cuts); `l2` 0.15042 on 2.6 times the boxes;
`pos` 0.15043; `lam0` 0.15405 in 3686 predicted seconds, `lam1` 0.15425 in 3142, `lam3` 0.15494 in 2794,
`lam10` 0.16060 in 1879, `lam30` 0.17193 in 1198, `lam100` 0.20144 in 673; `break`: dropped boxes of two primes
41.8%, of four 22.2%, of six 1.1%, reversed boxes of three primes 33.8% (33.7% the dropped boxes of the chain's
first prime), of five 1.1%.

Needs Python 3 only.
"""
import multiprocessing
import os
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rev_cert as rc  # noqa: E402
import fill_cert as fc  # noqa: E402
import flip_cert as fl  # noqa: E402
import hint_cert as hc  # noqa: E402
from tree_cert import DEN, K, BIG, cdiv, tsub, loSum, hiSum, mSum, dropCost  # noqa: E402
from rev_cert import CAPK, dropK  # noqa: E402
from flip_cert import flipT, flipOK  # noqa: E402

# the planner that is at work in this process: the virtual box of a frozen part is asked of it at the second level
PL = None
_vboxF = fl.vboxF


def vboxX(ctx, beta, bl):
    if PL is not None and PL.l2 is not None:
        return PL.vbox2(bl)
    return _vboxF(ctx, beta, bl)


fl.vboxF = vboxX
hc.vboxF = vboxX


def midI(bl):
    return [((c[0] + c[1]) // 2, (c[0] + c[1]) // 2) for c in bl]


def midJ(bl):
    x = bl[0]
    return [(x[0], (x[0] + x[1]) // 2 + 1)] + [((c[0] + c[1]) // 2, (c[0] + c[1]) // 2 + 1) for c in bl[1:]]


class Probe(hc.Planner):
    """`hint_cert.Planner` with the variants that the flags `fl_` name."""

    merge = False
    dmerge = None
    fl_ = ()
    lamK = 0
    l2 = None
    penf = 3
    frac = 8
    ncut = 0

    # the tests at midpoints
    def _frozMid(self, f, blm, deg):
        frz, ctx = self.frz, self.fctx
        m = (ctx[0] + ctx[1]) // 2
        nb = len(frz[3])
        try:
            if deg:
                self.frz, self.fctx = (DEN - m, DEN - m + 1, frz[2], blm[len(blm) - nb:]), (m, m)
            else:
                self.frz, self.fctx = (DEN - m - 1, DEN - m + 1, frz[2], blm[len(blm) - nb:]), (m, m + 1)
            return f(blm)
        finally:
            self.frz, self.fctx = frz, ctx

    def anyI(self, bl):
        sup = super().anyI
        if self.l2 is not None:
            return sup(bl)
        if self.frz is None:
            return sup(midI(bl) if 'mI' in self.fl_ else bl)
        if 'fI' in self.fl_:
            return self._frozMid(sup, midI(bl), True)
        part = [x for x in ('fIc', 'fIb', 'fIs') if x in self.fl_]
        if not part:
            return sup(bl)
        frz, ctx = self.frz, self.fctx
        nb = len(frz[3])
        ch, beta = bl[:len(bl) - nb], bl[len(bl) - nb:]
        if 'fIc' in part:
            ch = midI(ch)
        if 'fIb' in part:
            beta = midI(beta)
        e1, e2, c2 = frz[0], frz[1], ctx
        if 'fIs' in part:
            m = (ctx[0] + ctx[1]) // 2
            e1, e2, c2 = DEN - m, DEN - m + 1, (m, m)
        try:
            self.frz, self.fctx = (e1, e2, frz[2], beta), c2
            return sup(ch + beta)
        finally:
            self.frz, self.fctx = frz, ctx

    def floorOf(self, bl, lo0):
        sup = super().floorOf
        if self.l2 is not None:
            return sup(bl, lo0)
        if self.frz is None:
            return sup(midJ(bl) if 'mJ' in self.fl_ else bl, lo0)
        if 'fJ' in self.fl_:
            return self._frozMid(lambda b: sup(b, lo0), midJ(bl), False)
        return sup(bl, lo0)

    # the newest cell cut at the ends of the part that a configuration evaluates
    def passCfg(self, bl):
        if self.frz is None:
            for cfg in self.propI2(bl, loSum(bl)):
                if self.T.okI(bl, cfg):
                    return cfg
            return None
        blv = fl.vboxF(self.fctx, self.frz[3], bl)
        for cfg in self.propI2(blv, loSum(blv)):
            if self.okIF(bl, cfg):
                return cfg
        return None

    def okc(self, bl, cfg):
        return self.T.okI(bl, cfg) if self.frz is None else self.okIF(bl, cfg)

    def bestCut(self, bl):
        (a, top), b = bl[0], bl[1:]
        w = top - a
        if w < 2 * self.wmin:
            return None
        best = None
        for p in (a, (a + top) // 2, top):
            cfg = self.passCfg([(p, p)] + b)
            if cfg is None:
                continue
            lo, hi = a, p
            for _ in range(8):
                if lo >= hi:
                    break
                mid = (lo + hi) // 2
                if self.okc([(mid, p)] + b, cfg):
                    hi = mid
                else:
                    lo = mid + 1
            c1 = hi
            lo, hi = p, top
            for _ in range(8):
                if lo >= hi:
                    break
                mid = (lo + hi + 1) // 2
                if self.okc([(c1, mid)] + b, cfg):
                    lo = mid
                else:
                    hi = mid - 1
            if best is None or lo - c1 > best[1] - best[0]:
                best = (c1, lo)
        if best is not None and best[1] - best[0] >= max(self.wmin, w // self.frac):
            return best
        return None

    # the roles of the second level: the bits of a set are the second chain's cells, the first chain's, the frozen
    # primes of R2, its cofactor m, the first chain's cofactor m'
    def roles2(self, nd, m):
        _, nch, nb = self.l2
        mb = m >> nd
        return (m & ((1 << nd) - 1), mb & ((1 << nch) - 1), (mb >> nch) & ((1 << nb) - 1), (mb >> (nch + nb)) & 1,
                (mb >> (nch + nb + 1)) & 1)

    def loR(self, e1, beta, ch, m):
        if self.l2 is None:
            return super().loR(e1, beta, ch, m)
        ctx1, nch, _ = self.l2
        ch1, bp = beta[:nch], beta[nch:]
        C1, C2 = tsub(ctx1[0], 1), ctx1[1] + 1
        D, C, B, im, im2 = self.roles2(len(ch), m)
        if im and im2:
            a = tsub(e1, tsub(hiSum(bp), mSum(1, bp, B)) + tsub(hiSum(ch1), mSum(1, ch1, C)))
        elif im:
            a = tsub(tsub(e1, C2), tsub(hiSum(bp), mSum(1, bp, B))) + mSum(0, ch1, C)
        elif im2:
            a = tsub(C1, tsub(hiSum(ch1), mSum(1, ch1, C))) + mSum(0, bp, B)
        else:
            a = mSum(0, bp, B) + mSum(0, ch1, C)
        return a + mSum(0, ch, D)

    def hiR(self, e2, beta, ch, m):
        if self.l2 is None:
            return super().hiR(e2, beta, ch, m)
        ctx1, nch, _ = self.l2
        ch1, bp = beta[:nch], beta[nch:]
        C1, C2 = tsub(ctx1[0], 1), ctx1[1] + 1
        D, C, B, im, im2 = self.roles2(len(ch), m)
        if im and im2:
            a = tsub(e2, tsub(loSum(bp), mSum(0, bp, B)) + tsub(loSum(ch1), mSum(0, ch1, C)))
        elif im:
            a = tsub(tsub(e2, C1), tsub(loSum(bp), mSum(0, bp, B))) + mSum(1, ch1, C)
        elif im2:
            a = tsub(C2, tsub(loSum(ch1), mSum(0, ch1, C))) + mSum(1, bp, B)
        else:
            a = mSum(1, bp, B) + mSum(1, ch1, C)
        return a + mSum(1, ch, D)

    def hiRc(self, e2, beta, ch, m):
        if self.l2 is None:
            return super().hiRc(e2, beta, ch, m)
        full = (1 << (len(ch) + len(beta) + 2)) - 1
        return self.hiR(e2, beta, ch, full & ~m)

    def vbox2(self, bl):
        ctx1, nch, _ = self.l2
        E1, E2, _, base = self.frz
        ch1, bp = base[:nch], base[nch:]
        C1, C2 = tsub(ctx1[0], 1), ctx1[1] + 1
        mlo = max(1, tsub(tsub(E1, C2), hiSum(bp)))
        mhi = max(mlo, tsub(tsub(E2, C1), loSum(bp)))
        m2lo = max(1, tsub(C1, hiSum(ch1)))
        m2hi = max(m2lo, tsub(C1, loSum(ch1)))
        return bl + [(mlo, mhi), (m2lo, m2hi)]

    def pFlip2(self, bl, lim):
        """The chain's box `bl` (over the frozen part of the first level) reversed through the largest prime of
        the frozen number."""
        frz, ctx1 = self.frz, self.fctx
        beta = frz[3]
        nb = len(beta)
        ch1 = bl[:len(bl) - nb]
        if nb < (1 if 'one' in self.fl_ else 2) or not ch1 or len(bl) - 1 > 9:
            return lim, None
        ctx2, bp = beta[-1], beta[:-1]
        t2 = flipT(ctx2)
        if not ((not bp or bp[-1][1] + 1 <= ctx2[0]) and 3 <= ctx2[0] and t2 <= ctx2[0] and ctx2[1] + t2 + 1 <= DEN):
            return lim, None
        D1 = dropK(ctx1, ch1, True)
        if D1 is None:
            return lim, None
        self.stat['flip2try'] += 1
        A = ctx2[1] * D1
        if A == 0:
            return 0, ('F2',)
        pen = 0 if bp else cdiv(self.penf * D1 * (ctx2[1] - ctx2[0]), ctx2[0])
        if lim <= pen:
            return lim, None
        cl = min(CAPK, tsub(lim - pen, 1) * (DEN * K) // A + 1)
        base = ch1 + bp
        lomin = min([c[0] for c in base] + [ctx2[0]])
        Kb = 12 + DEN // (bp[0][0] if bp else ctx2[0]) + DEN // ch1[0][0]
        self.frz, self.fctx, self.l2 = ((tsub(DEN, ctx2[1]), tsub(DEN, ctx2[0]) + 1, Kb, base), ctx2,
                                        (ctx1, len(ch1), len(bp)))
        w0 = self.W['calls']
        try:
            S = self.stratF(ctx2, base)
            fj = self.floorOf(base, min(lomin, t2))
            if fj is None:
                self.stat['flip2root'] += 1
                return lim, None
            sel, f = fj
            O = self.opsK(ctx2, len(base))
            cc, ns = self.pKids(lambda b, p, l: self.pSolve(O, S, self.fuel, b, p, l), t2, base, True,
                                S.cuts(base, f), f, cl, O.drp)
        finally:
            self.frz, self.fctx, self.l2 = frz, ctx1, None
            self.W['calls2'] += self.W['calls'] - w0
        if cl <= cc:
            return lim, None
        return cdiv(cc * A, DEN * K) + pen, ('F2', sel) + ns

    def pFlipAt(self, bl, j, lim, pos):
        """The box reversed through the prime of its cell `j`; for a box of the sign `+` (`pos`) the chain's
        first boxes need upper bounds."""
        ctx, beta = bl[j], bl[:j] + bl[j + 1:]
        t = flipT(ctx)
        if j + 1 < len(bl) and not (rc.cellsOK(bl) and hiSum(bl) + 2 <= DEN and bl[j - 1][1] + 1 <= ctx[0]
                                    and ctx[1] + 1 <= bl[j + 1][0] and 3 <= ctx[0] and t <= ctx[0]
                                    and ctx[1] + t + 1 <= DEN):
            return lim, None
        E = ((ctx[1] + 1) * dropCost(bl[:j] + [(tsub(ctx[1], 1), ctx[1] + 1)] + bl[j + 1:])
             + (ctx[0] + 1) * dropCost(bl[:j] + [(tsub(ctx[0], 1), ctx[0] + 1)] + bl[j + 1:]))
        A, B = ctx[1] * dropCost(bl) + (0 if pos else E), rc.bdK(ctx, t) * E
        if A == 0:
            return lim, None
        cl = min(CAPK, tsub(tsub(lim, 1) * (DEN * K), B) // A + 1)
        c = beta[0]
        self.frz, self.fctx = (tsub(DEN, ctx[1]), tsub(DEN, ctx[0]) + 1, 12 + DEN // c[0], beta), ctx
        try:
            S = self.stratF(ctx, beta)
            fj = self.floorOf(beta, min(c[0], t))
            if fj is None:
                return lim, None
            sel, f = fj
            O = self.opsK(ctx, len(beta))
            cc, ns = self.pKids(lambda b, p, l: self.pSolve(O, S, self.fuel, b, p, l), t, beta, not pos,
                                S.cuts(beta, f), f, cl, O.drp)
        finally:
            self.frz = None
        if cl <= cc:
            return lim, None
        return cdiv(cc * A + B, DEN * K), ('FP' if pos else 'FJ', sel) + ns

    def pSolve(self, O, S, n, bl, par, lim):
        key = 'cm' if self.frz is None else 'cf'
        if key in self.fl_ and self.l2 is None and n > 0 and bl and O.grd(bl) and not O.van(bl) and not self.anyI(bl):
            iv = self.bestCut(bl)
            if iv is not None:
                self.ncut += 1
                x, tot = bl[0], 0
                for s, e in ((x[0], iv[0]), (iv[1], x[1])):
                    if s < e:
                        c, _ = self.pSolve(O, S, n - 1, [(s, e)] + bl[1:], par, lim - tot)
                        tot += c
                        if lim <= tot:
                            return tot, None
                return tot, ('C',)
        return self.pNode(O, S, n, bl, par, lim)

    def pNode(self, O, S, n, bl, par, lim):
        """`hint_cert.Planner.pSolve`, with the variants."""
        self.minfuel = min(self.minfuel, n)
        if n == 0 or not bl or not O.grd(bl):
            return lim, None
        self.W['calls'] += 1
        if O.van(bl):
            return 0, ('V',)
        if self.anyI(bl):
            return 0, ('E',)
        x, fz = bl[0], self.frz is not None
        dc = O.drp(bl, par)
        if dc is not None:
            bc, nb = self.pBuch(O, S, n - 1, x, bl, par, dc if dc <= lim else lim)
            if dc <= bc or nb is None:
                r, how = dc, ('D',)
            elif self.lamK and dc - bc < self.lamK * (hc.secs(nb, fz) - hc.SEC[('D', fz)]):
                r, how = dc, ('D',)
            else:
                r, how = bc, nb
            if 'pos' in self.fl_ and O is self.OR and par and flipOK(self.maxlen, bl) and r > 0:
                self.stat['postry'] += 1
                c, nf = self.pFlipAt(bl, len(bl) - 1, r if r <= lim else lim, True)
                if c < r:
                    self.stat['poswin'] += 1
                    return c, nf
            return r, how
        bc, nb = self.pBuch(O, S, n - 1, x, bl, par, lim)
        l2 = bc if bc <= lim else lim
        if O is self.OR and not par:
            r, how = l2, None
            if self.flip and flipOK(self.maxlen, bl):
                self.stat['fliptry'] += 1
                if self.lamK and nb is not None:
                    c, nf = self.pFlip(bl, lim)
                    if nf is not None and c + self.lamK * hc.secs(nf) < bc + self.lamK * hc.secs(nb):
                        self.stat['flipwin'] += 1
                        return c, nf
                else:
                    c, nf = self.pFlip(bl, r)
                    if c < r:
                        self.stat['flipwin'] += 1
                        r, how = c, nf
            if 'any' in self.fl_ and 3 <= len(bl) <= self.maxlen:
                for j in range(len(bl) - 2, 0, -1):
                    self.stat['anytry'] += 1
                    c, nf = self.pFlipAt(bl, j, r, False)
                    if c < r:
                        self.stat['anywin'] += 1
                        r, how = c, nf
            if r < l2:
                return r, how
        elif 'l2' in self.fl_ and fz and self.l2 is None and not par:
            c, nf = self.pFlip2(bl, l2)
            if c < l2:
                self.stat['flip2win'] += 1
                return c, nf
        if bc < BIG:
            return bc, nb
        return self.pSplit(O, S, n - 1, x, bl, par, lim)


# where the cost of a plan is

def cellsOf(cuts, f, top, bits):
    ends, it = [f], iter(bits)
    for c in cuts:
        if ends[-1] < c < top and next(it):
            ends.append(c)
    ends.append(top)
    return list(zip(ends, ends[1:]))


def wFroz(P, O, S, node, bl, par, acc, nb):
    k = node[0]
    if k in ('E', 'V'):
        return 0
    if k == 'D':
        c = O.drp(bl, par)
        acc[len(bl) - nb] += c
        return c
    if k == 'S':
        x = bl[0]
        mid = (x[0] + x[1]) // 2
        return (wFroz(P, O, S, node[1], [(x[0], mid)] + bl[1:], par, acc, nb)
                + wFroz(P, O, S, node[2], [(mid, x[1])] + bl[1:], par, acc, nb))
    f, _ = P.guide(bl, node[1])
    return sum(wFroz(P, O, S, kid, [(s, e)] + bl, not par, acc, nb)
               for (s, e), kid in zip(cellsOf(S.cuts(bl, f), f, bl[0][1], node[3]), node[2]))


def wFlip(P, node, bl, out):
    ctx, beta = bl[-1], bl[:-1]
    E = ((ctx[1] + 1) * dropCost(beta + [(tsub(ctx[1], 1), ctx[1] + 1)])
         + (ctx[0] + 1) * dropCost(beta + [(tsub(ctx[0], 1), ctx[0] + 1)]))
    A, B = ctx[1] * dropCost(bl) + E, rc.bdK(ctx, flipT(ctx)) * E
    c, t, acc = beta[0], flipT(ctx), Counter()
    P.frz, P.fctx = (tsub(DEN, ctx[1]), tsub(DEN, ctx[0]) + 1, 12 + DEN // c[0], beta), ctx
    try:
        S = P.stratF(ctx, beta)
        f, _ = P.guide(beta, node[1])
        O = P.opsK(ctx, len(beta))
        cc = sum(wFroz(P, O, S, kid, [(s, e)] + beta, True, acc, len(beta))
                 for (s, e), kid in zip(cellsOf(S.cuts(beta, f), f, t, node[3]), node[2]))
    finally:
        P.frz = None
    cost = cdiv(cc * A + B, DEN * K)
    out[f'reversed boxes of {len(bl)} primes'] += cost
    out[f'the share of the reversed boxes of {len(bl)} primes'] += dropCost(bl)
    for j, v in acc.items():
        out[f'reversed boxes of {len(bl)} primes: dropped boxes of a chain of {j}'] += v * A // (DEN * K)
    return cost


def wMain(P, node, bl, par, out):
    k = node[0]
    if k in ('E', 'V'):
        return 0
    if k == 'D':
        c = P.OR.drp(bl, par)
        out[f'dropped boxes of {len(bl)} primes'] += c
        return c
    if k == 'S':
        x = bl[0]
        mid = (x[0] + x[1]) // 2
        return (wMain(P, node[1], [(x[0], mid)] + bl[1:], par, out)
                + wMain(P, node[2], [(mid, x[1])] + bl[1:], par, out))
    if k == 'F':
        return wFlip(P, node, bl, out)
    f, _ = P.guide(bl, node[1])
    return sum(wMain(P, kid, [(s, e)] + bl, not par, out)
               for (s, e), kid in zip(cellsOf(P.SG.cuts(bl, f), f, bl[0][1], node[3]), node[2]))


def job(args):
    global PL
    (ln, ld, h, hF, maxlen, flags), a, b = args
    par_ = hc.Par('probe', ln, ld, h=h, hF=hF, maxlen=maxlen, rev=False)
    P = Probe(fc.TestsF(ln, ld), par_.hI, par_.depth, fc.WMIN, par_.kappa, par_.hR, par_.depthR, par_.hQ, fc.FUEL,
              par_.hF, par_.depthF, par_.maxlen, rev=False)
    P.stat.update(flip2try=0, flip2win=0, flip2root=0, postry=0, poswin=0, anytry=0, anywin=0)
    P.W['calls2'] = 0
    P.fl_ = flags
    lam = [x for x in flags if x.startswith('lam')]
    if lam:
        P.merge, P.dmerge = hc.Planner.merge, hc.Planner.dmerge
        P.lamK = int(lam[0][3:]) * K // 10 ** 6
    for x in flags:
        if x.startswith('pen'):
            P.penf = int(x[3:])
    PL = P
    sys.setrecursionlimit(100000)
    c, node = P.plan([(a, b)], False, 4 * K)
    out = {'cost': c, 'boxes': P.W['calls'], 'second level': P.W['calls2'], 'cuts': P.ncut}
    out.update({k: v for k, v in P.stat.items() if v})
    if lam:
        cnt = Counter()
        hc.count(node, cnt)
        out['seconds'], out['steps'] = hc.secs(node), sum(cnt.values())
    if 'break' in flags:
        bd = Counter()
        assert wMain(P, node, [(a, b)], False, bd) == c
        out['break'] = dict(bd)
    return out


def main():
    a = sys.argv[1:]
    if len(a) < 7:
        print(__doc__)
        return 2
    ln, ld = map(int, a[0].split('/'))
    h, hF, maxlen, step, procs = float(a[1]), float(a[2]), int(a[3]), int(a[4]), int(a[5])
    P = hc.Par('probe', ln, ld, h=h, hF=hF, maxlen=maxlen, rev=False).planner()
    cuts = fc.rowCuts(P, fc.root_of(P)[0])
    rows = list(zip(cuts, cuts[1:]))[::step]
    for mode in a[6:]:
        flags = tuple(x for x in mode.split(',') if x != 'base')
        assert not [x for x in flags if x.startswith('lam')] or len(flags) == 1, 'lamN stands alone'
        t = time.time()
        jobs = [((ln, ld, h, hF, maxlen, flags), x, y) for x, y in rows]
        if procs > 1:
            with multiprocessing.Pool(procs) as pool:
                res = pool.map(job, jobs, chunksize=1)
        else:
            res = [job(j) for j in jobs]
        tot, bd = Counter(), Counter()
        for r in res:
            bd.update(r.pop('break', {}))
            tot.update(r)
        cost = tot.pop('cost')
        rest = ', '.join(f'{k} {v:.0f}' if isinstance(v, float) else f'{k} {v}' for k, v in tot.items() if v)
        print(f'{a[0]} h={h} hF={hF} cells {len(rows)}/{len(cuts) - 1} {mode}: cost {cost / K:.5f}; {rest}; '
              f'{time.time() - t:.0f} s', flush=True)
        for k in sorted(bd):
            print(f'    {k}: {bd[k] / K:.5f} ({100 * bd[k] / cost:.1f}%)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
