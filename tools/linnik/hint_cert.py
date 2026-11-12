#!/usr/bin/env python3
"""hint_cert.py [--check] [--out DIR] [--procs N] | --try TAG a/b H HF MAXLEN [--rows I J] [--out DIR]: the
search with the reversal through the largest prime as a plan, the hints that lead the kernel through the plan, and
the Lean files of the theorem at L = 2150/1000.

`flip_cert.py`'s search tries, at each box, what its strategy proposes, and keeps the cheapest; the kernel, running
it, spends most of its time on what is not kept, on the search for a configuration among the sets of a box's
cells, and on traversals of the box. Here the search is run once, in Python, and the plan it keeps is written as
hints: a number read from its low end in the order of the search (`lib/pnt/SieveAdDirDefs.lean`). At a box:

    0        a configuration evaluates the box: `0` for the rest at the first cell, or `1` and three bits for
             its cell; then the set of the first variable, a bit for each cell of the box
    10       Buchstab's identity: four bits `sel` name the rest and with it the floor (`sel` even: the rest at
             the cell `sel/2`, the floor the least of the lower ends and of the window's width; `sel` odd: the
             rest among the tree's primes, the floor after `sel/2` steps `f -> 3f/4` from the largest); the set
             `s0`; `0` for the set `s1` of all the cells but the last and the side `true`, or `1`, the set `s1`
             and the side; then the cells of the new prime
    110      dropped
    1110     the reversal through the largest prime: the fields of a Buchstab step for the terms of the frozen
             part, then the cells of the chain's first prime
    11110    the last cell cut in two
    111110   no term

and the cells of a new prime are given by their cuts, a code each: `0`, no more cut; `1` and two bits `j < 3`,
a cut `j + 1` steps of the grid after the last grid point used; `1`, `11` and three bits `t`: `t < 4`, a cut
`t + 4` steps after; `t = 4`, seven steps and no cut; `t = 5, 6, 7`, a cut at one of the three cuts that are not
on the grid. Consecutive evaluated cells that one test covers are one cell. Over a frozen part a set has one more
bit, the cofactor's. The kernel follows the hints (`SieveAd.solveD`) and checks each step; the cost it returns is
a bound whatever the hints are (`lib/pnt/SieveAdDir.lean`).

  * `Planner`: `flip_cert.FlipSearch`'s search, returning with each cost the plan kept, as a tree
    (`pSolve`, `pBuch`, `pKids`, `pSplit`, `pFlip`); `tryJ2`, `guideJ`, `guide`: the proposal of the strategy that
    four bits name; `dser`, `dserF`, `dserKids` write a plan as fields and `pack` as a number;
  * `dSolve`, `dStep`, `dKidsC`, `dPart`, `dFlipTree`, `dFlipCost`, `dAltF`, with `cfgIP`, `cfgJP`, `pickP`,
    `cfgIM`, `cfgJM`, `cfgIF`, `cfgJF`, `parM`, `parF`: `solveD`, `stepD`, `kidsC`, `partD`, `flipTreeD`,
    `flipCostD`, `altFD` and what they read from the hints, definition by definition; every part is run through
    them before it is written;
  * `plan_all`, `cut`, `add_part`: the cells of the first prime planned one by one (in `--procs` processes), and
    the plan cut into parts of at most `cap` predicted seconds of the kernel: consecutive cells of one prime, a
    heavy cell cut by its own Buchstab step.

It writes `lib/pnt/SieveHint21500.lean` (the exponent and the search), `SieveHint21500P<k>.lean` (the parts, each
by `decide +kernel`) and `Linnik21500.lean` (the route, the bound from the parts, and the theorem). With
`--check`, nothing is written: the files are regenerated in memory and compared with `lib/pnt` (exit 1 on a
difference); it is not part of `check_certificate.py`, for it searches for ten minutes on four cores. With
`--try`, the search is planned with other parameters (cells of side H, chains' cells of side HF over the frozen
parts, boxes of at most MAXLEN primes reversed) and its cost and the plan's size are printed; with `--out`, its
files are written to DIR.

Values (12 November 2026): at 2150/1000 with cells of side 0.004 and chains' cells 0.006, boxes of three and five
primes reversed, the search costs 0.94847 K on 3.4·10^7 boxes (2.8·10^7 over frozen parts; nine minutes on four
cores), and its plan has 3.4·10^6 steps. The kernel takes 0.3 ms on an evaluated box (0.8 ms over a frozen part),
1.2 ms on a Buchstab step (2.1 ms), 0.25 ms on a dropped box (0.35 ms) and 3 ms on a reversal's root; with the
configurations searched by the kernel and the box read sum by sum, as in the first certificate of this theorem,
it took 3.7 ms, 7.6 ms (13 ms), 0.9 ms and 20 ms.

Needs Python 3 only.
"""
import os
import sys
import textwrap
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import rev_cert as rc  # noqa: E402
import fill_cert as fc  # noqa: E402
import flip_cert as fl  # noqa: E402
from tree_cert import DEN, K, BIG, cdiv, tsub, loSum, hiSum, dropCost  # noqa: E402
from rev_cert import bdK, CAPK  # noqa: E402
from flip_cert import flipT, flipOK, vboxF  # noqa: E402


# the theorem's exponent and parameters: cells of side at most H, chains' cells over the frozen parts at most HF,
# boxes of at most MAXLEN primes reversed through their largest prime, and no three-prime reversal in the plan
TAG, LNUM, LDEN, H, HF, MAXLEN = '21500', 2150, 1000, 0.004, 0.006, 6
# dropped cells next to each other are one cell while its bound is at most DMERGE of the sum of theirs
DMERGE = (1002, 1000)


def pack(fields):
    """The fields `(value, bits)` of the hints as a number: the first field in the low bits."""
    n = 0
    for v, b in reversed(fields):
        assert 0 <= v < 1 << b
        n = n << b | v
    return n


class Planner(fl.FlipSearch):
    """The search of `flip_cert.FlipSearch` as a plan: each method returns a cost and, when the cost is below the
    limit it was given, the plan below the box: `('V',)` no term, `('E',)` evaluated, `('D',)` dropped,
    `('B', sel, cells, bits)` Buchstab's identity at the floor that `guide` gives for `sel`,
    `('F', sel, cells, bits)` the reversal through the largest prime, `('S', half, half)` cut in two. `bits`
    has, for each cut that the strategy proposes inside the range, whether the range is cut there: consecutive
    evaluated cells that one test covers are one cell. The search has no three-prime reversal."""

    merge = True
    dmerge = DMERGE

    # the proposal of the strategy that four bits name: its floor is the one that `SieveAd.cfgJP` computes
    def tryJ2(self, bl, lomin, ls, hs, c, bit):
        if not self.restOK(c):
            return None
        u, v = self.uOfF(c[0]), self.vOfF(c[1])
        f = min(lomin, tsub(v, u + 1))
        if not (0 < f and hs + tsub(u, tsub(ls, c[0])) <= self.T5):
            return None
        b = self.bestSub(v, bit, bl, 1, 0, 0, 0, tsub(ls, c[0]), (0, 0))
        sp = self.leavesOf(bl, hs, tsub(u, b[0]))
        return None if sp is None else (f, (1, b[1], bit, sp[0], sp[1]))

    def guideJ(self, bl, lomin, sel):
        ls, hs = loSum(bl), hiSum(bl)
        if self.T5 < hs:
            return None
        j = sel // 2
        if sel % 2 == 0:
            return self.tryJ2(bl, lomin, ls, hs, bl[j] if j < len(bl) else (0, 0), 2 ** j)
        f = min(lomin, self.fmax3)
        for _ in range(j):
            f = 3 * f // 4
        return self.tryJ3(bl, ls, hs, f)

    def guide(self, bl, sel):
        """The proposal that `sel` names, on the box or, inside a tree over a frozen part, on the box with the
        cofactor as one more cell, widened by the room of the tests."""
        if self.frz is None:
            return self.guideJ(bl, min([DEN] + [c[0] for c in bl]), sel)
        Kb, beta = self.frz[2], self.frz[3]
        return self.guideJ(fl.widen(Kb, vboxF(self.fctx, beta, bl)), min([DEN] + [c[0] for c in fl.widen(Kb, bl)]),
                           sel)

    def okJm(self, bl, f, cfg):
        """`τ.okJ bl f cfg` for the tests of the tree being searched."""
        if self.frz is None:
            return self.T.okJ(bl, f, cfg)
        return self.okJF3(bl, f, cfg) if cfg[0] == 2 else self.okJF2(bl, f, cfg)

    def floorOf(self, bl, lo0):
        """The first proposed floor that passes, as the bits that name it to the guide, with the floor."""
        fj = self.firstJ(bl, lo0, self.propJ(bl))
        if fj is None:
            return None
        f, cfg = fj
        if cfg[0] == 1:
            sel = 2 * (cfg[2].bit_length() - 1)
        else:
            g, sel = min(self.guideLomin(bl), self.fmax3), None
            for i in range(8):
                if g == f:
                    sel = 2 * i + 1
                    break
                g = 3 * g // 4
        if sel is None or sel > 15 or self.guide(bl, sel) != (f, cfg):
            self.stat['noguide'] = self.stat.get('noguide', 0) + 1
            return None
        return sel, f

    def guideLomin(self, bl):
        if self.frz is None:
            return min([DEN] + [c[0] for c in bl])
        return min([DEN] + [c[0] for c in fl.widen(self.frz[2], bl)])

    def pKids(self, rec, top, bl, par, cs, a, lim, drp=None):
        cells, tot, s = [], 0, a
        for c in cs:
            if s < c < top:
                c1, n1 = rec([(s, c)] + bl, par, lim - tot)
                tot += c1
                if lim <= tot:
                    return tot, None
                cells.append((s, c, n1, c1))
                s = c
        c1, n1 = rec([(s, top)] + bl, par, lim - tot)
        tot += c1
        if lim <= tot:
            return tot, None
        cells.append((s, top, n1, c1))
        # consecutive evaluated cells that one test covers are one cell; so are consecutive dropped cells whose
        # one bound is within `dmerge` of the sum of theirs
        kids, keep, i = [], set(), 0
        while i < len(cells):
            j = i
            kind = cells[i][2][0]
            if self.merge and kind == 'E':
                while (j + 1 < len(cells) and cells[j + 1][2][0] == 'E'
                       and self.anyI([(cells[i][0], cells[j + 1][1])] + bl)):
                    j += 1
            elif self.dmerge and kind == 'D' and drp is not None:
                tsum = cells[i][3]
                while j + 1 < len(cells) and cells[j + 1][2][0] == 'D':
                    u = drp([(cells[i][0], cells[j + 1][1])] + bl, par)
                    if u is None or self.dmerge[1] * u > self.dmerge[0] * (tsum + cells[j + 1][3]):
                        break
                    j += 1
                    tsum += cells[j][3]
                if j > i:
                    u = drp([(cells[i][0], cells[j][1])] + bl, par)
                    tot += u - tsum
            kids.append(cells[i][2])
            if j + 1 < len(cells):
                keep.add(cells[j][1])
            i = j + 1
        if lim <= tot:
            return tot, None
        # the bits of the cuts, as the kernel reads them
        bits, s = [], a
        for c in cs:
            if s < c < top:
                if c in keep:
                    bits.append(1)
                    s = c
                else:
                    bits.append(0)
        return tot, (kids, bits)

    def pBuch(self, O, S, n, x, bl, par, lim):
        if len(bl) < S.depth:
            fj = self.floorOf(bl, x[0])
            if fj is not None:
                sel, f = fj
                self.W['cuts'] += 1
                c, ns = self.pKids(lambda b, p, l: self.pSolve(O, S, n, b, p, l), x[1], bl, not par,
                                   S.cuts(bl, f), f, lim, O.drp)
                return c, (None if ns is None else ('B', sel) + ns)
        return lim + BIG, None

    def pSplit(self, O, S, n, x, bl, par, lim):
        mid = (x[0] + x[1]) // 2
        if S.wmin < tsub(x[1], x[0]) and x[0] < mid < x[1]:
            c1, n1 = self.pSolve(O, S, n, [(x[0], mid)] + bl[1:], par, lim)
            if lim <= c1:
                return c1, None
            c2, n2 = self.pSolve(O, S, n, [(mid, x[1])] + bl[1:], par, lim - c1)
            if lim <= c1 + c2:
                return c1 + c2, None
            return c1 + c2, ('S', n1, n2)
        return lim + BIG, None

    def pFlip(self, bl, lim):
        """`flipCost` with the plan of its tree."""
        ctx, beta = bl[-1], bl[:-1]
        self.W['flips'] += 1
        E = ((ctx[1] + 1) * dropCost(beta + [(tsub(ctx[1], 1), ctx[1] + 1)])
             + (ctx[0] + 1) * dropCost(beta + [(tsub(ctx[0], 1), ctx[0] + 1)]))
        A, B = ctx[1] * dropCost(bl) + E, bdK(ctx, flipT(ctx)) * E
        cl = min(CAPK, tsub(tsub(lim, 1) * (DEN * K), B) // A + 1)
        c, t = beta[0], flipT(ctx)
        self.frz, self.fctx = (tsub(DEN, ctx[1]), tsub(DEN, ctx[0]) + 1, 12 + DEN // c[0], beta), ctx
        w0 = (self.W['calls'], self.W['dfs'])
        try:
            S = self.stratF(ctx, beta)
            fj = self.floorOf(beta, min(c[0], t))
            if fj is None:
                self.stat['fliproot'] += 1
                return lim, None
            sel, f = fj
            O = self.opsK(ctx, len(beta))
            cc, ns = self.pKids(lambda b, p, l: self.pSolve(O, S, self.fuel, b, p, l), t, beta, True,
                                S.cuts(beta, f), f, cl, O.drp)
        finally:
            self.frz = None
            self.W['fcalls'] += self.W['calls'] - w0[0]
            self.W['fdfs'] += self.W['dfs'] - w0[1]
        if cl <= cc:
            self.stat['flipcap'] += 1
            return lim, None
        return cdiv(cc * A + B, DEN * K), ('F', sel) + ns

    def pSolve(self, O, S, n, bl, par, lim):
        self.minfuel = min(self.minfuel, n)
        if n == 0 or not bl or not O.grd(bl):
            return lim, None
        self.W['calls'] += 1
        if O.van(bl):
            return 0, ('V',)
        if self.anyI(bl):
            return 0, ('E',)
        x = bl[0]
        dc = O.drp(bl, par)
        if dc is not None:
            bc, nb = self.pBuch(O, S, n - 1, x, bl, par, dc if dc <= lim else lim)
            if dc <= bc:
                return dc, ('D',)
            return bc, nb
        bc, nb = self.pBuch(O, S, n - 1, x, bl, par, lim)
        l2 = bc if bc <= lim else lim
        if O is self.OR and not par:
            r, how = l2, None
            if self.flip and flipOK(self.maxlen, bl):
                self.stat['fliptry'] += 1
                c, nf = self.pFlip(bl, r)
                if c < r:
                    self.stat['flipwin'] += 1
                    r, how = c, nf
            if r < l2:
                return r, how
        if bc < BIG:
            return bc, nb
        return self.pSplit(O, S, n - 1, x, bl, par, lim)

    def plan(self, bl, par, lim):
        """The cost of the box and its plan (`None` if the cost is not below `lim`)."""
        return self.pSolve(self.OR, self.SG, self.fuel, bl, par, lim)

    # the kernel's search led by hints (SieveAdDirDefs.lean): what it reads from the hints
    def cfgIP(self, pw, h):
        if h & 1 == 0:
            return (1, (h >> 1) % pw, 1, 0, False), (h >> 1) // pw
        return (1, (h >> 4) % pw, 2 ** ((h >> 1) & 7), 0, False), (h >> 4) // pw

    def floorP(self, i, f):
        for _ in range(i):
            f = 3 * f // 4
        return f

    def cfgJP(self, sel, lm, lo, hi, pw, h):
        s0, h2 = h % pw, h // pw
        if h2 & 1 == 0:
            s1, e, h4 = tsub(pw // 2, 1), True, h2 // 2
        else:
            s1, e, h4 = (h2 // 2) % pw, (h2 // 2) // pw & 1 == 1, (h2 // 2) // pw // 2
        if sel & 1 == 0:
            return (min(lm, tsub(self.vOfF(hi), self.uOfF(lo) + 1)), (1, s0, 2 ** (sel // 2), s1, e)), h4
        return (self.floorP(sel // 2, min(lm, self.fmax3)), (2, s0, 0, s1, e)), h4

    def pickP(self, bl, m):
        lm, lo, hi, pw = DEN, 0, 0, 1
        for x in bl:
            lm = min(lm, x[0])
            lo += (m & 1) * x[0]
            hi += (m & 1) * x[1]
            m >>= 1
            pw *= 2
        return m, lm, lo, hi, pw

    def cfgIM(self, bl, h):
        return self.cfgIP(2 ** len(bl), h)

    def cfgJM(self, bl, h):
        sel = h & 15
        _, lm, lo, hi, pw = self.pickP(bl, 2 ** (sel // 2))
        return self.cfgJP(sel, lm, lo, hi, pw, h >> 4)

    def cfgIF(self, bl, h):
        return self.cfgIP(2 ** (len(bl) + 1), h)

    def cfgJF(self, Kb, cl, ch, bl, h):
        sel = h & 15
        m, lm, lo, hi, pw = self.pickP(bl, 2 ** (sel // 2))
        return self.cfgJP(sel, max(1, tsub(lm, Kb)), max(1, tsub(lo + (m & 1) * cl, Kb)), hi + (m & 1) * ch + Kb,
                          2 * pw, h >> 4)

    # the cells of the new prime, their cuts read from the hints (gridP, cutK, kidsC, kidsM, kidsF)
    def stpP(self, st, c):
        m = min(st, c // self.kappa)
        return m + tsub(1, m)

    def gridP(self, st, k, c):
        for _ in range(k):
            c = c + self.stpP(st, c)
        return c

    def parM(self, bl, top):
        """The grid's step and the three other cuts of the main tree: `st`, `reg`, `e`, `last`."""
        return (self.stepOf(len(bl) + 1), min(top, tsub(DEN, loSum(bl)) // 2 + 2), tsub(bl[-1][0], 1),
                tsub(tsub(DEN, 1), hiSum(bl)))

    def parF(self, ctx, lsb, hsb, nb, bl, top):
        """Those of a tree over a frozen part."""
        return (self.hF if tsub(len(bl), nb) < 2 else 2 * self.hF,
                min(top, tsub(ctx[1] + 1, tsub(loSum(bl), lsb)) // 2 + 2), 0,
                tsub(tsub(ctx[0], 1), tsub(hiSum(bl), hsb)))

    def dKidsC(self, rec, top, bl, par, prm, f, lim, h):
        st, reg, e, last = prm
        c, a, tot = f, f, 0
        for _ in range(4096):
            if h & 1 == 0:
                r = rec([(a, top)] + bl, par, lim, h >> 1)
                return tot + r[0], r[1]
            j, h1 = (h >> 1) & 3, h >> 3
            if j != 3:
                p, hh = self.gridP(st, j + 1, c), h1
                nc = p
            else:
                t, h2 = h1 & 7, h1 >> 3
                if t <= 3:
                    p, hh = self.gridP(st, t + 4, c), h2
                    nc = p
                elif t == 4:
                    c, h = self.gridP(st, 7, c), h2
                    continue
                else:
                    p, hh, nc = (reg if t == 5 else e if t == 6 else last), h2, c
            if not a < p < top:
                return tot + lim, hh
            r = rec([(a, p)] + bl, par, lim, hh)
            if lim <= r[0]:
                return tot + r[0], r[1]
            tot, lim, h, a, c = tot + r[0], lim - r[0], r[1], p, nc
        return tot + lim, h

    def kdM(self, rec, top, bl, par, f, lim, h):
        return self.dKidsC(rec, top, bl, par, self.parM(bl, top), f, lim, h)

    def dPart(self, rec, top, bl, par, cs, a, lim, h):
        tot = 0
        for c in cs:
            if not a < c < top:
                return tot + lim, h
            r = rec([(a, c)] + bl, par, lim, h)
            if lim <= r[0]:
                return tot + r[0], r[1]
            tot, lim, h, a = tot + r[0], lim - r[0], r[1], c
        r = rec([(a, top)] + bl, par, lim, h)
        return tot + r[0], r[1]

    # the search (stepD, solveD)
    def okIm(self, bl, cfg):
        return self.T.okI(bl, cfg) if self.frz is None else self.okIF(bl, cfg)

    def dStep(self, O, dI, dJ, kd, altH, rec, bl, par, lim, h):
        if not bl or not O.grd(bl):
            return lim, h
        x = bl[0]
        if h & 1 == 0:
            cfg, h2 = dI(bl, h >> 1)
            return (0 if self.okIm(bl, cfg) else lim), h2
        if h & 3 == 1:
            (f, cfg), h2 = dJ(bl, h >> 2)
            if not (1 <= f <= x[0] and self.okJm(bl, f, cfg)):
                return lim, h2
            return kd(rec, x[1], bl, not par, f, lim, h2)
        if h & 7 == 3:
            dc = O.drp(bl, par)
            return (lim if dc is None else dc), h >> 3
        if h & 15 == 7:
            return altH(bl, par, lim, h >> 4)
        if h & 31 == 15:
            mid, h2 = (x[0] + x[1]) // 2, h >> 5
            if x[0] < mid < x[1]:
                r = rec([(x[0], mid)] + bl[1:], par, lim, h2)
                if lim <= r[0]:
                    return r
                r2 = rec([(mid, x[1])] + bl[1:], par, tsub(lim, r[0]), r[1])
                return r[0] + r2[0], r2[1]
            return lim, h2
        if h & 63 == 31:
            return (0 if O.van(bl) else lim), h >> 6
        return O.alt(bl, par, lim), h >> 6

    def dSolve(self, O, dI, dJ, kd, altH, n, bl, par, lim, h):
        if n == 0:
            return lim, h
        return self.dStep(O, dI, dJ, kd, altH,
                          lambda b, p, l, hh: self.dSolve(O, dI, dJ, kd, altH, n - 1, b, p, l, hh), bl, par, lim, h)

    # the reversal through the largest prime (flipTreeD, flipCostD, altFD)
    def frozen(self, ctx, beta):
        """The tree over the frozen part of `β` and the slab of `ctx`: its decoders, its cells and its search."""
        lsb, hsb, nb = loSum(beta), hiSum(beta), len(beta)
        Kb = 12 + DEN // beta[0][0]
        cl, ch = max(1, tsub(tsub(DEN, ctx[1]), hsb)), tsub(tsub(DEN, ctx[0]) + 1, lsb)
        O = self.opsK(ctx, nb)

        def dJ(b, hh):
            return self.cfgJF(Kb, cl, ch, b, hh)

        def kd(rec, top, b, p, ff, l, hh):
            return self.dKidsC(rec, top, b, p, self.parF(ctx, lsb, hsb, nb, b, top), ff, l, hh)

        def rec(b, p, l, hh):
            return self.dSolve(O, self.cfgIF, dJ, kd, lambda b2, p2, l2, h2: (l2, h2), self.fuel, b, p, l, hh)
        return Kb, O, dJ, kd, rec

    def dFlipTree(self, ctx, beta, lim, h):
        c, t = beta[0], flipT(ctx)
        Kb, O, dJ, kd, rec = self.frozen(ctx, beta)
        self.frz, self.fctx = (tsub(DEN, ctx[1]), tsub(DEN, ctx[0]) + 1, Kb, beta), ctx
        try:
            (f, cfg), h2 = dJ(beta, h)
            if not (1 <= f <= min(c[0], t) and self.okJm(beta, f, cfg)):
                return lim, h2
            return kd(rec, t, beta, True, f, lim, h2)
        finally:
            self.frz = None

    def dFlipCost(self, bl, lim, h):
        if not flipOK(self.maxlen, bl):
            return lim, h
        ctx, beta = bl[-1], bl[:-1]
        E = ((ctx[1] + 1) * dropCost(beta + [(tsub(ctx[1], 1), ctx[1] + 1)])
             + (ctx[0] + 1) * dropCost(beta + [(tsub(ctx[0], 1), ctx[0] + 1)]))
        r = self.dFlipTree(ctx, beta, CAPK, h)
        if CAPK <= r[0]:
            return lim, r[1]
        return cdiv(r[0] * (ctx[1] * dropCost(bl) + E) + bdK(ctx, flipT(ctx)) * E, DEN * K), r[1]

    def dAltF(self, bl, par, l, h):
        return (l, h) if par else self.dFlipCost(bl, l, h)

    def dCheck(self, bl, par, lim, h):
        """`solveD opsMP fillTestsF cfgIM cfgJM (kidsM κ hI) (altFD κ hF fuel maxlen) fuel bl par lim h`."""
        O = rc.Ops(lambda b: True, tc.vanishOK, tc.dropC, lambda b, p, l: l)
        return self.dSolve(O, self.cfgIM, self.cfgJM, self.kdM, self.dAltF, self.fuel, bl, par, lim, h)

    # the hints of a plan
    def kidCells(self, cuts, f, top, bits):
        """The cells of the new prime that the plan's bits cut out of the proposed cuts `cuts`."""
        ends, it = [f], iter(bits)
        for c in cuts:
            if ends[-1] < c < top and next(it):
                ends.append(c)
        ends.append(top)
        return list(zip(ends, ends[1:]))

    def dserKids(self, prm, f, cells, kids, bl, par, top, out, sub):
        """The fields of the cells `cells` of the new prime with the plans `kids`: a code for each cut."""
        st, reg, e, last = prm
        c, a = f, f
        for i, cell in enumerate(cells[:-1]):
            p = cell[1]
            k, g = 0, c
            while g < p:
                g, k = g + self.stpP(st, g), k + 1
            if g == p and k >= 1:
                while k > 7:
                    out.extend(((1, 1), (3, 2), (4, 3)))
                    k -= 7
                if k <= 3:
                    out.extend(((1, 1), (k - 1, 2)))
                else:
                    out.extend(((1, 1), (3, 2), (k - 4, 3)))
                c = p
            else:
                assert p in (reg, e, last), ('a cut off the grid', p, prm, f)
                out.extend(((1, 1), (3, 2), (5 if p == reg else 6 if p == e else 7, 3)))
            sub(kids[i], [(a, p)] + bl, par, out)
            a = p
        out.append((0, 1))
        sub(kids[-1], [(a, top)] + bl, par, out)

    def cfgFields(self, bl, sel, cfg, w):
        if cfg[3] == 2 ** (w - 1) - 1 and cfg[4]:
            return [(sel, 4), (cfg[1], w), (0, 1)]
        return [(sel, 4), (cfg[1], w), (1, 1), (cfg[3], w), (int(cfg[4]), 1)]

    def evalFields(self, cfg, w):
        j = cfg[2].bit_length() - 1
        return [(0, 1)] + ([(0, 1)] if j == 0 else [(1, 1), (j, 3)]) + [(cfg[1], w)]

    def dserF(self, ctx, beta, node, bl, par, out):
        """A node of a tree over a frozen part."""
        kind = node[0]
        w = len(bl) + 1
        if kind == 'V':
            out.append((31, 6))
        elif kind == 'E':
            blv = fl.vboxF(ctx, beta, bl)
            cf = self.propI2(blv, loSum(blv))
            assert cf and self.okIF(bl, cf[0])
            out.extend(self.evalFields(cf[0], w))
        elif kind == 'D':
            out.append((3, 3))
        elif kind == 'S':
            x = bl[0]
            mid = (x[0] + x[1]) // 2
            out.append((15, 5))
            self.dserF(ctx, beta, node[1], [(x[0], mid)] + bl[1:], par, out)
            self.dserF(ctx, beta, node[2], [(mid, x[1])] + bl[1:], par, out)
        elif kind == 'B':
            f, cfg = self.guide(bl, node[1])
            out.append((1, 2))
            out.extend(self.cfgFields(bl, node[1], cfg, w))
            top = bl[0][1]
            cells = self.kidCells(self.stratF(ctx, beta).cuts(bl, f), f, top, node[3])
            self.dserKids(self.parF(ctx, loSum(beta), hiSum(beta), len(beta), bl, top), f, cells, node[2], bl,
                          not par, top, out, lambda k, b, p, o: self.dserF(ctx, beta, k, b, p, o))
        else:
            raise ValueError(kind)

    def dser(self, node, bl, par, out):
        """A node of the main tree."""
        kind = node[0]
        w = len(bl)
        if kind == 'V':
            out.append((31, 6))
        elif kind == 'E':
            cf = self.propI2(bl, loSum(bl))
            assert cf and self.T.okI(bl, cf[0])
            out.extend(self.evalFields(cf[0], w))
        elif kind == 'D':
            out.append((3, 3))
        elif kind == 'S':
            x = bl[0]
            mid = (x[0] + x[1]) // 2
            out.append((15, 5))
            self.dser(node[1], [(x[0], mid)] + bl[1:], par, out)
            self.dser(node[2], [(mid, x[1])] + bl[1:], par, out)
        elif kind == 'B':
            f, cfg = self.guide(bl, node[1])
            out.append((1, 2))
            out.extend(self.cfgFields(bl, node[1], cfg, w))
            top = bl[0][1]
            cells = self.kidCells(self.SG.cuts(bl, f), f, top, node[3])
            self.dserKids(self.parM(bl, top), f, cells, node[2], bl, not par, top, out, self.dser)
        elif kind == 'F':
            ctx, beta = bl[-1], bl[:-1]
            c, t = beta[0], flipT(ctx)
            self.frz, self.fctx = (tsub(DEN, ctx[1]), tsub(DEN, ctx[0]) + 1, 12 + DEN // c[0], beta), ctx
            try:
                f, cfg = self.guide(beta, node[1])
                out.append((7, 4))
                out.extend(self.cfgFields(beta, node[1], cfg, len(beta) + 1))
                cells = self.kidCells(self.stratF(ctx, beta).cuts(beta, f), f, t, node[3])
                self.dserKids(self.parF(ctx, loSum(beta), hiSum(beta), len(beta), beta, t), f, cells, node[2],
                              beta, True, t, out, lambda k, b, p, o: self.dserF(ctx, beta, k, b, p, o))
            finally:
                self.frz = None
        else:
            raise ValueError(kind)

    def dHints(self, group, bl, par):
        """The hints of the consecutive cells `group` = [(lo, hi, plan)] of the new prime under the box `bl`."""
        out = []
        for lo, hi, k in group:
            self.dser(k, [(lo, hi)] + bl, par, out)
        return pack(out)


def count(node, cnt, frozen=False):
    cnt[(node[0], frozen)] += 1
    if node[0] in ('B', 'F'):
        for k in node[2]:
            count(k, cnt, frozen or node[0] == 'F')
    elif node[0] == 'S':
        count(node[1], cnt, frozen)
        count(node[2], cnt, frozen)


# the certificate

class Par:
    """The exponent and the parameters of a certificate."""

    def __init__(self, tag, lnum, lden, h=0.005, depth=6, kappa=10, depthR=3, hR=0.012, hQ=0.02, hF=0.006,
                 depthF=3, maxlen=6, cap=3.5, pmax=100, fcap=240.0, levels=5, rev=False):
        assert not rev, 'the search led by hints has no three-prime reversal'
        self.tag, self.lnum, self.lden, self.rev = tag, lnum, lden, rev
        self.h, self.hI, self.depth, self.kappa = h, round(h * DEN), depth, kappa
        self.depthR, self.hR, self.hQ = depthR, round(hR * DEN), round(hQ * DEN)
        self.hF, self.depthF, self.maxlen = round(hF * DEN), depthF, maxlen
        self.hRf, self.hQf, self.hFf = hR, hQ, hF
        self.cap, self.pmax, self.fcap, self.levels = cap, pmax, fcap, levels

    def planner(self):
        return Planner(fc.TestsF(self.lnum, self.lden), self.hI, self.depth, fc.WMIN, self.kappa, self.hR,
                       self.depthR, self.hQ, fc.FUEL, self.hF, self.depthF, self.maxlen, rev=self.rev)


# the kernel's seconds a step, by kind and whether over a frozen part (12 November 2026: timed in the kernel on
# 300 boxes of each kind of the plan at 2150/1000, least of three runs, times 1.3, which is what twenty-four whole
# parts take over the sum of their steps)
SEC = {('E', False): 4.0e-4, ('E', True): 1.05e-3, ('V', False): 1.3e-4, ('V', True): 1.3e-4, ('B', False): 1.6e-3,
       ('B', True): 2.7e-3, ('D', False): 3.0e-4, ('D', True): 4.7e-4, ('F', False): 3.9e-3, ('S', False): 2.6e-4,
       ('S', True): 2.6e-4}


def secs(node, frozen=False):
    """The kernel's predicted seconds on the plan `node`."""
    k = node[0]
    t = SEC[(k, frozen)]
    if k in ('B', 'F'):
        fz = frozen or k == 'F'
        for x in node[2]:
            t += secs(x, fz)
    elif k == 'S':
        t += secs(node[1], frozen) + secs(node[2], frozen)
    return t


def kid_cells(P, bl, sel, bits):
    """The floor and the configuration of a Buchstab step at the box `bl`, and the cells of the new prime as the
    kernel cuts them with the bits `bits`."""
    f, cfg = P.guide(bl, sel)
    x, ends, it = bl[0], [f], iter(bits)
    for c in P.SG.cuts(bl, f):
        if ends[-1] < c < x[1] and next(it):
            ends.append(c)
    ends.append(x[1])
    return f, cfg, list(zip(ends, ends[1:]))


def add_part(P, bl, par, group, parts):
    """A part: the consecutive cells `group` = [(lo, hi, plan)] of the new prime under the box `bl`."""
    cnt = Counter()
    for _, _, k in group:
        count(k, cnt)
    h = P.dHints(group, bl, par)
    a, top, cs = group[0][0], group[-1][1], [g[0] for g in group[1:]]
    c, rest = P.dPart(P.dCheck, top, bl, par, cs, a, K, h)
    assert rest == 0 and c < K, (c, rest)
    parts.append((top, bl, par, cs, a, c, h, sum(secs(g[2]) for g in group), sum(cnt.values()), dict(cnt)))
    return len(parts) - 1


def piece_cost(p, parts):
    return parts[p[1]][5] if p[0] == 'part' else p[6]


def cut(P, par_, node, bl, par, parts):
    """The pieces of the Buchstab step `node` at the box `bl`: parts of consecutive cells of the new prime of at
    most `cap` predicted seconds, and cells with their own step."""
    _, sel, kids, bits = node
    f, cfg, cells = kid_cells(P, bl, sel, bits)
    assert len(cells) == len(kids), (len(cells), len(kids))
    out, group, gs = [], [], 0.0
    for (s, e), k in zip(cells, kids):
        t = secs(k)
        if t > par_.cap and k[0] == 'B' and len(bl) + 1 < par_.levels:
            if group:
                out.append(('part', add_part(P, bl, not par, group, parts)))
                group, gs = [], 0.0
            out.append(cut(P, par_, k, [(s, e)] + bl, not par, parts))
            continue
        if group and gs + t > par_.cap:
            out.append(('part', add_part(P, bl, not par, group, parts)))
            group, gs = [], 0.0
        group.append((s, e, k))
        gs += t
    if group:
        out.append(('part', add_part(P, bl, not par, group, parts)))
    return ('buch', bl, par, f, cfg, out, sum(piece_cost(p, parts) for p in out))


def row_job(args):
    """The plan of one cell of the first prime: light, to be put in a part with its neighbours, or cut."""
    par_, a, b = args
    P = par_.planner()
    sys.setrecursionlimit(100000)
    c, node = P.plan([(a, b)], False, K)
    assert node is not None and c < K, (a, b, c)
    cnt = Counter()
    count(node, cnt)
    info = (c, dict(cnt), P.W['calls'], P.W['fcalls'], dict(P.stat))
    if secs(node) <= par_.cap or node[0] != 'B':
        return ('light', a, b, node, info)
    parts = []
    piece = cut(P, par_, node, [(a, b)], False, parts)
    assert piece[6] == c, (piece[6], c)
    return ('heavy', a, b, piece, parts, info)


def shift(piece, off):
    if piece[0] == 'part':
        return ('part', piece[1] + off)
    return piece[:5] + ([shift(x, off) for x in piece[5]], piece[6])


def plan_all(par_, procs=4, rows=None):
    """The parts and the assembly of the bound of the first term: (f0, cfg0, parts, root, total, stats)."""
    import multiprocessing
    P = par_.planner()
    sys.setrecursionlimit(100000)
    f0, cfg0 = fc.root_of(P)
    cuts = fc.rowCuts(P, f0)
    assert cuts[0] == f0 and cuts[-1] == DEN // 2 + 1 and P.T.okJ([], f0, cfg0)
    jobs = [(par_, a, b) for a, b in zip(cuts, cuts[1:])]
    if rows is not None:
        jobs = jobs[rows[0]:rows[1]]
    if procs > 1:
        with multiprocessing.Pool(procs) as pool:
            res = pool.map(row_job, jobs, chunksize=1)
    else:
        res = [row_job(j) for j in jobs]
    parts, root, group, gs = [], [], [], 0.0
    tot, st = Counter(), Counter()
    stats = dict(boxes=0, fboxes=0, cost=0)

    def flush():
        nonlocal group, gs
        if group:
            root.append(('part', add_part(P, [], False, group, parts)))
            group, gs = [], 0.0

    for r in res:
        info = r[-1]
        stats['cost'] += info[0]
        stats['boxes'] += info[2]
        stats['fboxes'] += info[3]
        tot.update(info[1])
        st.update(info[4])
        if r[0] == 'light':
            t = secs(r[3])
            if group and gs + t > par_.cap:
                flush()
            group.append((r[1], r[2], r[3]))
            gs += t
        else:
            flush()
            off = len(parts)
            parts.extend(r[4])
            root.append(shift(r[3], off))
    flush()
    total = sum(piece_cost(p, parts) for p in root)
    assert total == stats['cost'], (total, stats['cost'])
    stats['steps'] = dict(tot)
    stats['search'] = dict(st)
    return f0, cfg0, parts, root, total, stats


# the Lean files

def part_stmt(par_, k, p):
    top, bl, par, cs, a, c, h = p[:7]
    T = par_.tag
    return rc.wrap(f'theorem tree{T}_{k} : (partD solve{T} {tc.nat(top)} {rc.box(bl)} {rc.bool_(par)} '
                   f'[{", ".join(map(str, cs))}] {a} K\xa00x{h:x}).1 ≤ {c} :=\xa0by\xa0decide\xa0+kernel').replace(
                       '\xa0', ' ')


def defs_file(par_):
    T, LN = par_.tag, f'{par_.lnum}/{par_.lden}'
    return f"""/-
# The exponent and the search led by hints at `L = {LN}`

Generated by `tools/linnik/hint_cert.py`; do not edit by hand.

The bilinear Type I rule's exponent `{LN}` (`ibPar{T}`), and `solve{T}`, the search led by hints
(`SieveAd.solveD`):

* the nodes of the main tree with a dropped box's cost in one pass (`SieveAd.opsMP`), and the tests in one pass
  (`SieveAd.fillTestsF`);
* the configurations read from the hints (`SieveAd.cfgIM`, `SieveAd.cfgJM`), and the cells of a new prime
  (`SieveAd.kidsM`) on the grid of side at most `{par_.hI}/DEN` (`{par_.h}`) and at most the exponent over
  `{par_.kappa}`;
* as its hinted bound, the reversal through the largest prime of boxes of at most `{par_.maxlen}` primes
  (`SieveAd.altFD`), with the tests `SieveAd.frozTestsF` and the chains over the frozen parts on the grid of side
  at most `{par_.hF}/DEN` (`{par_.hFf}`);
* the depth of recursion `{fc.FUEL}`.

The file imports `SieveAdDirDefs.lean`; so neither it nor the part files (`SieveHint{T}P1.lean` …) load more of
`Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveAdDirDefs

namespace SieveCert

/-- **The bilinear Type I rule's exponent** at `L = {LN}`. -/
@[instance_reducible] def ibPar{T} : IBPar := ⟨{par_.lnum}, {par_.lden}⟩

end SieveCert

namespace SieveAd

open SieveCert

/-- **The search led by hints at `{LN}`**, with the reversal through the largest prime as its hinted bound. -/
noncomputable def solve{T} : List Cell → Bool → ℕ → ℕ → ℕ × ℕ :=
  solveD opsMP (@fillTestsF ibPar{T}) cfgIM (@cfgJM ibPar{T}) (kidsM {par_.kappa} {par_.hI})
    (@altFD ibPar{T} {par_.kappa} {par_.hF} {fc.FUEL} {par_.maxlen}) {fc.FUEL}

end SieveAd
"""


def part_files(par_, parts):
    """The parts in files: consecutive parts, at most `pmax` of them and `fcap` predicted seconds a file."""
    T, LN = par_.tag, f'{par_.lnum}/{par_.lden}'
    files, cur, t = [], [], 0.0
    for k, p in enumerate(parts):
        if cur and (len(cur) >= par_.pmax or t + p[7] > par_.fcap):
            files.append(cur)
            cur, t = [], 0.0
        cur.append(k)
        t += p[7]
    if cur:
        files.append(cur)
    out = {}
    for i, g in enumerate(files, 1):
        secs_, steps = sum(parts[k][7] for k in g), sum(parts[k][8] for k in g)
        desc = textwrap.fill(
            f'File {i} of {len(files)}: the parts `tree{T}_{g[0]}` … `tree{T}_{g[-1]}` of the search led by hints '
            f'at `L = {LN}` ({len(g)} parts, {steps} steps, predicted {secs_:.0f} s of the kernel). A part is a '
            f'range of consecutive cells of one prime: the sum of the costs that the search `SieveAd.solve{T}` '
            f'returns on them, led by the hints written after `K`, is at most the part\'s bound, by `decide '
            f'+kernel`, one at a time (`Elab.async false`). The hints are the plan of the search that '
            f'`tools/linnik/hint_cert.py` ran; the bound holds whatever they are. `Linnik{T}.lean` makes the bound '
            f'of the first term from the parts.', width=116)
        body = '\n\n'.join(part_stmt(par_, k, parts[k]) for k in g)
        out[f'SieveHint{T}P{i}.lean'] = f"""/-
# The search led by hints at `L = {LN}`, parts {g[0]}–{g[-1]} of {len(parts)}

Generated by `tools/linnik/hint_cert.py`; do not edit by hand.

{desc}

The file imports `SieveHint{T}.lean`.
-/
import SieveHint{T}

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveAd

open SieveCert

section

attribute [local instance] ibPar{T}

{body}

end

end SieveAd

#print axioms SieveAd.tree{T}_{g[0]}
#print axioms SieveAd.tree{T}_{g[-1]}
"""
    return out


def final_file(par_, f0, cfg0, parts, root, total, nfiles, stats):
    T, LN = par_.tag, f'{par_.lnum} / {par_.lden}'
    nodes = []

    def term(p):
        if p[0] == 'part':
            return f'part{T} tree{T}_{p[1]} (by decide)'
        _, bl, par, f, cfg, ps, c = p
        items = [term(x) for x in ps]
        i = len(nodes)
        what = ('first', 'second', 'third', 'fourth', 'fifth')[len(bl) - 1]
        doc = rc.wrap(f"/-- The cell `{rc.cell(bl[0])}` of the {what} prime: Buchstab's identity at the floor `{f}`, "
                      f"and the pieces of the next prime's range. -/", '')
        nodes.append(f"""{doc}
theorem node{T}_{i} : PR {rc.box(bl)} {rc.bool_(par)} {c} :=
  pr_mono (pr_buch sound{T} (x := {rc.cell(bl[0])}) (b := {rc.box(bl[1:])}) (par := {rc.bool_(par)}) (f := {f})
    (cfg := {fc.cfg_(cfg)}) (by decide) (by decide +kernel) (
{rc.chain(items)})) (by decide)""")
        return f'node{T}_{i}'

    items = [term(p) for p in root]
    st = stats['steps']
    nsteps = sum(st.values())
    nflip = st.get(('F', False), 0)
    imports = '\n'.join(f'import SieveHint{T}P{i}' for i in range(1, nfiles + 1))
    plain = textwrap.fill(
        f'Plain statement (`linnik_{T}`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there '
        f'is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`, with no hypothesis. The route is at `L = {LN}` '
        f'(`route{T}`), with the estimate in two variables alone, and the tests are `SieveAd.fillTests`, as for the '
        f'theorem at `2165/1000`. The sieve\'s decomposition is a tree of Buchstab steps with the reversal of a '
        f'term of the sign `−` of three or five primes through its largest prime, the cofactor kept as one number '
        f'(`SieveAdFlipDefs.lean`): its tree runs over the frozen numbers, with the tests `SieveAd.frozTests`. The '
        f'kernel does not search for the tree: it follows hints (`SieveAd.solveD`, `SieveAdDirDefs.lean`), the '
        f'plan of the search that `tools/linnik/hint_cert.py` ran ({stats["boxes"]} boxes, {stats["fboxes"]} of '
        f'them over frozen parts), in {nsteps} steps, {nflip} of them reversals through the largest prime: what is '
        f'done at each box, with which configuration, and where the range of each new prime is cut. Each step is '
        f'checked, and a cost that the search returns below its limit bounds the term whatever the hints are '
        f'(`SieveAd.pr_of_partD`). The search is in {len(parts)} parts, {nfiles} files (`SieveHint{T}P1.lean` … '
        f'`SieveHint{T}P{nfiles}.lean`). The kernel evaluates the tests in one pass over a box '
        f'(`SieveAd.fillTestsF`, `SieveAd.frozTestsF`), and they are equal to the tests that are proved sound '
        f'(`SieveAdFast.lean`).', width=116)
    return f"""/-
# Linnik's theorem with exponent `{LN}`, by a search led by hints

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/hint_cert.py`; do not edit by hand.

{plain}

* `route{T}`, `routeOK{T}`, `ibFits{T}`: the route and its exponent.
* `sound{T}`, `soundF{T}`: the tests are sound, and so are the tests in one pass.
* `part{T}`: a part of the search bounds its term.
* `node{T}_0` … `node{T}_{len(nodes) - 1}`: the {len(nodes)} cells whose search is cut into parts by the cells of the next prime:
  the cell's own Buchstab step (`SieveAd.pr_buch`), and the pieces below it.
* `tree{T}`: the term of the box of the first prime, of the sign `−`, is at most `(c/K + o(1))x/(φ(q) log x)` in
  `𝒜` minus the comparison set, with `c = {total}`, which is `{total / K:.5f}·K`.
* `linnik_{T}`: `SieveAd.linnik_pr` at them, with the root at the floor `{f0}/DEN`, by the comparison with the rest
  among the tree's primes.

The file imports `SieveAdDir.lean`, `SieveAdFill.lean` and the part files.
-/
import SieveAdDir
import SieveAdFill
{imports}

namespace Linnik{T}

open SieveCert SieveRoute SieveQ SieveAd

/-- **The route's parameters at `{LN}`**: `L = {LN}`; the window's ends, `1/3` and `1/2`, are not used. -/
@[instance_reducible] noncomputable def route{T} : Route := ⟨{LN}, 1 / 3, 1 / 2⟩

/-- `route{T}` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK{T} : @RouteOK route{T} :=
  @RouteOK.mk route{T} (show (2 : ℝ) < {LN} by norm_num) (show (0 : ℝ) < 1 / 3 by norm_num)
    (show (1 / 3 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    (show ({LN} : ℝ) ≤ 5 / 2 by norm_num)

/-- `ibPar{T}`'s exponent `Lnum/Lden` is the route's `L = {LN}`. -/
theorem ibFits{T} : @IBFits route{T} ibPar{T} :=
  @IBFits.mk route{T} ibPar{T} (show (({par_.lnum} : ℕ) : ℝ) / (({par_.lden} : ℕ) : ℝ) = {LN} by norm_num)

section

attribute [local instance] route{T} routeOK{T} ibPar{T} ibFits{T}

/-- The tests at `{LN}` are sound. -/
theorem sound{T} : (fillTests).Sound := fillTests_sound

/-- The tests in one pass at `{LN}` are sound: they are the tests. -/
theorem soundF{T} : (fillTestsF).Sound := by
  rw [fillTestsF_eq]
  exact fillTests_sound

/-- **A part of the search bounds its term**: `SieveAd.pr_of_partD` at the route. -/
theorem part{T} {{top : ℕ}} {{bl : List Cell}} {{par : Bool}} {{cs : List ℕ}} {{a c h : ℕ}}
    (hk : (partD solve{T} top bl par cs a K h).1 ≤ c) (hc : c < K) : PR ((a, top) :: bl) par c :=
  pr_of_partD soundF{T} cfgIM cfgJM {par_.kappa} {par_.hI} {par_.hF} {fc.FUEL} {par_.maxlen} {fc.FUEL} hk hc

{chr(10).join(n + chr(10) for n in nodes)}
/-- **The first term at `{LN}`**: the term of the box of the first prime, with the cell `({f0}, DEN/2 + 1)`, of the
sign `−`, is at most `(c/K + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set, with `c = {total}`, below `K`. -/
theorem tree{T} : PR [({f0}, DEN / 2 + 1)] false {total} :=
  pr_mono (
{rc.chain(items)}) (by decide)

/-- **Linnik's theorem with exponent `{LN}`, by a search led by hints**: there is `K` such that for every `q ≥ 1`
and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`. -/
theorem linnik_{T} : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ ({LN} : ℝ) :=
  linnik_pr sound{T} {f0} {fc.cfg_(cfg0)} (by decide) (by decide +kernel) tree{T} (by decide)

end

end Linnik{T}

#print axioms Linnik{T}.tree{T}
#print axioms Linnik{T}.linnik_{T}
"""


def generate(par_, procs=4, rows=None):
    f0, cfg0, parts, root, total, stats = plan_all(par_, procs, rows)
    files = {f'SieveHint{par_.tag}.lean': defs_file(par_)}
    pf = part_files(par_, parts)
    files.update(pf)
    files[f'Linnik{par_.tag}.lean'] = final_file(par_, f0, cfg0, parts, root, total, len(pf), stats)
    return files, (parts, root, total, stats)


def main():
    a = sys.argv[1:]
    sys.setrecursionlimit(100000)
    import time
    procs = int(a[a.index('--procs') + 1]) if '--procs' in a else 4
    out = a[a.index('--out') + 1] if '--out' in a else None
    if a and a[0] == '--try':
        ln, ld = map(int, a[2].split('/'))
        par_ = Par(a[1], ln, ld, h=float(a[3]), hF=float(a[4]), maxlen=int(a[5]))
        rows = tuple(int(x) for x in a[a.index('--rows') + 1:][:2]) if '--rows' in a else None
    elif not a or a[0] in ('--check', '--out', '--procs'):
        par_, rows = Par(TAG, LNUM, LDEN, h=H, hF=HF, maxlen=MAXLEN), None
        if out is None and '--check' not in a:
            out = tc.PNT
    else:
        print(__doc__)
        return 2
    t0 = time.time()
    files, (parts, root, total, stats) = generate(par_, procs, rows)
    times = [p[7] for p in parts]
    bits = sum(p[6].bit_length() for p in parts)
    print(f'L = {par_.lnum}/{par_.lden}: cost/K = {total / K:.5f}; {stats["boxes"]} boxes searched '
          f'({stats["fboxes"]} over frozen parts); {sum(stats["steps"].values())} steps {stats["steps"]}; '
          f'{len(parts)} parts in {len(files) - 2} files; {bits} bits of hints; predicted seconds of the kernel '
          f'{sum(times):.0f}, a part at most {max(times):.0f}; the search: {stats["search"]}; '
          f'{time.time() - t0:.0f} s', flush=True)
    if '--check' in a:
        T = par_.tag
        there = sorted(f for f in os.listdir(tc.PNT)
                       if f.startswith(f'SieveHint{T}') or f == f'Linnik{T}.lean')
        bad = [n for n, t in files.items() if not os.path.exists(os.path.join(tc.PNT, n))
               or open(os.path.join(tc.PNT, n), encoding='utf-8').read() != t]
        bad += [n for n in there if n not in files]
        print('SEARCH', T, 'FAIL: ' + ', '.join(bad) if bad else 'PASS')
        return 1 if bad else 0
    if out is not None:
        os.makedirs(out, exist_ok=True)
        for n in os.listdir(out):
            if n.startswith(f'SieveHint{par_.tag}P') and n not in files:
                os.remove(os.path.join(out, n))
        for n, t in files.items():
            with open(os.path.join(out, n), 'w', encoding='utf-8') as fh:
                fh.write(t)
        print(f'wrote {len(files)} files to {out}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
