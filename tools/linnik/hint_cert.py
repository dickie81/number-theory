#!/usr/bin/env python3
"""hint_cert.py [--check] [--out DIR] [--procs N] | --try TAG a/b H HF MAXLEN [--norev] [--rows I J] [--out DIR] |
--box L1 H1 L2 H2 [MAXLEN] [--norev]: the search with the reversal through the largest prime as a plan, the hints
that lead the kernel through the plan, and the Lean files of the theorem at L = 2150/1000.

`flip_cert.py`'s search tries, at each box, what its strategy proposes, and keeps the cheapest; the kernel, running
it, spends most of its time on what is not kept, and on searching every proposal of a floor where one is used.
Here the search is run once, in Python, and the plan it keeps is written as hints: a number read from its low end
in the order of the search (`lib/pnt/SieveAdHintDefs.lean`). An action is a run of ones closed by a zero:

    0        no term, or a proposed configuration evaluates the box
    10       Buchstab's identity at the floor that the guide gives for the four bits that follow, then the cells
    110      dropped
    1110     the three-prime reversal of rev_cert.py (searched by the kernel without hints; not used in a plan
             made with --norev)
    11110    the reversal through the largest prime: four bits for the floor of the frozen part's terms, then
             the cells of the chain's first prime
    111110   the last cell cut in two

and among the cells of a new prime, at each proposed cut that lies inside the range, one bit says whether the
range is cut there: consecutive evaluated cells that one test covers are one cell. The guide
(`lib/pnt/SieveAdHintStratDefs.lean`) computes the one proposal of the strategy that the four bits name. The
kernel follows the hints (`SieveAd.solveH`) and checks each step; the cost it returns is a bound whatever the
hints are (`lib/pnt/SieveAdHint.lean`).

  * `Planner`: `flip_cert.FlipSearch`'s search, returning with each cost the plan kept, as a tree
    (`pSolve`, `pBuch`, `pKids`, `pSplit`, `pFlip`); `tryJ2`, `guideJ`, `guide`: the guides; `ser` writes a plan
    as fields and `pack` as a number;
  * `cSolve`, `cStep`, `cKids`, `cFlipTree`, `cFlipCost`, `cAltF`: `solveH`, `stepH`, `kidsH`, `flipTreeH`,
    `flipCostH`, `altFH`, definition by definition; every part is run through them before it is written;
  * `plan_all`, `cut`, `add_part`: the cells of the first prime planned one by one (in `--procs` processes), and
    the plan cut into parts of at most `cap` predicted seconds of the kernel: consecutive cells of one prime, a
    heavy cell cut by its own Buchstab step.

It writes `lib/pnt/SieveHint21500.lean` (the exponent, the strategies and the search), `SieveHint21500P<k>.lean`
(the parts, each by `decide +kernel`) and `Linnik21500.lean` (the route, the bound from the parts, and the
theorem). With `--check`, nothing is written: the files are regenerated in memory and compared with `lib/pnt`
(exit 1 on a difference); it is not part of `check_certificate.py`, for it searches for ten minutes on four
cores. With `--try`, the search is planned with other parameters (cells of side H, chains' cells of side HF over
the frozen parts, boxes of at most MAXLEN primes reversed) and its cost and the plan's size are printed; with
`--out`, its files are written to DIR. `--box` plans one box of two primes at 2165/1000 with the parameters of
the theorem there and prints its statement.

Values (12 November 2026), all without the three-prime reversal: at 2150/1000 with cells of side 0.004 and
chains' cells 0.006, boxes of three and five primes reversed, the search costs 0.94835 K on 3.4·10^7 boxes
(2.8·10^7 over frozen parts; nine minutes on four cores), and its plan has 3.7·10^6 steps and 2.6 MB of hints.
At 2155/1000 with cells of side 0.005: 0.96558 K on 1.6·10^7 boxes. The kernel takes 3.6 ms on an evaluated
box, 8.4 ms on a Buchstab step (11.5 ms over a frozen part), 1.7 ms on a dropped box and 42 ms on a reversal's
root, where it takes 4 ms and 13 ms on every box of the search that tries.

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
from rev_cert import bdK, revOK, CAPK  # noqa: E402
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


def ser_kids(kids, flags, out):
    """The fields of the cells of a new prime: at each proposed cut that lies inside, a bit (the range is cut
    there or not), and after a cut the cell before it; last, the cell up to the top."""
    it = iter(kids)
    for b in flags:
        out.append((b, 1))
        if b:
            ser(next(it), out)
    ser(next(it), out)


def ser(node, out):
    """The fields of the plan `node`: a run of ones closed by a zero for the action, low bit first."""
    kind = node[0]
    if kind in ('V', 'E'):
        out.append((0, 1))
    elif kind == 'B':
        out.extend(((1, 2), (node[1], 4)))
        ser_kids(node[2], node[3], out)
    elif kind == 'D':
        out.append((3, 3))
    elif kind == 'R':
        out.append((7, 4))
    elif kind == 'F':
        out.extend(((15, 5), (node[1], 4)))
        ser_kids(node[2], node[3], out)
    elif kind == 'S':
        out.append((31, 6))
        ser(node[1], out)
        ser(node[2], out)
    else:
        raise ValueError(kind)


class Planner(fl.FlipSearch):
    """The search of `flip_cert.FlipSearch` as a plan: each method returns a cost and, when the cost is below the
    limit it was given, the plan below the box: `('V',)` no term, `('E',)` evaluated, `('D',)` dropped,
    `('B', sel, cells, bits)` Buchstab's identity at the floor that the guide gives for `sel`, `('R',)` the
    three-prime reversal, `('F', sel, cells, bits)` the reversal through the largest prime, `('S', half, half)`
    cut in two. `bits` has, for each proposed cut that the kernel meets inside the range, whether the range is cut
    there: consecutive evaluated cells that one test covers are one cell."""

    merge = True
    dmerge = DMERGE

    # the guides (SieveAdHintStratDefs.lean)
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
        """`guideG bl sel`, or inside a tree over a frozen part `guideF ctx β bl sel`."""
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
            if self.rev and revOK(bl):
                self.stat['revtry'] += 1
                c = self.revCost(bl, l2)
                if c < r:
                    self.stat['revwin'] += 1
                    r, how = c, ('R',)
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

    # the kernel's search led by hints (SieveAdHintDefs.lean)
    def cKids(self, rec, top, bl, par, cs, a, lim, h):
        for i, c in enumerate(cs):
            if a < c < top:
                if h % 2 == 1:
                    r = rec([(a, c)] + bl, par, lim, h // 2)
                    if lim <= r[0]:
                        return r
                    r2 = self.cKids(rec, top, bl, par, cs[i + 1:], c, tsub(lim, r[0]), r[1])
                    return r[0] + r2[0], r2[1]
                h //= 2
        return rec([(a, top)] + bl, par, lim, h)

    def cStep(self, O, S, altH, rec, bl, par, lim, h):
        if not bl or not O.grd(bl):
            return lim, h
        x = bl[0]
        if h % 2 == 0:
            return (0, h // 2) if O.van(bl) or self.anyI(bl) else (lim, h // 2)
        if h % 4 == 1:
            p = self.guide(bl, h // 4 % 16)
            if p is None or not (0 < p[0] <= x[0] and self.okJm(bl, p[0], p[1])):
                return lim, h // 64
            return self.cKids(rec, x[1], bl, not par, S.cuts(bl, p[0]), p[0], lim, h // 64)
        if h % 8 == 3:
            dc = O.drp(bl, par)
            return (lim, h // 8) if dc is None else (dc, h // 8)
        if h % 16 == 7:
            return O.alt(bl, par, lim), h // 16
        if h % 32 == 15:
            return altH(bl, par, lim, h // 32)
        if h % 64 == 31:
            mid, h2 = (x[0] + x[1]) // 2, h // 64
            if x[0] < mid < x[1]:
                r = rec([(x[0], mid)] + bl[1:], par, lim, h2)
                if lim <= r[0]:
                    return r
                r2 = rec([(mid, x[1])] + bl[1:], par, tsub(lim, r[0]), r[1])
                return r[0] + r2[0], r2[1]
            return lim, h2
        return lim, h // 64

    def cSolve(self, O, S, altH, n, bl, par, lim, h):
        if n == 0:
            return lim, h
        return self.cStep(O, S, altH, lambda b, p, l, hh: self.cSolve(O, S, altH, n - 1, b, p, l, hh), bl, par,
                          lim, h)

    def cFlipTree(self, ctx, beta, lim, h):
        if not beta:
            return lim, h
        c, t = beta[0], flipT(ctx)
        self.frz, self.fctx = (tsub(DEN, ctx[1]), tsub(DEN, ctx[0]) + 1, 12 + DEN // c[0], beta), ctx
        try:
            S = self.stratF(ctx, beta)
            p = self.guide(beta, h % 16)
            if p is None or not (0 < p[0] <= min(c[0], t) and self.okJm(beta, p[0], p[1])):
                return lim, h // 16
            O = self.opsK(ctx, len(beta))
            return self.cKids(lambda b, pp, l, hh: self.cSolve(O, S, lambda b2, p2, l2, h2: (l2, h2), self.fuel,
                                                               b, pp, l, hh),
                              t, beta, True, S.cuts(beta, p[0]), p[0], lim, h // 16)
        finally:
            self.frz = None

    def cFlipCost(self, bl, lim, h):
        ctx, beta = bl[-1], bl[:-1]
        E = ((ctx[1] + 1) * dropCost(beta + [(tsub(ctx[1], 1), ctx[1] + 1)])
             + (ctx[0] + 1) * dropCost(beta + [(tsub(ctx[0], 1), ctx[0] + 1)]))
        r = self.cFlipTree(ctx, beta, CAPK, h)
        if CAPK <= r[0]:
            return lim, r[1]
        return cdiv(r[0] * (ctx[1] * dropCost(bl) + E) + bdK(ctx, flipT(ctx)) * E, DEN * K), r[1]

    def cAltF(self, bl, par, l, h):
        if not par and flipOK(self.maxlen, bl):
            return self.cFlipCost(bl, l, h)
        return l, h

    def altR0(self, bl, par, l):
        """`(opsR …).alt bl par l`, without counts."""
        if not par and revOK(bl):
            return self.revCost(bl, l)
        return l

    def check(self, bl, par, lim, h):
        """`solveH (opsR …) fillTests stratGFF guideG (altFH stratFF guideF …) fuel bl par lim h`."""
        O = rc.Ops(lambda b: True, tc.vanishOK, tc.dropC, self.altR0)
        return self.cSolve(O, self.SG, self.cAltF, self.fuel, bl, par, lim, h)


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
                 depthF=3, maxlen=6, cap=20.0, pmax=40, fcap=600.0, levels=5, rev=True):
        self.tag, self.lnum, self.lden, self.rev = tag, lnum, lden, rev
        self.h, self.hI, self.depth, self.kappa = h, round(h * DEN), depth, kappa
        self.depthR, self.hR, self.hQ = depthR, round(hR * DEN), round(hQ * DEN)
        self.hF, self.depthF, self.maxlen = round(hF * DEN), depthF, maxlen
        self.hRf, self.hQf, self.hFf = hR, hQ, hF
        self.cap, self.pmax, self.fcap, self.levels = cap, pmax, fcap, levels

    def planner(self):
        return Planner(fc.TestsF(self.lnum, self.lden), self.hI, self.depth, fc.WMIN, self.kappa, self.hR,
                       self.depthR, self.hQ, fc.FUEL, self.hF, self.depthF, self.maxlen, rev=self.rev)


# the kernel's seconds a step, by kind and whether over a frozen part (12 November 2026: twenty-four parts at
# 2150/1000, of 2800 to 4600 steps, in 12 to 32 s each, three at a time on four cores; fitted with a mean error of
# 1.6 s; the three-prime reversal, which the kernel searches without hints, about 2 s)
SEC = {('E', False): 3.6e-3, ('E', True): 3.8e-3, ('V', False): 1e-4, ('V', True): 1e-4, ('B', False): 8.4e-3,
       ('B', True): 1.15e-2, ('D', False): 1.7e-3, ('D', True): 1.05e-3, ('F', False): 4.2e-2, ('R', False): 2.0,
       ('S', False): 7e-4, ('S', True): 7e-4}


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
    fields, cnt = [], Counter()
    for i, (_, _, k) in enumerate(group):
        if i + 1 < len(group):
            fields.append((1, 1))
        ser(k, fields)
        count(k, cnt)
    h = pack(fields)
    a, top, cs = group[0][0], group[-1][1], [g[0] for g in group[1:]]
    c, rest = P.cKids(P.check, top, bl, par, cs, a, K, h)
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
    return rc.wrap(f'theorem tree{T}_{k} : (kidsH solve{T} {tc.nat(top)} {rc.box(bl)} {rc.bool_(par)} '
                   f'[{", ".join(map(str, cs))}] {a} K\xa00x{h:x}).1 ≤ {c} :=\xa0by\xa0decide\xa0+kernel').replace(
                       '\xa0', ' ')


def defs_file(par_):
    T, LN = par_.tag, f'{par_.lnum}/{par_.lden}'
    return f"""/-
# The exponent, the strategies and the search led by hints at `L = {LN}`

Generated by `tools/linnik/hint_cert.py`; do not edit by hand.

The bilinear Type I rule's exponent `{LN}` (`ibPar{T}`), and:

* `strat{T}`, the strategy of the search: `SieveAd.stratGFF` with cells of side at most `{par_.hI}/DEN`
  (`{par_.h}`) and at most the exponent over `{par_.kappa}`, boxes of fewer than `{par_.depth}` primes decomposed, and
  cells wider than `{fc.WMIN}/DEN` (`0.0005`) cut for want of a test;
* `stratK{T}`, the strategy of the trees of the reversal of three primes: `SieveAd.stratKF` with chains of fewer
  than `{par_.depthR}` primes, in cells of side at most `{par_.hR}/DEN` (`{par_.hRf}`);
* `stratF{T}`, the strategy of the trees over the frozen parts: `SieveAd.stratFF` with chains of fewer than
  `{par_.depthF}` primes, in cells of side at most `{par_.hF}/DEN` (`{par_.hFf}`);
* `ops{T}`, the nodes of the search: `SieveAd.opsR` with the tests `SieveAd.fillTestsF` and the reversal of three
  primes, its trees searched with the fuel `{fc.FUEL}` and the smaller prime of a cofactor of two primes in cells of
  side at most `{par_.hQ}/DEN` (`{par_.hQf}`);
* `solve{T}`, the search led by hints: `SieveAd.solveH` with these, the guides `SieveAd.guideG` and
  `SieveAd.guideF`, and as its hinted bound the reversal through the largest prime of boxes of at most
  `{par_.maxlen}` primes, with the tests `SieveAd.frozTestsF` over the frozen parts (`SieveAd.altFHT`).

The tests are the ones that the kernel evaluates in one pass over a box (`SieveAdFastDefs.lean`); they are equal
to `SieveAd.fillTests` and `SieveAd.frozTests` (`SieveAdFast.lean`), and `Linnik{T}.lean` uses the search through
that equality.

The file imports `SieveAdHintStratDefs.lean` and `SieveAdFastDefs.lean`; so neither it nor the part files
(`SieveHint{T}P1.lean` …) load more of `Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveAdHintStratDefs
import SieveAdFastDefs

namespace SieveCert

/-- **The bilinear Type I rule's exponent** at `L = {LN}`. -/
@[instance_reducible] def ibPar{T} : IBPar := ⟨{par_.lnum}, {par_.lden}⟩

end SieveCert

namespace SieveAd

open SieveCert

/-- **The strategy of the search at `{LN}`.** -/
def strat{T} : Strat := @stratGFF ibPar{T} {par_.kappa} {par_.hI} {par_.depth} {fc.WMIN}

/-- **The strategy of the trees of the reversal of three primes at `{LN}`.** -/
def stratK{T} : Cell → ℕ → Strat := @stratKF ibPar{T} {par_.kappa} {par_.hR} {par_.depthR} {fc.WMIN}

/-- **The strategy of the trees over the frozen parts at `{LN}`.** -/
def stratF{T} : Cell → List Cell → Strat := @stratFF ibPar{T} {par_.kappa} {par_.hF} {par_.depthF} {fc.WMIN}

/-- **The nodes of the search at `{LN}`**: those of a tree, and the reversal of three primes. -/
noncomputable def ops{T} : Ops := opsR (@fillTestsF ibPar{T}) stratK{T} {fc.FUEL} (cutsQ {par_.hQ})

/-- **The search led by hints at `{LN}`**, with the reversal through the largest prime as its hinted bound. -/
noncomputable def solve{T} : List Cell → Bool → ℕ → ℕ → ℕ × ℕ :=
  solveH ops{T} (@fillTestsF ibPar{T}) strat{T} (@guideG ibPar{T})
    (altFHT (@frozTestsF ibPar{T}) stratF{T} (@guideF ibPar{T}) {fc.FUEL} {par_.maxlen}) {fc.FUEL}

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
    nrev = st.get(('R', False), 0)
    revtxt = (f' and {nrev} reversals of three primes (`SieveAdRevDefs.lean`)' if nrev else
              ' (the reversal of three primes of the theorem at `218/100` is among the search\'s nodes, and the '
              'plan does not use it)')
    imports = '\n'.join(f'import SieveHint{T}P{i}' for i in range(1, nfiles + 1))
    plain = textwrap.fill(
        f'Plain statement (`linnik_{T}`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there '
        f'is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`, with no hypothesis. The route is at `L = {LN}` '
        f'(`route{T}`), with the estimate in two variables alone, and the tests are `SieveAd.fillTests`, as for the '
        f'theorem at `2165/1000`. The sieve\'s decomposition is a tree of Buchstab steps with the reversal of a '
        f'term of the sign `−` of three or five primes through its largest prime, the cofactor kept as one number '
        f'(`SieveAdFlipDefs.lean`): its tree runs over the frozen numbers, with the tests `SieveAd.frozTests`. The '
        f'kernel does not search for the tree: it follows hints (`SieveAd.solveH`, `SieveAdHintDefs.lean`), the '
        f'plan of the search that `tools/linnik/hint_cert.py` ran ({stats["boxes"]} boxes, {stats["fboxes"]} of '
        f'them over frozen parts), in {nsteps} steps, {nflip} of them reversals through the largest prime{revtxt}; '
        f'each step is checked, and a cost that the search returns below its limit bounds the term whatever the '
        f'hints are (`SieveAd.pr_of_kidsH`). The search is in {len(parts)} parts, {nfiles} files '
        f'(`SieveHint{T}P1.lean` … `SieveHint{T}P{nfiles}.lean`). The kernel evaluates the tests in one pass over '
        f'a box (`SieveAd.fillTestsF`, `SieveAd.frozTestsF`), and they are equal to the tests that are proved sound '
        f'(`SieveAdFast.lean`).', width=116)
    return f"""/-
# Linnik's theorem with exponent `{LN}`, by a search led by hints

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/hint_cert.py`; do not edit by hand.

{plain}

* `route{T}`, `routeOK{T}`, `ibFits{T}`: the route and its exponent.
* `sound{T}`, `soundX{T}`: the tests are sound, and sound under two more atoms.
* `solve{T}_eq`: the search of the part files, with its tests in one pass, is the search with the tests
  `fillTests` and `frozTests`.
* `part{T}`: a part of the search bounds its term.
* `node{T}_0` … `node{T}_{len(nodes) - 1}`: the {len(nodes)} cells whose search is cut into parts by the cells of the next prime:
  the cell's own Buchstab step (`SieveAd.pr_buch`), and the pieces below it.
* `tree{T}`: the term of the box of the first prime, of the sign `−`, is at most `(c/K + o(1))x/(φ(q) log x)` in
  `𝒜` minus the comparison set, with `c = {total}`, which is `{total / K:.5f}·K`.
* `linnik_{T}`: `SieveAd.linnik_pr` at them, with the root at the floor `{f0}/DEN`, by the comparison with the rest
  among the tree's primes.

The file imports `SieveAdHint.lean`, `SieveAdFill.lean`, `SieveAdFast.lean` and the part files.
-/
import SieveAdHint
import SieveAdFill
import SieveAdFast
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

/-- The tests at `{LN}` are sound under two more atoms. -/
theorem soundX{T} : (fillTests).SoundX := fillTests_soundX

/-- **The search of the part files is the search with the tests that are proved sound**: its tests in one pass
are equal to `fillTests` and `frozTests`. -/
theorem solve{T}_eq : solve{T} = solveH (opsR fillTests stratK{T} {fc.FUEL} (cutsQ {par_.hQ})) fillTests strat{T}
    guideG (altFH stratF{T} guideF {fc.FUEL} {par_.maxlen}) {fc.FUEL} := by
  unfold solve{T} ops{T}
  rw [fillTestsF_eq, altFHT_fast]

/-- **A part of the search bounds its term**: `SieveAd.pr_of_kidsH` at the route. -/
theorem part{T} {{top : ℕ}} {{bl : List Cell}} {{par : Bool}} {{cs : List ℕ}} {{a c h : ℕ}}
    (hk : (kidsH solve{T} top bl par cs a K h).1 ≤ c) (hc : c < K) : PR ((a, top) :: bl) par c := by
  rw [solve{T}_eq] at hk
  exact pr_of_kidsH sound{T} soundX{T} stratK{T} {fc.FUEL} (cutsQ {par_.hQ}) stratF{T} guideF {fc.FUEL} {par_.maxlen}
    strat{T} guideG {fc.FUEL} hk hc

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
    if a and a[0] == '--box':
        v = [int(x) for x in a[1:5]]
        maxlen = int(a[5]) if len(a) > 5 and a[5].isdigit() else 4
        P = Planner(fc.TestsF(fc.LNUM, fc.LDEN), fc.HI, fc.DEPTH, fc.WMIN, fc.KAPPA, fc.HR, fc.DEPTHR, fc.HQ,
                    fc.FUEL, round(0.012 * DEN), 3, maxlen, rev='--norev' not in a)
        bl = [(v[2], v[3]), (v[0], v[1])]
        (c, node), w = P.work(lambda: P.plan(bl, True, K))
        out = []
        ser(node, out)
        h = pack(out)
        r = P.check(bl, True, K, h)
        assert r == (c, 0), (r, c)
        cnt = Counter()
        count(node, cnt)
        print(f'theorem hintPart : (solveH ops fillTests strat guide altH {fc.FUEL} {rc.box(bl)} true K 0x{h:x}).1 = '
              f'{c} := by decide +kernel')
        print(f'cost/K = {c / K:.6f}; {sum(cnt.values())} steps {dict(cnt)}; {h.bit_length()} bits of hints; '
              f'the search: {w["calls"]} boxes ({w["fcalls"]} over frozen parts); {P.stat}')
        return 0
    import time
    procs = int(a[a.index('--procs') + 1]) if '--procs' in a else 4
    out = a[a.index('--out') + 1] if '--out' in a else None
    if a and a[0] == '--try':
        ln, ld = map(int, a[2].split('/'))
        par_ = Par(a[1], ln, ld, h=float(a[3]), hF=float(a[4]), maxlen=int(a[5]), rev='--norev' not in a)
        rows = tuple(int(x) for x in a[a.index('--rows') + 1:][:2]) if '--rows' in a else None
    elif not a or a[0] in ('--check', '--out', '--procs'):
        par_, rows = Par(TAG, LNUM, LDEN, h=H, hF=HF, maxlen=MAXLEN, rev=False), None
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
