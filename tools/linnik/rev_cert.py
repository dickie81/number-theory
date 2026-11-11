#!/usr/bin/env python3
"""rev_cert.py [--check] [--stats] [--try H DEPTH KAPPA DEPTHR HR HQ [W1 W2 a/b] [--norev]]: the search with role
reversal at L = 218/100, searched as the kernel searches it, cut into parts, and the Lean files of the theorem there.

The route is L = 218/100 with the window [45073, 46472]/10^5 (`gen_cgl_curve.py` computes it and writes its
Proposition 3'). There the search of `tree_cert.py` (a tree of Buchstab steps with the window's tests and those of the
estimate in two variables) does not reach a cost below K. This search has one more node, **role reversal**
(`lib/pnt/SieveAdRevDefs.lean`): a term of three primes p1 > p2 > p3 of the sign −, whose numbers are n = p1 p2 p3 m
with m a prime or a product of two, is bounded by the sums over r' = n/p1 of the n that are rough at p3's least
value, each a term of the usual kind for the atoms of r' under a condition on their product, with its own tree.
`SieveAd.solveG` with the nodes `SieveAd.opsR` is that search, the kernel runs it, and a cost that it returns below
its limit bounds the term (`SieveAd.solveR_sound`, `lib/pnt/SieveAdRevSearch.lean`). This script is the search in
Python, definition by definition:

  * `tree_cert.py`'s tests, proposers and costs (`Tests`, `Search`: `mixTests`, `propI2`, `propJ`, `dropC`, ...);
  * `Ops`, `nodeG`, `stepG`, `solveG`; `vanishK`, `dropK`, `opsK`; `rootJ`, `famCost`, `cellQ`, `revOK`,
    `revCost`, `opsR`; `geoCuts`, `cutsOfG`, `cutsK`, `cutsQ`, `stratG`, `stratK` (SieveAdRevDefs.lean).

The search treats a box as `tree_cert.py`'s does, with the new prime's range cut into cells of side at most HI and at
most the exponent over KAPPA, and for a box of three primes of the sign − it takes the reversal's cost if that is
below the cost of Buchstab's identity. A reversal's trees have chains of fewer than DEPTHR primes, in cells of side
at most HR (twice that from the second prime of a chain on), and the smaller prime of a cofactor of two primes is in
cells of side at most HQ.

The kernel checks the search in parts, each a range of consecutive cells of one prime (`kids`). The bound of the
first term is put together from them (`plan`): the cells of the first prime in order, and for a cell whose search is
long, its own Buchstab step (`SieveAd.pr_buch`) and the cells of the next prime below it, and so on down; a cell
that the search drops, after a long search for a tree that costs less, is dropped outright (`SieveAd.pr_drop`: half
of the search's time was there); a cell that is neither is cut in two if that costs no more. A part's time is
predicted from the search's work in it (`pred`), and the parts are cut at CAP predicted seconds, because the
kernel's memory in a part grows with its time.

It writes `lib/pnt/SieveGrid21800.lean` (the grid, the strategies and the nodes), `lib/pnt/SieveTree21800P<k>.lean`
(the parts, each by `decide +kernel`) and `lib/pnt/Linnik21800.lean` (the route, the bound from the parts, and the
theorem). With `--check`, nothing is written: the files are regenerated in memory and compared with `lib/pnt` (exit
1 on a difference). With `--stats`, the search's work and the parts' predicted times are printed. With `--try`, only
the search is run, with other parameters (and on another route, if given; without the reversal, with `--norev`),
and its cost is printed.

Values (11 November 2026): the search costs 0.91849 K on 1063672 boxes, with 3664 reversals taken of 8185 tried;
without the reversal it costs 1.16057 K (`--try 0.006 6 10 3 0.012 0.02 --norev`). The bound of the files costs
0.91812 K (five cells are cut in two): 587 parts in 16 files, 105 cells with their own Buchstab step and 216
dropped outright, which the kernel checks in 5832 seconds in all (66 to 564 a file, with at most 3.1 GB).
`--try 0.006 6 10 4 0.006 0.006`: 0.90043, 1309777 boxes; `--try 0.007 6 10 3 0.009 0.012`:
1.01637; `--try 0.006 5 10 3 0.009 0.012`: 2.10153; `--try 0.006 6 10 2 0.012 0.02`: 1.05710;
`--try 0.006 6 10 4 0.006 0.006 45481 46349 2175/1000`: 1.05257;
`--try 0.005 6 10 4 0.006 0.006 45481 46349 2175/1000`: 0.98482, 2631876 boxes;
`--try 0.006 6 10 4 0.006 0.006 45892 46226 217/100`: 1.26965;
`--try 0.005 6 10 4 0.006 0.006 45892 46226 217/100`: 1.18333;
`--try 0.004 7 12 4 0.005 0.005 45892 46226 217/100`: 1.03938, 10140441 boxes.

Needs Python 3 only. Two minutes.
"""
import os
import sys
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
from tree_cert import (DEN, K, SC, BIG, CFGW, cdiv, tsub, omKw, loSum, hiSum, vanishOK, dropC, trF, exF, wrap,  # noqa: E402
                       nat)

PNT = tc.PNT
# the route, the window and the strategy
TAG, LNUM, LDEN, W1, W2, GN = '21800', 218, 100, 45073, 46472, 272
HI, DEPTH, WMIN, FUEL = round(0.006 * DEN), 6, round(0.0005 * DEN), 200
KAPPA, HR, DEPTHR, HQ = 10, round(0.012 * DEN), 3, round(0.02 * DEN)
CAPK = 64 * K
# the parts: at most CAP predicted seconds each (a cell that is not cut further may be longer), a file of at most
# PMAX parts and FCAP predicted seconds; a cell is cut by the next prime's cells down to the LEVELS-th prime
CAP, PMAX, FCAP, LEVELS = 22.0, 40, 600.0, 5
# a cell that the search drops after more than CAPD predicted seconds is dropped outright, without the search
CAPD = 6.0


# SieveAdRevDefs.lean, definition by definition

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
    """`SieveAd.solveG (opsR mixTests (stratK κ hR depthR wmin) fuel (cutsQ hQ)) mixTests (stratG κ hI depth wmin)`,
    with counts of its work."""

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
        """`solveG O mixTests S n bl par lim`."""
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
        """`solveG opsR mixTests stratG fuel bl par lim`."""
        return self.solveG(self.OR, self.SG, self.fuel, bl, par, lim)

    def kidsR(self, top, bl, par, cs, a, lim):
        """`kids (solveG opsR mixTests stratG fuel) top bl par cs a lim`."""
        return self.kidsG(self.solveR, top, bl, par, cs, a, lim)


def rowCuts(S):
    """The ends of the cells of the first prime: steps of at most hI and at most the exponent over κ from V to
    DEN/2 + 1, the window's ends, and a thin cell at the top."""
    T = S.T
    return sorted(set([T.V] + geoCuts(S.kappa, S.hI, DEN // 2 + 1, 4096, T.V))
                  | {T.U1 + 1, T.U2 - 1, DEN // 2 - S.wmin})


def search_only(h, depth, kappa, depthR, hR, hQ, w1, w2, ln, ld, rev=True):
    """The cost of the search with other parameters, the number of boxes searched and the reversals' counts; with
    `rev` false, the search without the reversal (not `SieveAd.opsR`'s: its node `alt` returns its limit)."""
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
    second, so a part of CAP seconds needs about 3.2 GB."""
    return tc.pred(dict(w, dfs=w['dfs'] - w['kdfs'])) + 3.3e-4 * w['kdfs']


def addw(a, b):
    return {k: a[k] + b[k] for k in a}


def groups(cells, cap):
    """Consecutive cells [(lo, hi, cost, work)] in groups of at most `cap` predicted seconds."""
    out, cur, w = [], [], None
    for c in cells:
        w2 = c[3] if w is None else addw(w, c[3])
        if cur and pred(w2) > cap:
            out.append(cur)
            cur, w2 = [], c[3]
        cur.append(c)
        w = w2
    if cur:
        out.append(cur)
    return out


def plan():
    """The parts of the search and the bound's assembly: (T, searched, stat, parts, root, total), with

    parts: [(top, bl, par, cuts, a, cost, work)], a part being `kids (solveG ... FUEL) top bl par cuts a K <= cost`;
    root: the pieces of the first prime's range, in order. A piece of a prime's range is ('part', k), or
    ('buch', bl, par, f, cfg, pieces, cost) for a cell, the newest of the box `bl` of the sign `par`, decomposed at
    the floor f with the configuration cfg, the new prime's range in the pieces `pieces`, or ('drop', bl, par, cost)
    for a cell that is dropped.

    A cell that the search drops, after more than CAPD predicted seconds of search for a tree that costs less, is
    dropped outright (`SieveAd.pr_drop`). A cell whose search is predicted longer than CAP is decomposed by its own
    Buchstab step, if the search decomposes it so and the cell has fewer than LEVELS primes; otherwise it is cut in
    two, if the two halves cost no more together and each is shorter than three quarters of the cell; otherwise it
    is a part by itself."""
    T = tc.Tests(W1, W2, LNUM, LDEN)
    S = RevSearch(T, HI, DEPTH, WMIN, KAPPA, HR, DEPTHR, HQ, FUEL)
    sys.setrecursionlimit(100000)
    cuts = rowCuts(S)
    assert cuts[0] == T.V and cuts[-1] == DEN // 2 + 1 and T.okJ([], T.V, CFGW)
    parts = []
    count = dict.fromkeys(('buch', 'halved', 'long', 'drop'), 0)
    saved = [0.0]

    def cell_of(bl, par, s, e):
        c, w = S.work(lambda: S.solveR([(s, e)] + bl, par, K))
        return s, e, c, w

    def part(top, bl, par, cells):
        cs = [c[0] for c in cells[1:]]
        if len(cells) == 1:
            c, w = cells[0][2], cells[0][3]
        else:
            c, w = S.work(lambda: S.kidsR(top, bl, par, cs, cells[0][0], K))
        assert c < K
        count['long'] += pred(w) > 1.5 * CAP
        parts.append((top, bl, par, cs, cells[0][0], c, w))
        return len(parts) - 1

    def piece_cost(p):
        return parts[p[1]][5] if p[0] == 'part' else p[3] if p[0] == 'drop' else p[6]

    def decompose(bl, par, c):
        if vanishOK(bl) or S.anyI(bl) or len(bl) >= DEPTH:
            return None
        fj = S.firstJ(bl, bl[0][0], S.propJ(bl))
        if fj is None:
            return None
        f, cfg = fj
        ends = [f]
        for x in S.cutsOfG(bl, f):
            if ends[-1] < x < bl[0][1]:
                ends.append(x)
        ends.append(bl[0][1])
        cells = [cell_of(bl, not par, s, e) for s, e in zip(ends, ends[1:])]
        if sum(x[2] for x in cells) > c:
            return None
        ps = pieces(bl, not par, cells)
        count['buch'] += 1
        return ('buch', bl, par, f, cfg, ps, sum(piece_cost(p) for p in ps))

    def pieces(bl, par, cells):
        out, light = [], []

        def flush():
            for g in groups(light, CAP):
                out.append(('part', part(g[-1][1], bl, par, g)))
            light.clear()

        def handle(x):
            s, e, c, w = x
            if pred(w) > CAPD and dropC([(s, e)] + bl, par) == c:
                flush()
                out.append(('drop', [(s, e)] + bl, par, c))
                count['drop'] += 1
                saved[0] += pred(w)
                return
            if pred(w) <= CAP:
                light.append(x)
                return
            sub = decompose([(s, e)] + bl, par, c) if len(bl) + 1 < LEVELS else None
            if sub is not None:
                flush()
                out.append(sub)
                return
            mid = (s + e) // 2
            if s < mid < e:
                h1, h2 = cell_of(bl, par, s, mid), cell_of(bl, par, mid, e)
                if h1[2] + h2[2] <= c and max(pred(h1[3]), pred(h2[3])) <= 0.75 * pred(w):
                    count['halved'] += 1
                    handle(h1)
                    handle(h2)
                    return
            light.append(x)

        for x in cells:
            handle(x)
        flush()
        return out

    rows = [cell_of([], False, a, b) for a, b in zip(cuts, cuts[1:])]
    searched, stat = dict(S.W), dict(S.stat)
    root = pieces([], False, rows)
    assert S.minfuel > 100
    total = sum(piece_cost(p) for p in root)
    assert total < K
    stat.update(count)
    stat['saved'] = round(saved[0])
    return T, searched, stat, parts, root, total


# the Lean files

def cell(c):
    return f'({c[0]}, {nat(c[1]).strip("()")})'


def box(bl):
    return '[' + ', '.join(cell(c) for c in bl) + ']'


def bool_(b):
    return 'true' if b else 'false'


def part_stmt(k, p):
    top, bl, par, cs, a, c, _ = p
    return wrap(f'theorem tree{TAG}_{k} : kids (solveG ops{TAG} mixTests strat{TAG} {FUEL}) {nat(top)} {box(bl)} '
                f'{bool_(par)} [{", ".join(map(str, cs))}] {a} K ≤ {c} :=\xa0by\xa0decide\xa0+kernel').replace('\xa0', ' ')


def grid_file(T):
    return f"""/-
# The grid, the strategies and the nodes of the search with role reversal at `L = {LNUM}/{LDEN}`

Generated by `tools/linnik/rev_cert.py`; do not edit by hand.

The grid of `SieveTypeIIU{TAG}D.typeII_{TAG}d`'s window: `U1 = ⌈({W1}/100000)DEN⌉`, `U2 = ⌊({W2}/100000)DEN⌋`
(`grid{TAG}`, `gridOK{TAG}`; its number of cells is not used by a search), the bilinear Type I rule's exponent
`{LNUM}/{LDEN}` (`ibPar{TAG}`), and:

* `strat{TAG}`, the strategy of the search: `SieveAd.stratG` with cells of side at most `{HI}/DEN` (`0.006`) and at
  most the exponent over `{KAPPA}`, boxes of fewer than `{DEPTH}` primes decomposed, and cells wider than
  `{WMIN}/DEN` (`0.0005`) cut for want of a test;
* `stratK{TAG}`, the strategy of a reversal's trees: `SieveAd.stratK` with chains of fewer than `{DEPTHR}` primes, in
  cells of side at most `{HR}/DEN` (`0.012`) and at most the exponent over `{KAPPA}`;
* `ops{TAG}`, the nodes of the search: `SieveAd.opsR` with those trees, searched with the fuel `{FUEL}`, and the
  smaller prime of a cofactor of two primes in cells of side at most `{HQ}/DEN` (`0.02`).

The file imports `SieveAdRevDefs.lean`; so neither it nor the part files (`SieveTree{TAG}P1.lean` …) load more of
`Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveAdRevDefs

namespace SieveCert

/-- **The grid at `L = {LNUM}/{LDEN}`**: `U1 = ⌈({W1}/100000)DEN⌉`, `U2 = ⌊({W2}/100000)DEN⌋`. -/
@[instance_reducible] def grid{TAG} : Grid := ⟨({W1} * DEN + 99999) / 100000, {W2} * DEN / 100000, {GN}, 1⟩

theorem gridOK{TAG} : @GridOK grid{TAG} :=
  @GridOK.mk grid{TAG} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The bilinear Type I rule's exponent** at `L = {LNUM}/{LDEN}`. -/
@[instance_reducible] def ibPar{TAG} : IBPar := ⟨{LNUM}, {LDEN}⟩

end SieveCert

namespace SieveAd

open SieveCert

/-- **The strategy of the search at `{LNUM}/{LDEN}`.** -/
def strat{TAG} : Strat := @stratG grid{TAG} ibPar{TAG} {KAPPA} {HI} {DEPTH} {WMIN}

/-- **The strategy of a reversal's trees at `{LNUM}/{LDEN}`.** -/
def stratK{TAG} : Cell → ℕ → Strat := @stratK grid{TAG} ibPar{TAG} {KAPPA} {HR} {DEPTHR} {WMIN}

/-- **The nodes of the search at `{LNUM}/{LDEN}`**: those of a tree, and role reversal. -/
def ops{TAG} : Ops := opsR (@mixTests grid{TAG} ibPar{TAG}) stratK{TAG} {FUEL} (cutsQ {HQ})

end SieveAd

#print axioms SieveCert.gridOK{TAG}
"""


def part_files(parts):
    """The parts in files: consecutive parts, at most PMAX of them and FCAP predicted seconds a file."""
    files, cur, t = [], [], 0.0
    for k, p in enumerate(parts):
        tp = pred(p[6])
        if cur and (len(cur) >= PMAX or t + tp > FCAP):
            files.append(cur)
            cur, t = [], 0.0
        cur.append(k)
        t += tp
    if cur:
        files.append(cur)
    out = {}
    for i, g in enumerate(files, 1):
        secs = sum(pred(parts[k][6]) for k in g)
        desc = textwrap.fill(
            f'File {i} of {len(files)}: the parts `tree{TAG}_{g[0]}` … `tree{TAG}_{g[-1]}` of the search with role '
            f'reversal at `L = {LNUM}/{LDEN}`, with the strategy `SieveAd.strat{TAG}` and the nodes `SieveAd.ops{TAG}` '
            f'({len(g)} parts, predicted {secs:.0f} s of the kernel). A part is a range of consecutive cells of one '
            f'prime: the sum of the costs that the search (`SieveAd.solveG`) returns on them, each searched with the '
            f'limit that the cells before it leave of `K`, is at most the part\'s bound, by `decide +kernel`, one at '
            f'a time (`Elab.async false`). `Linnik{TAG}.lean` makes the bound of the first term from the parts.',
            width=116)
        body = '\n\n'.join(part_stmt(k, parts[k]) for k in g)
        out[f'SieveTree{TAG}P{i}.lean'] = f"""/-
# The search with role reversal at `L = {LNUM}/{LDEN}`, parts {g[0]}–{g[-1]} of {len(parts)}

Generated by `tools/linnik/rev_cert.py`; do not edit by hand.

{desc}

The file imports `SieveGrid{TAG}.lean`.
-/
import SieveGrid{TAG}

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveAd

open SieveCert

section

attribute [local instance] grid{TAG} ibPar{TAG}

{body}

end

end SieveAd

#print axioms SieveAd.tree{TAG}_{g[0]}
#print axioms SieveAd.tree{TAG}_{g[-1]}
"""
    return out


def chain(items):
    """`pr_split` over the pieces `items` (Lean terms), nested to the right, one piece a line."""
    if len(items) == 1:
        return f'    {items[0]}'
    lines = [f'    pr_split (by decide) (by decide) ({x}) (' for x in items[:-1]]
    return '\n'.join(lines) + f'\n    {items[-1]}' + ')' * (len(items) - 1)


def final_file(T, parts, root, total, nfiles):
    LN = f'{LNUM} / {LDEN}'
    nodes = []

    def term(p):
        """The Lean term of a piece; a cell with its own Buchstab step becomes a theorem `node{TAG}_<i>` first."""
        if p[0] == 'part':
            return f'part{TAG} tree{TAG}_{p[1]} (by decide)'
        if p[0] == 'drop':
            return f'pr_drop sound{TAG} (bl := {box(p[1])}) (par := {bool_(p[2])}) (dc := {p[3]}) (by decide +kernel)'
        _, bl, par, f, cfg, ps, c = p
        items = [term(x) for x in ps]
        i = len(nodes)
        cfgs = f'⟨{cfg[0]}, {cfg[1]}, {cfg[2]}, {cfg[3]}, {bool_(cfg[4])}⟩'
        what = ('first', 'second', 'third', 'fourth', 'fifth')[len(bl) - 1]
        doc = wrap(f"/-- The cell `{cell(bl[0])}` of the {what} prime: Buchstab's identity at the floor `{f}`, and the "
                   f"pieces of the next prime's range. -/", '')
        nodes.append(f"""{doc}
theorem node{TAG}_{i} : PR {box(bl)} {bool_(par)} {c} :=
  pr_mono (pr_buch sound{TAG} (x := {cell(bl[0])}) (b := {box(bl[1:])}) (par := {bool_(par)}) (f := {f})
    (cfg := {cfgs}) (by decide) (by decide +kernel) (
{chain(items)})) (by decide)""")
        return f'node{TAG}_{i}'

    items = [term(p) for p in root]

    def drops(ps):
        return sum(1 if p[0] == 'drop' else drops(p[5]) if p[0] == 'buch' else 0 for p in ps)

    ndrop = drops(root)
    imports = '\n'.join(f'import SieveTree{TAG}P{i}' for i in range(1, nfiles + 1))
    return f"""/-
# Linnik's theorem with exponent `{LN}`, by a search with role reversal

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/rev_cert.py`; do not edit by hand.

Plain statement (`linnik_{TAG}`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`, with no hypothesis. The route is at `L = {LN}` on the window
`[{W1}/100000, {W2}/100000]` (`route{TAG}`, with its Type II estimate `SieveTypeIIU{TAG}D.typeII_{TAG}d`). The
sieve's decomposition is chosen term by term, as a tree of Buchstab steps (`SieveAdDefs.lean`) with the window's
tests and those of the estimate in two variables (`SieveAd.mixTests`), and with one more step, **role reversal**
(`SieveAdRevDefs.lean`): a term of three primes of the sign `−` is bounded through the sums over the cofactor of its
largest prime. Nothing is written out: the kernel runs a search (`SieveAd.solveG`, with the strategy
`SieveAd.strat{TAG}` and the nodes `SieveAd.ops{TAG}`) in {len(parts)} parts, {nfiles} files (`SieveTree{TAG}P1.lean` …
`SieveTree{TAG}P{nfiles}.lean`), and a cost that the search returns below its limit bounds the term
(`SieveAd.pr_of_kids`).

* `route{TAG}`, `routeOK{TAG}`, `typeII{TAG}`, `fits{TAG}`, `ibFits{TAG}`: the route, its estimate and the grid's fit.
* `sound{TAG}`, `soundX{TAG}`: the tests are sound, and sound under two more atoms (`SieveAd.mixTests_sound`,
  `SieveAd.mixTests_soundX`).
* `part{TAG}`: a part of the search bounds its term.
* `node{TAG}_0` … `node{TAG}_{len(nodes) - 1}`: the {len(nodes)} cells whose search is cut into parts by the cells of the next prime:
  the cell's own Buchstab step (`SieveAd.pr_buch`), and the pieces below it. A piece is a part, another such cell,
  or a cell dropped outright (`SieveAd.pr_drop`): one of the {ndrop} that the search drops after a long search for a
  tree that costs less.
* `tree{TAG}`: the term of the box of the first prime, of the sign `−`, is at most `(c/K + o(1))x/(φ(q) log x)` in
  `𝒜` minus the comparison set, with `c = {total}`, which is `{total / K:.5f}·K`.
* `linnik_{TAG}`: `SieveAd.linnik_pr` at them.

The file imports `SieveAdRevSearch.lean`, `SieveAdMix.lean`, `SieveTypeIIU{TAG}D.lean` and the part files.
-/
import SieveAdRevSearch
import SieveAdMix
import SieveTypeIIU{TAG}D
{imports}

namespace Linnik{TAG}

open SieveCert SieveRoute SieveQ SieveAd

/-- **The route's parameters at `{LN}`**: `L = {LN}` on the window `[{W1}/100000, {W2}/100000]`. -/
@[instance_reducible] noncomputable def route{TAG} : Route := ⟨{LN}, {W1} / 100000, {W2} / 100000⟩

/-- `route{TAG}` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK{TAG} : @RouteOK route{TAG} :=
  @RouteOK.mk route{TAG} (show (2 : ℝ) < {LN} by norm_num) (show (0 : ℝ) < {W1} / 100000 by norm_num)
    (show ({W1} / 100000 : ℝ) < {W2} / 100000 by norm_num) (show ({W2} / 100000 : ℝ) < 1 by norm_num)
    (show ({LN} : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU{TAG}D.typeII_{TAG}d` as `TypeIIAt`** at the route's parameters. -/
theorem typeII{TAG} : @TypeIIAt route{TAG} := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU{TAG}D.typeII_{TAG}d hf0 hsupp K₀ he₁ hη hη1

/-- `grid{TAG}` fits `route{TAG}`: `({W1}/100000)·DEN < U1`, `U2 < ({W2}/100000)·DEN` and `DEN < ({LN})·U2`. -/
theorem fits{TAG} : @Fits route{TAG} grid{TAG} := by
  refine @Fits.mk route{TAG} grid{TAG} ?_ ?_ ?_
  · have h : ({W1} * DEN : ℕ) < 100000 * (({W1} * DEN + 99999) / 100000) := by decide
    have h' : ({W1} : ℝ) * DEN < 100000 * ((({W1} * DEN + 99999) / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show ({W1} / 100000 : ℝ) * DEN < ((({W1} * DEN + 99999) / 100000 : ℕ) : ℝ)
    linarith
  · have h : 100000 * ({W2} * DEN / 100000) < {W2} * DEN := by decide
    have h' : (100000 : ℝ) * (({W2} * DEN / 100000 : ℕ) : ℝ) < {W2} * DEN := by exact_mod_cast h
    show (({W2} * DEN / 100000 : ℕ) : ℝ) < {W2} / 100000 * DEN
    linarith
  · have h : {LDEN} * DEN < {LNUM} * ({W2} * DEN / 100000) := by decide
    have h' : ({LDEN} : ℝ) * DEN < {LNUM} * (({W2} * DEN / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < {LN} * (({W2} * DEN / 100000 : ℕ) : ℝ)
    linarith

/-- `ibPar{TAG}`'s exponent `Lnum/Lden` is the route's `L = {LN}`. -/
theorem ibFits{TAG} : @IBFits route{TAG} ibPar{TAG} :=
  @IBFits.mk route{TAG} ibPar{TAG} (show (({LNUM} : ℕ) : ℝ) / (({LDEN} : ℕ) : ℝ) = {LN} by norm_num)

section

attribute [local instance] route{TAG} routeOK{TAG} grid{TAG} gridOK{TAG} fits{TAG} ibPar{TAG} ibFits{TAG}

/-- The tests at `{LN}` are sound. -/
theorem sound{TAG} : (mixTests).Sound := mixTests_sound typeII{TAG}

/-- The tests at `{LN}` are sound under two more atoms. -/
theorem soundX{TAG} : (mixTests).SoundX := mixTests_soundX typeII{TAG}

/-- **A part of the search bounds its term**: `SieveAd.pr_of_kids` at the route. -/
theorem part{TAG} {{top : ℕ}} {{bl : List Cell}} {{par : Bool}} {{cs : List ℕ}} {{a c : ℕ}}
    (h : kids (solveG ops{TAG} mixTests strat{TAG} {FUEL}) top bl par cs a K ≤ c) (hc : c < K) :
    PR ((a, top) :: bl) par c :=
  pr_of_kids sound{TAG} soundX{TAG} stratK{TAG} {FUEL} (cutsQ {HQ}) strat{TAG} {FUEL} h hc

{chr(10).join(n + chr(10) for n in nodes)}
/-- **The first term at `{LN}`**: the term of the box of the first prime, with the cell `({T.V}, DEN/2 + 1)`, of the
sign `−`, is at most `(c/K + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set, with `c = {total}`, below `K`. -/
theorem tree{TAG} : PR [({T.V}, DEN / 2 + 1)] false {total} :=
  pr_mono (
{chain(items)}) (by decide)

/-- **Linnik's theorem with exponent `{LN}`, by a search with role reversal**: there is `K` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`. -/
theorem linnik_{TAG} : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ ({LN} : ℝ) :=
  linnik_pr sound{TAG} {T.V} cfgW (by decide) (by decide +kernel) tree{TAG} (by decide)

end

end Linnik{TAG}

#print axioms Linnik{TAG}.tree{TAG}
#print axioms Linnik{TAG}.linnik_{TAG}
"""


def generate():
    T, searched, stat, parts, root, total = plan()
    files = {f'SieveGrid{TAG}.lean': grid_file(T)}
    pf = part_files(parts)
    files.update(pf)
    files[f'Linnik{TAG}.lean'] = final_file(T, parts, root, total, len(pf))
    return files, (searched, stat, parts, root, total)


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
    files, (searched, stat, parts, root, total) = generate()
    times = [pred(p[6]) for p in parts]
    print(f'L = {LNUM}/{LDEN}, window [{W1}, {W2}]/10^5: cost/K = {total / K:.5f}; {searched["calls"]} boxes searched; '
          f'reversals tried {stat["revtry"]}, taken {stat["revwin"]}; {len(parts)} parts in {len(files) - 2} files, '
          f'{stat["buch"]} cells cut by the next prime, {stat["halved"]} in two and {stat["drop"]} dropped outright '
          f'(their search: {stat["saved"]} predicted seconds); predicted seconds of the kernel {sum(times):.0f}, a part '
          f'at most {max(times):.0f}, {stat["long"]} above {1.5 * CAP:.0f}')
    if '--stats' in sys.argv:
        print('work:', searched, stat)
        for k, p in enumerate(parts):
            print(f'part {k}: {times[k]:.1f} s; box of {len(p[1])} primes, {len(p[3]) + 1} cells', p[6])
    if '--check' in sys.argv:
        there = sorted(f for f in os.listdir(PNT)
                       if f.startswith(f'SieveTree{TAG}P') or f in (f'SieveGrid{TAG}.lean', f'Linnik{TAG}.lean'))
        bad = [n for n, t in files.items()
               if not os.path.exists(os.path.join(PNT, n)) or open(os.path.join(PNT, n), encoding='utf-8').read() != t]
        bad += [n for n in there if n not in files]
        print('SEARCH', TAG, 'FAIL: ' + ', '.join(bad) if bad else 'PASS')
        return 1 if bad else 0
    for n in os.listdir(PNT):
        if n.startswith(f'SieveTree{TAG}P') and n not in files:
            os.remove(os.path.join(PNT, n))
    for n, t in files.items():
        with open(os.path.join(PNT, n), 'w', encoding='utf-8') as f:
            f.write(t)
    print('wrote', len(files), 'files')
    return 0


if __name__ == '__main__':
    sys.exit(main())
