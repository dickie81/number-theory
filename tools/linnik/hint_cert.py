#!/usr/bin/env python3
"""hint_cert.py [TAG] [--check] [--out DIR] [--procs N] [--cache DIR] [--rows I J [STEP]] [--plan-only] | --try TAG a/b
H HF MAXLEN [--lam N]
[--pos] [--blk N] [--skip N] [--energy] [--res | --resF] [--cof] [--lv] [--lazy] [--split J] [--rows I J] [--out DIR]:
the search with the reversal through the largest prime as a plan, the hints that lead the kernel through the plan,
and the Lean files of a theorem (`TAG`: one of `CERTS`; `21500`, the theorem at L = 2150/1000, if none is given).

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
    four bits name; `dser`, `dserF`, `dserKids` write a plan as fields and `pack` as a number. With `Par.pos` a
    box of the sign `+` may be reversed through its largest prime too (`SieveAd.bd_flip_core_pos`: the frozen
    numbers of the narrower slab, the chain's first cells of the sign `−`). With `Par.lam > 0` the planner
    counts the kernel's time: it chooses by the cost plus `lam` millionths of `K` for each second that `SEC`
    predicts (dropped or decomposed; reversed or decomposed; dropped cells next to each other as one cell),
    and with `Par.blk > 1` a new prime's cells are up to `blk` steps of the grid, each kept whole or halved
    by the same count (`pBlock`). With `Par.skip > 0` the planner's own search is shorter: an alternative that
    lost at two cells of a new prime in a row (the decomposition of a box that may be dropped; the reversal of
    a box of the sign `+`; the decomposition of a box of the sign `−` where its reversal won) is not tried at
    the next cells, and the cells that skipped it are solved again when it comes out the other way (`want`,
    `note`, `again`). The kernel reads the same hints in every case;
  * `dSolve`, `dStep`, `dKidsC`, `dPart`, `dFlipTree`, `dFlipCost`, `dAltF`, with `cfgIP`, `cfgJP`, `pickP`,
    `pickC`, `cfgIM`, `cfgJM`, `cfgIF`, `cfgJF`, `parM`, `parF`: `solveD`, `stepD`, `kidsC`, `partD`, `flipTreeD`,
    `flipCostD`, `altFD` and what they read from the hints, definition by definition; every part is run through
    them before it is written. The tests are `flip_cert.py`'s, the ones that are proved sound: over a frozen part
    the kernel evaluates `SieveAd.frozTestsC`, which reads the frozen primes once for a tree and has the same
    value on the boxes of the tree;
  * `plan_all`, `cut`, `add_part`: the cells of the first prime planned one by one (in `--procs` processes), and
    the plan cut into parts of at most `cap` predicted seconds of the kernel: consecutive cells of one prime, a
    heavy cell cut by its own Buchstab step.

It writes `lib/pnt/SieveHint<TAG>.lean` (the exponent and the search), `SieveHint<TAG>P<k>.lean` (the parts, each
by `decide +kernel`) and `Linnik<TAG>.lean` (the route, the bound from the parts, and the theorem). With
`--check`, nothing is written: the files are regenerated in memory and compared with `lib/pnt` (exit 1 on a
difference); it is not part of `check_certificate.py`, for it searches for ten minutes on four cores at
`21500`. With `--cache DIR` the plan of each cell of the first prime is kept in DIR, so that a long plan can be
stopped and taken up again. With `--try`, the search is planned with other parameters (cells of side H, chains'
cells of side HF over the frozen parts, boxes of at most MAXLEN primes reversed; `--pos`, `--lam N`, `--blk N`,
`--skip N`, `--energy` as `Par.pos`, `Par.lam`, `Par.blk`, `Par.skip`, `Par.energy`) and its cost and the plan's
size are printed; with `--out`, its files are written to DIR. PyPy runs it one and a half times as fast as
CPython, with the same output.

Values (12 November 2026): at 2150/1000 with cells of side 0.004 and chains' cells 0.006, boxes of three and five
primes reversed, the search costs 0.94847 K on 3.4·10^7 boxes (2.8·10^7 over frozen parts; nine minutes on four
cores), and its plan has 3.4·10^6 steps. The kernel takes 0.3 ms on an evaluated box (0.5 ms over a frozen part),
1.2 ms on a Buchstab step (1.1 ms), 0.25 ms on a dropped box (0.45 ms) and 3 ms on a reversal's root, and 63
minutes on the 17 files; with the configurations searched by the kernel and the box read sum by sum, as in the
first certificate of this theorem, it took 3.7 ms, 7.6 ms (13 ms), 0.9 ms and 20 ms. At 2140/1000 with cells of
side 0.003, chains' cells 0.006 and boxes of two to six primes of either sign reversed, the search costs 0.96408 K
on 2.7·10^8 boxes with no price on the kernel's time (1.87·10^7 steps), and 0.99055 K on 3.5·10^8 boxes with
`lam = 10` (9.8·10^6 steps, 39 part files; eighty minutes on three cores with PyPy): the certificate `21400`.
Of the boxes of that search, 2% to 9% are under the plan that is kept (four cells of the first prime from
x^0.28 to x^0.50); with `skip = 3`, on every sixth cell of the first prime, the search is 0.55 of its boxes and
the plan costs 0.17% more, on 1% fewer steps (13 November 2026).
At 2135/1000 with the leaves of the comparisons cut in three (`energy`) and the cells of 2140/1000, the search
costs 0.98988 K on 3.7·10^8 boxes with no price on the kernel's time (2.4·10^7 steps, 98 part files, a predicted
6.5 hours of the kernel; three hours on four cores with PyPy): the certificate `21350`. With `lam = 10` its first
prime's cells from x^0.43 to x^0.50 cost 2.1% more, and the planner, which then tries each reversal at the full
limit, takes fifteen to twenty-five minutes on a cell near x^0.40 (13 November 2026).

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
import fill_cert as fc
import res_test as rt  # noqa: E402
import flip_cert as fl  # noqa: E402
from tree_cert import DEN, K, BIG, cdiv, tsub, loSum, hiSum, dropCost  # noqa: E402
from rev_cert import bdK, CAPK  # noqa: E402
from flip_cert import flipT, flipOK, vboxF  # noqa: E402


# the certificates, by tag: the exponent and the parameters of each (`Par`): cells of side at most `h`, chains'
# cells over the frozen parts at most `hF`, boxes of at most `maxlen` primes reversed through their largest prime,
# and no three-prime reversal in the plan
CERTS = {'21500': dict(lnum=2150, lden=1000, h=0.004, hF=0.006, maxlen=6),
         # boxes of the sign `+` reversed too, and each step chosen by its cost plus ten millionths of `K` for
         # each second of the kernel
         '21400': dict(lnum=2140, lden=1000, h=0.003, hF=0.006, maxlen=6, pos=True, lam=10, sec=2),
         # and the leaves of the comparisons cut in three where the paper's conditions fail
         '21350': dict(lnum=2135, lden=1000, h=0.003, hF=0.006, maxlen=6, pos=True, lam=0, sec=2, energy=True),
         # and the resonant window for the main tree's boxes (`SieveAd.chkIR`)
         '21300': dict(lnum=2130, lden=1000, h=0.003, hF=0.006, maxlen=6, pos=True, lam=0, sec=2, energy=True,
                       res=True),
         # and for the boxes of the trees over the frozen parts (`SieveAd.frozResTestsC`)
         '21280': dict(lnum=2128, lden=1000, h=0.003, hF=0.006, maxlen=6, pos=True, lam=0, sec=2, energy=True,
                       res=True, resF=True),
         # and the cofactor in the rest (`SieveAd.chkIRC`, `chkIRF`), the large values of the powers
         # (`SieveResTest.resX`), lazy hints, a box cut where its first cell's top passes the window, and the
         # planner's search shortened (`skip`)
         '21100': dict(lnum=2110, lden=1000, h=0.003, hF=0.006, maxlen=6, pos=True, lam=0, sec=2, energy=True,
                       res=True, resF=True, cof=True, lv=True, lazy=True, split=2, skip=3)}
TAG = '21500'
LNUM, LDEN, H, HF, MAXLEN = (CERTS[TAG][k] for k in ('lnum', 'lden', 'h', 'hF', 'maxlen'))
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
    `('F', sel, cells, bits)` the reversal through the largest prime of a box of the sign `−`, `('P', …)` that
    of a box of the sign `+`, `('S', half, half)` cut in two. `bits` has, for each cut that the strategy proposes
    inside the range, whether the range is cut there: consecutive evaluated cells that one test covers are one
    cell. The search has no three-prime reversal. With `lamK > 0` a step is chosen by its cost plus `lamK` for
    each second that `SEC` predicts of the kernel on its plan: a box that may be dropped is decomposed only if
    that saves more than its time is worth, and a box of the sign `−` is reversed or decomposed by the same
    count. With `pos`, a box of the sign `+` of the main tree may be reversed too."""

    merge = True
    dmerge = DMERGE
    # the price of a second of the kernel, in units of the cost, and whether boxes of the sign `+` are reversed
    lamK = 0
    pos = False
    # with a price on the kernel's time, a new prime's cells are up to `blk` steps of the grid (a power of two)
    # in the main tree, and up to `blkF` over a frozen part
    blk = 1
    blkF = 1
    # with `skip > 0`, an alternative that lost at two cells of a new prime in a row is not tried at the next
    # cells of that prime: after its `k`-th loss in a row, not at the next `2^min(k − 1, skip) − 1` cells, a loss
    # counting only if its search took `skipmin` boxes or more. The alternatives (`skipk`): `d`, a box that may
    # be dropped decomposed; `p`, a box of the sign `+` reversed; `b`, a box of the sign `−` decomposed where its
    # reversal won, the reversal then taken without the comparison; `f`, a box of the sign `−` reversed, is not
    # among them: skipping it costs 4% at cells of the first prime near x^0.40. An alternative is always tried at
    # the last cell of the prime's range, and when it is tried again and comes out the other way, the cells that
    # skipped it are solved again with every alternative (`redo`), backwards until one comes out as it was. The
    # plan is one that the kernel follows all the same; the search is shorter.
    skip = 0
    skipk = 'dpb'
    skipmin = 30
    redo = True
    sib = None

    def want(self, key):
        """Whether the alternative `key` is tried at this cell, by what it did at the cells before."""
        sib = self.sib
        if sib is None or '!' in sib or key not in self.skipk:
            return True
        st = sib.get(key)
        if st is None or st[1] == 0:
            return True
        if '$' in sib:
            st[1] = 0
            return True
        st[1] -= 1
        st[3] += 1
        return False

    def note(self, key, won, used):
        """The alternative `key` was tried at this cell, on `used` boxes, and was kept (`won`) or not."""
        sib = self.sib
        if sib is None or '!' in sib:
            return
        st = sib.setdefault(key, [0, 0, None, 0])
        if st[3] and st[2] is not None and won != st[2] and self.redo:
            sib['<'] = max(sib.get('<', 0), st[3])
        st[2], st[3] = won, 0
        if won:
            st[0] = st[1] = 0
        elif used >= self.skipmin:
            st[0] = min(st[0] + 1, self.skip + 1)
            st[1] = (1 << (st[0] - 1)) - 1

    def again(self, rec, bl, par, cells, tot, lim, grp):
        """The cells before the last, which skipped an alternative that has now come out the other way, solved
        again with every alternative tried, backwards until one comes out as it was. The new total."""
        m, j = grp.pop('<'), len(cells) - 2
        grp['!'] = True
        try:
            while m > 0 and j >= 0:
                s, c, n0, c0 = cells[j]
                l1 = lim - (tot - c0)
                c1, n1 = rec([(s, c)] + bl, par, l1)
                if n1 is None or l1 <= c1 or (c1 == c0 and n1[0] == n0[0]):
                    break
                cells[j] = (s, c, n1, c1)
                tot += c1 - c0
                self.stat['again'] = self.stat.get('again', 0) + 1
                m, j = m - 1, j - 1
        finally:
            del grp['!']
        return tot

    # the proposal of the strategy that four bits name: its floor is the one that `SieveAd.cfgJP` computes
    def tryJ2(self, bl, lomin, ls, hs, c, bit):
        if not self.restOK(c):
            return None
        u, v = self.uOfF(c[0]), self.vOfF(c[1])
        f = min(lomin, tsub(v, u + 1))
        if not (0 < f and hs + tsub(u, tsub(ls, c[0])) <= self.t5J()):
            return None
        b = self.bestSub(v, bit, bl, 1, 0, 0, 0, tsub(ls, c[0]), (0, 0))
        sp = self.leavesOfJ2(bl, hs, tsub(u, b[0]))
        return None if sp is None else (f, (1, b[1], bit, sp[0], sp[1]))

    def guideJ(self, bl, lomin, sel):
        ls, hs = loSum(bl), hiSum(bl)
        if self.t5J() < hs:
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

    def pBlock(self, rec, bl, par, ends, i, j, lim):
        """The range from `ends[i]` to `ends[j]` of the new prime as one cell, or as its two halves (cut at a
        proposed cut, each half again one cell or its halves), whichever is less by the cost and the kernel's
        time together. The cost and the cells `(lo, hi, plan, cost)`."""
        fz, lam = self.frz is not None, self.lamK
        c0, n0 = rec([(ends[i], ends[j])] + bl, par, lim)
        ok0 = n0 is not None and c0 < lim
        one = [(ends[i], ends[j], n0, c0)]
        if j - i == 1:
            return c0, (one if ok0 else None)
        t0, l2 = 0.0, lim
        if ok0:
            # one cell that costs nothing is kept (its halves cost the kernel less once in a hundred); one that
            # is dropped can be bettered only by more than the time of one more step is worth
            if c0 == 0 or (n0[0] == 'D' and c0 <= lam * SEC[('E', fz)]):
                return c0, one
            t0 = secs(n0, fz)
            l2 = min(lim, c0 + int(lam * t0))
        m = (i + j) // 2
        cl, left = self.pBlock(rec, bl, par, ends, i, m, l2)
        if left is not None:
            cr, right = self.pBlock(rec, bl, par, ends, m, j, l2 - cl)
            if right is not None:
                cf, tf = cl + cr, sum(secs(x[2], fz) for x in left + right)
                if not ok0 or cf + lam * tf < c0 + lam * t0:
                    return cf, left + right
        return (c0, one) if ok0 else (max(lim, c0), None)

    def pKids(self, rec, top, bl, par, cs, a, lim, drp=None):
        if not self.skip:
            return self.pKids1(rec, top, bl, par, cs, a, lim, drp)
        # the cells of this prime remember what lost at the cells before them
        sib0, mine = self.sib, {}

        def rec2(b, p, l):
            self.sib = mine
            return rec(b, p, l)
        try:
            return self.pKids1(rec2, top, bl, par, cs, a, lim, drp, mine)
        finally:
            self.sib = sib0

    def pKids1(self, rec, top, bl, par, cs, a, lim, drp=None, grp=None):
        cells, tot, s = [], 0, a
        if self.lamK and (self.blk if self.frz is None else self.blkF) > 1:
            # the proposed cuts are a fine grid: cells of up to `blk` of its steps, halved where that pays
            blk = self.blk if self.frz is None else self.blkF
            ends = [a]
            for c in cs:
                if ends[-1] < c < top:
                    ends.append(c)
            ends.append(top)
            for i in range(0, len(ends) - 1, blk):
                c1, got = self.pBlock(rec, bl, par, ends, i, min(i + blk, len(ends) - 1), lim - tot)
                tot += c1
                if got is None or lim <= tot:
                    return max(tot, lim), None
                cells.extend(got)
        else:
            for c in cs:
                if s < c < top:
                    c1, n1 = rec([(s, c)] + bl, par, lim - tot)
                    tot += c1
                    if lim <= tot:
                        return tot, None
                    cells.append((s, c, n1, c1))
                    s = c
                    if grp and '<' in grp:
                        tot = self.again(rec, bl, par, cells, tot, lim, grp)
            if grp is not None:
                grp['$'] = True
            c1, n1 = rec([(s, top)] + bl, par, lim - tot)
            tot += c1
            if lim <= tot:
                return tot, None
            cells.append((s, top, n1, c1))
            if grp and '<' in grp:
                tot = self.again(rec, bl, par, cells, tot, lim, grp)
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
                    if u is None or (self.dmerge[1] * u > self.dmerge[0] * (tsum + cells[j + 1][3])
                                     and u - (tsum + cells[j + 1][3])
                                     > self.lamK * SEC[('D', self.frz is not None)]):
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

    def frzOf(self, ctx, beta, pos):
        """What the tests of the tree over the frozen part of `beta` and the slab of `ctx` read: the ends of the
        slab, one unit narrower at each end for the reversal of a box of the sign `+`, and the room `Kb`."""
        return (tsub(DEN, ctx[1]) + pos, tsub(DEN, ctx[0]) + 1 - pos, 12 + DEN // beta[0][0], beta)

    def pFlip(self, bl, lim, pos=False):
        """`flipCostD` with the plan of its tree: the box reversed through its largest prime. For a box of the sign
        `+` (`pos`) the tree's cost weighs on the share of the box alone, the frozen numbers are those of the
        narrower slab, and the chain's first cells have the sign `−`."""
        ctx, beta = bl[-1], bl[:-1]
        self.W['flips'] += 1
        E = ((ctx[1] + 1) * dropCost(beta + [(tsub(ctx[1], 1), ctx[1] + 1)])
             + (ctx[0] + 1) * dropCost(beta + [(tsub(ctx[0], 1), ctx[0] + 1)]))
        A, B = ctx[1] * dropCost(bl) + (0 if pos else E), bdK(ctx, flipT(ctx)) * E
        if A == 0:
            return lim, None
        cl = min(CAPK, tsub(tsub(lim, 1) * (DEN * K), B) // A + 1)
        c, t = beta[0], flipT(ctx)
        self.frz, self.fctx = self.frzOf(ctx, beta, pos), ctx
        w0 = (self.W['calls'], self.W['dfs'])
        try:
            S = self.stratF(ctx, beta)
            fj = self.floorOf(beta, min(c[0], t))
            if fj is None:
                self.stat['posroot' if pos else 'fliproot'] += 1
                return lim, None
            sel, f = fj
            O = self.opsK(ctx, len(beta))
            cc, ns = self.pKids(lambda b, p, l: self.pSolve(O, S, self.fuel, b, p, l), t, beta, not pos,
                                S.cuts(beta, f), f, cl, O.drp)
        finally:
            self.frz = None
            self.W['fcalls'] += self.W['calls'] - w0[0]
            self.W['fdfs'] += self.W['dfs'] - w0[1]
        if cl <= cc:
            self.stat['poscap' if pos else 'flipcap'] += 1
            return lim, None
        return cdiv(cc * A + B, DEN * K), ('P' if pos else 'F', sel) + ns

    # the resonant window (`SieveAd.chkIR`): a rest of at least two of the box's primes, in the main tree
    res = False
    res_frozen = False   # the window over the frozen parts too (`SieveAd.frozResTestsC`), the rest among the chain's
    # and the frozen primes; for measurement, 'chain': among the chain's alone
    res_cof = False      # a cofactor that is one prime (shorter than the square of the box's least prime) may be in
    # the rest, its cell from the box's cells: the main tree's (`SieveAd.chkIRC`) and, with `res_frozen`, the chain's
    # in the trees over the frozen parts, its cell from the slab and the chain's cells too (`SieveAd.chkIRF`); for
    # measurement only (no hints), 'main': the main tree's alone, and 'mom': that and any cofactor but 1, counted by
    # its moments alone (`res_test.mkTmM`)
    res_lv = False       # the test with the large values of the powers too (`SieveResTest.resT2`)
    res_lazy = False     # a rest that the strict float filter passes is taken as passing, and its hint is found
    # when the plan is written (`resolve`): `('R', mask, -1, key)` until then
    resmemo = None

    def resHint(self, bl, probe=False):
        """`(mask, k, h)` for a rest of the box `bl` that the kernel's test passes with its hint, or `None`: the
        rests of at least two primes, in the order of their masks. The box is the main tree's, or with `res_frozen`
        a tree's over a frozen part, `ch ++ β`. With `probe`, the strict float filter's word alone, and nothing
        kept."""
        if not self.res:
            return None
        if self.frz is not None and not self.res_frozen:
            return None
        # a box of a tree over a frozen part is the chain's cells followed by the frozen primes' (`ch ++ β`)
        if len(bl) > 13:
            return None
        if any(not (1 <= c[0] <= c[1] <= DEN) for c in bl):
            return None
        if self.resmemo is None:
            self.resmemo = {}
        n, ln, ld = len(bl), self.T.Ln, self.T.Ld
        # a rest whose exponents sum to less than 1 + 2/25000 fails (`res_test.quick`): in units of the cells,
        # Σ(c − 1) at least `need`
        need = (DEN * ld * 25002 + ln * 25000 - 1) // (ln * 25000)
        nch = n - len(self.frz[3]) if self.frz is not None and self.res_frozen == 'chain' else n
        cofm = False
        if self.res_cof in (True, 'main', 'mom') and self.frz is None:
            # the cofactor `m = n/∏p` with `n ∈ (x, 2x]`: `m ∈ (x^{(DEN − Σhi)/DEN}, x^{(DEN − Σlo + 1)/DEN})`, one
            # prime at least the least prime `x^{lo₀/DEN}` when its upper end is at most twice `lo₀`
            # (the kernel's cell and conditions, `SieveAd.chkIRC`)
            slo, shi = sum(c[0] for c in bl), sum(c[1] for c in bl)
            one = shi + 2 <= DEN and DEN + 1 <= slo + 2 * bl[0][0]
            cofm = self.res_cof == 'mom' and shi + 1 < DEN and not one
            if one or cofm:
                bl = list(bl) + [(max(tsub(tsub(DEN, shi), 1), bl[0][0]), tsub(DEN, slo) + 1)]
                n = nch = n + 1
        elif self.res_cof is True and self.frz is not None and self.res_frozen is True and n > len(self.frz[3]):
            # in a tree over a frozen part, the chain's cofactor `M` with `n = R·∏ch·M`, `R` in the slab
            # `(x^{e₁/DEN}, x^{e₂/DEN}]`: one prime at least the chain's least prime when its upper end is at most
            # twice that prime's lower end (the kernel's cell and conditions, `SieveAd.chkIRF`)
            e1, e2, ch = self.frz[0], self.frz[1], bl[:n - len(self.frz[3])]
            slo, shi = sum(c[0] for c in ch), sum(c[1] for c in ch)
            if e2 + shi + 2 <= DEN and DEN + 1 <= e1 + slo + 2 * ch[0][0]:
                bl = list(bl) + [(max(tsub(tsub(tsub(DEN, e2), shi), 1), ch[0][0]), tsub(tsub(DEN, e1), slo) + 1)]
                n = nch = n + 1
        if nch < 2:
            return None
        for mask in range(3, 1 << nch):
            if mask & (mask - 1) == 0:
                continue
            if sum(bl[p][0] - 1 for p in range(n) if mask >> p & 1) < need:
                continue
            cs = tuple(bl[p][0] for p in range(n) if mask >> p & 1)
            hs = sum(bl[p][1] for p in range(n) if mask >> p & 1)
            mom = 1 << (len(cs) - 1) if cofm and mask >> (n - 1) & 1 else 0
            if not rt.quick(ln, ld, list(cs), hs, mom=mom, lv=self.res_lv):
                continue
            key = (cs, hs, mom)
            r = self.resmemo.get(key, 0)
            if r == 0 and probe:
                if rt.quick(ln, ld, list(cs), hs, fuel=12, slack=-1e-7, mom=mom, lv=self.res_lv, maxleaf=15):
                    return (mask, -1, key)
                continue
            if r == 0:
                if self.res_lazy and rt.quick(ln, ld, list(cs), hs, fuel=12, slack=-1e-7, mom=mom, lv=self.res_lv,
                                              maxleaf=15):
                    r = (-1, key)
                else:
                    r = rt.hint(ln, ld, list(cs), hs, mom, lv=self.res_lv, fast=self.res_lazy)
                self.resmemo[key] = r
            if r is not None:
                if not probe:
                    self.stat['res'] = self.stat.get('res', 0) + 1
                return (mask,) + r
        return None

    # a box that the plan does not evaluate is cut in two (the kernel's step `S`) when the top `1/2^j` of its first
    # cell, for some `j ≤ res_split` that the cuts can reach, passes the window's float filter for some rest, and the
    # halves cost less
    res_split = 0

    def nearRes(self, S, bl):
        """The top `1/2^j` of the box's first cell passes the window's float filter for some rest, for some
        `j ≤ res_split` that cuts at the midpoints, each of a cell wider than `S.wmin`, reach."""
        x = bl[0]
        lo, w = x[0], tsub(x[1], x[0])
        for _ in range(self.res_split):
            if not (S.wmin < w and lo < (lo + x[1]) // 2 < x[1]):
                return False
            lo = (lo + x[1]) // 2
            w = tsub(x[1], lo)
            if self.resHint([(lo, x[1])] + bl[1:], True) is not None:
                return True
        return False

    def pSolve(self, O, S, n, bl, par, lim):
        c, node = self.pSolve1(O, S, n, bl, par, lim)
        if not self.res_split or node is None or c == 0 or n <= 1 or not bl or node[0] in ('E', 'R', 'V', 'S'):
            return c, node
        x = bl[0]
        if not self.nearRes(S, bl):
            return c, node
        self.stat['splittry'] = self.stat.get('splittry', 0) + 1
        cs, ns = self.pSplit(O, S, n - 1, x, bl, par, c)
        if ns is not None and cs < c:
            self.stat['splitwin'] = self.stat.get('splitwin', 0) + 1
            return cs, ns
        return c, node

    def pSolve1(self, O, S, n, bl, par, lim):
        self.minfuel = min(self.minfuel, n)
        if n == 0 or not bl or not O.grd(bl):
            return lim, None
        self.W['calls'] += 1
        if O.van(bl):
            return 0, ('V',)
        if self.anyI(bl):
            return 0, ('E',)
        rh = self.resHint(bl)
        if rh is not None:
            return 0, ('R',) + rh
        x, fz, lam = bl[0], self.frz is not None, self.lamK
        skip, sib = self.skip, self.sib
        dc = O.drp(bl, par)
        if dc is not None:
            # a box that may be dropped: dropped, or decomposed if that costs less by more than the kernel's
            # time on the decomposition is worth
            if skip and dc <= lim and not self.want('d'):
                r, how = dc, ('D',)
            else:
                w0 = self.W['calls']
                bc, nb = self.pBuch(O, S, n - 1, x, bl, par, dc if dc <= lim else lim)
                if dc <= bc:
                    r, how = dc, ('D',)
                elif lam and nb is not None and dc < lim and dc - bc < lam * (secs(nb, fz) - SEC[('D', fz)]):
                    r, how = dc, ('D',)
                else:
                    r, how = bc, nb
                if skip and dc <= lim:
                    self.sib = sib
                    self.note('d', how is not None and how[0] != 'D', self.W['calls'] - w0)
            if (self.pos and O is self.OR and par and 0 < r and how is not None and flipOK(self.maxlen, bl)
                    and (not skip or self.want('p'))):
                # a box of the sign `+` of the main tree, reversed through its largest prime
                self.stat['postry'] += 1
                w0 = self.W['calls']
                c, nf = self.pFlip(bl, r if r <= lim else lim, True)
                won = nf is not None and c < r and (not lam or c + lam * secs(nf) < r + lam * secs(how, fz))
                if skip:
                    self.sib = sib
                    self.note('p', won, self.W['calls'] - w0)
                if won:
                    self.stat['poswin'] += 1
                    return c, nf
            return r, how
        rev = O is self.OR and not par and self.flip and flipOK(self.maxlen, bl)
        if skip and rev and not self.want('b'):
            # the reversal won at the cells before: it is taken, if it is below the limit, without the
            # decomposition that it would be compared with
            self.stat['fliptry'] += 1
            w0 = self.W['calls']
            c, nf = self.pFlip(bl, lim)
            if nf is not None:
                self.stat['flipwin'] += 1
                return c, nf
            self.sib = sib
            self.note('f', False, self.W['calls'] - w0)
            self.note('b', True, 0)
            rev = False
        w0 = self.W['calls']
        bc, nb = self.pBuch(O, S, n - 1, x, bl, par, lim)
        w1 = self.W['calls']
        l2 = bc if bc <= lim else lim
        if O is self.OR and not par:
            r, how = l2, None
            if rev and (not skip or nb is None or self.want('f')):
                self.stat['fliptry'] += 1
                if lam and nb is not None:
                    # reversed or decomposed, by the cost and the kernel's time together
                    c, nf = self.pFlip(bl, lim)
                    won = nf is not None and c + lam * secs(nf) < bc + lam * secs(nb)
                    if skip:
                        self.sib = sib
                        self.note('f', won, self.W['calls'] - w1)
                        self.note('b', not won, w1 - w0)
                    if won:
                        self.stat['flipwin'] += 1
                        return c, nf
                else:
                    c, nf = self.pFlip(bl, r)
                    if skip and nb is not None:
                        self.sib = sib
                        self.note('f', c < r, self.W['calls'] - w1)
                        self.note('b', not c < r, w1 - w0)
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

    def cfgIPR(self, pw, h):
        """`SieveAd.cfgIPR`: `0` and `cfgIP`'s code, or `1`, the rest, four bits `k` and the `k` intervals' ends,
        `rt.EB` bits each."""
        if h & 1 == 0:
            return self.cfgIP(pw, h >> 1)
        h1 = h >> 1
        k, h2 = (h1 // pw) % 16, (h1 // pw) // 16
        if k == 0:
            # the test with the large values' term: its number of intervals in the next four bits
            k2, h3 = h2 % 16, h2 // 16
            nb = rt.EB * k2
            return (3, 0, h1 % pw, 16 * (k2 + 16 * (h3 % (1 << nb))), False), h3 >> nb
        nb = rt.EB * k
        return (3, 0, h1 % pw, k + 16 * (h2 % (1 << nb)), False), h2 >> nb

    def cfgIMR(self, bl, h):
        return self.cfgIPR(2 ** len(bl), h)

    def chkIR(self, bl, sr, k, h):
        """`SieveAd.chkIR`."""
        if len(bl) > 13 or any(not (1 <= c[0] <= c[1] <= DEN) for c in bl):
            return False
        cs = [bl[p][0] for p in range(len(bl)) if sr >> p & 1]
        hs = sum(bl[p][1] for p in range(len(bl)) if sr >> p & 1)
        return bool(cs) and rt.resX(self.T.Ln, self.T.Ld, cs, hs, k, h)

    def chkIRC(self, bl, sr, k, h):
        """`SieveAd.chkIRC`: `chkIR`, with the box's cofactor in the rest at the bit after its cells: one prime when
        the box's upper ends sum to at most `DEN − 2` and its lower ends with twice its least prime's reach
        `DEN + 1`, in the cell `(max(DEN − Σhi − 1, lo₀), DEN − Σlo + 1)`."""
        n = len(bl)
        if n > 13 or any(not (1 <= c[0] <= c[1] <= DEN) for c in bl):
            return False
        cs = [bl[p][0] for p in range(n) if sr >> p & 1]
        hs = sum(bl[p][1] for p in range(n) if sr >> p & 1)
        if not cs:
            return False
        if sr >> n & 1:
            slo, shi, lk = loSum(bl), hiSum(bl), bl[0][0]
            if not (shi + 2 <= DEN and DEN + 1 <= slo + 2 * lk):
                return False
            cs, hs = cs + [max(tsub(tsub(DEN, shi), 1), lk)], hs + tsub(DEN, slo) + 1
        return rt.resX(self.T.Ln, self.T.Ld, cs, hs, k, h)

    def chkIRF(self, e1, e2, beta, bl, sr, k, h):
        """`SieveAd.chkIRF`: `chkIR` on the box `ch ++ β` of a tree over a frozen part, with the chain's cofactor in
        the rest at the bit after the box's cells: one prime when the chain's upper ends (the box's less `β`'s) with
        `e₂` sum to at most `DEN − 2` and its lower ends with `e₁` and twice its least prime's reach `DEN + 1`, in the
        cell `(max(DEN − e₂ − Σhi − 1, lo₀), DEN − e₁ − Σlo + 1)`."""
        n = len(bl)
        if n > 13 or any(not (1 <= c[0] <= c[1] <= DEN) for c in bl):
            return False
        cs = [bl[p][0] for p in range(n) if sr >> p & 1]
        hs = sum(bl[p][1] for p in range(n) if sr >> p & 1)
        if not cs:
            return False
        if sr >> n & 1:
            slo, shi = tsub(loSum(bl), loSum(beta)), tsub(hiSum(bl), hiSum(beta))
            lk = bl[0][0] if bl else 0
            if not (e2 + shi + 2 <= DEN and DEN + 1 <= e1 + slo + 2 * lk):
                return False
            cs = cs + [max(tsub(tsub(tsub(DEN, e2), shi), 1), lk)]
            hs += tsub(tsub(DEN, e1), slo) + 1
        return rt.resX(self.T.Ln, self.T.Ld, cs, hs, k, h)

    def cfgIMRC(self, bl, h):
        """`SieveAd.cfgIMRC`: `cfgIPR` with a set of one more bit than the box has cells, the cofactor's."""
        return self.cfgIPR(2 ** (len(bl) + 1), h)

    def cfgJM(self, bl, h):
        sel = h & 15
        _, lm, lo, hi, pw = self.pickP(bl, 2 ** (sel // 2))
        return self.cfgJP(sel, lm, lo, hi, pw, h >> 4)

    def cfgIF(self, bl, h):
        return self.cfgIP(2 ** (len(bl) + 1), h)

    def cfgIFR(self, bl, h):
        """`SieveAd.cfgIFR`: `cfgIPR` with a set of as many bits as the box has cells and one more."""
        return self.cfgIPR(2 ** (len(bl) + 1), h)

    def pickC(self, bl, j, m):
        """`pickP` over the first `j` cells."""
        lm, lo, hi = DEN, 0, 0
        for x in bl[:j]:
            lm = min(lm, x[0])
            lo += (m & 1) * x[0]
            hi += (m & 1) * x[1]
            m >>= 1
        return m, lm, lo, hi

    def cfgJF(self, Kb, cl, ch, beta, nb, lomb, bl, h):
        """The rest's cell among the chain's cells, read in a pass over the chain, the `nb` frozen primes `beta`,
        whose least lower end is `lomb`, and the cofactor."""
        sel, n = h & 15, len(bl)
        m, lm, lo, hi = self.pickC(bl, tsub(n, nb), 2 ** (sel // 2))
        cofb = (m >> nb) & 1
        return self.cfgJP(sel, max(1, tsub(min(lm, lomb), Kb)),
                          max(1, tsub(lo + tc.mSum(0, beta, m) + cofb * cl, Kb)),
                          hi + tc.mSum(1, beta, m) + cofb * ch + Kb, 2 ** (n + 1), h >> 4)

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

    def parF(self, ctx, nb, bl, top):
        """Those of a tree over a frozen part of `nb` frozen primes, from the sums of the chain's cells."""
        nch = tsub(len(bl), nb)
        return (self.hF if nch < 2 else 2 * self.hF,
                min(top, tsub(ctx[1] + 1, loSum(bl[:nch])) // 2 + 2), 0,
                tsub(tsub(ctx[0], 1), hiSum(bl[:nch])))

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
        if (self.res if self.frz is None else self.res_frozen) and cfg[0] == 3:
            if self.frz is not None:
                return self.chkIRF(self.frz[0], self.frz[1], self.frz[3], bl, cfg[2], cfg[3] & 15, cfg[3] >> 4)
            chk = self.chkIRC if self.res_cof is True else self.chkIR
            return chk(bl, cfg[2], cfg[3] & 15, cfg[3] >> 4)
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
    def frozen(self, ctx, beta, pos):
        """The tree over the frozen part of `β` and the slab of `ctx`, for the reversal of a box of the sign `+`
        (`pos`) or `−`: its decoders, its cells and its search."""
        lsb, hsb, nb, lomb = loSum(beta), hiSum(beta), len(beta), min([DEN] + [c[0] for c in beta])
        e1, e2, Kb, _ = self.frzOf(ctx, beta, pos)
        cl, ch = max(1, tsub(e1, hsb)), tsub(e2, lsb)
        O = self.opsK(ctx, nb)

        def dJ(b, hh):
            return self.cfgJF(Kb, cl, ch, beta, nb, lomb, b, hh)

        def kd(rec, top, b, p, ff, l, hh):
            return self.dKidsC(rec, top, b, p, self.parF(ctx, nb, b, top), ff, l, hh)

        def rec(b, p, l, hh):
            return self.dSolve(O, self.cfgIFR if self.res_frozen else self.cfgIF, dJ, kd,
                               lambda b2, p2, l2, h2: (l2, h2), self.fuel, b, p, l, hh)
        return Kb, O, dJ, kd, rec

    def dFlipTree(self, ctx, beta, pos, lim, h):
        c, t = beta[0], flipT(ctx)
        Kb, O, dJ, kd, rec = self.frozen(ctx, beta, pos)
        self.frz, self.fctx = self.frzOf(ctx, beta, pos), ctx
        try:
            (f, cfg), h2 = dJ(beta, h)
            if not (1 <= f <= min(c[0], t) and self.okJm(beta, f, cfg)):
                return lim, h2
            return kd(rec, t, beta, not pos, f, lim, h2)
        finally:
            self.frz = None

    def dFlipCost(self, bl, pos, lim, h):
        if not flipOK(self.maxlen, bl):
            return lim, h
        ctx, beta = bl[-1], bl[:-1]
        E = ((ctx[1] + 1) * dropCost(beta + [(tsub(ctx[1], 1), ctx[1] + 1)])
             + (ctx[0] + 1) * dropCost(beta + [(tsub(ctx[0], 1), ctx[0] + 1)]))
        r = self.dFlipTree(ctx, beta, pos, CAPK, h)
        if CAPK <= r[0]:
            return lim, r[1]
        return cdiv(r[0] * (ctx[1] * dropCost(bl) + (0 if pos else E)) + bdK(ctx, flipT(ctx)) * E, DEN * K), r[1]

    def dAltF(self, bl, par, l, h):
        return self.dFlipCost(bl, par, l, h)

    def dCheck(self, bl, par, lim, h):
        """`solveD opsMP fillTestsF cfgIM cfgJM (kidsM κ hI) (altFD κ hF fuel maxlen) fuel bl par lim h`."""
        O = rc.Ops(lambda b: True, tc.vanishOK, tc.dropC, lambda b, p, l: l)
        dI = self.cfgIMRC if self.res_cof is True else self.cfgIMR if self.res else self.cfgIM
        return self.dSolve(O, dI, self.cfgJM, self.kdM, self.dAltF, self.fuel, bl, par, lim, h)

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

    def evalFields(self, cfg, w, res=False):
        j = cfg[2].bit_length() - 1
        return [(0, 1)] + ([(0, 1)] if res else []) + ([(0, 1)] if j == 0 else [(1, 1), (j, 3)]) + [(cfg[1], w)]

    def resFields(self, node, w):
        """A resonant leaf `('R', mask, k, h)`: the evaluation's bit, `1`, the rest, four bits `k`, the `k` ends."""
        mask, k, h = node[1:]
        if k == 0:
            # the test with the large values' term: `0`, then its number of intervals and their ends
            k2, h2 = h % 16, h // 16
            assert 0 < k2 < 16 and mask < 1 << w and h2 < 1 << (rt.EB * k2)
            return [(0, 1), (1, 1), (mask, w), (0, 4), (k2, 4), (h2, rt.EB * k2)]
        assert 0 < k < 16 and mask < 1 << w and h < 1 << (rt.EB * k)
        return [(0, 1), (1, 1), (mask, w), (k, 4), (h, rt.EB * k)]

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
            out.extend(self.evalFields(cf[0], w, bool(self.res_frozen)))
        elif kind == 'R':
            assert self.res_frozen and self.chkIRF(self.frz[0], self.frz[1], beta, bl, node[1], node[2], node[3])
            out.extend(self.resFields(node, w))
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
            self.dserKids(self.parF(ctx, len(beta), bl, top), f, cells, node[2], bl,
                          not par, top, out, lambda k, b, p, o: self.dserF(ctx, beta, k, b, p, o))
        else:
            raise ValueError(kind)

    def dser(self, node, bl, par, out):
        """A node of the main tree."""
        kind = node[0]
        w = len(bl)
        wI = w + (1 if self.res_cof is True else 0)    # an evaluation's set, with the cofactor's bit (`cfgIMRC`)
        if kind == 'V':
            out.append((31, 6))
        elif kind == 'E':
            cf = self.propI2(bl, loSum(bl))
            assert cf and self.T.okI(bl, cf[0])
            out.extend(self.evalFields(cf[0], wI, self.res))
        elif kind == 'R':
            assert (self.chkIRC if self.res_cof is True else self.chkIR)(bl, node[1], node[2], node[3])
            out.extend(self.resFields(node, wI))
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
        elif kind in ('F', 'P'):
            assert par == (kind == 'P')
            ctx, beta = bl[-1], bl[:-1]
            t = flipT(ctx)
            self.frz, self.fctx = self.frzOf(ctx, beta, par), ctx
            try:
                f, cfg = self.guide(beta, node[1])
                out.append((7, 4))
                out.extend(self.cfgFields(beta, node[1], cfg, len(beta) + 1))
                cells = self.kidCells(self.stratF(ctx, beta).cuts(beta, f), f, t, node[3])
                self.dserKids(self.parF(ctx, len(beta), beta, t), f, cells, node[2],
                              beta, not par, t, out, lambda k, b, p, o: self.dserF(ctx, beta, k, b, p, o))
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
    if node[0] in ('B', 'F', 'P'):
        for k in node[2]:
            count(k, cnt, frozen or node[0] != 'B')
    elif node[0] == 'S':
        count(node[1], cnt, frozen)
        count(node[2], cnt, frozen)


# the certificate

class Par:
    """The exponent and the parameters of a certificate."""

    def __init__(self, tag, lnum, lden, h=0.005, depth=6, kappa=10, depthR=3, hR=0.012, hQ=0.02, hF=0.006,
                 depthF=3, maxlen=6, cap=3.5, pmax=100, fcap=240.0, levels=5, rev=False, lam=0, pos=False, sec=1,
                 blk=1, blkF=None, skip=0, skipmin=30, energy=False, res=False, resF=False, cof=False, lv=False,
                 lazy=False, split=0):
        """`lam`: the planner's price of a second of the kernel, in millionths of `K`; `pos`: boxes of the sign
        `+` may be reversed; `sec`: the table of the kernel's seconds a step (`SEC1` or `SEC2`); `blk`: with
        `lam > 0`, a new prime's cells are up to `blk` steps of the grid of side `h` in the main tree, and up to
        `blkF` (`blk` if not given) steps of the grid of side `hF` over a frozen part; `skip`: the planner does
        not try again, at the next cells of a prime, an alternative that lost at two cells in a row (at most
        `2^skip − 1` cells are skipped), a loss counting only if its search took `skipmin` boxes or more; `energy`:
        the planner may cut in three the leaves of the comparisons, in the main tree and over the frozen parts, as
        the kernel's tests allow (`SieveAd.leavesE`); `res`: the resonant window's leaves in the main tree
        (`SieveAd.resTestsF`), and with `resF` in the trees over the frozen parts too (`SieveAd.frozResTestsC`); `cof`:
        the boxes with their cofactor in the rest when it is one prime (`SieveAd.resTestsFC`, and with `resF`
        `SieveAd.chkIRF`); `lv`: the window's test with the large values of the powers too (`SieveResTest.resX`);
        `lazy`: the planner takes the strict float filter's word that a rest passes, and finds the hints of the plan
        it keeps when the plan is written (`resolve`); `split`: a box that the plan does not evaluate is cut in two
        where the top `1/2^j` of its first cell, `j ≤ split`, passes the window's float filter
        (`Planner.res_split`)."""
        assert not rev, 'the search led by hints has no three-prime reversal'
        self.tag, self.lnum, self.lden, self.rev = tag, lnum, lden, rev
        self.lam, self.pos, self.sec, self.blk, self.blkF = lam, pos, sec, blk, blk if blkF is None else blkF
        self.skip, self.skipmin, self.energy, self.res, self.resF, self.cof = skip, skipmin, energy, res, resF, cof
        self.lv, self.lazy, self.split = lv, lazy, split
        assert res or not (resF or cof or split), 'the window over the frozen parts, the cofactor and the cuts come ' \
            'with the main tree\'s'
        self.h, self.hI, self.depth, self.kappa = h, round(h * DEN), depth, kappa
        self.depthR, self.hR, self.hQ = depthR, round(hR * DEN), round(hQ * DEN)
        self.hF, self.depthF, self.maxlen = round(hF * DEN), depthF, maxlen
        self.hRf, self.hQf, self.hFf = hR, hQ, hF
        self.cap, self.pmax, self.fcap, self.levels = cap, pmax, fcap, levels

    def planner(self):
        """The planner of this certificate; the table of the kernel's seconds becomes this certificate's."""
        global SEC
        SEC = {1: SEC1, 2: SEC2}[self.sec]
        P = Planner(fc.TestsF(self.lnum, self.lden), self.hI, self.depth, fc.WMIN, self.kappa, self.hR,
                    self.depthR, self.hQ, fc.FUEL, self.hF, self.depthF, self.maxlen, rev=self.rev)
        P.lamK, P.pos, P.blk, P.blkF = self.lam * K // 10 ** 6, self.pos, self.blk, self.blkF
        P.skip, P.skipmin = self.skip, self.skipmin
        P.T.energy = self.energy
        P.res = self.res
        P.res_frozen = self.resF
        P.res_cof = self.cof
        P.res_lv, P.res_lazy, P.res_split = self.lv, self.lazy, self.split
        P.stat.update(postry=0, poswin=0, posroot=0, poscap=0)
        return P


# the kernel's seconds a step, by kind and whether over a frozen part (12 November 2026: timed in the kernel on
# 300 boxes of each kind of the plan at 2150/1000, least of three runs, times 1.3, which is what twenty-four whole
# parts take over the sum of their steps). `SEC1` is the table that cut the certificate at 2150/1000 into its
# parts. `SEC2` has the steps over a frozen part as they are since the tests read the frozen primes once for a
# tree, timed a tree at a time (0.50 ms an evaluated box, 1.07 ms a Buchstab step, 0.45 ms a dropped box, times
# 1.3), and the reversal of a box of the sign `+`, which the kernel does as that of a box of the sign `−`.
SEC1 = {('E', False): 4.0e-4, ('E', True): 1.05e-3, ('V', False): 1.3e-4, ('V', True): 1.3e-4,
        ('B', False): 1.6e-3, ('B', True): 2.7e-3, ('D', False): 3.0e-4, ('D', True): 4.7e-4, ('F', False): 3.9e-3,
        ('S', False): 2.6e-4, ('S', True): 2.6e-4}
SEC2 = dict(SEC1)
SEC2.update({('E', True): 6.5e-4, ('B', True): 1.4e-3, ('D', True): 5.9e-4, ('P', False): 3.9e-3})
for _t in (SEC1, SEC2):
    _t[('R', False)] = _t[('E', False)] + 1.6e-4
    _t[('R', True)] = _t[('E', True)] + 1.6e-4
# the resonant window's leaves, timed in part files (14 November 2026; one row at 2135/1000 with the window in both
# trees, the cofactor and the large values, unloaded): about 64 ms in the main tree and 8 ms over a frozen part, the
# test of the rest by `resX` dominating; the step of the window's leaf in SEC1 above is far too low
SEC2.update({('R', False): 6.4e-2, ('R', True): 8.0e-3})
SEC = SEC1


def secs(node, frozen=False):
    """The kernel's predicted seconds on the plan `node`."""
    k = node[0]
    t = SEC[(k, frozen)]
    if k in ('B', 'F', 'P'):
        fz = frozen or k != 'B'
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


def resolve(P, node, bad, seen):
    """The plan `node` with the hints of its resonant leaves found (`Par.lazy`): a leaf `('R', mask, -1, key)`
    becomes `('R', mask, k, h)`; the keys for which no hint is found are added to `bad`."""
    got = seen.get(id(node))
    if got is not None:
        return got[1]
    k = node[0]
    if k == 'R' and node[2] == -1:
        key = node[3]
        r = P.resmemo.get(key)
        if r is None or r[0] == -1:
            cs, hs, mom = key
            r = rt.hint(P.T.Ln, P.T.Ld, list(cs), hs, mom, lv=P.res_lv, fast=True)
            P.resmemo[key] = r
        if r is None:
            bad.add(key)
            out = node
        else:
            out = ('R', node[1]) + r
    elif k in ('B', 'F', 'P'):
        out = node[:2] + ([resolve(P, x, bad, seen) for x in node[2]],) + node[3:]
    elif k == 'S':
        out = ('S', resolve(P, node[1], bad, seen), resolve(P, node[2], bad, seen))
    else:
        out = node
    seen[id(node)] = (node, out)
    return out


def row_job(args):
    """The plan of one cell of the first prime: light, to be put in a part with its neighbours, or cut."""
    par_, a, b = args
    P = par_.planner()
    sys.setrecursionlimit(100000)
    c, node = P.plan([(a, b)], False, K)
    assert node is not None and c < K, (a, b, c)
    while par_.lazy:
        # the hints of the plan's resonant leaves; a leaf with none (the float filter was wrong) fails from now
        # on, and the cell is planned again
        bad = set()
        node = resolve(P, node, bad, {})
        if not bad:
            break
        memo, calls, fcalls = P.resmemo, P.W['calls'], P.W['fcalls']
        for key in bad:
            memo[key] = None
        P = par_.planner()
        P.resmemo = memo
        P.W['calls'], P.W['fcalls'] = calls, fcalls
        P.stat['replan'] = P.stat.get('replan', 0) + len(bad)
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


def row_cached(args):
    """`row_job`, its result kept in the directory `cache` (a file for each cell of the first prime) if one is
    given: a long plan can then be stopped and taken up again."""
    par_, a, b, cache = args
    if cache is None:
        return row_job((par_, a, b))
    import pickle
    path = os.path.join(cache, f'{a}_{b}.pkl')
    if os.path.exists(path):
        with open(path, 'rb') as fh:
            return pickle.load(fh)
    r = row_job((par_, a, b))
    with open(path + '.tmp', 'wb') as fh:
        pickle.dump(r, fh, protocol=4)
    os.replace(path + '.tmp', path)
    return r


def shift(piece, off):
    if piece[0] == 'part':
        return ('part', piece[1] + off)
    return piece[:5] + ([shift(x, off) for x in piece[5]], piece[6])


def plan_all(par_, procs=4, rows=None, cache=None):
    """The parts and the assembly of the bound of the first term: (f0, cfg0, parts, root, total, stats)."""
    import multiprocessing
    P = par_.planner()
    sys.setrecursionlimit(100000)
    f0, cfg0 = fc.root_of(P)
    cuts = fc.rowCuts(P, f0)
    assert cuts[0] == f0 and cuts[-1] == DEN // 2 + 1 and P.T.okJ([], f0, cfg0)
    if cache is not None:
        os.makedirs(cache, exist_ok=True)
    jobs = [(par_, a, b, cache) for a, b in zip(cuts, cuts[1:])]
    if rows is not None:
        jobs = jobs[rows[0]:rows[1]:rows[2] if len(rows) > 2 else 1]
    if procs > 1:
        with multiprocessing.Pool(procs) as pool:
            # the cells that take longest first, each alone in its task
            order = sorted(range(len(jobs)), key=lambda i: -jobs[i][1])
            got = pool.map(row_cached, [jobs[i] for i in order], chunksize=1)
            res = [None] * len(jobs)
            for i, r in zip(order, got):
                res[i] = r
    else:
        res = [row_cached(j) for j in jobs]
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
    res, resF, cof = getattr(par_, 'res', False), getattr(par_, 'resF', False), getattr(par_, 'cof', False)
    tests, cfgI = ('resTestsFC', 'cfgIMRC') if cof else ('resTestsF', 'cfgIMR') if res else ('fillTestsF', 'cfgIM')
    dimp = 'SieveAdFrozResDefs' if resF else 'SieveAdResDefs' if res else 'SieveAdDirDefs'
    alt, ftests = ('altFDR', 'frozResTestsC') if resF else ('altFD', 'frozTestsC')
    resdoc = ('With the resonant window: an evaluation of kind `3` in the main tree is `SieveAd.chkIR`\'s\n'
              '(`SieveAd.resTestsF`), its configuration read by `SieveAd.cfgIMR`' + (
                  ', with the box\'s cofactor in the rest when it\nis one prime (`SieveAd.chkIRC`, '
                  '`SieveAd.resTestsFC`, `SieveAd.cfgIMRC`)' if cof else '') + (
                  '; over the frozen parts too, the box\n`ch ++ β` (`SieveAd.frozResTestsC`), read by '
                  '`SieveAd.cfgIFR`.\n\n' if resF else '.\n\n') if res else '')
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
  (`SieveAd.{alt}`), with the tests `SieveAd.{ftests}` and the chains over the frozen parts on the grid of side
  at most `{par_.hF}/DEN` (`{par_.hFf}`);
* the depth of recursion `{fc.FUEL}`.

{resdoc}The file imports `{dimp}.lean`; so neither it nor the part files (`SieveHint{T}P1.lean` …) load more of
`Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import {dimp}

namespace SieveCert

/-- **The bilinear Type I rule's exponent** at `L = {LN}`. -/
@[instance_reducible] def ibPar{T} : IBPar := ⟨{par_.lnum}, {par_.lden}⟩

end SieveCert

namespace SieveAd

open SieveCert

/-- **The search led by hints at `{LN}`**, with the reversal through the largest prime as its hinted bound. -/
noncomputable def solve{T} : List Cell → Bool → ℕ → ℕ → ℕ × ℕ :=
  solveD opsMP (@{tests} ibPar{T}) {cfgI} (@cfgJM ibPar{T}) (kidsM {par_.kappa} {par_.hI})
    (@{alt} ibPar{T} {par_.kappa} {par_.hF} {fc.FUEL} {par_.maxlen}) {fc.FUEL}

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
    nflip, npos = st.get(('F', False), 0), st.get(('P', False), 0)
    if par_.pos:
        shapes = ('term through its largest prime, of the sign `−` (of three or five primes) or `+` (of two, four '
                  'or six), the cofactor kept as one number (`SieveAdFlipDefs.lean`, `SieveAdFlipPos.lean`)')
        flips = f'{nflip + npos} of them reversals through the largest prime ({npos} of boxes of the sign `+`)'
    else:
        shapes = ('term of the sign `−` of three or five primes through its largest prime, the cofactor kept as one '
                  'number (`SieveAdFlipDefs.lean`)')
        flips = f'{nflip} of them reversals through the largest prime'
    imports = '\n'.join(f'import SieveHint{T}P{i}' for i in range(1, nfiles + 1))
    res, resF, cof = getattr(par_, 'res', False), getattr(par_, 'resF', False), getattr(par_, 'cof', False)
    cfgI = 'cfgIMRC' if cof else 'cfgIMR' if res else 'cfgIM'
    resimp = ('import SieveAdRes\n' + ('import SieveAdFrozResTree\n' if resF else '') +
              ('import SieveAdResCof\n' if cof else '') if res else '')
    prof = 'pr_of_partDR' if resF else 'pr_of_partD'
    if cof:
        soundF = (f'/-- The tests in one pass with the resonant window and the cofactor at `{LN}` are sound. -/\n'
                  f'theorem soundF{T} : (resTestsFC).Sound := resTestsFC_sound\n')
    elif res:
        soundF = (f'/-- The tests in one pass with the resonant window at `{LN}` are sound. -/\n'
                  f'theorem soundF{T} : (resTestsF).Sound := resTestsF_sound\n')
    else:
        soundF = (f'/-- The tests in one pass at `{LN}` are sound: they are the tests. -/\n'
                  f'theorem soundF{T} : (fillTestsF).Sound := by\n  rw [fillTestsF_eq]\n  exact fillTests_sound\n')
    plain = textwrap.fill(
        f'Plain statement (`linnik_{T}`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there '
        f'is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`, with no hypothesis. The route is at `L = {LN}` '
        f'(`route{T}`), ' + (
            'with the estimate in two variables and the resonant window, and the tests are `SieveAd.fillTests` with '
            'the resonant window\'s for an evaluation of kind `3` (`SieveAd.resTestsF`). ' if res else
            'with the estimate in two variables alone, and the tests are `SieveAd.fillTests`, as for the theorem at '
            '`2165/1000`. ') + (
            'Where the paper\'s conditions on the leaves of a comparison fail, the plan cuts the box of leaves in '
            'three: the paper\'s lemma on two parts and, on the third, the leaves whose cofactor is shorter than '
            '`√q` by the estimate in two variables with the fourth moment (the tests\' `SieveAd.leavesE`; '
            '`SieveTwoCompE.prop6_two3_at`, `SieveFillCompE.prop6_fill3_at`). ' if par_.energy else '') + (
            'A box of the main tree may also be evaluated by the resonant window: a Type II estimate in one '
            'variable, the box\'s other primes and the cofactor, with the characters sorted by the sizes of a rest '
            'of its primes\' own sums as well as by their zeros, whose condition on the rest\'s cells the kernel '
            'checks led by a hint (`SieveAd.chkIR`, `SieveResTest.resT`; `SieveAd.evI_resE`, '
            '`SieveTypeIIHM.typeII_res`). ' if res else '') +
        f'The sieve\'s decomposition is a tree of Buchstab steps with the reversal of a '
        f'{shapes}: its tree runs over the frozen numbers, with the tests `SieveAd.frozTests`. The '
        f'kernel does not search for the tree: it follows hints (`SieveAd.solveD`, `SieveAdDirDefs.lean`), the '
        f'plan of the search that `tools/linnik/hint_cert.py` ran ({stats["boxes"]} boxes, {stats["fboxes"]} of '
        f'them over frozen parts), in {nsteps} steps, {flips}: what is '
        f'done at each box, with which configuration, and where the range of each new prime is cut. Each step is '
        f'checked, and a cost that the search returns below its limit bounds the term whatever the hints are '
        f'(`SieveAd.{prof}`). The search is in {len(parts)} parts, {nfiles} files (`SieveHint{T}P1.lean` … '
        f'`SieveHint{T}P{nfiles}.lean`). The kernel evaluates the tests in one pass over a box '
        f'(`SieveAd.fillTestsF`), equal to the tests that are proved sound; over a frozen part, in one pass over '
        f'the chain\'s cells, with what the tests read from the frozen primes computed once for a tree '
        f'(`SieveAd.frozTestsC`), and those imply the tests that are proved sound on the boxes of the tree '
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
{resimp}{imports}

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

{soundF}

/-- **A part of the search bounds its term**: `SieveAd.{prof}` at the route. -/
theorem part{T} {{top : ℕ}} {{bl : List Cell}} {{par : Bool}} {{cs : List ℕ}} {{a c h : ℕ}}
    (hk : (partD solve{T} top bl par cs a K h).1 ≤ c) (hc : c < K) : PR ((a, top) :: bl) par c :=
  {prof} soundF{T} {cfgI} cfgJM {par_.kappa} {par_.hI} {par_.hF} {fc.FUEL} {par_.maxlen} {fc.FUEL} hk hc

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


def generate(par_, procs=4, rows=None, cache=None):
    f0, cfg0, parts, root, total, stats = plan_all(par_, procs, rows, cache)
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
    tag = a.pop(0) if a and a[0] in CERTS else TAG
    if a and a[0] == '--try':
        ln, ld = map(int, a[2].split('/'))
        par_ = Par(a[1], ln, ld, h=float(a[3]), hF=float(a[4]), maxlen=int(a[5]),
                   lam=int(a[a.index('--lam') + 1]) if '--lam' in a else 0, pos='--pos' in a,
                   blk=int(a[a.index('--blk') + 1]) if '--blk' in a else 1,
                   skip=int(a[a.index('--skip') + 1]) if '--skip' in a else 0,
                   sec=2 if '--lam' in a or '--pos' in a else 1, energy='--energy' in a,
                   res='--res' in a or '--resF' in a or '--cof' in a, resF='--resF' in a, cof='--cof' in a,
                   lv='--lv' in a, lazy='--lazy' in a,
                   split=int(a[a.index('--split') + 1]) if '--split' in a else 0)
    elif not a or a[0] in ('--check', '--out', '--procs', '--cache', '--rows', '--plan-only'):
        par_ = Par(tag, **CERTS[tag])
        if out is None and '--check' not in a and '--plan-only' not in a:
            out = tc.PNT
    else:
        print(__doc__)
        return 2
    rows = None
    if '--rows' in a:
        # the cells `I` to `J` of the first prime, every `STEP`-th (`--rows I J [STEP]`)
        i = a.index('--rows') + 1
        rows = tuple(int(x) for x in a[i:i + 3] if x.isdigit())
    t0 = time.time()
    cache = a[a.index('--cache') + 1] if '--cache' in a else None
    if '--plan-only' in a:
        # the plans of the cells into the cache, and no file: for a search shared between machines
        assert cache is not None, '--plan-only keeps its plans in --cache DIR'
        f0, cfg0, parts, root, total, stats = plan_all(par_, procs, rows, cache)
        print(f'L = {par_.lnum}/{par_.lden} rows {rows}: cost/K = {total / K:.5f}; {stats["boxes"]} boxes searched; '
              f'{sum(stats["steps"].values())} steps; {time.time() - t0:.0f} s', flush=True)
        return 0
    files, (parts, root, total, stats) = generate(par_, procs, rows, cache)
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
