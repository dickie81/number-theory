#!/usr/bin/env python3
"""tree_cert.py [--check] [--stats] [--try H DEPTH [W1 W2 a/b]]: the tree of Buchstab steps at L = 219/100, searched
as the kernel searches it, cut into parts, and the Lean files of the theorem there.

The route is L = 219/100 with the window [44260, 46717]/10^5 (`gen_cgl_curve.py` computes it and writes its
Proposition 3'). A tree of `lib/pnt/SieveAdDefs.lean` on the box of the first prime, of cost below K, gives the
theorem (`SieveAd.linnik_tree`). No tree is written out: `SieveAd.solveF` (`lib/pnt/SieveAdSearchDefs.lean`) is a
search that the kernel runs, and a cost that it returns below its limit is the cost of a tree
(`SieveAd.solveF_sound`). This script is that search in Python, definition by definition:

  * the tests `SieveAd.mixTests` (`Tests`): `okIW`, `okJW` (SieveAdWinDefs.lean) and `okI2`, `okJ2`
    (SieveAdTwoDefs.lean), with `surelyEval`, `ibOK` of mirror8.py;
  * `vanishOK`, `dropOK`, `dropCost`, `dropBOK`, `dropBCost` (SieveAdDefs.lean);
  * the search (`Search`): `findSub2`, `bestSub`, `findSub1`, `tstarF`, `propI2`, `leavesOf`, `propJ2`, `ibFast`,
    `propJ`, `cutsOf`, `kids`, `buchC`, `splitC`, `node`, `step`, `solveF` and the strategy `mixStrat`.

A box is a list of cells (lo, hi), the newest prime first, in units of 1/DEN of exponents of x. The search treats a
box so: no term, or evaluated by the window or by the estimate in two variables (rest: one prime; first variable: a
set of the others in the window that the rest leaves), costs 0; otherwise it is dropped, if its sign is +, or
decomposed by Buchstab's identity at the largest floor at which the comparison passes, the new prime's range cut
into cells of side HI (coarser from the fifth prime on), whichever is cheaper; a box that can be neither dropped
nor decomposed is cut in two, down to the width WMIN. A box of DEPTH primes is not decomposed. A limit stops the
search of a subtree whose cost reaches it.

The kernel checks the search in parts, each a range of consecutive cells of one prime (`kids`): a range of cells of
the first prime, or, for a cell of the first prime whose search is long, ranges of the cells of the second prime
below it, glued by the cell's own Buchstab step. A part's time is predicted from the search's work in it (`pred`:
a least-squares fit to the kernel's checks of seventeen parts across the tree, of 26 to 63 seconds, with an error of
at most five seconds), and the parts are cut at CAP predicted seconds.

It writes `lib/pnt/SieveGrid21900.lean` (the grid and the strategy), `lib/pnt/SieveTree21900P<k>.lean` (the parts,
each by `decide +kernel`) and `lib/pnt/Linnik21900.lean` (the route, the tree from the parts, and the theorem).
With `--check`, nothing is written: the files are regenerated in memory and compared with `lib/pnt` (exit 1 on a
difference). With `--stats`, the search's work and the parts' predicted times are printed. With `--try`, only
the search is run, with cells of side H and boxes of fewer than DEPTH primes decomposed (and on another route, if
given), and its cost is printed.

Values (11 November 2026): cost/K 0.98189 with 301834 boxes searched, at H = 0.006 and DEPTH = 6, the strategy of
the Lean files: 81 parts in 11 files, which the kernel checks in 2515 seconds in all (180 to 260 a file). `--try 0.005 6`: 0.93489, 547117 boxes; `--try 0.005 8`: 0.92462, 558412; `--try 0.006 8`: 0.96227,
311103; `--try 0.0065 6`: 1.00099. Of these the first is the least search that passes.

Needs Python 3 only. Under a minute.
"""
import os
import sys
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mirror8 as m8  # noqa: E402

PNT = os.path.join(HERE, '..', '..', 'lib', 'pnt')
DEN, K, SC = m8.DEN, m8.K, m8.SC
cdiv, tsub, omKw = m8.cdiv, m8.tsub, m8.omKw

# the route, the window and the strategy
TAG, LNUM, LDEN, W1, W2, GN = '21900', 219, 100, 44260, 46717, 272
HI, DEPTH, WMIN, FUEL = round(0.006 * DEN), 6, round(0.0005 * DEN), 200
BIG = 2 ** 70
CFGW = (0, 0, 0, 0, False)
# the parts: at most CAP predicted seconds each, a file of at most PMAX parts and FCAP predicted seconds
CAP, PMAX, FCAP = 40.0, 10, 240.0


def leafxr_checks():
    """The inequalities of `SieveLeafZoneX.leafXR` (`lib/pnt/SieveLeafZoneXDefs.lean`, which `gen_leafzone.py`
    writes), read from the file: for each, the coefficients of the products `lp1`, `lp2`, `lr1`, `lr2`, `ld`, `ln`
    (`Ln·P₁`, `Ln·P₂`, `Ln·R₁`, `Ln·R₂`, `Ld·D`, `Ln·D`) on its two sides."""
    import re
    src = open(os.path.join(PNT, 'SieveLeafZoneXDefs.lean')).read()
    body = src[src.index('def leafXR'):]
    body = body[body.index('=>') + 2:body.index('(Nat.mul Ln P₁)')]
    atoms = ('lp1', 'lp2', 'lr1', 'lr2', 'ld', 'ln')
    toks = re.findall(r'\(|\)|Nat\.add|Nat\.mul|Nat\.ble|&&|\d+|lp1|lp2|lr1|lr2|ld|ln', body)
    pos = [0]

    def expr():
        t = toks[pos[0]]
        pos[0] += 1
        if t in atoms:
            return tuple(int(a == t) for a in atoms)
        if t.isdigit():
            assert t == '0', 'leafXR: a constant term'
            return (0,) * len(atoms)
        assert t == '(', t
        op = toks[pos[0]]
        pos[0] += 1
        if op == 'Nat.add':
            x, y = expr(), expr()
            r = tuple(a + b for a, b in zip(x, y))
        else:
            assert op == 'Nat.mul', op
            c = int(toks[pos[0]])
            pos[0] += 1
            r = tuple(c * a for a in expr())
        assert toks[pos[0]] == ')'
        pos[0] += 1
        return r

    out = []
    while pos[0] < len(toks):
        t = toks[pos[0]]
        pos[0] += 1
        if t in ('&&', ')'):
            continue
        assert t == 'Nat.ble', t
        out.append((expr(), expr()))
    assert len(out) == body.count('Nat.ble'), 'leafXR: a check was not read'
    return out


LEAFXR = leafxr_checks()


def leafXR(Ln, Ld, D, P1, P2, R1, R2):
    """`SieveLeafZoneX.leafXR Ln Ld D P₁ P₂ R₁ R₂`."""
    at = (Ln * P1, Ln * P2, Ln * R1, Ln * R2, Ld * D, Ln * D)
    return all(sum(c * x for c, x in zip(l, at)) <= sum(c * x for c, x in zip(r, at)) for l, r in LEAFXR)


def subsE(cs, lo, hi, rem, bit=1, s=0, mask=0, out=None, cap=24):
    """The first `cap` sets of the cells, as bits (the first cell's the lowest), whose upper ends' sum is in
    `[lo, hi]`, depth first with each cell in before out; `rem` is the sum of the upper ends of `cs`."""
    if out is None:
        out = []
    if len(out) >= cap or hi < s or s + rem < lo:
        return out
    if not cs:
        out.append(mask)
        return out
    c = cs[0]
    subsE(cs[1:], lo, hi, tsub(rem, c[1]), 2 * bit, s + c[1], mask + bit, out, cap)
    subsE(cs[1:], lo, hi, tsub(rem, c[1]), 2 * bit, s, mask, out, cap)
    return out


class Tests:
    """`SieveAd.mixTests` on the grid of the window and `IBPar ⟨Ln, Ld⟩`. The kernel's `chkJ2` and `coreJ2` take the
    leaves cut in three where the paper's conditions fail (`SieveAd.leavesE`, `lib/pnt/SieveAdLeafDefs.lean`); the
    planner proposes such leaves, and its tests accept them, only with `energy`."""

    energy = False

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

    # SieveAdLeafDefs.lean
    def pStar(self, D2):
        Ln, Ld = self.Ln, self.Ld
        return min((Ln * DEN - Ld * DEN - 1) // Ln, tsub((2 * Ln * DEN - Ld * DEN - 1) // (2 * Ln), D2),
                   tsub((2 * Ln * DEN - 2 * Ld * DEN - 1) // Ln, 2 * D2))

    def thetaL(self, D1):
        Ln, Ld = self.Ln, self.Ld
        return min(tsub((2 * Ln * DEN - Ld * DEN - 1) // (2 * Ln), D1),
                   tsub(2 * Ln * DEN - 2 * Ld * DEN - 1, Ln * D1) // (2 * Ln))

    def leavesE(self, D1, D2):
        Ln, Ld = self.Ln, self.Ld
        P, th = self.pStar(D2), self.thetaL(D1)
        return (self.leaves(P, D2) and self.leaves(D1, th) and D1 + D2 < DEN and 1 <= P and 1 <= th
                and leafXR(Ln, Ld, DEN, tsub(P, 1), D1 + 1, tsub(th, 1), D2 + 1))

    def chkJ2(self, bl, f, s0, sr, s1, e, u, v, t):
        r1, r2 = mSum(0, bl, sr), mSum(1, bl, sr)
        h1, hs = mSum(1, bl, s1), hiSum(bl)
        D1 = h1 + (t if e else 0)
        D2 = tsub(hs, h1) + (0 if e else t)
        return (0 < f and len(bl) <= 13 and all(f <= c[0] <= c[1] <= DEN for c in bl) and s0 & sr == 0
                and self.zone(r1, r2, u, v) and u + f < v and u <= t + mSum(0, bl, s0) and mSum(1, bl, s0) < v
                and (self.leaves(D1, D2) or (self.energy and self.leavesE(D1, D2))))

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
    """`dropBCost`: a bound, in units of 1/K, for the products n = r of the box in (x, 2x]."""
    b = bl[1:]
    tr = 1
    for d in b:
        tr *= trF(d[0], d[1] - d[0])
    return cdiv(K * DEN * tr, (DEN - hiSum(b)) * SC ** len(b))


def dropC(bl, par):
    if par:
        if dropOK(bl):
            return dropCost(bl)
        if dropBOK(bl):
            return dropBCost(bl)
    return None


# SieveAdSearchDefs.lean

class Search:
    """`SieveAd.solveF mixTests (mixStrat hI depth wmin)`, with counts of its work."""

    def __init__(self, T, hI, depth, wmin):
        self.T, self.hI, self.depth, self.wmin = T, hI, depth, wmin
        Ln, Ld = T.Ln, T.Ld
        self.restLo = cdiv(Ld * DEN + 2000 * Ln, 2000 * Ln)
        self.restHi = tsub(tsub(62500 * Ln * DEN, 125005 * Ld * DEN) // (34863 * Ln), 1)
        self.uC0 = cdiv(2 * Ld * DEN, 3 * Ln)
        self.uA, self.uB, self.uC = 62505 * Ld * DEN + 27637 * Ln, 27637 * Ln, 62500 * Ln
        self.vA = tsub(3 * Ln * DEN, 2 * Ld * DEN) // (3 * Ln)
        self.vB, self.vC = tsub(62500 * Ln * DEN, 62505 * Ld * DEN), 34863 * Ln
        self.umC0, self.umA = cdiv(2 * Ld * DEN + 3 * Ln, 3 * Ln), 62505 * Ld * DEN + 90137 * Ln
        self.D1max = tsub((Ln - Ld) * DEN, 1) // Ln
        self.T5 = tsub(2 * Ln * DEN, Ld * DEN + 1) // (2 * Ln)
        self.T6 = tsub(2 * Ln * DEN, 2 * Ld * DEN + 1) // Ln
        # with the leaves cut in three, the sizes' sum is at most (1 − 2/(5L))·DEN: the region asks m₂ ≥ 2/5
        self.T5E = (5 * Ln * DEN - 2 * Ld * DEN) // (5 * Ln)
        self.W = dict.fromkeys(('calls', 'dfs', 'rest', 'okIW', 'okI2', 'okJ2', 'okJW', 'drop', 'cuts'), 0)
        self.minfuel = FUEL

    # the sets of a box's cells
    def findSub2(self, umin, vmax, skip, cs, bit, slo, shi, mask, rem):
        self.W['dfs'] += 1
        if vmax < shi:
            return None
        if umin <= slo:
            return mask
        if not cs or slo + rem < umin:
            return None
        c = cs[0]
        if bit == skip:
            return self.findSub2(umin, vmax, skip, cs[1:], 2 * bit, slo, shi, mask, rem)
        m = self.findSub2(umin, vmax, skip, cs[1:], 2 * bit, slo + c[0], shi + c[1], mask + bit, tsub(rem, c[0]))
        if m is not None:
            return m
        return self.findSub2(umin, vmax, skip, cs[1:], 2 * bit, slo, shi, mask, tsub(rem, c[0]))

    def bestSub(self, v, skip, cs, bit, slo, shi, mask, rem, best):
        self.W['dfs'] += 1
        if slo + rem <= best[0]:
            return best
        if not cs:
            return (slo, mask)
        c = cs[0]
        if bit == skip:
            return self.bestSub(v, skip, cs[1:], 2 * bit, slo, shi, mask, rem, best)
        if shi + c[1] < v:
            best = self.bestSub(v, skip, cs[1:], 2 * bit, slo + c[0], shi + c[1], mask + bit, tsub(rem, c[0]), best)
        return self.bestSub(v, skip, cs[1:], 2 * bit, slo, shi, mask, tsub(rem, c[0]), best)

    def findSub1(self, lo, hi, cs, bit, s, mask, rem):
        self.W['dfs'] += 1
        if hi < s or s + rem < lo:
            return None
        if not cs:
            return mask
        c = cs[0]
        m = self.findSub1(lo, hi, cs[1:], 2 * bit, s + c[1], mask + bit, tsub(rem, c[1]))
        if m is not None:
            return m
        return self.findSub1(lo, hi, cs[1:], 2 * bit, s, mask, tsub(rem, c[1]))

    def cIBF(self, slo, shi):
        U1, U2 = self.T.U1, self.T.U2
        return max(tsub(U1, slo), tsub(DEN - U2, max(slo, U2)) if U2 <= shi else 0)

    def tstarF(self, lim, cs, slo, shi, rem, best):
        self.W['dfs'] += 1
        if best <= tsub(self.T.U1, slo + rem):
            return best
        if not cs:
            return min(best, self.cIBF(slo, shi))
        c = cs[0]
        if shi + c[1] < lim:
            best = self.tstarF(lim, cs[1:], slo + c[0], shi + c[1], tsub(rem, c[0]), best)
        return self.tstarF(lim, cs[1:], slo, shi, tsub(rem, c[0]), best)

    # the proposals
    def restOK(self, c):
        self.W['rest'] += 1
        return self.restLo <= c[0] and c[1] <= self.restHi

    def uOfF(self, r1):
        return max(self.uC0, tsub(tsub(self.uA, self.uB * r1) + self.uC, 1) // self.uC)

    def vOfF(self, r2):
        return min(tsub(self.vA, r2 + 1), tsub(self.vB, self.vC * (r2 + 1)) // self.uC)

    def uminOf(self, r1):
        return max(self.umC0, tsub(tsub(self.umA, self.uB * r1) + self.uC, 1) // self.uC)

    def propI2(self, bl, ls):
        bit = 1
        for c in bl:
            if self.restOK(c):
                m = self.findSub2(self.uminOf(c[0]), self.vOfF(c[1]), bit, bl, 1, 0, 0, 0, tsub(ls, c[0]))
                if m is not None:
                    return [(1, m, bit, 0, False)]
            bit *= 2
        return []

    def leavesOf(self, bl, hs, t):
        if self.T5 < hs + t:
            return None
        lo = tsub(2 * (hs + t), self.T6)
        m = self.findSub1(tsub(lo, t), tsub(self.D1max, t), bl, 1, 0, 0, hs) if t <= self.D1max else None
        if m is not None:
            return (m, True)
        m = self.findSub1(lo, self.D1max, bl, 1, 0, 0, hs)
        if m is not None:
            return (m, False)
        return None

    def energyHere(self):
        """Whether the leaves of the comparisons may be cut in three: with `T.energy`, in the main tree and over the
        frozen parts, with the rest among the box's primes or among the tree's."""
        return self.T.energy

    def t5J(self):
        """The largest sum of the leaves' sizes for a comparison here."""
        return max(self.T5, self.T5E) if self.energyHere() else self.T5

    def leavesOfE(self, bl, hs, t):
        """The leaves cut in three (`SieveAd.leavesE`): the first set of cells, with the small primes on its side and
        then not, whose first side's exponent is from 0.85 to 1.25 (the region asks 0.9 to 1.2) and whose sizes
        pass."""
        if self.T5E < hs + t:
            return None
        T = self.T
        p_lo, p_hi = 85 * T.Ld * DEN // (100 * T.Ln), cdiv(125 * T.Ld * DEN, 100 * T.Ln)
        for e in (True, False):
            tt = t if e else 0
            for m in subsE(bl, tsub(p_lo, tt), tsub(p_hi, tt), hs):
                h1 = mSum(1, bl, m)
                if T.leavesE(h1 + tt, hs - h1 + (t - tt)):
                    return (m, e)
        return None

    def leavesOfJ2(self, bl, hs, t):
        """`leavesOf`, or where its conditions fail and `energyHere`, `leavesOfE`."""
        sp = self.leavesOf(bl, hs, t)
        if sp is None and self.energyHere():
            sp = self.leavesOfE(bl, hs, t)
        return sp

    def propJ2(self, bl, lomin, ls, hs):
        acc = (0, None)
        bit = 1
        for c in bl:
            if lomin <= acc[0]:
                return acc
            if self.restOK(c):
                u, v = self.uOfF(c[0]), self.vOfF(c[1])
                f = min(lomin, tsub(v, u + 1))
                if acc[0] < f and hs + tsub(u, tsub(ls, c[0])) <= self.t5J():
                    b = self.bestSub(v, bit, bl, 1, 0, 0, 0, tsub(ls, c[0]), (0, 0))
                    sp = self.leavesOfJ2(bl, hs, tsub(u, b[0]))
                    if sp is not None:
                        acc = (f, (1, b[1], bit, sp[0], sp[1]))
            bit *= 2
        return acc

    def ibFast(self, bl, ls, hs):
        if not tsub(2 * hs + 1, DEN) <= self.D1max:
            return False
        Tg = self.tstarF(DEN - self.T.U1, bl, 0, 0, ls, DEN)
        if Tg <= self.D1max and self.findSub1(tsub(2 * hs + Tg + 1, DEN), self.D1max - Tg, bl, 1, 0, 0, hs) is not None:
            return True
        return self.findSub1(tsub(2 * (hs + Tg) + 1, DEN), self.D1max, bl, 1, 0, 0, hs) is not None

    def propJ(self, bl):
        lomin, ls, hs = min([DEN] + [c[0] for c in bl]), loSum(bl), hiSum(bl)
        r = (0, None) if self.T5 < hs else self.propJ2(bl, lomin, ls, hs)
        out = []
        if r[0] < self.T.V and self.T.V <= lomin and self.ibFast(bl, ls, hs):
            out.append((self.T.V, CFGW))
        if r[1] is not None:
            out.append(r)
        return out

    def stepOf(self, d):
        return self.hI if d <= 4 else self.hI * (1 + tsub(d, 3) // 2)

    def cutsOf(self, bl, f):
        if not bl:
            return []
        x = bl[0]
        reg = min(x[1], tsub(DEN, loSum(bl)) // 2 + 2)
        last = tsub(DEN - 1, hiSum(bl))
        if f < reg:
            st = self.stepOf(len(bl) + 1)
            n = max(1, tsub(reg - f + st, 1) // st)
            return [f + (reg - f) * j // n for j in range(1, n + 1)] + [last]
        return [last]

    # the search
    def anyI(self, bl):
        T = self.T
        self.W['okIW'] += 1
        if T.okI(bl, CFGW):
            return True
        for cfg in self.propI2(bl, loSum(bl)):
            self.W['okI2'] += 1
            if T.okI(bl, cfg):
                return True
        return False

    def firstJ(self, bl, lo0, ps):
        """The first proposed floor that passes, with its configuration."""
        for f, cfg in ps:
            self.W['okJW' if cfg[0] == 0 else 'okJ2'] += 1
            if 0 < f <= lo0 and self.T.okJ(bl, f, cfg):
                return f, cfg
        return None

    def kids(self, top, bl, par, cs, a, lim, n):
        """`kids (solveF n) top bl par cs a lim`."""
        for i, c in enumerate(cs):
            if a < c < top:
                c1 = self.solve([(a, c)] + bl, par, lim, n)
                if lim <= c1:
                    return c1
                return c1 + self.kids(top, bl, par, cs[i + 1:], c, tsub(lim, c1), n)
        return self.solve([(a, top)] + bl, par, lim, n)

    def buchC(self, x, bl, par, lim, n):
        if len(bl) < self.depth:
            fj = self.firstJ(bl, x[0], self.propJ(bl))
            if fj is not None:
                self.W['cuts'] += 1
                return self.kids(x[1], bl, not par, self.cutsOf(bl, fj[0]), fj[0], lim, n)
        return lim + BIG

    def splitC(self, x, bl, par, lim, n):
        mid = (x[0] + x[1]) // 2
        if self.wmin < tsub(x[1], x[0]) and x[0] < mid < x[1]:
            c1 = self.solve([(x[0], mid)] + bl[1:], par, lim, n)
            if lim <= c1:
                return c1
            return c1 + self.solve([(mid, x[1])] + bl[1:], par, tsub(lim, c1), n)
        return lim + BIG

    def node(self, x, bl, par, lim, n):
        dc = dropC(bl, par)
        if par:
            self.W['drop'] += 1
        if dc is not None:
            bc = self.buchC(x, bl, par, dc if dc <= lim else lim, n)
            return dc if dc <= bc else bc
        bc = self.buchC(x, bl, par, lim, n)
        if bc < BIG:
            return bc
        return self.splitC(x, bl, par, lim, n)

    def solve(self, bl, par, lim, n):
        """`solveF n bl par lim`."""
        self.minfuel = min(self.minfuel, n)
        if n == 0 or not bl:
            return lim
        self.W['calls'] += 1
        if vanishOK(bl) or self.anyI(bl):
            return 0
        return self.node(bl[0], bl, par, lim, n - 1)

    def work(self, f):
        """The value of `f()` and the work of the search in it."""
        w0 = dict(self.W)
        r = f()
        return r, {k: self.W[k] - w0[k] for k in self.W}


def pred(w):
    """The kernel's time on a part, in seconds, from the search's work in it: the boxes searched, the steps of the
    searches over the sets of a box's cells, and the boxes decomposed by the estimate's comparison."""
    return 1.3 + 3.0e-3 * w['calls'] + 8.8e-5 * w['dfs'] + 8.3e-3 * w['okJ2']


def addw(a, b):
    return {k: a[k] + b[k] for k in a}


def rowCuts(T, hI, wmin):
    """The ends of the cells of the first prime: steps of at most hI from V to DEN/2 + 1, the window's ends, and a
    thin cell at the top (the corner where two primes are near x^{1/2} costs its width)."""
    top = DEN // 2 + 1
    n = max(1, cdiv(top - T.V, hI))
    return sorted({T.V + (top - T.V) * j // n for j in range(n + 1)} | {T.U1 + 1, T.U2 - 1, DEN // 2 - wmin})


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


def search_only(h, depth, w1, w2, ln, ld):
    """The cost of the search with other parameters, and the number of boxes searched."""
    T = Tests(w1, w2, ln, ld)
    hI = round(h * DEN)
    S = Search(T, hI, depth, WMIN)
    sys.setrecursionlimit(100000)
    cuts = rowCuts(T, hI, WMIN)
    return S.kids(DEN // 2 + 1, [], False, cuts[1:-1], cuts[0], K, FUEL), S.W['calls']


def plan():
    """The parts of the search and the tree's assembly: (parts, root), with

    parts: [(top, bl, par, cuts, a, cost, work)], a part being `kids (solveF FUEL) top bl par cuts a K <= cost`;
    root: the pieces of the first prime's range, in order: ('part', k), or ('row', (a, b), f, cfg, [k, ...]) for a
    cell (a, b) of the first prime decomposed at the floor f with the configuration cfg, its second prime's range
    in the parts k."""
    T = Tests(W1, W2, LNUM, LDEN)
    S = Search(T, HI, DEPTH, WMIN)
    sys.setrecursionlimit(100000)
    cuts = rowCuts(T, HI, WMIN)
    assert cuts[0] == T.V and cuts[-1] == DEN // 2 + 1 and T.okJ([], T.V, CFGW)
    rows = []
    for a, b in zip(cuts, cuts[1:]):
        c, w = S.work(lambda: S.solve([(a, b)], False, K, FUEL))
        rows.append((a, b, c, w))
    searched = dict(S.W)
    parts, root = [], []

    def part(top, bl, par, cells):
        cs = [c[0] for c in cells[1:]]
        c, w = S.work(lambda: S.kids(top, bl, par, cs, cells[0][0], K, FUEL))
        assert c == sum(x[2] for x in cells) < K
        parts.append((top, bl, par, cs, cells[0][0], c, w))
        return len(parts) - 1

    light = []

    def flush():
        for g in groups(light, CAP):
            root.append(('part', part(g[-1][1], [], False, g)))
        light.clear()

    for a, b, c, w in rows:
        if pred(w) <= CAP:
            light.append((a, b, c, w))
            continue
        # a long cell: its own Buchstab step, and the cells of the second prime below it
        bl = [(a, b)]
        assert not vanishOK(bl) and not S.anyI(bl) and dropC(bl, False) is None
        fj = S.firstJ(bl, a, S.propJ(bl))
        assert fj is not None
        f, cfg = fj
        ends = [f]
        for x in S.cutsOf(bl, f):
            if ends[-1] < x < b:
                ends.append(x)
        ends.append(b)
        cells = []
        for s, e in zip(ends, ends[1:]):
            c2, w2 = S.work(lambda: S.solve([(s, e)] + bl, True, K, FUEL))
            cells.append((s, e, c2, w2))
        assert sum(x[2] for x in cells) == c
        flush()
        root.append(('row', (a, b), f, cfg, [part(g[-1][1], bl, True, g) for g in groups(cells, CAP)]))
    flush()
    assert S.minfuel > 100
    total = sum(r[2] for r in rows)
    assert total == sum(p[5] for p in parts) < K
    return T, searched, parts, root, total


# the Lean files

def wrap(s, indent='    '):
    return ('\n' + indent).join(textwrap.wrap(s, 116 - len(indent), break_long_words=False))


def nat(x):
    """A number of the grid as Lean text: `DEN / 2 + 1` for the top of the first prime's range."""
    return '(DEN / 2 + 1)' if x == DEN // 2 + 1 else str(x)


def boxlit(bl):
    return '[' + ', '.join(f'({a}, {b})' for a, b in bl) + ']'


def part_stmt(k, p):
    top, bl, par, cs, a, c, _ = p
    return wrap(f'theorem tree{TAG}_{k} : kids (solveF mixTests strat{TAG} {FUEL}) {nat(top)} {boxlit(bl)} '
                f'{"true" if par else "false"} [{", ".join(map(str, cs))}] {a} K ≤ {c} := by decide +kernel')


def grid_file(T):
    return f'''/-
# The grid and the strategy of the tree at `L = {LNUM}/{LDEN}`

Generated by `tools/linnik/tree_cert.py`; do not edit by hand.

The grid of `SieveTypeIIU{TAG}D.typeII_{TAG}d`'s window: `U1 = ⌈({W1}/100000)DEN⌉`, `U2 = ⌊({W2}/100000)DEN⌋`
(`grid{TAG}`, `gridOK{TAG}`; its number of cells is not used by a tree), the bilinear Type I rule's exponent
`{LNUM}/{LDEN}` (`ibPar{TAG}`), and the strategy of the search for a tree (`strat{TAG}`): `SieveAd.mixStrat` with
cells of side `{HI}/DEN` (`0.006`), boxes of fewer than `{DEPTH}` primes decomposed, and cells wider than
`{WMIN}/DEN` (`0.0005`) cut for want of a test.

The file imports `SieveAdSearchDefs.lean`; so neither it nor the part files (`SieveTree{TAG}P1.lean` …) load more of
`Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveAdSearchDefs

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

/-- **The strategy of the search for a tree at `{LNUM}/{LDEN}`.** -/
def strat{TAG} : Strat := @mixStrat grid{TAG} ibPar{TAG} {HI} {DEPTH} {WMIN}

end SieveAd

#print axioms SieveCert.gridOK{TAG}
'''


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
            f'File {i} of {len(files)}: the parts `tree{TAG}_{g[0]}` … `tree{TAG}_{g[-1]}` of the search for a tree '
            f'at `L = {LNUM}/{LDEN}` with the strategy `SieveAd.strat{TAG}` ({len(g)} parts, predicted {secs:.0f} s of '
            f'the kernel). A part is a range of consecutive cells of one prime: the sum of the costs that the search '
            f'(`SieveAd.solveF`) returns on them, each searched with the limit that the cells before it leave of `K`, '
            f'is at most the part\'s bound, by `decide +kernel`, one at a time (`Elab.async false`). '
            f'`Linnik{TAG}.lean` makes the tree from the parts.', width=116)
        body = '\n\n'.join(part_stmt(k, parts[k]) for k in g)
        out[f'SieveTree{TAG}P{i}.lean'] = f'''/-
# The tree at `L = {LNUM}/{LDEN}`, parts {g[0]}–{g[-1]} of {len(parts)}

Generated by `tools/linnik/tree_cert.py`; do not edit by hand.

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
'''
    return out


def chain(items, indent):
    """`has_split` over the pieces `items` (Lean terms), nested to the right."""
    if len(items) == 1:
        return items[0]
    pad = ' ' * indent
    return (f'has_split (by decide) (by decide)\n{pad}  ({items[0]})\n{pad}  ('
            + chain(items[1:], indent + 2) + ')')


def final_file(T, parts, root, total, nfiles):
    LN = f'{LNUM} / {LDEN}'
    piece = lambda k: f'has_of_kids strat{TAG} {FUEL} tree{TAG}_{k} (by decide)'  # noqa: E731
    rows, items = [], []
    for r in root:
        if r[0] == 'part':
            items.append(piece(r[1]))
            continue
        _, (a, b), f, cfg, ks = r
        i = len(rows)
        c = sum(parts[k][5] for k in ks)
        cfgs = f'⟨{cfg[0]}, {cfg[1]}, {cfg[2]}, {cfg[3]}, {"true" if cfg[4] else "false"}⟩'
        rows.append(f'''/-- The cell `({a}, {b})` of the first prime: Buchstab's identity at the floor `{f}`, and
the parts of the second prime's range. -/
theorem row{TAG}_{i} : Has mixTests [({a}, {b})] false {c} :=
  (has_buch (τ := mixTests) (x := ({a}, {b})) (b := []) (par := false) (f := {f})
    (cfg := {cfgs}) (by decide) (by decide) (by decide +kernel)
    ({chain([piece(k) for k in ks], 4)})).mono (by decide)''')
        items.append(f'row{TAG}_{i}')
    imports = '\n'.join(f'import SieveTree{TAG}P{i}' for i in range(1, nfiles + 1))
    nrow = len(rows)
    return f'''/-
# Linnik's theorem with exponent `{LN}`, by a tree of Buchstab steps

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/tree_cert.py`; do not edit by hand.

Plain statement (`linnik_{TAG}`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`, with no hypothesis. The route is at `L = {LN}` on the window
`[{W1}/100000, {W2}/100000]` (`route{TAG}`, with its Type II estimate `SieveTypeIIU{TAG}D.typeII_{TAG}d`), and the
sieve's decomposition is a tree of Buchstab steps chosen term by term (`SieveAdDefs.lean`), with the window's tests
and those of the estimate in two variables (`SieveAd.mixTests`, sound by `SieveAd.mixTests_sound`). The tree is not
written out: the kernel runs a search for it (`SieveAd.solveF`, with the strategy `SieveAd.strat{TAG}`) in
{len(parts)} parts, {nfiles} files (`SieveTree{TAG}P1.lean` … `SieveTree{TAG}P{nfiles}.lean`), and a cost that the search returns is the
cost of a tree (`SieveAd.has_of_kids`).

* `route{TAG}`, `routeOK{TAG}`, `typeII{TAG}`, `fits{TAG}`, `ibFits{TAG}`: the route, its estimate and the grid's fit.
* `row{TAG}_0` … `row{TAG}_{nrow - 1}`: the {nrow} cells of the first prime whose search is cut into parts by the cells of the
  second prime: the cell's own Buchstab step (`SieveAd.has_buch`), and the parts below it.
* `tree{TAG}`: a tree on the box of the first prime, of cost `{total}`, which is `{total / K:.5f}·K`.
* `linnik_{TAG}`: `SieveAd.linnik_has` at them.

The file imports `SieveAdSearch.lean`, `SieveAdMix.lean`, `SieveTypeIIU{TAG}D.lean` and the part files.
-/
import SieveAdSearch
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

attribute [local instance] grid{TAG} ibPar{TAG}

{chr(10).join(r + chr(10) for r in rows)}
/-- **The tree at `{LN}`**: the box of the first prime, with the cell `({T.V}, DEN/2 + 1)`, has a tree that passes
`SieveAd.ok` with the tests `SieveAd.mixTests`, for a term of the sign `−`, at the cost `{total}`, below `K`. -/
theorem tree{TAG} : Has mixTests [({T.V}, DEN / 2 + 1)] false {total} :=
  ({chain(items, 2)}).mono (by decide)

end

/-- **Linnik's theorem with exponent `{LN}`, by a tree of Buchstab steps**: there is `K` such that for every `q ≥ 1`
and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`. -/
theorem linnik_{TAG} : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ ({LN} : ℝ) :=
  @linnik_has route{TAG} routeOK{TAG} (@mixTests grid{TAG} ibPar{TAG})
    (@mixTests_sound route{TAG} routeOK{TAG} grid{TAG} gridOK{TAG} fits{TAG} ibPar{TAG} ibFits{TAG} typeII{TAG})
    {T.V} cfgW (by decide) (by decide +kernel) {total} tree{TAG} (by decide)

end Linnik{TAG}

#print axioms Linnik{TAG}.tree{TAG}
#print axioms Linnik{TAG}.linnik_{TAG}
'''


def generate():
    T, searched, parts, root, total = plan()
    files = {f'SieveGrid{TAG}.lean': grid_file(T)}
    pf = part_files(parts)
    files.update(pf)
    files[f'Linnik{TAG}.lean'] = final_file(T, parts, root, total, len(pf))
    return files, (searched, parts, root, total)


def main():
    if '--try' in sys.argv:
        a = sys.argv[sys.argv.index('--try') + 1:]
        w1, w2, (ln, ld) = (int(a[2]), int(a[3]), map(int, a[4].split('/'))) if len(a) >= 5 else (W1, W2, (LNUM, LDEN))
        c, n = search_only(float(a[0]), int(a[1]), w1, w2, ln, ld)
        print(f'L = {ln}/{ld}, window [{w1}, {w2}]/10^5, cells of side {a[0]}, depth {a[1]}: cost/K = {c / K:.5f}; '
              f'{n} boxes searched')
        return 0
    files, (searched, parts, root, total) = generate()
    nrow = sum(1 for r in root if r[0] == 'row')
    times = [pred(p[6]) for p in parts]
    print(f'L = {LNUM}/{LDEN}, window [{W1}, {W2}]/10^5, cells of side {HI / DEN:.4f}, depth {DEPTH}: cost/K = '
          f'{total / K:.5f}; {searched["calls"]} boxes searched; {len(parts)} parts in {len(files) - 2} files, {nrow} '
          f'cells of the first prime cut by the second; predicted seconds of the kernel {sum(times):.0f}, a part at '
          f'most {max(times):.0f}')
    if '--stats' in sys.argv:
        print('work:', searched)
        for k, p in enumerate(parts):
            print(f'part {k}: {times[k]:.1f} s', p[6])
    if '--check' in sys.argv:
        there = sorted(f for f in os.listdir(PNT)
                       if f.startswith(f'SieveTree{TAG}P') or f in (f'SieveGrid{TAG}.lean', f'Linnik{TAG}.lean'))
        bad = [n for n, t in files.items()
               if not os.path.exists(os.path.join(PNT, n)) or open(os.path.join(PNT, n), encoding='utf-8').read() != t]
        bad += [n for n in there if n not in files]
        print('TREE', TAG, 'FAIL: ' + ', '.join(bad) if bad else 'PASS')
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
