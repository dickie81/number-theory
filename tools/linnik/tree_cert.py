#!/usr/bin/env python3
"""tree_cert.py --try H DEPTH [W1 W2 a/b]: the search for a tree of Buchstab steps with the window's tests and those
of the estimate in two variables, and the base of the searches of `rev_cert.py`, `fill_cert.py`, `flip_cert.py` and
`hint_cert.py`.

A tree of `lib/pnt/SieveAdDefs.lean` on the box of the first prime, of cost below K, gives Linnik's theorem
(`SieveAd.linnik_tree`). The search returns a cost and no tree. This script has, in Python:

  * the tests (`Tests`): the window's, `okIW` with mirror8.py's `surelyEval` and `okJW` with `ibOK`, built here from
    mirror8.py's `tstar`, `condIB`, `subsetSums` and `hiSum`; and those of the estimate in two variables, `okI2`,
    `okJ2` (SieveAdTwoDefs.lean), the leaves cut in three only with `energy`;
  * `vanishOK`, `dropOK`, `dropCost`, `dropBOK`, `dropBCost` (SieveAdDefs.lean), definition by definition;
  * the search (`Search`): the searches over the sets of a box's cells `findSub2`, `bestSub`, `findSub1`,
    `tstarF`, and the steps `anyI`, `firstJ`, `kids`, `buchC` and `splitC`, definition by definition as
    `lib/pnt/SieveAdSearchDefs.lean` has them, and `node` and `step` (as `solve`, with the fuel of the recursion)
    as it had them until 18 November 2026 (in the git history at commit 99ea246), with the proposals of the
    configurations, the floors and the cuts.

The window's tests, the proposals and the recursion are those of the theorem at L = 219/100, whose Lean is in the
git history at commit 76abe3c.

A box is a list of cells (lo, hi), the newest prime first, in units of 1/DEN of exponents of x. The search treats a
box so: no term, or evaluated by the window or by the estimate in two variables (rest: one prime; first variable: a
set of the others in the window that the rest leaves), costs 0; otherwise it is dropped, if its sign is +, or
decomposed by Buchstab's identity at the largest floor at which the comparison passes, the new prime's range cut
into cells of side H (coarser from the fifth prime on), whichever is cheaper; a box that can be neither dropped
nor decomposed is cut in two, down to the width WMIN. A box of DEPTH primes is not decomposed. A limit stops the
search of a subtree whose cost reaches it. `pred` predicts the kernel's time on a part of the search from the
search's work in it (a least-squares fit to the kernel's checks of seventeen parts, of 26 to 63 seconds, with an
error of at most five seconds); `rev_cert.py` and `fill_cert.py` build their predictions on it.

What is here is what the other scripts import, and `--try`, which runs the search with cells of side H and boxes of
fewer than DEPTH primes decomposed, on the window [W1, W2]/10^5 at L = a/b (by default [44260, 46717]/10^5 at
219/100), and prints its cost.

Values (11 November 2026), at 219/100: `--try 0.006 6`: 0.98189, 301834 boxes; `--try 0.005 6`: 0.93489, 547117
boxes; `--try 0.005 8`: 0.92462, 558412; `--try 0.006 8`: 0.96227, 311103; `--try 0.0065 6`: 1.00099.

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

# the route of `--try` when none is given, the least width of a cell that is cut for want of a test, and the fuel
LNUM, LDEN, W1, W2 = 219, 100, 44260, 46717
WMIN, FUEL = round(0.0005 * DEN), 200
BIG = 2 ** 70
CFGW = (0, 0, 0, 0, False)


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
    """The window's tests and those of the estimate in two variables on the grid of the window and `IBPar ⟨Ln, Ld⟩`
    (`okI` and `okJ` take a configuration of kind `0` to the window, any other to the estimate). The kernel's
    `chkJ2` and `coreJ2` take the leaves cut in three where the paper's conditions fail (`SieveAd.leavesE`,
    `lib/pnt/SieveAdLeafDefs.lean`); the planner proposes such leaves, and its tests accept them, only with
    `energy`."""

    energy = False

    def __init__(self, W1, W2, Ln, Ld):
        self.U1, self.U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
        self.V = self.U2 - self.U1
        self.Ln, self.Ld = Ln, Ld
        m8.G.update(U1=self.U1, U2=self.U2, Lnum=Ln, Lden=Ld)

    # the window's tests
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

    # the tests of either kind, by the configuration's kind
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
    """The search with these tests, cells of side at most hI (`stepOf`), boxes of fewer than `depth` primes
    decomposed and cells cut in two down to the width `wmin`, with counts of its work."""

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
        """`kids` of SieveAdSearchDefs.lean, with `solve` at the fuel `n` for `rec`."""
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
        """`step` of SieveAdSearchDefs.lean at commit 99ea246, with `solve` at the fuel `n − 1` for `rec`; at the fuel
        0, the limit."""
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


def rowCuts(T, hI, wmin):
    """The ends of the cells of the first prime: steps of at most hI from V to DEN/2 + 1, the window's ends, and a
    thin cell at the top (the corner where two primes are near x^{1/2} costs its width)."""
    top = DEN // 2 + 1
    n = max(1, cdiv(top - T.V, hI))
    return sorted({T.V + (top - T.V) * j // n for j in range(n + 1)} | {T.U1 + 1, T.U2 - 1, DEN // 2 - wmin})


def search_only(h, depth, w1, w2, ln, ld):
    """The cost of the search with other parameters, and the number of boxes searched."""
    T = Tests(w1, w2, ln, ld)
    hI = round(h * DEN)
    S = Search(T, hI, depth, WMIN)
    sys.setrecursionlimit(100000)
    cuts = rowCuts(T, hI, WMIN)
    return S.kids(DEN // 2 + 1, [], False, cuts[1:-1], cuts[0], K, FUEL), S.W['calls']


# the Lean text, as `rev_cert.py` and `hint_cert.py` write it

def wrap(s, indent='    '):
    return ('\n' + indent).join(textwrap.wrap(s, 116 - len(indent), break_long_words=False))


def nat(x):
    """A number of the grid as Lean text: `DEN / 2 + 1` for the top of the first prime's range."""
    return '(DEN / 2 + 1)' if x == DEN // 2 + 1 else str(x)


def main():
    if '--try' in sys.argv:
        a = sys.argv[sys.argv.index('--try') + 1:]
        w1, w2, (ln, ld) = (int(a[2]), int(a[3]), map(int, a[4].split('/'))) if len(a) >= 5 else (W1, W2, (LNUM, LDEN))
        c, n = search_only(float(a[0]), int(a[1]), w1, w2, ln, ld)
        print(f'L = {ln}/{ld}, window [{w1}, {w2}]/10^5, cells of side {a[0]}, depth {a[1]}: cost/K = {c / K:.5f}; '
              f'{n} boxes searched')
        return 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main())
