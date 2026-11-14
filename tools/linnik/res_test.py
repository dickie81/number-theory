#!/usr/bin/env python3
"""The resonant window's test on a box, led by a hint: the kernel's test (`lib/pnt/SieveResTestDefs.lean`), its
mirror here, and the search for its hints.

    python3 tools/linnik/res_test.py            write the Lean file
    python3 tools/linnik/res_test.py --check    fail if the file on disk differs from what would be written

A box's rest is a set of its primes, each in its cell of exponents of `x = q^L` (units of `1/DEN`): the lower ends
`c_j` and the sum `hs` of the upper ends. The variable is everything else, of exponent at least
`m = κ(DEN − hs − 1)`, and the rest's exponents are at least `lo_j = κ(c_j − 1)`, `κ = L/DEN`
(`SieveTypeIIHM.ResBox`). Its condition is that for every count exponent `γ` of a class of characters,

    F(γ) = Lτ + MARG + Σ_j U_j(γ) + γ/2 + min(c₁, max(0, y(γ))) ≤ 0,
    U_j(γ) = min(lo_j(β̄(γ) + w − 1), min_k (max(1 − k·lo_j, 0) − γ)/(2k)),

where `β̄(γ)` bounds the zeros' real parts with count exponent `γ` on the curve `ghx`, `c₁ = max(1 − m, 0)/2` and
`y(γ) = γ/2 + (5/12 + d + 2e − m(11/12 + d))/2` (the two inequalities of Halász and Montgomery). For `γ ≤ 0` the
half-plane at `11/12` bounds it. On `[0, 1]` a hint cuts the range of `γ` into intervals and names, on each, a line
above each term; the kernel checks the sum of the lines at the two ends of each interval, in fixed point
(`S = 2^64`, every quantity rounded the way that keeps the sum above `F`). The lines on `[a, b]`, with `a` in the
curve's piece `pa` and `b` in `pb` (pieces from the top, `17` the trivial count):

* `kA`, `kB`: the moments' lines for `k = k₀ − 1` and `k₀ = ⌈1/lo⌉`;
* `C`: `lo(β̄(a) + w − 1)`, `β̄(a) = min(hi_pa, 1 − a/A_pa)` (`β̄` does not increase);
* `W`: `lo(w − γ/A)`, `A = max(A_pa, A_pb)`, above `lo(β̄(γ) + w − 1)` on `[a, b]` since the steps' `A` fall then rise;

and for the clamp `max(0, y(b))`, `y + max(0, −y(a))` and `c₁`. A hint is, for each interval, its right end on the
grid `2^-24` (25 bits, `2^24` for `γ = 1`), the piece of that end (5 bits), the clamp's line (2 bits) and each term's
line (2 bits each), the first interval in the lowest bits.
"""
import argparse
import difflib
import pathlib
import sys
from fractions import Fraction as Fr

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import route_limits as rl  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / 'lib' / 'pnt' / 'SieveResTestDefs.lean'

S = 1 << 64
DEN = 1 << 40
G24 = 24
SLOT = 96
W = Fr(4, 10 ** 6)
TAU = Fr(1, 10 ** 6)
MARG = Fr(1, 25000)
DD = EE = Fr(1, 1000)

_P = rl.parse('ghx')
HUX = [p for p in _P if p[2] is not None][::-1]       # top first: (lo, hi, A)
NP = len(HUX)                                         # 17; the piece NP is the trivial count
CONST_HI = _P[0][1]                                   # 7789/10000
TOPS = [A * (1 - lo) for lo, hi, A in HUX]


def fl(x):
    """floor(x S) for a nonnegative fraction."""
    return (x.numerator * S) // x.denominator


def ce(x):
    """ceil(x S) for a nonnegative fraction."""
    return -((-x.numerator * S) // x.denominator)


FT = [fl(t) for t in TOPS] + [S]
FTM = [0] + [fl(t) for t in TOPS]
IA = [S * A.denominator // A.numerator for lo, hi, A in HUX] + [0]
DH = [fl(1 - W - hi) for lo, hi, A in HUX] + [fl(1 - W - CONST_HI)]
WC = ce(W)
MG = ce(MARG)
K1U = ce(Fr(5, 12) + DD + 2 * EE)
K1D = fl(Fr(5, 12) + DD + 2 * EE)
M1U = ce(Fr(11, 12) + DD)
M1D = fl(Fr(11, 12) + DD)
HP = fl(1 - W - Fr(11, 12))
MSK = (1 << SLOT) - 1


def pack(vals):
    n = 0
    for i, v in enumerate(vals):
        assert 0 <= v < 1 << SLOT
        n |= v << (SLOT * i)
    return n


# ---------------------------------------------------------------------------------------------------------------
# The kernel's test, as the Lean computes it.

def sub(a, b):
    return a - b if a > b else 0


def mulF(x, y):
    return (x * y) >> 64


def mulC(x, y):
    return (x * y + S - 1) >> 64


def mkTm(lo):
    """(lo, a0, a1, b1, lw)."""
    k0 = (S + sub(lo, 1)) // lo if lo else 0
    if k0 <= 1:
        a0, a1 = S * S, 0
    else:
        k = k0 - 1
        a0 = (sub(S, k * lo) + sub(2 * k, 1)) // (2 * k)
        a1 = S // (2 * k)
    b1 = S // (2 * k0) if k0 else 0
    return (lo, a0, a1, b1, mulC(lo, WC))


def loOf(Lnum, Lden, c):
    return (Lnum * sub(c, 1) * S) // (Lden * DEN)


def addTerms(dS, iax, ts, h, p0, n0, n1):
    for lo, a0, a1, b1, lw in ts:
        c = h & 3
        h >>= 2
        if c == 0:
            p0, n1 = p0 + a0, n1 + a1
        elif c == 1:
            n1 = n1 + b1
        elif c == 2:
            n0 = n0 + mulF(lo, dS)
        else:
            p0, n1 = p0 + lw, n1 + mulF(lo, iax)
    return p0, n0, n1


def le0(p0, p1, n0, n1, x):
    return p0 + mulC(p1, x) <= n0 + mulF(n1, x)


def get(t, p):
    return (t >> (SLOT * p)) & MSK


TFT, TFTM, TIA, TDH = pack(FT), pack(FTM), pack(IA), pack(DH)


def intv(ts, c1, yuP, yuN, ydP, ydN, ltm, a, pa, r):
    b, pb, cc = (r & 0x1FFFFFF) << 40, (r >> 25) & 31, (r >> 30) & 3
    if not (pb <= 17 and get(TFTM, pb) < b and b <= get(TFT, pb) and a <= b):
        return False
    dS = max(get(TDH, pa), sub(mulF(a, get(TIA, pa)), WC))
    iax = min(get(TIA, pa), get(TIA, pb))
    if cc == 0:
        cp0, cp1, cn0 = sub(((b + 1) >> 1) + yuP, yuN), 0, 0
    elif cc == 1:
        cp0, cp1, cn0 = yuP + sub(ydN, (a >> 1) + ydP), S // 2, yuN
    else:
        cp0, cp1, cn0 = c1, 0, 0
    p0, n0, n1 = addTerms(dS, iax, ts, r >> 32, ltm + cp0, cn0, 0)
    p1 = S // 2 + cp1
    return le0(p0, p1, n0, n1, a) and le0(p0, p1, n0, n1, b)


def resT(Lnum, Lden, cs, hs, k, h):
    """The test: the rest's lower cells `cs`, the sum `hs` of its upper ends, `k` intervals in the hint `h`."""
    ts = [mkTm(loOf(Lnum, Lden, c)) for c in cs]
    mlo = (Lnum * sub(sub(DEN, hs), 1) * S) // (Lden * DEN)
    ltm = (Lnum * S + sub(Lden * 10 ** 6, 1)) // (Lden * 10 ** 6) + MG
    mtu, mtd = mulC(mlo, M1U), mulF(mlo, M1D)
    c1 = (sub(S, mlo) + 1) >> 1
    yuP, yuN = (sub(K1U, mtd) + 1) >> 1, sub(mtd, K1U) >> 1
    ydP, ydN = sub(K1D, mtu) >> 1, (sub(mtu, K1D) + 1) >> 1
    if not (hs + 1 < DEN and ltm + min(c1, yuP) <= sum(mulF(t[0], HP) for t in ts)):
        return False
    w = 32 + 2 * len(ts)
    a, pa = 0, 0
    for _ in range(k):
        r = h & ((1 << w) - 1)
        if not intv(ts, c1, yuP, yuN, ydP, ydN, ltm, a, pa, r):
            return False
        a, pa, h = (r & 0x1FFFFFF) << 40, (r >> 25) & 31, h >> w
    return a == S


# ---------------------------------------------------------------------------------------------------------------
# The hints: on each interval, for a few points between its ends, each term's least line there; the intervals by a
# greedy cover from the left, each as far as some choice passes (the curve's and the clamp's kinks first, then a
# binary search on the grid).

class Box:
    """The test's state for one box, with the hint search."""

    def __init__(self, Lnum, Lden, cs, hs):
        self.Lnum, self.Lden, self.cs, self.hs = Lnum, Lden, cs, hs
        self.ts = [mkTm(loOf(Lnum, Lden, c)) for c in cs]
        mlo = (Lnum * sub(sub(DEN, hs), 1) * S) // (Lden * DEN)
        self.ltm = (Lnum * S + sub(Lden * 10 ** 6, 1)) // (Lden * 10 ** 6) + MG
        mtu, mtd = mulC(mlo, M1U), mulF(mlo, M1D)
        self.c1 = (sub(S, mlo) + 1) >> 1
        self.yuP, self.yuN = (sub(K1U, mtd) + 1) >> 1, sub(mtd, K1U) >> 1
        self.ydP, self.ydN = sub(K1D, mtu) >> 1, (sub(mtu, K1D) + 1) >> 1
        self.ok = hs + 1 < DEN and self.ltm + min(self.c1, self.yuP) <= sum(mulF(t[0], HP) for t in self.ts)
        self.y0 = self.yuP - self.yuN

    def rec(self, e, pb, ch, cc):
        r = e | pb << 25 | cc << 30
        for j, c in enumerate(ch):
            r |= c << (32 + 2 * j)
        return r

    def try_choice(self, aS, pa, e, pb):
        """Some choices that pass on [a, e 2^-24], as a record, or None."""
        bS = e << 40
        ts = self.ts
        dS = max(DH[pa], sub(mulF(aS, IA[pa]), WC))
        iax = min(IA[pa], IA[pb])
        cl = [(sub(((bS + 1) >> 1) + self.yuP, self.yuN), 0, 0),
              (self.yuP + sub(self.ydN, (aS >> 1) + self.ydP), S // 2, self.yuN),
              (self.c1, 0, 0)]

        def v(ln, x):
            p0, p1, n0, n1 = ln
            return p0 + mulC(p1, x) - n0 - mulF(n1, x)
        lines = []
        for lo, a0, a1, b1, lw in ts:
            lines.append([(a0, 0, 0, a1), (0, 0, 0, b1), (0, 0, mulF(lo, dS), 0), (lw, 0, 0, mulF(lo, iax))])
        for lam in (0.5, 0.0, 1.0, 0.25, 0.75, 0.1, 0.9):
            xS = int(lam * aS + (1 - lam) * bS)
            ch = [min(range(4), key=lambda i: v(ln[i], xS)) for ln in lines]
            cc = min(range(3), key=lambda i: v((cl[i][0], cl[i][1], cl[i][2], 0), xS))
            r = self.rec(e, pb, ch, cc)
            if intv(ts, self.c1, self.yuP, self.yuN, self.ydP, self.ydN, self.ltm, aS, pa, r):
                return r
        return None

    def kinks(self):
        pts = set()
        for (lo, hi, A), t in zip(HUX, TOPS):
            pts.add(fl(t))
            pts.add(fl(A * (1 - hi)))
        g0 = -2 * self.y0
        pts.add(g0)
        pts.add(g0 + 2 * self.c1)
        for lo, a0, a1, b1, lw in self.ts:
            k0 = (S + lo - 1) // lo if lo else 0
            if k0 >= 2:
                pts.add(k0 * sub(S, (k0 - 1) * lo))
        out = set()
        for x in pts:
            e = x >> 40
            if 0 < e < 1 << G24:
                out.add(e)
                out.add(e + 1)
        return sorted(out)

    def find(self, maxint=15):
        """(k, h) for the test, or None."""
        if not self.ok:
            return None
        K = self.kinks()
        aS, pa, recs = 0, 0, []
        while aS < S:
            if len(recs) >= maxint:
                return None
            a24 = aS >> 40

            def feas(e):
                return self.try_choice(aS, pa, e, piece_of(e << 40))
            r = feas(1 << G24)
            if r is None:
                cand = [e for e in K if e > a24]
                lo_e, best = a24, None
                for e in cand:
                    rr = feas(e)
                    if rr is not None:
                        lo_e, best = e, rr
                hi_e = next((e for e in cand if e > lo_e), 1 << G24)
                while hi_e - lo_e > 1:
                    mid = (lo_e + hi_e) // 2
                    rr = feas(mid)
                    if rr is not None:
                        lo_e, best = mid, rr
                    else:
                        hi_e = mid
                if best is None:
                    return None
                r = best
            recs.append(r)
            aS, pa = (r & 0x1FFFFFF) << 40, (r >> 25) & 31
        w = 32 + 2 * len(self.ts)
        h = 0
        for i, r in enumerate(recs):
            h |= r << (w * i)
        return len(recs), h


def piece_of(xS):
    for p in range(NP):
        if xS <= FT[p]:
            return p
    return NP


def hint(Lnum, Lden, cs, hs):
    """The test's hint (k, h) for the rest's cells, or None; checked by the mirror of the kernel's test."""
    r = Box(Lnum, Lden, cs, hs).find()
    if r is not None:
        assert resT(Lnum, Lden, cs, hs, *r)
    return r


# ---------------------------------------------------------------------------------------------------------------
# The Lean file.

def lean():
    num = lambda x: str(x)  # noqa: E731
    pieces = '\n'.join(f'  {p:2d}: [{lo}, {hi}], A = {A}' for p, (lo, hi, A) in enumerate(HUX))
    return f'''/-
# The resonant window's test on a box, led by a hint, in natural numbers, without Mathlib

Generated by `tools/linnik/res_test.py`; do not edit by hand.

The condition `SieveTypeIIHM.ResBox` on a box's rest (lower cells `c_j`, upper ends' sum `hs`, in units of `1/DEN` of
exponents of `x = q^L`): for every count exponent `γ` of a class of characters,
`F(γ) = Lτ + MARG + Σ_j U_j(γ) + γ/2 + min(c₁, max(0, y(γ))) ≤ 0` with
`U_j(γ) = min(lo_j(β̄(γ) + w − 1), min_k (max(1 − k·lo_j, 0) − γ)/(2k))`, `lo_j = κ(c_j − 1)`, the variable's exponent
`m ≥ κ(DEN − hs − 1)`, `c₁ = max(1 − m, 0)/2`, `y(γ) = γ/2 + (5/12 + d + 2e − m(11/12 + d))/2`, and `β̄(γ)` the largest
real part of a zero on the curve `ghx` with count exponent `γ`. The half-plane at `11/12` bounds it for `γ ≤ 0`; on
`[0, 1]` the hint cuts the range of `γ` into intervals and names a line above each term on each, and `resT` checks
the sum of the lines at the ends of each interval. Everything is in fixed point, `S = 2^64`, rounded so that the sum
stays above `F`. Its soundness is `SieveResTest.resT_sound`.

The curve's steps, from the top (piece `17` is the trivial count, below `{CONST_HI}`), `[lo, hi]` and `A`:
{pieces}

* `tFT`, `tFTm`, `tIA`, `tDH`: tables of 96-bit entries by piece: `⌊A(1 − lo)·S⌋` (the largest `γ` of the piece;
  `S` for piece `17`), the same one piece up (`0` for piece `0`), `⌊S/A⌋` (`0` for piece `17`) and
  `⌊(1 − w − hi)·S⌋`.
* `Tm`, `mkTm`: a term's constants. `addTerms`: the sum of the terms' lines that the hint names. `le0`: a line is at
  most `0` at a point. `clampL`: the clamp's line. `chkI`: the check at an interval's ends. `intv`: one interval.
  `runI`: the intervals. `hpSum`: the half-plane's sum. `resTM`, `resT`: **the test**.
-/

namespace SieveResTest

/-- The fixed point's unit `S = 2^64`. -/
def S : Nat := {S}

/-- `S − 1`. -/
def SM : Nat := {S - 1}

/-- `S/2`. -/
def H : Nat := {S // 2}

/-- `S² = 2^128`: the constant of a line that is no bound (where `k₀ ≤ 1`). -/
def SS : Nat := {S * S}

/-- `DEN = 2^40`, the cells' unit. -/
def DEN : Nat := {DEN}

/-- `2^96 − 1`. -/
def MSK : Nat := {MSK}

/-- `⌊xy/S⌋`. -/
def mulF (x y : Nat) : Nat := Nat.shiftRight (Nat.mul x y) 64

/-- `⌈xy/S⌉`. -/
def mulC (x y : Nat) : Nat := Nat.shiftRight (Nat.add (Nat.mul x y) SM) 64

/-- The smaller of two numbers. -/
def minN (a b : Nat) : Nat := cond (Nat.ble a b) a b

/-- The larger of two numbers. -/
def maxN (a b : Nat) : Nat := cond (Nat.ble a b) b a

/-- The entry `p` of a table of 96-bit entries. -/
def get (t p : Nat) : Nat := Nat.land (Nat.shiftRight t (Nat.mul 96 p)) MSK

/-- `⌊A(1 − lo)·S⌋` by piece, the largest `γ` of the piece in fixed point; `S` for piece `17`. -/
def tFT : Nat := {num(TFT)}

/-- `tFT` one piece up: `0` for piece `0`. -/
def tFTm : Nat := {num(TFTM)}

/-- `⌊S/A⌋` by piece; `0` for piece `17`. -/
def tIA : Nat := {num(TIA)}

/-- `⌊(1 − w − hi)·S⌋` by piece, `w = 4·10⁻⁶`; `hi = {CONST_HI}` for piece `17`. -/
def tDH : Nat := {num(TDH)}

/-- `⌈w·S⌉`. -/
def WC : Nat := {WC}

/-- `⌈S/25000⌉`, the margin. -/
def MG : Nat := {MG}

/-- `⌈(5/12 + d + 2e)·S⌉`, `d = e = 1/1000`. -/
def K1U : Nat := {K1U}

/-- `⌊(5/12 + d + 2e)·S⌋`. -/
def K1D : Nat := {K1D}

/-- `⌈(11/12 + d)·S⌉`. -/
def M1U : Nat := {M1U}

/-- `⌊(11/12 + d)·S⌋`. -/
def M1D : Nat := {M1D}

/-- `⌊(1 − w − 11/12)·S⌋`, the half-plane's. -/
def HP : Nat := {HP}

/-- A term of the rest: `lo` (its exponent's lower bound, times `S`); the line `(a0 − γ·a1)/S` of `k = k₀ − 1`,
`k₀ = ⌈S/lo⌉` (`a0 = S²` where `k₀ ≤ 1`); the slope `b1` of the line `−γ·b1/S` of `k₀`; and `lw = ⌈lo·w⌉`. -/
structure Tm where
  /-- The exponent's lower bound, times `S`. -/
  lo : Nat
  /-- The constant of the line of `k₀ − 1`, times `S`. -/
  a0 : Nat
  /-- The slope of the line of `k₀ − 1`, times `S`. -/
  a1 : Nat
  /-- The slope of the line of `k₀`, times `S`. -/
  b1 : Nat
  /-- `⌈lo·w⌉`. -/
  lw : Nat

/-- A term's constants with `k₀` given. -/
def mkTmK (lo k0 : Nat) : Tm :=
  ⟨lo,
    cond (Nat.ble k0 1) SS
      (Nat.div (Nat.add (Nat.sub S (Nat.mul (Nat.sub k0 1) lo)) (Nat.sub (Nat.mul 2 (Nat.sub k0 1)) 1))
        (Nat.mul 2 (Nat.sub k0 1))),
    cond (Nat.ble k0 1) 0 (Nat.div S (Nat.mul 2 (Nat.sub k0 1))),
    Nat.div S (Nat.mul 2 k0),
    mulC lo WC⟩

/-- A term's constants: `k₀ = ⌈S/lo⌉`. -/
def mkTm (lo : Nat) : Tm := mkTmK lo (Nat.div (Nat.add S (Nat.sub lo 1)) lo)

/-- `⌊κ(c − 1)·S⌋`, `κ = L/DEN`. -/
def loOf (Lnum Lden c : Nat) : Nat := Nat.div (Nat.mul (Nat.mul Lnum (Nat.sub c 1)) S) (Nat.mul Lden DEN)

/-- The terms' lines named by the hint `h` (two bits each: the lines of `k₀ − 1` and `k₀`, `C` with `dS`, `W` with
`iax`), added to `(P0, N0, N1)`. -/
def addTerms (dS iax : Nat) : List Tm → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | [], _, p0, n0, n1 => (p0, n0, n1)
  | t :: ts, h, p0, n0, n1 =>
    (fun c =>
      cond (Nat.beq c 0) (addTerms dS iax ts (Nat.shiftRight h 2) (Nat.add p0 t.a0) n0 (Nat.add n1 t.a1))
        (cond (Nat.beq c 1) (addTerms dS iax ts (Nat.shiftRight h 2) p0 n0 (Nat.add n1 t.b1))
          (cond (Nat.beq c 2) (addTerms dS iax ts (Nat.shiftRight h 2) p0 (Nat.add n0 (mulF t.lo dS)) n1)
            (addTerms dS iax ts (Nat.shiftRight h 2) (Nat.add p0 t.lw) n0 (Nat.add n1 (mulF t.lo iax))))))
      (Nat.land h 3)

/-- The line `(P0 + P1·γ − N0 − N1·γ)/S` is at most `0` at `γ = x/S`. -/
def le0 (p0 p1 n0 n1 x : Nat) : Bool := Nat.ble (Nat.add p0 (mulC p1 x)) (Nat.add n0 (mulF n1 x))

/-- The clamp's line `(P0, P1, N0)` by `cc`: `max(0, y(b))`, `y + max(0, −y(a))`, `c₁`. -/
def clampL (c1 yuP yuN ydP ydN a b cc : Nat) : Nat × Nat × Nat :=
  cond (Nat.beq cc 0) (Nat.sub (Nat.add (Nat.shiftRight (Nat.add b 1) 1) yuP) yuN, 0, 0)
    (cond (Nat.beq cc 1) (Nat.add yuP (Nat.sub ydN (Nat.add (Nat.shiftRight a 1) ydP)), H, yuN) (c1, 0, 0))

/-- The sum's check on `[a, b]` with the terms' and the clamp's lines. -/
def chkI (ts : List Tm) (ltm dS iax a b ch : Nat) (cl : Nat × Nat × Nat) : Bool :=
  (fun s => le0 s.1 (Nat.add H cl.2.1) s.2.1 s.2.2 a && le0 s.1 (Nat.add H cl.2.1) s.2.1 s.2.2 b)
    (addTerms dS iax ts ch (Nat.add ltm cl.1) cl.2.2 0)

/-- A record's right end `b`: 25 bits on the grid `2^-24`, times `S`. -/
def bOf (r : Nat) : Nat := Nat.shiftLeft (Nat.land r 33554431) 40

/-- A record's piece of its right end: 5 bits. -/
def pbOf (r : Nat) : Nat := Nat.land (Nat.shiftRight r 25) 31

/-- **One interval** `[a, b]` with the record `r`: `b = bOf r`, its piece `pbOf r`, the clamp's line (2 bits from
bit 30) and the terms' lines (from bit 32). `a` is in the piece `pa`. -/
def intv (ts : List Tm) (c1 yuP yuN ydP ydN ltm a pa r : Nat) : Bool :=
  (fun b pb =>
    Nat.ble pb 17 && Nat.blt (get tFTm pb) b && Nat.ble b (get tFT pb) && Nat.ble a b &&
      chkI ts ltm (maxN (get tDH pa) (Nat.sub (mulF a (get tIA pa)) WC)) (minN (get tIA pa) (get tIA pb)) a b
        (Nat.shiftRight r 32) (clampL c1 yuP yuN ydP ydN a b (Nat.land (Nat.shiftRight r 30) 3)))
    (bOf r) (pbOf r)

/-- **The intervals**, `k` of them from `(a, pa)`, each a record of `w` bits of `h`; the last ends at `S`. -/
def runI (ts : List Tm) (w c1 yuP yuN ydP ydN ltm : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun a _ _ => Nat.beq a S)
    (fun _ ih a pa h =>
      (fun r => intv ts c1 yuP yuN ydP ydN ltm a pa r && ih (bOf r) (pbOf r) (Nat.shiftRight h w))
        (Nat.land h (Nat.sub (Nat.shiftLeft 1 w) 1)))

/-- The half-plane's sum `Σ ⌊lo·HP/S⌋` over the terms. -/
def hpSum : List Tm → Nat
  | [] => 0
  | t :: ts => Nat.add (mulF t.lo HP) (hpSum ts)

/-- The test with the variable's `m` times `S` (`mlo`) and `Lτ + MARG` times `S` (`ltm`) given. -/
def resTM (ts : List Tm) (mlo ltm k h : Nat) : Bool :=
  (fun mtu mtd c1 =>
    (fun yuP yuN ydP ydN =>
      Nat.ble (Nat.add ltm (minN c1 yuP)) (hpSum ts) &&
        runI ts (Nat.add 32 (Nat.mul 2 ts.length)) c1 yuP yuN ydP ydN ltm k 0 0 h)
      (Nat.shiftRight (Nat.add (Nat.sub K1U mtd) 1) 1) (Nat.shiftRight (Nat.sub mtd K1U) 1)
      (Nat.shiftRight (Nat.sub K1D mtu) 1) (Nat.shiftRight (Nat.add (Nat.sub mtu K1D) 1) 1))
    (mulC mlo M1U) (mulF mlo M1D) (Nat.shiftRight (Nat.add (Nat.sub S mlo) 1) 1)

/-- **The test** at `L = Lnum/Lden`: the rest's lower cells `cs`, the sum `hs` of its upper ends, `k` intervals in
the hint `h`. -/
def resT (Lnum Lden : Nat) (cs : List Nat) (hs k h : Nat) : Bool :=
  Nat.blt (Nat.add hs 1) DEN &&
    resTM (cs.map fun c => mkTm (loOf Lnum Lden c))
      (Nat.div (Nat.mul (Nat.mul Lnum (Nat.sub (Nat.sub DEN hs) 1)) S) (Nat.mul Lden DEN))
      (Nat.add (Nat.div (Nat.add (Nat.mul Lnum S) (Nat.sub (Nat.mul Lden 1000000) 1)) (Nat.mul Lden 1000000)) MG)
      k h

end SieveResTest
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args()
    text = lean()
    if a.check:
        old = OUT.read_text() if OUT.exists() else ''
        if old != text:
            sys.stdout.writelines(difflib.unified_diff(old.splitlines(True), text.splitlines(True), str(OUT), 'new'))
            sys.exit(1)
        return
    OUT.write_text(text)
    print('wrote', OUT)


if __name__ == '__main__':
    main()
