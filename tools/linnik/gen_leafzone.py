#!/usr/bin/env python3
"""The zone of the leaves with the fourth moment: the region `LeafZone` and its proof (`lib/pnt/SieveLeafZone.lean`).

    python3 tools/linnik/gen_leafzone.py            write the Lean file
    python3 tools/linnik/gen_leafzone.py --check    fail if the file on disk differs from what would be written
    python3 tools/linnik/gen_leafzone.py --table    the region's inequalities, and its extent at some exponents

A leaf of Buchstab's tree is a sum over `n = d₁d₂k` with `d₁` (with the cofactor's small primes and anything else of
arbitrary coefficients) of length `q^{m₁}`, the cofactor `k` of length `q^{m₂}`, `m₂ ≤ 1/2`, and the primes of `d₂`
a rest of length `q^ρ`, `ρ = L − m₁ − m₂`. Proposition 3′ in two variables with the fourth moment
(`SieveTwoTypeII4.typeII_two_gen4`) evaluates it when the zone's condition `ZoneOK4` holds: for every
`β ∈ [1/2, 11/12]` and `w ∈ [0, 4·10⁻⁶]` there are exponents `M₁`, `M₂` with

    ρ(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000.

The curve is `g7d` (`SieveCurve7D`): `1` below `4/7`, then Ingham's, Chen, Gupta and Li's and Huxley's steps
`A(1 − β)`, and `(101/50)(1 − β)` from `5/6`. On each piece the modes (`SieveTwoPieces4`) are:

* below `4/7` (the curve `1`), both variables by orthogonality, `M_i = max(m_i, 1)` (`zonePiece4_OO`);
* on a step where the curve is at least `T = 1/2 − 2e` at the step's right end, `d₁` by orthogonality and the
  cofactor by the fourth moment, `M₂ = max(m₂, A(1 − β)/2 + 1/2 + 2e)` (`zonePiece4_OE`);
* on the other steps, `d₁` by the Halász–Montgomery inequality, `M₁ = max(m₁, A(1 − β) + 5/12 + m₁/12 + d(1 − m₁)
  + 2e)`, and the cofactor by the fourth moment (`zonePiece4_HE`).

Each case at an end of a piece is linear in `(m₁, m₂, ρ)`. The region is the box below cut by the cases that bind:
starting from the box, the case most violated at a vertex of the region is added to it, until every case holds at
every vertex (exact rationals). So every inequality of the region is a case of the proof (none is stronger than the
zone needs), and the Lean proof of each case is `linarith` from the region's inequalities.

    box:  9/10 ≤ m₁ ≤ 6/5,   2/5 ≤ m₂ ≤ 1/2,   3/10 ≤ ρ ≤ 1.

Needs Python 3 only (and `route_limits.py` for the curve).
"""
import itertools
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

PNT = os.path.join(HERE, '..', '..', 'lib', 'pnt')
OUT = os.path.join(PNT, 'SieveLeafZone.lean')
D = E = Fr(1, 1000)
W = Fr(4, 10 ** 6)
T = Fr(1, 2) - 2 * E
BOX = dict(m1=(Fr(9, 10), Fr(6, 5)), m2=(Fr(2, 5), Fr(1, 2)), rho=(Fr(3, 10), Fr(1)))

# a linear form a·m₁ + b·m₂ + c·ρ + k, as a tuple (a, b, c, k); a constraint is form ≤ 0


def lin(a=0, b=0, c=0, k=0):
    return (Fr(a), Fr(b), Fr(c), Fr(k))


def add(f, g):
    return tuple(x + y for x, y in zip(f, g))


def scale(s, f):
    return tuple(s * x for x in f)


def ev(f, v):
    return f[0] * v[0] + f[1] * v[1] + f[2] * v[2] + f[3]


def cands(mode, A, beta):
    """The candidates `c₁` and `c₂` of a mode at `β`, as forms (with `m` itself first)."""
    m1, m2 = lin(a=1), lin(b=1)
    one = lin(k=1)
    if mode == 'OO':
        return [m1, one], [m2, one]
    g = A * (1 - beta)
    energy = lin(k=g / 2 + Fr(1, 2) + 2 * E)
    if mode == 'OE':
        return [m1, one], [m2, energy]
    hm = lin(a=Fr(1, 12) - D, k=g + Fr(5, 12) + D + 2 * E)
    return [m1, hm], [m2, energy]


def case_form(beta, c1, c2):
    """`ρ(β + w) + (m₁ + c₁)/2 + (m₂ + c₂)/2 − (ρ + m₁ + m₂ − 1/25000)`, at `w = 4·10⁻⁶`."""
    f = lin(c=beta + W)
    f = add(f, scale(Fr(1, 2), add(lin(a=1), c1)))
    f = add(f, scale(Fr(1, 2), add(lin(b=1), c2)))
    f = add(f, lin(a=-1, b=-1, c=-1, k=Fr(1, 25000)))
    return f


def pieces():
    """The pieces of `g7d` with their modes: `(lo, hi, A, mode)`."""
    out = []
    for lo, hi, A in rl.parse('g7d'):
        if A is None:
            out.append((lo, hi, None, 'OO'))
        else:
            out.append((lo, hi, A, 'OE' if A * (1 - hi) >= T else 'HE'))
    return out


def cases():
    """Every case of the proof: `(piece index, β, i₁, i₂, form)`."""
    out = []
    for k, (lo, hi, A, mode) in enumerate(pieces()):
        for beta in (lo, hi):
            c1s, c2s = cands(mode, A, beta)
            for i1, c1 in enumerate(c1s):
                for i2, c2 in enumerate(c2s):
                    out.append((k, beta, i1, i2, case_form(beta, c1, c2)))
    return out


def box_forms():
    (a0, a1), (b0, b1), (r0, r1) = BOX['m1'], BOX['m2'], BOX['rho']
    return [lin(a=-1, k=a0), lin(a=1, k=-a1), lin(b=-1, k=b0), lin(b=1, k=-b1), lin(c=-1, k=r0), lin(c=1, k=-r1)]


def solve3(rows):
    """The point where three forms vanish, or `None`."""
    M = [[r[0], r[1], r[2], -r[3]] for r in rows]
    for col in range(3):
        piv = next((i for i in range(col, 3) if M[i][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        for i in range(3):
            if i != col and M[i][col] != 0:
                f = M[i][col] / M[col][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[col])]
    return tuple(M[i][3] / M[i][i] for i in range(3))


def vertices(forms):
    out = set()
    for tri in itertools.combinations(forms, 3):
        v = solve3(tri)
        if v is not None and all(ev(f, v) <= 0 for f in forms):
            out.add(v)
    return out


def region():
    """The box cut by the cases that bind, and every case: `(forms, cases)`."""
    forms = box_forms()
    allc = cases()
    while True:
        V = vertices(forms)
        assert V, 'the region is empty'
        worst, wv = None, Fr(0)
        for c in allc:
            m = max(ev(c[4], v) for v in V)
            if m > wv:
                worst, wv = c, m
        if worst is None:
            return forms, allc
        forms.append(worst[4])


def fmt(x):
    x = Fr(x)
    return str(x.numerator) if x.denominator == 1 else f'{x.numerator} / {x.denominator}'


def lean_ineq(f):
    """`a·m₁ + b·m₂ + c·ρ + k ≤ 0` in Lean, with `ρ = L − m₁ − m₂`, as `lhs ≤ rhs` with positive coefficients."""
    names = ['m₁', 'm₂', '(L - m₁ - m₂)']
    lhs, rhs = [], []
    for coef, nm in zip(f[:3], names):
        if coef > 0:
            lhs.append(f'{fmt(coef)} * {nm}')
        elif coef < 0:
            rhs.append(f'{fmt(-coef)} * {nm}')
    if f[3] > 0:
        lhs.append(fmt(f[3]))
    elif f[3] < 0:
        rhs.append(fmt(-f[3]))
    return f"{' + '.join(lhs) or '0'} ≤ {' + '.join(rhs) or '0'}"


def lean_file():
    forms, _ = region()
    n = len(forms)
    hs = ', '.join(f'h{i}' for i in range(n))
    zone = ' ∧\n    '.join(lean_ineq(f) for f in forms)
    body = []
    pcs = pieces()
    for k, (lo, hi, A, mode) in enumerate(pcs):
        last = k == len(pcs) - 1
        hi_ = Fr(11, 12) if last else hi
        if mode == 'OO':
            pc = f'zonePiece4_OO (fun _ => 1) (lo := {fmt(lo)}) (hi := {fmt(hi_)}) (leafZone_le L) (by lzends)'
        else:
            pc = (f'zonePiece4_{mode} (A := {fmt(A)}) (lo := {fmt(lo)}) (hi := {fmt(hi_)}) (leafZone_le L) '
                  f'(leafZone_half L)\n        (by lzends)')
        body.append(pc if last else f'zonePiece4_glue ({pc}) <|')
    proof = '\n    '.join(body)
    return f'''/-
# The zone of the leaves with the fourth moment, for the curve `g7d`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Written by `tools/linnik/gen_leafzone.py`; do not edit.

A leaf of Buchstab's tree, `n = d₁d₂k` with `d₁` of length `q^{{m₁}}`, the cofactor `k` of length `q^{{m₂}}` and the
primes of `d₂` a rest of length `q^ρ`, `ρ = L − m₁ − m₂`, is evaluated by Proposition 3′ in two variables with the
fourth moment (`SieveTwoTypeII4.typeII_two_gen4`) on a region where the zone's condition `ZoneOK4` holds. This file
gives such a region for the curve `g7d` (`SieveCurve7D`: Ingham's, Chen, Gupta and Li's and Huxley's density
estimates), for every `L`.

* `LeafZone L m₁ m₂`: the box `9/10 ≤ m₁ ≤ 6/5`, `2/5 ≤ m₂ ≤ 1/2`, `3/10 ≤ ρ ≤ 1`, cut by {n - 6} cases of the proof
  below, the ones that bind (each a linear inequality in `(m₁, m₂, ρ)`).
* `zone_leaf`: `ZoneOK4 g7d L (1/1000) (1/1000) (LeafZone L)`, glued from the curve's pieces (`SieveTwoPieces4`):
  below `4/7` both variables by orthogonality, then `d₁` by orthogonality and the cofactor by the fourth moment
  while the curve is at least `1/2 − 2/1000`, and from there on `d₁` by the Halász–Montgomery inequality. Each
  case at an end of a piece is `linarith` from the region's inequalities.

The file imports `SieveTwoPieces4.lean` and `SieveCurve7D.lean`.
-/
import SieveTwoPieces4
import SieveCurve7D

namespace SieveTypeIIHM

open SieveCurve7D

/-- **The region of the leaves with the fourth moment**: `d₁` of length `q^{{m₁}}`, the cofactor of length `q^{{m₂}}`
(at most `√q`), the rest of length `q^{{L − m₁ − m₂}}`. -/
def LeafZone (L m₁ m₂ : ℝ) : Prop :=
  {zone}

/-- The region lies in `m₁ + m₂ ≤ L`. -/
lemma leafZone_le (L : ℝ) (m₁ m₂ : ℝ) (h : LeafZone L m₁ m₂) : m₁ + m₂ ≤ L := by
  obtain ⟨{hs}⟩ := h
  linarith

/-- The cofactor is at most `√q` on the region. -/
lemma leafZone_half (L : ℝ) (m₁ m₂ : ℝ) (h : LeafZone L m₁ m₂) : m₂ ≤ 1 / 2 := by
  obtain ⟨{hs}⟩ := h
  linarith

set_option hygiene false in
/-- The cases at the ends of a piece, each by `linarith` from the region's inequalities. -/
local macro "lzends" : tactic =>
  `(tactic| (intro β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂
             obtain ⟨{hs}⟩ := hRm
             rcases hb with rfl | rfl <;> rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl <;> linarith))

set_option maxHeartbeats 40000000 in
/-- **The zone's exponents with the fourth moment for the curve `g7d` on the region `LeafZone L`**, for every `L`. -/
theorem zone_leaf (L : ℝ) : ZoneOK4 g7d L (1 / 1000) (1 / 1000) (LeafZone L) :=
  zoneOK4_of_piece <|
    {proof}

end SieveTypeIIHM

#print axioms SieveTypeIIHM.zone_leaf
'''


def main():
    if '--table' in sys.argv[1:]:
        forms, allc = region()
        print(f'{len(forms)} inequalities ({len(forms) - 6} cases on the box), {len(allc)} cases')
        for f in forms:
            print('  ', lean_ineq(f))
        return 0
    text = lean_file()
    if '--check' in sys.argv[1:]:
        cur = open(OUT, encoding='utf-8').read() if os.path.exists(OUT) else ''
        if cur != text:
            print(f'{OUT} differs from what gen_leafzone.py writes')
            return 1
        print(f'{OUT} is current')
        return 0
    with open(OUT, 'w', encoding='utf-8') as fh:
        fh.write(text)
    print(f'wrote {OUT}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
