/-
# The zone of the leaves with the fourth moment, for the curve `g7d`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Written by `tools/linnik/gen_leafzone.py`; do not edit.

A leaf of Buchstab's tree, `n = d₁d₂k` with `d₁` of length `q^{m₁}`, the cofactor `k` of length `q^{m₂}` and the
primes of `d₂` a rest of length `q^ρ`, `ρ = L − m₁ − m₂`, is evaluated by Proposition 3′ in two variables with the
fourth moment (`SieveTwoTypeII4.typeII_two_gen4`) on a region where the zone's condition `ZoneOK4` holds. This file
gives such a region for the curve `g7d` (`SieveCurve7D`: Ingham's, Chen, Gupta and Li's and Huxley's density
estimates), for every `L`.

* `LeafZone L m₁ m₂`: the box `9/10 ≤ m₁ ≤ 6/5`, `2/5 ≤ m₂ ≤ 1/2`, `3/10 ≤ ρ ≤ 1`, cut by 7 cases of the proof
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

/-- **The region of the leaves with the fourth moment**: `d₁` of length `q^{m₁}`, the cofactor of length `q^{m₂}`
(at most `√q`), the rest of length `q^{L − m₁ − m₂}`. -/
def LeafZone (L m₁ m₂ : ℝ) : Prop :=
  9 / 10 ≤ 1 * m₁ ∧
    1 * m₁ ≤ 6 / 5 ∧
    2 / 5 ≤ 1 * m₂ ∧
    1 * m₂ ≤ 1 / 2 ∧
    3 / 10 ≤ 1 * (L - m₁ - m₂) ∧
    1 * (L - m₁ - m₂) ≤ 1 ∧
    25001 / 25000 ≤ 1 / 2 * m₁ + 1 / 2 * m₂ + 749993 / 1750000 * (L - m₁ - m₂) ∧
    12501 / 25000 ≤ 1 / 2 * m₂ + 749993 / 1750000 * (L - m₁ - m₂) ∧
    73693427 / 84000000 ≤ 1 / 2 * m₁ + 1 / 2 * m₂ + 1174979 / 5250000 * (L - m₁ - m₂) ∧
    87937 / 300000 ≤ 1 / 2 * m₂ + 62497 / 750000 * (L - m₁ - m₂) ∧
    10274479 / 11200000 ≤ 1 / 2 * m₁ + 1 / 2 * m₂ + 748427 / 2625000 * (L - m₁ - m₂) ∧
    4674479 / 11200000 ≤ 1 / 2 * m₂ + 748427 / 2625000 * (L - m₁ - m₂) ∧
    70467547 / 84000000 ≤ 2753 / 6000 * m₁ + 1 / 2 * m₂ + 1174979 / 5250000 * (L - m₁ - m₂)

/-- The region lies in `m₁ + m₂ ≤ L`. -/
lemma leafZone_le (L : ℝ) (m₁ m₂ : ℝ) (h : LeafZone L m₁ m₂) : m₁ + m₂ ≤ L := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  linarith

/-- The cofactor is at most `√q` on the region. -/
lemma leafZone_half (L : ℝ) (m₁ m₂ : ℝ) (h : LeafZone L m₁ m₂) : m₂ ≤ 1 / 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  linarith

set_option hygiene false in
/-- The cases at the ends of a piece, each by `linarith` from the region's inequalities. -/
local macro "lzends" : tactic =>
  `(tactic| (intro β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂
             obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hRm
             rcases hb with rfl | rfl <;> rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl <;> linarith))

set_option maxHeartbeats 40000000 in
/-- **The zone's exponents with the fourth moment for the curve `g7d` on the region `LeafZone L`**, for every `L`. -/
theorem zone_leaf (L : ℝ) : ZoneOK4 g7d L (1 / 1000) (1 / 1000) (LeafZone L) :=
  zoneOK4_of_piece <|
    zonePiece4_glue (zonePiece4_OO (fun _ => 1) (lo := 1 / 2) (hi := 4 / 7) (leafZone_le L) (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 840199 / 398000) (lo := 4 / 7) (hi := 81 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 140033 / 66000) (lo := 81 / 140) (hi := 41 / 70) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 840197 / 394000) (lo := 41 / 70) (hi := 83 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 30007 / 14000) (lo := 83 / 140) (hi := 3 / 5) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 56013 / 26000) (lo := 3 / 5) (hi := 17 / 28) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 420097 / 194000) (lo := 17 / 28) (hi := 43 / 70) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 840193 / 386000) (lo := 43 / 70) (hi := 87 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 547 / 250) (lo := 87 / 140) (hi := 22 / 35) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 840191 / 382000) (lo := 22 / 35) (hi := 89 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 84019 / 38000) (lo := 89 / 140) (hi := 9 / 14) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 40009 / 18000) (lo := 9 / 14) (hi := 13 / 20) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 210047 / 94000) (lo := 13 / 20) (hi := 23 / 35) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 840187 / 374000) (lo := 23 / 35) (hi := 93 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 140031 / 62000) (lo := 93 / 140) (hi := 47 / 70) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 168037 / 74000) (lo := 47 / 70) (hi := 19 / 28) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 105023 / 46000) (lo := 19 / 28) (hi := 24 / 35) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 280061 / 122000) (lo := 24 / 35) (hi := 97 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 60013 / 26000) (lo := 97 / 140) (hi := 7 / 10) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 840181 / 362000) (lo := 7 / 10) (hi := 99 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 700003 / 300000) (lo := 99 / 140) (hi := 5 / 7) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 11667 / 5000) (lo := 5 / 7) (hi := 1201 / 1680) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 116629 / 50000) (lo := 1201 / 1680) (hi := 601 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 116589 / 50000) (lo := 601 / 840) (hi := 401 / 560) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 29137 / 12500) (lo := 401 / 560) (hi := 43 / 60) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 29127 / 12500) (lo := 43 / 60) (hi := 241 / 336) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 116467 / 50000) (lo := 241 / 336) (hi := 201 / 280) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 116427 / 50000) (lo := 201 / 280) (hi := 1207 / 1680) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 58193 / 25000) (lo := 1207 / 1680) (hi := 151 / 210) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 58173 / 25000) (lo := 151 / 210) (hi := 403 / 560) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 23261 / 10000) (lo := 403 / 560) (hi := 121 / 168) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 58133 / 25000) (lo := 121 / 168) (hi := 173 / 240) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 58113 / 25000) (lo := 173 / 240) (hi := 101 / 140) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 23237 / 10000) (lo := 101 / 140) (hi := 1213 / 1680) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 23229 / 10000) (lo := 1213 / 1680) (hi := 607 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 58053 / 25000) (lo := 607 / 840) (hi := 61 / 84) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 14483 / 6250) (lo := 61 / 84) (hi := 613 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 57813 / 25000) (lo := 613 / 840) (hi := 11 / 15) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 115387 / 50000) (lo := 11 / 15) (hi := 619 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 2303 / 1000) (lo := 619 / 840) (hi := 311 / 420) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 114913 / 50000) (lo := 311 / 420) (hi := 125 / 168) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 114679 / 50000) (lo := 125 / 168) (hi := 157 / 210) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 228889 / 100000) (lo := 157 / 210) (hi := 631 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 228423 / 100000) (lo := 631 / 840) (hi := 317 / 420) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 227959 / 100000) (lo := 317 / 420) (hi := 91 / 120) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 227493 / 100000) (lo := 91 / 120) (hi := 16 / 21) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 45407 / 20000) (lo := 16 / 21) (hi := 643 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 9063 / 4000) (lo := 643 / 840) (hi := 323 / 420) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 226117 / 100000) (lo := 323 / 420) (hi := 649 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_OE (A := 225661 / 100000) (lo := 649 / 840) (hi := 163 / 210) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 225207 / 100000) (lo := 163 / 210) (hi := 131 / 168) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 4481 / 2000) (lo := 131 / 168) (hi := 47 / 60) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 40009 / 18000) (lo := 47 / 60) (hi := 661 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 560127 / 254000) (lo := 661 / 840) (hi := 83 / 105) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 547 / 250) (lo := 83 / 105) (hi := 667 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 560129 / 258000) (lo := 667 / 840) (hi := 67 / 84) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 56013 / 26000) (lo := 67 / 84) (hi := 673 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 560131 / 262000) (lo := 673 / 840) (hi := 169 / 210) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 140033 / 66000) (lo := 169 / 210) (hi := 97 / 120) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 80019 / 38000) (lo := 97 / 120) (hi := 341 / 420) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 280067 / 134000) (lo := 341 / 420) (hi := 137 / 168) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 112027 / 54000) (lo := 137 / 168) (hi := 86 / 105) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 70017 / 34000) (lo := 86 / 105) (hi := 691 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 560137 / 274000) (lo := 691 / 840) (hi := 347 / 420) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 280069 / 138000) (lo := 347 / 420) (hi := 697 / 840) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_glue (zonePiece4_HE (A := 560139 / 278000) (lo := 697 / 840) (hi := 5 / 6) (leafZone_le L) (leafZone_half L)
        (by lzends)) <|
    zonePiece4_HE (A := 101 / 50) (lo := 5 / 6) (hi := 11 / 12) (leafZone_le L) (leafZone_half L)
        (by lzends)

end SieveTypeIIHM

#print axioms SieveTypeIIHM.zone_leaf
