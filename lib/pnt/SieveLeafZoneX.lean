/-
# The leaves' region above `√q` as inequalities, and its test on a box in integers

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Written by `tools/linnik/gen_leafzone.py`; do not edit.

`SieveLeafTwo.LeafZoneX` is `LeafZone` below `m₂ = 1/2` and its slice at `m₂ = 1/2` above. Every case of the region
has `m₂` on its larger side, so `LeafZoneX` contains the intersection of 19 half-planes in `(m₁, m₂)`: the region's
inequalities but `m₂ ≤ 1/2`, and its cuts again at `m₂ = 1/2` (`LeafZoneXL`, `leafZoneX_of_XL`). An intersection of
half-planes holds on a rectangle of `(m₁, ρ)`, `ρ = L − m₁ − m₂`, when it holds at the four corners (`lin_rect`,
`leafZoneXL_rect`); and at a point `m₁ = κP`, `ρ = κR`, `L = κD` with `Ln = Ld·D·κ` (exponents of `x` in units of
`1/D`, `L = Ln/Ld`), each of its inequalities is one of natural numbers (`leafXN`, `leafXN_sound`).

The file imports `SieveLeafTwo.lean` and `SieveLeafZoneXDefs.lean` (`leafXN`, without Mathlib).
-/
import SieveLeafTwo
import SieveLeafZoneXDefs

namespace SieveLeafZoneX

/-- **The leaves' region above `√q` as 19 inequalities**: the region `LeafZone`'s but `m₂ ≤ 1/2`, and its cuts at
`m₂ = 1/2`. -/
def LeafZoneXL (L m₁ m₂ : ℝ) : Prop :=
  9 / 10 ≤ 1 * m₁ ∧
    1 * m₁ ≤ 6 / 5 ∧
    2 / 5 ≤ 1 * m₂ ∧
    3 / 10 ≤ 1 * (L - m₁ - m₂) ∧
    1 * (L - m₁ - m₂) ≤ 1 ∧
    25001 / 25000 ≤ 1 / 2 * m₁ + 1 / 2 * m₂ + 749993 / 1750000 * (L - m₁ - m₂) ∧
    12501 / 25000 ≤ 1 / 2 * m₂ + 749993 / 1750000 * (L - m₁ - m₂) ∧
    73693427 / 84000000 ≤ 1 / 2 * m₁ + 1 / 2 * m₂ + 1174979 / 5250000 * (L - m₁ - m₂) ∧
    87937 / 300000 ≤ 1 / 2 * m₂ + 62497 / 750000 * (L - m₁ - m₂) ∧
    10274479 / 11200000 ≤ 1 / 2 * m₁ + 1 / 2 * m₂ + 748427 / 2625000 * (L - m₁ - m₂) ∧
    4674479 / 11200000 ≤ 1 / 2 * m₂ + 748427 / 2625000 * (L - m₁ - m₂) ∧
    70467547 / 84000000 ≤ 2753 / 6000 * m₁ + 1 / 2 * m₂ + 1174979 / 5250000 * (L - m₁ - m₂) ∧
    25001 / 25000 ≤ 1 / 2 * m₁ + 1 / 2 * (1 / 2) + 749993 / 1750000 * (L - m₁ - m₂) ∧
    12501 / 25000 ≤ 1 / 2 * (1 / 2) + 749993 / 1750000 * (L - m₁ - m₂) ∧
    73693427 / 84000000 ≤ 1 / 2 * m₁ + 1 / 2 * (1 / 2) + 1174979 / 5250000 * (L - m₁ - m₂) ∧
    87937 / 300000 ≤ 1 / 2 * (1 / 2) + 62497 / 750000 * (L - m₁ - m₂) ∧
    10274479 / 11200000 ≤ 1 / 2 * m₁ + 1 / 2 * (1 / 2) + 748427 / 2625000 * (L - m₁ - m₂) ∧
    4674479 / 11200000 ≤ 1 / 2 * (1 / 2) + 748427 / 2625000 * (L - m₁ - m₂) ∧
    70467547 / 84000000 ≤ 2753 / 6000 * m₁ + 1 / 2 * (1 / 2) + 1174979 / 5250000 * (L - m₁ - m₂)

/-- `LeafZoneXL` is in `LeafZoneX`: below `m₂ = 1/2` it is `LeafZone`, above it the slice. -/
theorem leafZoneX_of_XL {L m₁ m₂ : ℝ} (h : LeafZoneXL L m₁ m₂) : SieveLeafTwo.LeafZoneX L m₁ m₂ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  rcases le_total m₂ (1 / 2) with hm | hm
  · refine Or.inl ⟨hm, ?_⟩
    unfold SieveTypeIIHM.LeafZone
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · refine Or.inr ⟨hm, ?_⟩
    unfold SieveTypeIIHM.LeafZone
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- A linear form at most `0` at the four corners of a rectangle is at most `0` on it. -/
theorem lin_rect {α β γ u₁ u₂ r₁ r₂ u r : ℝ} (hu₁ : u₁ ≤ u) (hu₂ : u ≤ u₂) (hr₁ : r₁ ≤ r) (hr₂ : r ≤ r₂)
    (h11 : α * u₁ + β * r₁ + γ ≤ 0) (h12 : α * u₁ + β * r₂ + γ ≤ 0) (h21 : α * u₂ + β * r₁ + γ ≤ 0)
    (h22 : α * u₂ + β * r₂ + γ ≤ 0) : α * u + β * r + γ ≤ 0 := by
  rcases le_total 0 α with hα | hα <;> rcases le_total 0 β with hβ | hβ
  · nlinarith [mul_le_mul_of_nonneg_left hu₂ hα, mul_le_mul_of_nonneg_left hr₂ hβ]
  · nlinarith [mul_le_mul_of_nonneg_left hu₂ hα, mul_le_mul_of_nonpos_left hr₁ hβ]
  · nlinarith [mul_le_mul_of_nonpos_left hu₁ hα, mul_le_mul_of_nonneg_left hr₂ hβ]
  · nlinarith [mul_le_mul_of_nonpos_left hu₁ hα, mul_le_mul_of_nonpos_left hr₁ hβ]

set_option maxHeartbeats 4000000 in
/-- **`LeafZoneXL` on a rectangle of `(m₁, ρ)` from its four corners.** -/
theorem leafZoneXL_rect {L u₁ u₂ r₁ r₂ u r : ℝ} (hu₁ : u₁ ≤ u) (hu₂ : u ≤ u₂) (hr₁ : r₁ ≤ r) (hr₂ : r ≤ r₂)
    (h11 : LeafZoneXL L u₁ (L - u₁ - r₁)) (h12 : LeafZoneXL L u₁ (L - u₁ - r₂))
    (h21 : LeafZoneXL L u₂ (L - u₂ - r₁)) (h22 : LeafZoneXL L u₂ (L - u₂ - r₂)) :
    LeafZoneXL L u (L - u - r) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h11
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18⟩ := h12
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := h21
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩ := h22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := lin_rect (α := -1) (β := 0) (γ := 9 / 10 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 1) (β := 0) (γ := -6 / 5 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 1) (β := 1) (γ := 2 / 5 + -1 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := -1) (γ := 3 / 10 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := 1) (γ := -1 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := 125007 / 1750000) (γ := 25001 / 25000 + -1 / 2 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 1 / 2) (β := 125007 / 1750000) (γ := 12501 / 25000 + -1 / 2 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := 1450021 / 5250000) (γ := 73693427 / 84000000 + -1 / 2 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 1 / 2) (β := 312503 / 750000) (γ := 87937 / 300000 + -1 / 2 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := 564073 / 2625000) (γ := 10274479 / 11200000 + -1 / 2 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 1 / 2) (β := 564073 / 2625000) (γ := 4674479 / 11200000 + -1 / 2 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 247 / 6000) (β := 1450021 / 5250000) (γ := 70467547 / 84000000 + -1 / 2 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := -1 / 2) (β := -749993 / 1750000) (γ := 18751 / 25000 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := -749993 / 1750000) (γ := 6251 / 25000 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := -1 / 2) (β := -1174979 / 5250000) (γ := 52693427 / 84000000 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := -62497 / 750000) (γ := 12937 / 300000 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := -1 / 2) (β := -748427 / 2625000) (γ := 7474479 / 11200000 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := 0) (β := -748427 / 2625000) (γ := 1874479 / 11200000 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · have := lin_rect (α := -2753 / 6000) (β := -1174979 / 5250000) (γ := 49467547 / 84000000 + 0 * L) hu₁ hu₂ hr₁ hr₂
      (by linarith) (by linarith) (by linarith) (by linarith)
    linarith

set_option maxHeartbeats 4000000 in
/-- **The test is sound**: for `Ld, D > 0` and `Ln = Ld·D·κ`, `leafXN` gives `LeafZoneXL` at `m₁ = κP`, `ρ = κR`,
`L = κD`. -/
theorem leafXN_sound {Ln Ld D P R : ℕ} {κ : ℝ} (hLd : 0 < Ld) (hD : 0 < D) (hLn : (Ln : ℝ) = Ld * D * κ)
    (h : leafXN Ln Ld D P R = true) : LeafZoneXL (κ * D) (κ * P) (κ * D - κ * P - κ * R) := by
  simp only [leafXN, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩, k11⟩, k12⟩, k13⟩, k14⟩, k15⟩, k16⟩, k17⟩, k18⟩ := h
  have hM : (0 : ℝ) < Ld * D := by positivity
  have cast : ∀ {a b : ℕ}, a ≤ b → (a : ℝ) ≤ b := fun hab => by exact_mod_cast hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := cast k0
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 10) hM)
    linarith [h]
  · have h := cast k1
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 5) hM)
    linarith [h]
  · have h := cast k2
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 5) hM)
    linarith [h]
  · have h := cast k3
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 10) hM)
    linarith [h]
  · have h := cast k4
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 1) hM)
    linarith [h]
  · have h := cast k5
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 1750000) hM)
    linarith [h]
  · have h := cast k6
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 1750000) hM)
    linarith [h]
  · have h := cast k7
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 84000000) hM)
    linarith [h]
  · have h := cast k8
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 1500000) hM)
    linarith [h]
  · have h := cast k9
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 168000000) hM)
    linarith [h]
  · have h := cast k10
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 168000000) hM)
    linarith [h]
  · have h := cast k11
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 84000000) hM)
    linarith [h]
  · have h := cast k12
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 1750000) hM)
    linarith [h]
  · have h := cast k13
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 1750000) hM)
    linarith [h]
  · have h := cast k14
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 84000000) hM)
    linarith [h]
  · have h := cast k15
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 1500000) hM)
    linarith [h]
  · have h := cast k16
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 168000000) hM)
    linarith [h]
  · have h := cast k17
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 168000000) hM)
    linarith [h]
  · have h := cast k18
    push_cast at h
    rw [hLn] at h
    refine le_of_mul_le_mul_left ?_ (mul_pos (by norm_num : (0 : ℝ) < 84000000) hM)
    linarith [h]

end SieveLeafZoneX
