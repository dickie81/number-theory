/-
# The leaves' region above `√q` as inequalities, and its test on a box in integers

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Written by `tools/linnik/gen_leafzone.py`; do not edit.

`SieveLeafTwo.LeafZoneX` is `LeafZone` below `m₂ = 1/2` and its slice at `m₂ = 1/2` above. Every case of the region
has `m₂` on its larger side, so `LeafZoneX` contains the intersection of 19 half-planes in `(m₁, m₂)`: the region's
inequalities but `m₂ ≤ 1/2`, and its cuts again at `m₂ = 1/2` (`LeafZoneXL`, `leafZoneX_of_XL`). A half-plane
holds on a rectangle of `(m₁, ρ)`, `ρ = L − m₁ − m₂`, when it holds at the corner where its linear form is largest;
for `m₁ = κP`, `ρ = κR`, `L = κD` with `Ln = Ld·D·κ` (exponents of `x` in units of `1/D`, `L = Ln/Ld`), that is an
inequality of natural numbers, and `leafXR`'s 19 of them give `LeafZoneXL` on the rectangle (`leafXR_sound`).

The file imports `SieveLeafTwo.lean` and `SieveLeafZoneXDefs.lean` (`leafXR`, without Mathlib).
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

set_option maxHeartbeats 4000000 in
/-- **The test is sound**: for `Ld, D > 0` and `Ln = Ld·D·κ`, `leafXR` gives `LeafZoneXL` at `L = κD` for every
`m₁` in `[κP₁, κP₂]` and `ρ` in `[κR₁, κR₂]`. -/
theorem leafXR_sound {Ln Ld D P₁ P₂ R₁ R₂ : ℕ} {κ : ℝ} (hLd : 0 < Ld) (hD : 0 < D)
    (hLn : (Ln : ℝ) = Ld * D * κ) (h : leafXR Ln Ld D P₁ P₂ R₁ R₂ = true) {m₁ ρ : ℝ} (h1 : κ * P₁ ≤ m₁)
    (h2 : m₁ ≤ κ * P₂) (h3 : κ * R₁ ≤ ρ) (h4 : ρ ≤ κ * R₂) : LeafZoneXL (κ * D) m₁ (κ * D - m₁ - ρ) := by
  simp only [leafXR, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩, k11⟩, k12⟩, k13⟩, k14⟩, k15⟩, k16⟩, k17⟩, k18⟩ := h
  have hM : (0 : ℝ) < Ld * D := by positivity
  have cast : ∀ {a b : ℕ}, a ≤ b → (a : ℝ) ≤ b := fun hab => by exact_mod_cast hab
  have b1 := mul_le_mul_of_nonneg_left h1 hM.le
  have b2 := mul_le_mul_of_nonneg_left h2 hM.le
  have b3 := mul_le_mul_of_nonneg_left h3 hM.le
  have b4 := mul_le_mul_of_nonneg_left h4 hM.le
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
