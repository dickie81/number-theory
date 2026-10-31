import Mathlib
import SwapRealize
import ParabolaGap

/-! # Simplicity of the ground state: small supports, and the criterion `λ₁ < s ≤ λ₂`

The chain reduces to `(a) + eventual simplicity ⇒ RH`. This file does two things.

1. **Every support `0 < a ≤ 0.36` has a simple ground state** (`simpleGround_036`), from the certified
   gap of ParabolaGap.lean and the passage "unique up to sign ⇒ simple" (`simpleGround_of_unique`).
2. **Monotonicity, and the criterion.** Enlarging the support enlarges the probe class, so `λ₁(a)` is
   nonincreasing (`lam_antitone`). A single inequality `λ₁(a) < s ≤ λ₂(a)` gives simplicity at `a`
   (`simpleGround_of_lam2`): a non-simple ground state gives an orthonormal pair of ground states
   (`degenerate_of_not_simple`).

`Lam2Ge a s` is the min–max statement `λ₂(a) ≥ s` in the even sector: every orthonormal pair of
probes spans a unit vector with `Q ≥ s`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace WeilForm

/-! ## Unique up to sign ⇒ simple -/

theorem simpleGround_of_unique {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hu : ∀ h, IsGroundState a h → h =ᵐ[volume] g ∨ h =ᵐ[volume] fun t => -g t) :
    SimpleGround a g := by
  refine ⟨hg, fun h hh => ?_⟩
  have hp : Probe a h := hh.1
  by_cases h0 : normSq h = 0
  · refine ⟨0, ?_⟩
    filter_upwards [ae_zero_of_normSq hp.memL2 h0] with t ht
    simp [ht]
  · have hpos : 0 < normSq h := lt_of_le_of_ne (normSq_nonneg h) (Ne.symm h0)
    set c := Real.sqrt (normSq h) with hc
    have hc0 : 0 < c := Real.sqrt_pos.2 hpos
    have hcsq : c ^ 2 = normSq h := Real.sq_sqrt hpos.le
    set h' : ℝ → ℝ := fun t => c⁻¹ * h t with hh'
    have hmem : h' ∈ groundSpace a := groundSpace_fun hh c⁻¹
    have hn : normSq h' = 1 := by
      rw [hh', normSq_smul, inv_pow, hcsq, inv_mul_cancel₀ h0]
    have hgs : IsGroundState a h' := (isGroundState_iff ha).2 ⟨hmem, hn⟩
    have hback : h = fun t => c * h' t := by
      funext t; simp only [hh']; field_simp
    rcases hu h' hgs with e | e
    · refine ⟨c, ?_⟩
      rw [hback]; filter_upwards [e] with t ht; rw [ht]
    · refine ⟨-c, ?_⟩
      rw [hback]; filter_upwards [e] with t ht; rw [ht]; ring

/-- **Every support `0 < a ≤ 0.36` has simple ground states.** -/
theorem simpleGround_036 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ}
    (hg : IsGroundState a g) : SimpleGround a g :=
  simpleGround_of_unique ha hg fun _ hh => groundState_unique_036 ha ha2 hh hg

/-! ## Monotonicity in the support -/

/-- **`λ₁` is nonincreasing in the support.** -/
theorem lam_antitone {a a₁ : ℝ} (ha : 0 < a) (h : a ≤ a₁) : lam a₁ ≤ lam a := by
  refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
  rintro q ⟨g, hp, hn, rfl⟩
  rw [← weilQ_mono ha.le h hp]
  exact lam_le (hp.mono h) hn

/-- `λ₂(a) ≥ s` in min–max form (even sector): every orthonormal pair of probes spans a unit vector
with `Q ≥ s`. -/
def Lam2Ge (a s : ℝ) : Prop :=
  ∀ g h : ℝ → ℝ, Probe a g → Probe a h → normSq g = 1 → normSq h = 1 → xcorr g h 0 = 0 →
    ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧ s ≤ weilQ a (fun t => α * g t + β * h t)

/-! ## The covering criterion -/

theorem normSq_comb {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (α β : ℝ) :
    normSq (fun t => α * g t + β * h t)
      = α ^ 2 * normSq g + 2 * α * β * xcorr g h 0 + β ^ 2 * normSq h := by
  have e := normSq_add_smul (hg.const_mul α) (hh.const_mul β) 1
  have ex : xcorr (fun t => α * g t) (fun t => β * h t) 0 = α * β * xcorr g h 0 := by
    rw [xcorr_zero_eq, xcorr_zero_eq, ← integral_const_mul]
    congr 1; funext t; ring
  simp only [one_mul] at e
  rw [e, ex, normSq_smul, normSq_smul]; ring

/-- **Degeneracy**: two orthonormal ground states. -/
def Degenerate (a : ℝ) : Prop :=
  ∃ g h, IsGroundState a g ∧ IsGroundState a h ∧ xcorr g h 0 = 0

/-- A non-simple ground state gives an orthonormal pair of ground states (Gram–Schmidt; from `SimpleCont.lean`
). -/
theorem degenerate_of_not_simple {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hns : ¬ SimpleGround a g) : Degenerate a := by
  have hgm : g ∈ groundSpace a := ((isGroundState_iff ha).1 hg).1
  obtain ⟨h, hh, hnot⟩ : ∃ h ∈ groundSpace a, ∀ c : ℝ, ¬ h =ᵐ[volume] fun t => c * g t := by
    by_contra H
    push Not at H
    exact hns ⟨hg, H⟩
  have hp : Probe a h := hh.1
  set c := xcorr h g 0 with hc
  set h' : ℝ → ℝ := fun t => h t + (-c) * g t with hh'
  have hmem' : h' ∈ groundSpace a := by
    have := (groundSpace a).add_mem hh ((groundSpace a).smul_mem (-c) hgm)
    convert this using 1
  have hp' : Probe a h' := hmem'.1
  have n0 := normSq_add_smul hp.memL2 hg.1.memL2 (-c)
  have n1 := normSq_add_smul hp'.memL2 hg.1.memL2 1
  have n2 := normSq_add_smul hp.memL2 hg.1.memL2 (1 - c)
  have eqf : (fun t => h' t + 1 * g t) = fun t => h t + (1 - c) * g t := by
    funext t; simp only [hh']; ring
  rw [eqf, n2] at n1
  rw [← hh'] at n0
  have hgn := hg.2.1
  have hx' : xcorr h' g 0 = 0 := by
    rw [hgn] at n0 n1; rw [← hc] at n0 n1
    linear_combination (-(1 : ℝ) / 2) * n1 + (-(1 : ℝ) / 2) * n0
  have h0 : normSq h' ≠ 0 := by
    intro h0
    apply hnot c
    filter_upwards [ae_zero_of_normSq hp'.memL2 h0] with t ht
    have : h t + (-c) * g t = 0 := by simpa [hh'] using ht
    linarith
  have hpos : 0 < normSq h' := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
  set k := (Real.sqrt (normSq h'))⁻¹
  have hk : k ^ 2 * normSq h' = 1 := by
    simp only [k, inv_pow, Real.sq_sqrt hpos.le]; exact inv_mul_cancel₀ h0
  refine ⟨g, fun t => k * h' t, hg, (isGroundState_iff ha).2 ⟨groundSpace_fun hmem' k, ?_⟩, ?_⟩
  · rw [normSq_smul]; exact hk
  · rw [xcorr_zero_eq]
    have : (fun t => g t * (k * h' t)) = fun t => k * (h' t * g t) := by funext t; ring
    rw [this, integral_const_mul, ← xcorr_zero_eq, hx', mul_zero]

/-- **Simplicity from `λ₁ < s ≤ λ₂`.** -/
theorem simpleGround_of_lam2 {a s : ℝ} (ha : 0 < a) (hl : lam a < s) (H : Lam2Ge a s)
    {g : ℝ → ℝ} (hg : IsGroundState a g) : SimpleGround a g := by
  by_contra hns
  obtain ⟨g₁, h₁, hg₁, hh₁, hx⟩ := degenerate_of_not_simple ha hg hns
  obtain ⟨α, β, hab, hs⟩ := H g₁ h₁ hg₁.1 hh₁.1 hg₁.2.1 hh₁.2.1 hx
  have hm1 := ((isGroundState_iff ha).1 hg₁).1
  have hm2 := ((isGroundState_iff ha).1 hh₁).1
  have hcomb : (fun t => α * g₁ t + β * h₁ t) ∈ groundSpace a := by
    have := (groundSpace a).add_mem ((groundSpace a).smul_mem α hm1) ((groundSpace a).smul_mem β hm2)
    convert this using 1
  have hN : normSq (fun t => α * g₁ t + β * h₁ t) = 1 := by
    rw [normSq_comb hg₁.1.memL2 hh₁.1.memL2, hg₁.2.1, hh₁.2.1, hx]; linarith
  have hq := hcomb.2
  rw [hq, hN, mul_one] at hs
  linarith

end WeilForm

#print axioms WeilForm.simpleGround_of_unique
#print axioms WeilForm.simpleGround_036
#print axioms WeilForm.lam_antitone
#print axioms WeilForm.simpleGround_of_lam2
