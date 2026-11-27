import Mathlib
import ModMaassSelberg

open Complex ComplexConjugate Filter Topology Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace ModLaxPhillips

/-! ## The Lax–Phillips semigroup of an abstract scattering system -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Lax–Phillips data**: a one-parameter group `U(t)` of unitary operators on a Hilbert space `H`, an incoming
subspace `D₋` with `U(−t)D₋ ⊆ D₋` and a closed outgoing subspace `D₊` with `U(t)D₊ ⊆ D₊` (`t ≥ 0`), `D₊ ⊥ D₋`. -/
structure LPData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  U : ℝ → H →L[ℂ] H
  U_zero : U 0 = ContinuousLinearMap.id ℂ H
  U_add : ∀ t s, U (t + s) = (U t).comp (U s)
  U_inner : ∀ t x y, ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ
  Dm : Submodule ℂ H
  Dp : Submodule ℂ H
  [hDp : Dp.HasOrthogonalProjection]
  Dm_inv : ∀ t, 0 ≤ t → ∀ x ∈ Dm, U (-t) x ∈ Dm
  Dp_inv : ∀ t, 0 ≤ t → ∀ x ∈ Dp, U t x ∈ Dp
  orth : Dp ≤ Dmᗮ

namespace LPData

attribute [instance] LPData.hDp

variable (D : LPData H)

lemma U_neg_U (t : ℝ) (x : H) : D.U t (D.U (-t) x) = x := by
  have := D.U_add t (-t)
  rw [add_neg_cancel, D.U_zero] at this
  exact (congrArg (fun A : H →L[ℂ] H => A x) this).symm

lemma inner_U_left (t : ℝ) (x y : H) : ⟪D.U t x, y⟫_ℂ = ⟪x, D.U (-t) y⟫_ℂ := by
  conv_lhs => rw [← D.U_neg_U t y]
  exact D.U_inner t x _

lemma inner_U_right (t : ℝ) (x y : H) : ⟪x, D.U t y⟫_ℂ = ⟪D.U (-t) x, y⟫_ℂ := by
  rw [D.inner_U_left (-t), neg_neg]

lemma norm_U (t : ℝ) (x : H) : ‖D.U t x‖ = ‖x‖ := by
  have h := congrArg Complex.re (D.U_inner t x x)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖D.U t x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- The **scattering subspace** `K = (D₋ ⊕ D₊)^⊥`. -/
abbrev K : Submodule ℂ H := (D.Dm ⊔ D.Dp)ᗮ

lemma mem_K {x : H} : x ∈ D.K ↔ x ∈ D.Dmᗮ ∧ x ∈ D.Dpᗮ := by
  rw [K, ← Submodule.inf_orthogonal, Submodule.mem_inf]

/-- `U(s)` maps `K` into `D₋^⊥` for `s ≥ 0`. -/
lemma U_K_perp_Dm {s : ℝ} (hs : 0 ≤ s) {k : H} (hk : k ∈ D.K) : D.U s k ∈ D.Dmᗮ := by
  rw [Submodule.mem_orthogonal]
  intro d hd
  rw [D.inner_U_right]
  exact ((D.mem_K.1 hk).1 :) _ (D.Dm_inv s hs d hd)

variable [CompleteSpace H]

/-- The orthogonal projection `P_K`. -/
def P : H →L[ℂ] H := D.K.starProjection

lemma P_eq_zero_of_perp {d : H} (hd : ∀ w ∈ D.K, ⟪d, w⟫_ℂ = 0) : D.P d = 0 :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) (fun w hw => by
    simpa using hd w hw)

lemma P_Dp {d : H} (hd : d ∈ D.Dp) : D.P d = 0 :=
  D.P_eq_zero_of_perp fun _ hw => ((D.mem_K.1 hw).2 :) _ hd

lemma P_Dm {d : H} (hd : d ∈ D.Dm) : D.P d = 0 :=
  D.P_eq_zero_of_perp fun _ hw => ((D.mem_K.1 hw).1 :) _ hd

lemma P_mem (x : H) : D.P x ∈ D.K := Submodule.starProjection_apply_mem _ _

lemma P_of_mem {x : H} (hx : x ∈ D.K) : D.P x = x := Submodule.starProjection_eq_self_iff.2 hx

lemma P_P (x : H) : D.P (D.P x) = D.P x := D.P_of_mem (D.P_mem x)

/-- For `w ⊥ D₋`: `P_K w = w − P₊ w`. -/
lemma P_of_perp_Dm {w : H} (hw : w ∈ D.Dmᗮ) : D.P w = w - D.Dp.starProjection w := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ (fun k hk => ?_)
  · refine D.mem_K.2 ⟨?_, Submodule.sub_starProjection_mem_orthogonal w⟩
    exact Submodule.sub_mem _ hw (D.orth (Submodule.starProjection_apply_mem _ _))
  · rw [sub_sub_cancel]
    exact ((D.mem_K.1 hk).2 :) _ (Submodule.starProjection_apply_mem _ _)

/-- **The Lax–Phillips semigroup** `Z(t) = P_K U(t) P_K`. -/
def Z (t : ℝ) : H →L[ℂ] H := D.P.comp ((D.U t).comp D.P)

/-- Its adjoint candidate `Z(t)* = P_K U(−t) P_K`. -/
def Zstar (t : ℝ) : H →L[ℂ] H := D.P.comp ((D.U (-t)).comp D.P)

/-- **`Z(0) = P_K`**: the identity on `K`. -/
theorem Z_zero : D.Z 0 = D.P := by
  ext x
  simp [Z, D.U_zero, D.P_P]

/-- **The semigroup law** `Z(t + s) = Z(t)Z(s)` for `t, s ≥ 0` (Lax–Phillips). -/
theorem Z_add {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) : D.Z (t + s) = (D.Z t).comp (D.Z s) := by
  ext x
  set k := D.P x
  have hk : k ∈ D.K := D.P_mem x
  have hw := D.U_K_perp_Dm hs hk
  simp only [Z, ContinuousLinearMap.comp_apply]
  rw [D.P_P, D.P_of_perp_Dm hw, map_sub, map_sub, D.P_Dp (D.Dp_inv t ht _ (Submodule.starProjection_apply_mem _ _)),
    sub_zero, D.U_add, ContinuousLinearMap.comp_apply]

/-- **`Z(t)` is a contraction**: `‖Z(t)x‖ ≤ ‖x‖`. -/
theorem norm_Z_le (t : ℝ) (x : H) : ‖D.Z t x‖ ≤ ‖x‖ := by
  simp only [Z, ContinuousLinearMap.comp_apply]
  calc ‖D.P (D.U t (D.P x))‖ ≤ ‖D.U t (D.P x)‖ := Submodule.norm_starProjection_apply_le _ _
    _ = ‖D.P x‖ := D.norm_U t _
    _ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le _ _

/-- **`Z(t)* = P_K U(−t) P_K`**: the adjoint of the Lax–Phillips semigroup. -/
theorem adjoint_Z (t : ℝ) : ContinuousLinearMap.adjoint (D.Z t) = D.Zstar t := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Z, Zstar, ContinuousLinearMap.comp_apply, P]
  rw [Submodule.inner_starProjection_left_eq_right, ← D.inner_U_right, ← Submodule.inner_starProjection_left_eq_right]

end LPData

end Abstract

/-! ## The inner scattering function `S₀(s) = ((s − 1)/s)φ(s)` -/

open PavlovFaddeev

/-- The numerator `(s − 1)(2s − 1)Λ(2s − 1)`, written with Mathlib's entire `Λ₀` so that it is entire. -/
def S0num (s : ℂ) : ℂ := (s - 1) * ((2 * s - 1) * completedRiemannZeta₀ (2 * s - 1) - 1) + (2 * s - 1) / 2

/-- The denominator `s(2s − 1)Λ(2s)`, written with Mathlib's entire `Λ₀`. -/
def S0den (s : ℂ) : ℂ := s * ((2 * s - 1) * completedRiemannZeta₀ (2 * s) + 1) - (2 * s - 1) / 2

/-- **The inner scattering function** `S₀(s) = ((s − 1)/s)φ(s)`: the scattering matrix with the pole of `φ` at
`s = 1` (the constant eigenfunction) removed by the Blaschke factor `(s − 1)/s`, in a form continuous at `s = ½`. -/
def S0 (s : ℂ) : ℂ := S0num s / S0den s

lemma two_mul_sub_one_ne {s : ℂ} (hh : s ≠ 1 / 2) : 2 * s - 1 ≠ 0 := by
  intro h; apply hh; linear_combination h / 2

lemma S0num_eq {s : ℂ} (hh : s ≠ 1 / 2) (h1 : s ≠ 1) :
    S0num s = (s - 1) * (2 * s - 1) * completedRiemannZeta (2 * s - 1) := by
  have a := two_mul_sub_one_ne hh
  have b : 1 - (2 * s - 1) ≠ 0 := by intro h; apply h1; linear_combination -h / 2
  have c : s - 1 ≠ 0 := sub_ne_zero.2 h1
  have e1 : (s - 1) * (2 * s - 1) * (1 / (2 * s - 1)) = s - 1 := by
    rw [mul_assoc, mul_one_div_cancel a, mul_one]
  have e2 : (s - 1) * (2 * s - 1) * (1 / (1 - (2 * s - 1))) = -((2 * s - 1) / 2) := by
    rw [show 1 - (2 * s - 1) = -2 * (s - 1) by ring]; field_simp
  rw [completedRiemannZeta_eq, S0num]
  conv_rhs => rw [sub_sub, mul_sub, mul_add, e1, e2]
  ring

lemma S0den_eq {s : ℂ} (h0 : s ≠ 0) (hh : s ≠ 1 / 2) :
    S0den s = s * (2 * s - 1) * completedRiemannZeta (2 * s) := by
  have a := two_mul_sub_one_ne hh
  have b : 1 - 2 * s ≠ 0 := by intro h; apply hh; linear_combination -h / 2
  have c : 2 * s ≠ 0 := mul_ne_zero two_ne_zero h0
  have e1 : s * (2 * s - 1) * (1 / (2 * s)) = (2 * s - 1) / 2 := by field_simp
  have e2 : s * (2 * s - 1) * (1 / (1 - 2 * s)) = -s := by
    rw [show 1 - 2 * s = -(2 * s - 1) by ring, one_div_neg_eq_neg_one_div, mul_neg, mul_assoc,
      mul_one_div_cancel a, mul_one]
  rw [completedRiemannZeta_eq, S0den]
  conv_rhs => rw [sub_sub, mul_sub, mul_add, e1, e2]
  ring

/-- **`S₀(s) = ((s − 1)/s)φ(s)`** for `s ≠ 0, ½, 1`. -/
theorem S0_eq {s : ℂ} (h0 : s ≠ 0) (hh : s ≠ 1 / 2) (h1 : s ≠ 1) : S0 s = (s - 1) / s * scatteringMatrix s := by
  rw [S0, S0num_eq hh h1, S0den_eq h0 hh, scatteringMatrix]
  have a := two_mul_sub_one_ne hh
  by_cases hΛ : completedRiemannZeta (2 * s) = 0
  · simp [hΛ]
  · rw [mul_right_comm (s - 1), mul_right_comm s, mul_div_mul_right _ _ a, mul_div_mul_comm]

/-- The denominator does not vanish on `Re s ≥ ½`. -/
lemma S0den_ne_zero {s : ℂ} (hs : 1 / 2 ≤ s.re) : S0den s ≠ 0 := by
  by_cases hh : s = 1 / 2
  · subst hh; norm_num [S0den]
  · have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
    rw [S0den_eq h0 hh]
    exact mul_ne_zero (mul_ne_zero h0 (two_mul_sub_one_ne hh))
      (completed_ne_zero_of_one_le_re (by simp; linarith))

/-- **`S₀` is holomorphic on a neighbourhood of every point of `Re s ≥ ½`**: the pole of `φ` at `s = 1` is removed,
and `φ` has no other pole there. -/
theorem differentiableAt_S0 {s : ℂ} (hs : 1 / 2 ≤ s.re) : DifferentiableAt ℂ S0 s := by
  have hN : DifferentiableAt ℂ S0num s := by
    unfold S0num
    have := (differentiable_completedZeta₀ (2 * s - 1)).comp s ((differentiableAt_id.const_mul 2).sub_const 1)
    fun_prop
  have hD : DifferentiableAt ℂ S0den s := by
    unfold S0den
    have := (differentiable_completedZeta₀ (2 * s)).comp s (differentiableAt_id.const_mul 2)
    fun_prop
  exact hN.div hD (S0den_ne_zero hs)

lemma norm_sub_one_eq_line (t : ℝ) : ‖(1 / 2 + t * I : ℂ) - 1‖ = ‖(1 / 2 + t * I : ℂ)‖ := by
  rw [show (1 / 2 + t * I : ℂ) - 1 = -conj (1 / 2 + t * I : ℂ) by
    apply Complex.ext <;> simp; norm_num, norm_neg, Complex.norm_conj]

/-- **`S₀` is unimodular on the critical line**: `|S₀(½ + it)| = 1` for every real `t`. -/
theorem norm_S0_line (t : ℝ) : ‖S0 (1 / 2 + t * I)‖ = 1 := by
  by_cases ht : t = 0
  · subst ht; norm_num [S0, S0num, S0den]
  · have hne : (1 / 2 + t * I : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have hh : (1 / 2 + t * I : ℂ) ≠ 1 / 2 := fun h => by
      have := congrArg Complex.im h; simp at this; exact ht this
    have h1 : (1 / 2 + t * I : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.im h; simp at this; exact ht this
    rw [S0_eq hne hh h1, norm_mul, norm_scatteringMatrix_line, mul_one, norm_div, norm_sub_one_eq_line,
      div_self (norm_ne_zero_iff.2 hne)]

/-- **The functional equation** `S₀(s)S₀(1 − s) = 1` (where `Λ(2s), Λ(2s − 1) ≠ 0`). -/
theorem S0_mul_one_sub {s : ℂ} (h0 : s ≠ 0) (hh : s ≠ 1 / 2) (h1 : s ≠ 1)
    (hΛ₀ : completedRiemannZeta (2 * s) ≠ 0) (hΛ₁ : completedRiemannZeta (2 * s - 1) ≠ 0) :
    S0 s * S0 (1 - s) = 1 := by
  have h0' : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hh' : 1 - s ≠ 1 / 2 := fun h => hh (by linear_combination -h)
  have h1' : 1 - s ≠ 1 := fun h => h0 (by linear_combination -h)
  have hφ := scatteringMatrix_mul_one_sub hΛ₀ hΛ₁
  rw [S0_eq h0 hh h1, S0_eq h0' hh' h1']
  have c : s - 1 ≠ 0 := sub_ne_zero.2 h1
  calc (s - 1) / s * scatteringMatrix s * ((1 - s - 1) / (1 - s) * scatteringMatrix (1 - s))
      = ((s - 1) / s * ((1 - s - 1) / (1 - s))) * (scatteringMatrix s * scatteringMatrix (1 - s)) := by ring
    _ = 1 := by rw [hφ]; field_simp; ring

/-- **The zeros of `S₀` in `Re s > ½`** are the zeros of `Λ(2s − 1)`: `s = (1 + ρ)/2` for the nontrivial zeros `ρ`. -/
theorem S0_eq_zero_iff {s : ℂ} (hs : 1 / 2 < s.re) : S0 s = 0 ↔ completedRiemannZeta (2 * s - 1) = 0 := by
  have hD := S0den_ne_zero hs.le
  have hh : s ≠ 1 / 2 := fun h => by rw [h] at hs; norm_num at hs
  by_cases h1 : s = 1
  · subst h1
    have hΛ : completedRiemannZeta (2 * 1 - 1) ≠ 0 := completed_ne_zero_of_one_le_re (by norm_num)
    have hN : S0num 1 ≠ 0 := by norm_num [S0num]
    simp only [S0, div_eq_zero_iff, hN, hD, or_self, hΛ]
  · have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
    rw [S0, div_eq_zero_iff, or_iff_left hD, S0num_eq hh h1, mul_eq_zero, mul_eq_zero,
      or_iff_right (sub_ne_zero.2 h1), or_iff_right (two_mul_sub_one_ne hh)]

/-! ## The resonances, and RH -/

/-- **The resonances**: `μ` with `Re μ > 0` and `S₀(½ + μ) = 0`. They are the eigenvalue exponents of the
Lax–Phillips semigroup below (decay rate `Re μ`). -/
def resonances : Set ℂ := {μ | 0 < μ.re ∧ S0 (1 / 2 + μ) = 0}

/-- **The resonances are half the nontrivial zeros**: `μ` is one iff `Re μ > 0` and `Λ(2μ) = 0`. -/
theorem mem_resonances {μ : ℂ} : μ ∈ resonances ↔ 0 < μ.re ∧ completedRiemannZeta (2 * μ) = 0 := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    rw [S0_eq_zero_iff (by simp; linarith)] at h
    rwa [show 2 * (1 / 2 + μ) - 1 = 2 * μ by ring] at h
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    rw [S0_eq_zero_iff (by simp; linarith), show 2 * (1 / 2 + μ) - 1 = 2 * μ by ring]
    exact h

lemma resonance_re_lt {μ : ℂ} (h : μ ∈ resonances) : μ.re < 1 / 2 :=
  (denominator_zero_strip (mem_resonances.1 h).2).2

/-- **The resonances come in pairs** `μ ↔ ½ − μ` (from `Λ(1 − s) = Λ(s)`). -/
theorem resonance_reflect {μ : ℂ} (h : μ ∈ resonances) : 1 / 2 - μ ∈ resonances := by
  have hlt := resonance_re_lt h
  refine mem_resonances.2 ⟨by simp; linarith, ?_⟩
  rw [show 2 * (1 / 2 - μ) = 1 - 2 * μ by ring, completedRiemannZeta_one_sub]
  exact (mem_resonances.1 h).2

/-- **RH is one decay rate for every resonance**: Mathlib's `RiemannHypothesis` iff every zero `μ` of `S₀(½ + ·)` in
`Re μ > 0` has `Re μ = ¼`. -/
theorem rh_iff_resonances_quarter : RiemannHypothesis ↔ ∀ μ ∈ resonances, μ.re = 1 / 4 := by
  rw [rh_iff_resonances_on_quarter]
  constructor
  · intro h μ hμ
    exact h μ (mem_resonances.1 hμ).1 (resonance_re_lt hμ) (mem_resonances.1 hμ).2
  · intro h s h0 _ hs
    exact h s (mem_resonances.2 ⟨h0, hs⟩)

/-- **RH is the slowest decay**: RH iff no resonance has `Re μ > ¼`; the pairing `μ ↔ ½ − μ` gives the rest. -/
theorem rh_iff_resonances_le_quarter : RiemannHypothesis ↔ ∀ μ ∈ resonances, μ.re ≤ 1 / 4 := by
  rw [rh_iff_resonances_quarter]
  refine ⟨fun h μ hμ => (h μ hμ).le, fun h μ hμ => le_antisymm (h μ hμ) ?_⟩
  have := h _ (resonance_reflect hμ)
  simp at this
  linarith

/-! ## The Maass–Selberg bound for `φ` and `S₀` -/

/-- **The Maass–Selberg inequality at `Y = 1`**: for `Re s = σ > ½`, `Im s = t ≠ 0`,
`(1 − |φ(s)|²)/(2σ − 1) − Im φ(s)/t ≥ 0`, from `‖E^1(·, s)‖² ≥ 0`. -/
theorem maass_selberg_ineq {s : ℂ} (hre : 1 / 2 < s.re) (him : s.im ≠ 0) :
    0 ≤ (1 - ‖scatteringMatrix s‖ ^ 2) / (2 * s.re - 1) - (scatteringMatrix s).im / s.im := by
  have h := ModMaassSelberg.integral_norm_EY_sq_re le_rfl hre him
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  have e : ((1 : ℂ) - ((‖scatteringMatrix s‖ ^ 2 : ℝ) : ℂ)) / (2 * (s.re : ℂ) - 1) +
      (conj (scatteringMatrix s) - scatteringMatrix s) / (2 * (s.im : ℂ) * I) =
      (((1 - ‖scatteringMatrix s‖ ^ 2) / (2 * s.re - 1) - (scatteringMatrix s).im / s.im : ℝ) : ℂ) := by
    have hI : (s.im : ℂ) ≠ 0 := by exact_mod_cast him
    have hσ : (2 * (s.re : ℂ) - 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hc : conj (scatteringMatrix s) - scatteringMatrix s = -(2 * ((scatteringMatrix s).im : ℂ) * I) := by
      exact Complex.ext (by simp) (by simp; ring)
    rw [hc]
    push_cast
    field_simp
    ring
  rw [e, Complex.ofReal_re] at h
  exact h

/-- **Polynomial growth of `φ` from Maass–Selberg**: `|φ(σ + it)| ≤ 1 + (2σ − 1)/|t|` for `σ > ½`, `t ≠ 0`. -/
theorem norm_scatteringMatrix_le {s : ℂ} (hre : 1 / 2 < s.re) (him : s.im ≠ 0) :
    ‖scatteringMatrix s‖ ≤ 1 + (2 * s.re - 1) / |s.im| := by
  have h := maass_selberg_ineq hre him
  set x := ‖scatteringMatrix s‖
  set a := (scatteringMatrix s).im
  have hσ : 0 < 2 * s.re - 1 := by linarith
  have ht : 0 < |s.im| := abs_pos.2 him
  have hax : |a| ≤ x := Complex.abs_im_le_norm _
  have hx : 0 ≤ x := norm_nonneg _
  have h1 : -(a / s.im) ≤ |a| / |s.im| := by
    rw [← abs_div]; exact neg_le_abs _
  have h2 : x ^ 2 ≤ 1 + (2 * s.re - 1) * (x / |s.im|) := by
    have h5 : -(a / s.im) ≤ x / |s.im| := h1.trans (div_le_div_of_nonneg_right hax ht.le)
    have h7 : x ^ 2 - 1 ≤ (2 * s.re - 1) * (x / |s.im|) := by
      have e : (1 - x ^ 2) / (2 * s.re - 1) = -((x ^ 2 - 1) / (2 * s.re - 1)) := by ring
      have : (x ^ 2 - 1) / (2 * s.re - 1) ≤ x / |s.im| := by linarith
      rwa [div_le_iff₀ hσ, mul_comm] at this
    linarith
  set c := (2 * s.re - 1) / |s.im|
  have hc : 0 ≤ c := div_nonneg hσ.le ht.le
  have h2' : x ^ 2 ≤ 1 + c * x := by
    calc x ^ 2 ≤ 1 + (2 * s.re - 1) * (x / |s.im|) := h2
      _ = 1 + c * x := by simp only [c]; ring
  nlinarith

/-- **The same bound for `S₀`**: `|(s − 1)/s| ≤ 1` on `Re s ≥ ½`, so `|S₀(σ + it)| ≤ 1 + (2σ − 1)/|t|`. -/
theorem norm_S0_le {s : ℂ} (hre : 1 / 2 < s.re) (him : s.im ≠ 0) :
    ‖S0 s‖ ≤ 1 + (2 * s.re - 1) / |s.im| := by
  have h0 : s ≠ 0 := fun h => by rw [h, zero_im] at him; exact him rfl
  have hh : s ≠ 1 / 2 := fun h => by rw [h] at him; simp at him
  have h1 : s ≠ 1 := fun h => by rw [h, one_im] at him; exact him rfl
  have hB : ‖(s - 1) / s‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 h0)]
    have e1 : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have e2 : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have : ‖s - 1‖ ^ 2 ≤ ‖s‖ ^ 2 := by rw [e1, e2]; nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  rw [S0_eq h0 hh h1, norm_mul]
  calc ‖(s - 1) / s‖ * ‖scatteringMatrix s‖ ≤ 1 * ‖scatteringMatrix s‖ :=
        mul_le_mul_of_nonneg_right hB (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact norm_scatteringMatrix_le hre him

/-! ## The translation representation: `L²(ℝ)`, the shift, and the resonant states -/

/-- The Hilbert space `L²(ℝ)` of the translation representation. -/
abbrev L2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **The translation group** `(U(t)f)(u) = f(u − t)`. -/
def shift (t : ℝ) : L2 →L[ℂ] L2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ => u - t) (measurePreserving_sub_right volume t)).toContinuousLinearMap

lemma coeFn_shift (t : ℝ) (f : L2) : (shift t f : ℝ → ℂ) =ᵐ[volume] fun u => f (u - t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume t)

lemma shift_zero : shift 0 = ContinuousLinearMap.id ℂ L2 := by
  ext1 f
  refine Lp.ext ((coeFn_shift 0 f).trans (Eventually.of_forall fun u => ?_))
  simp

lemma shift_add (t s : ℝ) : shift (t + s) = (shift t).comp (shift s) := by
  ext1 f
  refine Lp.ext ?_
  have h1 := coeFn_shift (t + s) f
  have h2 := coeFn_shift t (shift s f)
  have h3 := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae (coeFn_shift s f)
  filter_upwards [h1, h2, h3] with u e1 e2 e3
  rw [e1, ContinuousLinearMap.comp_apply, e2, e3, sub_sub]

lemma shift_inner (t : ℝ) (x y : L2) : ⟪shift t x, shift t y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ => u - t) (measurePreserving_sub_right volume t)).inner_map_map x y

/-- **The incoming subspace** `D₋ = L²(−∞, 0)`: the functions vanishing almost everywhere on `[0, ∞)`. -/
def Dminus : Submodule ℂ L2 where
  carrier := {f | ∀ᵐ u ∂volume, 0 ≤ u → (f : ℝ → ℂ) u = 0}
  add_mem' := by
    intro f g hf hg
    change ∀ᵐ u ∂volume, 0 ≤ u → (f : ℝ → ℂ) u = 0 at hf
    change ∀ᵐ u ∂volume, 0 ≤ u → (g : ℝ → ℂ) u = 0 at hg
    change ∀ᵐ u ∂volume, 0 ≤ u → ((f + g : L2) : ℝ → ℂ) u = 0
    filter_upwards [Lp.coeFn_add f g, hf, hg] with u h1 h2 h3 hu
    rw [h1, Pi.add_apply, h2 hu, h3 hu, add_zero]
  zero_mem' := by
    change ∀ᵐ u ∂volume, 0 ≤ u → ((0 : L2) : ℝ → ℂ) u = 0
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with u h _
    rw [h, Pi.zero_apply]
  smul_mem' := by
    intro c f hf
    change ∀ᵐ u ∂volume, 0 ≤ u → (f : ℝ → ℂ) u = 0 at hf
    change ∀ᵐ u ∂volume, 0 ≤ u → ((c • f : L2) : ℝ → ℂ) u = 0
    filter_upwards [Lp.coeFn_smul c f, hf] with u h1 h2 hu
    rw [h1, Pi.smul_apply, h2 hu, smul_zero]

/-- `U(−t)D₋ ⊆ D₋` for `t ≥ 0`. -/
lemma shift_neg_Dminus {t : ℝ} (ht : 0 ≤ t) {f : L2} (hf : f ∈ Dminus) : shift (-t) f ∈ Dminus := by
  have h := (measurePreserving_sub_right volume (-t)).quasiMeasurePreserving.ae hf
  filter_upwards [coeFn_shift (-t) f, h] with u e1 e2 hu
  rw [e1]
  exact e2 (by linarith)

/-- The function `u ↦ e^{−μu}` on `u ≥ 0`, `0` on `u < 0`. -/
def expFun (μ : ℂ) (u : ℝ) : ℂ := Set.indicator (Ici 0) (fun u : ℝ => cexp (-(μ * u))) u

lemma memLp_expFun {μ : ℂ} (hμ : 0 < μ.re) : MemLp (expFun μ) 2 volume := by
  have hm : Measurable (expFun μ) := (by fun_prop : Measurable fun u : ℝ => cexp (-(μ * u))).indicator
    measurableSet_Ici
  refine (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 ?_
  have e : (fun u => ‖expFun μ u‖ ^ 2) = Set.indicator (Ici 0) (fun u : ℝ => Real.exp ((-2 * μ.re) * u)) := by
    funext u
    by_cases hu : u ∈ Ici (0 : ℝ)
    · rw [expFun, indicator_of_mem hu, indicator_of_mem hu, Complex.norm_exp, sq, ← Real.exp_add]
      congr 1; simp; ring
    · rw [expFun, indicator_of_notMem hu, indicator_of_notMem hu]; simp
  rw [e]
  have hI : IntegrableOn (fun u : ℝ => Real.exp ((-2 * μ.re) * u)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  exact hI.integrable_indicator measurableSet_Ici

/-- **The resonant state** `e_μ(u) = e^{−μu} 1_{u ≥ 0}` in `L²(ℝ)` (for `Re μ > 0`; `0` otherwise). -/
def e (μ : ℂ) : L2 := if hμ : 0 < μ.re then (memLp_expFun hμ).toLp _ else 0

lemma coeFn_e {μ : ℂ} (hμ : 0 < μ.re) : (e μ : ℝ → ℂ) =ᵐ[volume] expFun μ := by
  simp only [e, hμ, ↓reduceDIte]
  exact MemLp.coeFn_toLp _

/-- `e_μ ≠ 0` for `Re μ > 0`. -/
lemma e_ne_zero {μ : ℂ} (hμ : 0 < μ.re) : e μ ≠ 0 := by
  intro h
  have h1 := coeFn_e hμ
  rw [h] at h1
  have h2 := (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)).symm.trans h1
  have h3 : ∀ᵐ u ∂(volume : Measure ℝ), u < 0 := by
    filter_upwards [h2] with u hu
    by_contra hnu
    have hmem : u ∈ Ici (0 : ℝ) := not_lt.1 hnu
    rw [Pi.zero_apply, expFun, indicator_of_mem hmem] at hu
    exact Complex.exp_ne_zero _ hu.symm
  rw [ae_iff] at h3
  have h4 : volume (Ici (0 : ℝ)) = 0 := measure_mono_null (fun u hu => not_lt.2 hu) h3
  rw [Real.volume_Ici] at h4
  exact ENNReal.top_ne_zero h4

/-- `e_μ ⊥ D₋`. -/
lemma e_mem_Dminus_perp {μ : ℂ} (hμ : 0 < μ.re) : e μ ∈ Dminusᗮ := by
  rw [Submodule.mem_orthogonal]
  intro g hg
  rw [MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(hg : ∀ᵐ u ∂volume, 0 ≤ u → (g : ℝ → ℂ) u = 0), coeFn_e hμ] with u h1 h2
  by_cases hu : 0 ≤ u
  · rw [h1 hu, inner_zero_left, Pi.zero_apply]
  · rw [h2, expFun, indicator_of_notMem (by simpa using hu), inner_zero_right, Pi.zero_apply]

/-- **`U(−t)e_μ = e^{−μt}e_μ` modulo `D₋`** for `t ≥ 0`: on `u ≥ 0`, `e^{−μ(u + t)} = e^{−μt}e^{−μu}`. -/
lemma shift_neg_e_sub_mem {μ : ℂ} (hμ : 0 < μ.re) {t : ℝ} (ht : 0 ≤ t) :
    shift (-t) (e μ) - cexp (-(μ * t)) • e μ ∈ Dminus := by
  have h := (measurePreserving_sub_right volume (-t)).quasiMeasurePreserving.ae (coeFn_e hμ)
  filter_upwards [Lp.coeFn_sub (shift (-t) (e μ)) (cexp (-(μ * t)) • e μ), Lp.coeFn_smul (cexp (-(μ * t))) (e μ),
    coeFn_shift (-t) (e μ), coeFn_e hμ, h] with u h1 h2 h3 h4 h5 hu
  have hu' : u - -t ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, expFun, expFun, indicator_of_mem hu',
    indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu), smul_eq_mul, ← Complex.exp_add, sub_eq_zero]
  congr 1
  push_cast
  ring

/-- The span of the resonant states `e_μ`, `μ` a resonance. -/
def resSpan : Submodule ℂ L2 := Submodule.span ℂ (e '' resonances)

/-- `W = D₋ + span{e_μ}` is invariant under `U(−t)`, `t ≥ 0`. -/
lemma shift_neg_W {t : ℝ} (ht : 0 ≤ t) : Dminus ⊔ resSpan ≤ (Dminus ⊔ resSpan).comap (shift (-t)).toLinearMap := by
  refine sup_le (fun f hf => Submodule.mem_sup_left (shift_neg_Dminus ht hf)) ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨μ, hμ, rfl⟩
  show shift (-t) (e μ) ∈ Dminus ⊔ resSpan
  have h := shift_neg_e_sub_mem hμ.1 ht
  rw [show shift (-t) (e μ) = (shift (-t) (e μ) - cexp (-(μ * t)) • e μ) + cexp (-(μ * t)) • e μ by abel]
  exact Submodule.add_mem_sup h (Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, rfl⟩))

/-- **The outgoing subspace** `D₊ = (D₋ + span{e_μ})^⊥`: the functions on `[0, ∞)` whose Laplace transform vanishes
at every resonance (the Beurling–Lax subspace `B·H²` of the Blaschke product `B` of the resonances). -/
abbrev Dplus : Submodule ℂ L2 := (Dminus ⊔ resSpan)ᗮ

/-- `U(t)D₊ ⊆ D₊` for `t ≥ 0`. -/
lemma shift_Dplus {t : ℝ} (ht : 0 ≤ t) {g : L2} (hg : g ∈ Dplus) : shift t g ∈ Dplus := by
  rw [Dplus, Submodule.mem_orthogonal] at hg ⊢
  intro w hw
  have hw' := shift_neg_W ht hw
  have hU : ⟪w, shift t g⟫_ℂ = ⟪shift (-t) w, g⟫_ℂ := by
    conv_lhs => rw [← show shift t (shift (-t) w) = w by
      rw [← ContinuousLinearMap.comp_apply, ← shift_add, add_neg_cancel, shift_zero]; rfl]
    exact shift_inner t _ _
  rw [hU]
  exact hg _ hw'

/-- **The Lax–Phillips scattering system of `S₀`** in its translation representation: `H = L²(ℝ)`, `U(t)` the
translations, `D₋ = L²(−∞, 0)`, `D₊ = (D₋ + span{e_μ : μ resonance})^⊥`. -/
abbrev LP : LPData L2 where
  U := shift
  U_zero := shift_zero
  U_add := shift_add
  U_inner := shift_inner
  Dm := Dminus
  Dp := Dplus
  hDp := Submodule.HasOrthogonalProjection.ofCompleteSpace (K := Dplus)
  Dm_inv := fun _ ht _ hx => shift_neg_Dminus ht hx
  Dp_inv := fun _ ht _ hx => shift_Dplus ht hx
  orth := Submodule.orthogonal_le le_sup_left

/-- **Each resonant state lies in the scattering subspace** `K = (D₋ ⊕ D₊)^⊥`. -/
theorem e_mem_K {μ : ℂ} (hμ : μ ∈ resonances) : e μ ∈ LP.K := by
  refine LP.mem_K.2 ⟨e_mem_Dminus_perp hμ.1, ?_⟩
  exact Submodule.le_orthogonal_orthogonal _ (Submodule.mem_sup_right (Submodule.subset_span ⟨μ, hμ, rfl⟩))

/-- **Each resonance is an eigenvalue of the Lax–Phillips semigroup**: `Z(t)* e_μ = e^{−μt} e_μ` for `t ≥ 0`. -/
theorem Zstar_e {μ : ℂ} (hμ : μ ∈ resonances) {t : ℝ} (ht : 0 ≤ t) :
    LP.Zstar t (e μ) = cexp (-(μ * t)) • e μ := by
  have hK := e_mem_K hμ
  have h := shift_neg_e_sub_mem hμ.1 ht
  simp only [LPData.Zstar, ContinuousLinearMap.comp_apply]
  rw [LP.P_of_mem hK]
  rw [show shift (-t) (e μ) = (shift (-t) (e μ) - cexp (-(μ * t)) • e μ) + cexp (-(μ * t)) • e μ by abel,
    map_add, LP.P_Dm h, zero_add, map_smul, LP.P_of_mem hK]

/-- **The decay rate of a resonant state** is `Re μ`: `‖Z(t)* e_μ‖ = e^{−t Re μ}‖e_μ‖`. -/
theorem norm_Zstar_e {μ : ℂ} (hμ : μ ∈ resonances) {t : ℝ} (ht : 0 ≤ t) :
    ‖LP.Zstar t (e μ)‖ = Real.exp (-(μ.re * t)) * ‖e μ‖ := by
  rw [Zstar_e hμ ht, norm_smul, Complex.norm_exp]
  congr 2
  simp

/-- **No faster decay of the semigroup than any resonance**: `e^{−t Re μ} ≤ ‖Z(t)‖ ≤ 1`. -/
theorem exp_le_norm_Z {μ : ℂ} (hμ : μ ∈ resonances) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(μ.re * t)) ≤ ‖LP.Z t‖ ∧ ‖LP.Z t‖ ≤ 1 := by
  have hpos : 0 < ‖e μ‖ := norm_pos_iff.2 (e_ne_zero hμ.1)
  refine ⟨?_, ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact LP.norm_Z_le t x⟩
  have h1 : ‖LP.Zstar t (e μ)‖ ≤ ‖LP.Z t‖ * ‖e μ‖ := by
    rw [← LP.adjoint_Z, ← ContinuousLinearMap.adjoint.norm_map (LP.Z t)]
    exact ContinuousLinearMap.le_opNorm _ _
  rw [norm_Zstar_e hμ ht] at h1
  exact le_of_mul_le_mul_right h1 hpos

/-- **RH is one uniform decay rate**: Mathlib's `RiemannHypothesis` holds iff every resonant state decays at exactly
the rate `¼`: `‖Z(t)* e_μ‖ = e^{−t/4}‖e_μ‖` for every resonance `μ` and `t ≥ 0`. -/
theorem rh_iff_uniform_decay : RiemannHypothesis ↔
    ∀ μ ∈ resonances, ∀ t : ℝ, 0 ≤ t → ‖LP.Zstar t (e μ)‖ = Real.exp (-(t / 4)) * ‖e μ‖ := by
  rw [rh_iff_resonances_quarter]
  constructor
  · intro h μ hμ t ht
    rw [norm_Zstar_e hμ ht, h μ hμ]
    ring_nf
  · intro h μ hμ
    have h1 := h μ hμ 1 zero_le_one
    rw [norm_Zstar_e hμ zero_le_one] at h1
    have h2 := mul_right_cancel₀ (norm_ne_zero_iff.2 (e_ne_zero hμ.1)) h1
    have h3 := Real.exp_injective h2
    linarith

/-- **RH is no resonant state decaying faster than `e^{−t/4}`**: RH iff `‖Z(t)* e_μ‖ ≥ e^{−t/4}‖e_μ‖` for every
resonance `μ` and `t ≥ 0` (the pairing `μ ↔ ½ − μ` gives the rest). -/
theorem rh_iff_decay_le_quarter : RiemannHypothesis ↔
    ∀ μ ∈ resonances, ∀ t : ℝ, 0 ≤ t → Real.exp (-(t / 4)) * ‖e μ‖ ≤ ‖LP.Zstar t (e μ)‖ := by
  rw [rh_iff_resonances_le_quarter]
  constructor
  · intro h μ hμ t ht
    rw [norm_Zstar_e hμ ht]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [h μ hμ]
  · intro h μ hμ
    have h1 := h μ hμ 1 zero_le_one
    rw [norm_Zstar_e hμ zero_le_one] at h1
    have h2 := le_of_mul_le_mul_right h1 (norm_pos_iff.2 (e_ne_zero hμ.1))
    have h3 := Real.exp_le_exp.1 h2
    linarith

end ModLaxPhillips
