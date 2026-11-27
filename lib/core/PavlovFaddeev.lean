/-
# The scattering matrix of the modular surface: unitarity, and RH as one decay rate for its resonances

Plain statement. On the modular surface `SL(2, ℤ)\ℍ²` the Eisenstein series has constant term
`y^s + φ(s)y^{1−s}` with `φ(s) = ξ(2s − 1)/ξ(2s)`, where `ξ = Λ` is the completed zeta function (Mathlib's
`completedRiemannZeta`, with `Λ(1 − s) = Λ(s)`). B. S. Pavlov and L. D. Faddeev (1972) read `φ` as the scattering
matrix of the automorphic wave equation, and P. Lax and R. Phillips (1976) built its incoming and outgoing
subspaces. Here `φ` is the definition `scatteringMatrix`, and the results are about it alone; the Eisenstein series is
not built.
* **Functional equation** (`scatteringMatrix_mul_one_sub`): `φ(s)φ(1 − s) = 1` wherever `Λ(2s) ≠ 0` and
  `Λ(2s − 1) ≠ 0`, from `Λ(1 − s) = Λ(s)` alone.
* **Conjugation** (`completed_conj`, `scatteringMatrix_conj`): `Λ(s̄) = conj Λ(s)` for every `s`, from
  `XiReflection.xi_conj`, and so `φ(s̄) = conj φ(s)`.
* **Unitarity on the line of the continuous spectrum** (`norm_scatteringMatrix_line`): `|φ(½ + it)| = 1` for every
  real `t`, unconditionally: `Λ(1 + 2it) ≠ 0` (Mathlib's `ζ ≠ 0` on `Re s ≥ 1`, and `Γ_ℝ ≠ 0` on
  `Re s > 0`), and the numerator is the conjugate of the denominator.
* **The poles** (`completed_ne_zero_of_one_le_re`, `completed_ne_zero_of_re_le_zero`, `numerator_ne_zero`,
  `denominator_zero_strip`): `Λ` has no zeros off `0 < Re s < 1`, so the numerator `Λ(2s − 1)` vanishes nowhere on
  `Re s ≤ ½`, and the denominator `Λ(2s)` vanishes only in `0 < Re s < ½`. Each zero of the denominator is a pole of
  `φ` (`tendsto_norm_scatteringMatrix`), and in `0 < Re s < ½` the poles of `φ` are exactly the zeros of `Λ(2s)`
  (`pole_iff`): the resonances, at `s = ρ/2` for the nontrivial zeros `ρ` of `ζ`.
* **RH is one decay rate for every resonance** (`rh_iff_resonances_on_quarter`, `rh_iff_poles_on_quarter`):
  Mathlib's `RiemannHypothesis` holds if and only if every zero of `Λ(2s)` with `0 < Re s < ½` has `Re s = ¼`, if and
  only if every pole of `φ` in `0 < Re s < ½` lies on `Re s = ¼`.
These are equivalences: no bearing on RH. At `t = 0`, `φ(½) = Λ(0)/Λ(1) = 1` uses Lean's values of `Λ` at its poles
(Mathlib's `Λ(0) = Λ(1) = (γ − log 4π)/2`); the limit of `φ` there is `−1`, of norm `1` as well.
-/
import Mathlib
import XiReflection

open Complex ComplexConjugate Filter Topology Set

noncomputable section

namespace PavlovFaddeev

/-- **The scattering matrix of `SL(2, ℤ)\ℍ²`**: `φ(s) = Λ(2s − 1)/Λ(2s)`, with Mathlib's completed zeta `Λ`. -/
def scatteringMatrix (s : ℂ) : ℂ := completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)

/-! ## The functional equation and conjugation -/

/-- **`φ(s)φ(1 − s) = 1`**, wherever `Λ(2s)` and `Λ(2s − 1)` are nonzero. -/
theorem scatteringMatrix_mul_one_sub {s : ℂ} (h0 : completedRiemannZeta (2 * s) ≠ 0)
    (h1 : completedRiemannZeta (2 * s - 1) ≠ 0) : scatteringMatrix s * scatteringMatrix (1 - s) = 1 := by
  unfold scatteringMatrix
  have e1 : completedRiemannZeta (2 * (1 - s) - 1) = completedRiemannZeta (2 * s) := by
    rw [← completedRiemannZeta_one_sub (2 * s)]; congr 1; ring
  have e2 : completedRiemannZeta (2 * (1 - s)) = completedRiemannZeta (2 * s - 1) := by
    rw [← completedRiemannZeta_one_sub (2 * s - 1)]; congr 1; ring
  rw [e1, e2]
  field_simp

/-- `Λ(1)` is real: Mathlib's value `(γ − log 4π)/2`. -/
lemma conj_completed_one : conj (completedRiemannZeta 1) = completedRiemannZeta 1 := by
  rw [completedRiemannZeta_one, map_div₀, map_sub, conj_ofReal, map_ofNat]
  congr 2
  rw [show (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_log (by positivity), conj_ofReal]

/-- **`Λ(s̄) = conj Λ(s)`** for every `s`: off `0` and `1` from `ξ(s̄) = conj ξ(s)` (`XiReflection.xi_conj`), and at
`0` and `1` because `Λ(0) = Λ(1)` is real. -/
theorem completed_conj (s : ℂ) : completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  by_cases h0 : s = 0
  · subst h0
    rw [map_zero, ← completedRiemannZeta_one_sub 0, sub_zero, conj_completed_one]
  by_cases h1 : s = 1
  · subst h1
    rw [map_one, conj_completed_one]
  have h0' : conj s ≠ 0 := fun h => h0 (by simpa using congrArg conj h)
  have h1' : conj s ≠ 1 := fun h => h1 (by simpa using congrArg conj h)
  have hx := XiReflection.xi_conj s
  rw [WeilForm.xi_eq h0' h1', WeilForm.xi_eq h0 h1] at hx
  simp only [map_div₀, map_mul, map_sub, map_one, map_ofNat] at hx
  have hne : conj s * (conj s - 1) ≠ 0 := mul_ne_zero h0' (sub_ne_zero.2 h1')
  have : conj s * (conj s - 1) * completedRiemannZeta (conj s) =
      conj s * (conj s - 1) * conj (completedRiemannZeta s) := by
    linear_combination 2 * hx
  exact mul_left_cancel₀ hne this

/-- **`φ(s̄) = conj φ(s)`**. -/
theorem scatteringMatrix_conj (s : ℂ) : scatteringMatrix (conj s) = conj (scatteringMatrix s) := by
  unfold scatteringMatrix
  rw [map_div₀, ← completed_conj, ← completed_conj]
  simp only [map_sub, map_mul, map_ofNat, map_one]

/-! ## Where `Λ` vanishes -/

/-- `Λ(s) = ζ(s)Γ_ℝ(s)` for `s ≠ 0` with `Γ_ℝ(s) ≠ 0`. -/
lemma completed_eq_mul {s : ℂ} (h0 : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero h0, div_mul_cancel₀ _ hG]

/-- **`Λ` has no zero on `Re s ≥ 1`**: Mathlib's `ζ ≠ 0` there, and `Γ_ℝ ≠ 0` on `Re s > 0`. -/
theorem completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : completedRiemannZeta s ≠ 0 := by
  have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hG := Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < s.re)
  rw [completed_eq_mul h0 hG]
  exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hs) hG

/-- **`Λ` has no zero on `Re s ≤ 0`**, by `Λ(1 − s) = Λ(s)`. -/
theorem completed_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  exact completed_ne_zero_of_one_le_re (by simp; linarith)

/-- In the strip `0 < Re s < 1`, `Λ(s) = 0` exactly when `ζ(s) = 0`. -/
lemma completed_eq_zero_iff {s : ℂ} (hs : 0 < s.re) : completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl _ hs
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [completed_eq_mul h0 hG, mul_eq_zero, or_iff_left hG]

/-- **The numerator vanishes nowhere on `Re s ≤ ½`**: there `Re(2s − 1) ≤ 0`. So each zero of `Λ(2s)` in
`0 < Re s < ½` is a genuine pole of `φ`. -/
theorem numerator_ne_zero {s : ℂ} (hs : s.re ≤ 1 / 2) : completedRiemannZeta (2 * s - 1) ≠ 0 :=
  completed_ne_zero_of_re_le_zero (by simp; linarith)

/-- **The denominator vanishes only in `0 < Re s < ½`**. -/
theorem denominator_zero_strip {s : ℂ} (hs : completedRiemannZeta (2 * s) = 0) : 0 < s.re ∧ s.re < 1 / 2 := by
  constructor
  · by_contra h
    exact completed_ne_zero_of_re_le_zero (by simp; linarith) hs
  · by_contra h
    exact completed_ne_zero_of_one_le_re (by simp; linarith) hs

/-! ## Unitarity on `Re s = ½` -/

/-- **`φ` is unitary on the line of the continuous spectrum**: `|φ(½ + it)| = 1` for every real `t`, with no
hypothesis. The numerator `Λ(2it) = Λ(1 − 2it)` is the conjugate of the denominator `Λ(1 + 2it) ≠ 0`. -/
theorem norm_scatteringMatrix_line (t : ℝ) : ‖scatteringMatrix (1 / 2 + t * I)‖ = 1 := by
  have hD : completedRiemannZeta (1 + 2 * t * I) ≠ 0 := completed_ne_zero_of_one_le_re (by simp)
  have e1 : 2 * (1 / 2 + t * I) = 1 + 2 * t * I := by ring
  have e2 : completedRiemannZeta (2 * (1 / 2 + t * I) - 1) = conj (completedRiemannZeta (1 + 2 * t * I)) := by
    rw [← completed_conj, ← completedRiemannZeta_one_sub]
    congr 1
    apply Complex.ext <;> simp
  unfold scatteringMatrix
  rw [e2, e1, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hD)]

/-! ## The resonances, and RH -/

/-- The complement of `{0, 1}` in `ℂ` is preconnected. -/
lemma isPreconnected_compl_zero_one : IsPreconnected ({0, 1}ᶜ : Set ℂ) :=
  ((countable_singleton (1 : ℂ)).insert 0).isConnected_compl_of_one_lt_rank (by simp) |>.isPreconnected

/-- `Λ` is analytic off `0` and `1`. -/
lemma analyticOnNhd_completed : AnalyticOnNhd ℂ completedRiemannZeta ({0, 1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) ?_
  · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  · exact ((finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl

/-- The zeros of `Λ` off `0` and `1` are isolated: `Λ(2) ≠ 0` and the identity theorem. -/
lemma completed_eventually_ne {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    ∀ᶠ z in 𝓝[≠] w, completedRiemannZeta z ≠ 0 := by
  have hw : w ∈ ({0, 1}ᶜ : Set ℂ) := by simp [h0, h1]
  rw [← not_frequently]
  intro hfr
  have h := analyticOnNhd_completed.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_compl_zero_one hw hfr (show (2 : ℂ) ∈ ({0, 1}ᶜ : Set ℂ) by norm_num)
  exact completed_ne_zero_of_one_le_re (s := 2) (by norm_num) h

/-- **Each zero of the denominator is a pole of `φ`**: if `Λ(2s₀) = 0`, then `|φ(s)| → ∞` as `s → s₀`. -/
theorem tendsto_norm_scatteringMatrix {s₀ : ℂ} (hs : completedRiemannZeta (2 * s₀) = 0) :
    Tendsto (fun s => ‖scatteringMatrix s‖) (𝓝[≠] s₀) atTop := by
  obtain ⟨hre0, hre1⟩ := denominator_zero_strip hs
  have h20 : 2 * s₀ ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have h21 : 2 * s₀ ≠ 1 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hN0 := numerator_ne_zero hre1.le
  have hm0 : 2 * s₀ - 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hm1 : 2 * s₀ - 1 ≠ 1 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hcN : ContinuousAt (fun s => completedRiemannZeta (2 * s - 1)) s₀ :=
    ContinuousAt.comp (g := completedRiemannZeta) (f := fun s : ℂ => 2 * s - 1) (x := s₀)
      (differentiableAt_completedZeta hm0 hm1).continuousAt (by fun_prop)
  have hcD : ContinuousAt (fun s => completedRiemannZeta (2 * s)) s₀ :=
    ContinuousAt.comp (g := completedRiemannZeta) (f := fun s : ℂ => 2 * s) (x := s₀)
      (differentiableAt_completedZeta h20 h21).continuousAt (by fun_prop)
  have hmap : Tendsto (fun s : ℂ => 2 * s) (𝓝[≠] s₀) (𝓝[≠] (2 * s₀)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.mul continuous_id).tendsto s₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_compl_iff, mem_singleton_iff] at hs ⊢
      exact fun h => hs (mul_left_cancel₀ two_ne_zero h)
  have hev : ∀ᶠ s in 𝓝[≠] s₀, completedRiemannZeta (2 * s) ≠ 0 := hmap.eventually (completed_eventually_ne h20 h21)
  have hD : Tendsto (fun s => ‖completedRiemannZeta (2 * s)‖) (𝓝[≠] s₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun s h => norm_pos_iff.2 h⟩
    have h := hcD.tendsto.norm
    rw [hs, norm_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hN : Tendsto (fun s => ‖completedRiemannZeta (2 * s - 1)‖) (𝓝[≠] s₀)
      (𝓝 ‖completedRiemannZeta (2 * s₀ - 1)‖) := hcN.norm.mono_left nhdsWithin_le_nhds
  refine (hN.pos_mul_atTop (norm_pos_iff.2 hN0) (tendsto_inv_nhdsGT_zero.comp hD)).congr fun s => ?_
  simp [scatteringMatrix, div_eq_mul_inv]

/-- **In `0 < Re s < ½` the poles of `φ` are the zeros of `Λ(2s)`**: `|φ(s)| → ∞` at `s₀` exactly when
`Λ(2s₀) = 0`; elsewhere `φ` is continuous at `s₀`. -/
theorem pole_iff {s₀ : ℂ} (h0 : 0 < s₀.re) (h1 : s₀.re < 1 / 2) :
    Tendsto (fun s => ‖scatteringMatrix s‖) (𝓝[≠] s₀) atTop ↔ completedRiemannZeta (2 * s₀) = 0 := by
  refine ⟨fun hT => ?_, tendsto_norm_scatteringMatrix⟩
  by_contra hD
  have h20 : 2 * s₀ ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have h21 : 2 * s₀ ≠ 1 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hm0 : 2 * s₀ - 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hm1 : 2 * s₀ - 1 ≠ 1 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hcN : ContinuousAt (fun s => completedRiemannZeta (2 * s - 1)) s₀ :=
    ContinuousAt.comp (g := completedRiemannZeta) (f := fun s : ℂ => 2 * s - 1) (x := s₀)
      (differentiableAt_completedZeta hm0 hm1).continuousAt (by fun_prop)
  have hcD : ContinuousAt (fun s => completedRiemannZeta (2 * s)) s₀ :=
    ContinuousAt.comp (g := completedRiemannZeta) (f := fun s : ℂ => 2 * s) (x := s₀)
      (differentiableAt_completedZeta h20 h21).continuousAt (by fun_prop)
  have hc : ContinuousAt (fun s => ‖scatteringMatrix s‖) s₀ := (hcN.div hcD hD).norm
  exact not_tendsto_nhds_of_tendsto_atTop hT _ (hc.tendsto.mono_left nhdsWithin_le_nhds)

/-- **RH is one decay rate for every resonance** (Pavlov–Faddeev): Mathlib's `RiemannHypothesis` holds if and only
if every zero of `Λ(2s)` with `0 < Re s < ½` lies on `Re s = ¼`. -/
theorem rh_iff_resonances_on_quarter : RiemannHypothesis ↔
    ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → completedRiemannZeta (2 * s) = 0 → s.re = 1 / 4 := by
  constructor
  · intro hRH s h0 h1 hs
    have hre : (2 * s).re = 2 * s.re := by simp
    have hz : riemannZeta (2 * s) = 0 := (completed_eq_zero_iff (by rw [hre]; linarith)).1 hs
    have hnt : ¬∃ n : ℕ, 2 * s = -2 * (n + 1) := fun ⟨n, hn⟩ => by
      have := congrArg re hn
      simp at this
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have h21 : 2 * s ≠ 1 := fun h => by
      have := congrArg re h; simp at this; linarith
    have := hRH _ hz hnt h21
    rw [hre] at this
    linarith
  · intro h w hw hnt hw1
    obtain ⟨hr0, hr1⟩ := WeilTest.IsNontrivialZero.mem_strip ⟨hw, hnt⟩
    have e : 2 * (w / 2) = w := by ring
    have hre : (w / 2).re = w.re / 2 := by simp
    have := h (w / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [e]; exact (completed_eq_zero_iff hr0).2 hw)
    rw [hre] at this
    linarith

/-- **RH is the poles of `φ` on one line**: Mathlib's `RiemannHypothesis` holds if and only if every pole of the
scattering matrix in `0 < Re s < ½` lies on `Re s = ¼`. -/
theorem rh_iff_poles_on_quarter : RiemannHypothesis ↔
    ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → Tendsto (fun z => ‖scatteringMatrix z‖) (𝓝[≠] s) atTop → s.re = 1 / 4 := by
  rw [rh_iff_resonances_on_quarter]
  exact forall_congr' fun s => forall_congr' fun h0 => forall_congr' fun h1 => by rw [pole_iff h0 h1]

end PavlovFaddeev
