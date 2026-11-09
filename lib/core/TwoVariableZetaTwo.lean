/-
# The two-variable zeta function at `w = 2` is the completed Dedekind zeta function of `ℚ(i)`

Plain statement. At `w = 2` the theta function of Lagarias and Rains's `Z(w, s)` (`TwoVariableZeta.Z`) is that of the
Gaussian integers: `θ(t)² = Σ_{n ≥ 0} r₂(n)e^{−πnt}` with `r₂ = GlobalTeeth.R`. With Jacobi's two-square theorem in
the form `Σ r₂(n)n^{−z} = 4ζ(z)L(z, χ₋₄)` (`Madelung.lseries_R`), the Mellin transform gives
`Z(2, s) = 2Γ_ℝ(s)ζ(s/2)L(s/2, χ₋₄)` on `Re s > 2` (`Z_two`). With `Γ_ℝ(z)Γ_ℝ(z + 1) = Γ_ℂ(z)` this reads
`Z(2, 2z) = 2^z ζ̂(z)Λ(z, χ₋₄)`, with Mathlib's completed functions `completedRiemannZeta` and
`DirichletCharacter.completedLFunction`: the completed Dedekind zeta function `|d|^{z/2}Γ_ℂ(z)ζ_{ℚ(i)}(z)` of `ℚ(i)`.
Both sides are holomorphic off `z = 0, 1`, so by the identity theorem the equation holds there (`Z_two_eq`).
* In the strip `0 < Re s < 2` the zeros of `Z(2, ·)` are those of `ζ(s/2)L(s/2, χ₋₄)` (`Z_two_eq_zero_iff`).
* **The Riemann hypothesis for `Z(2, ·)` on its line `Re s = 1` is RH for `ζ` and GRH for `χ₋₄`** (`rh_two_iff`),
  and so it is Weil's twin criterion for `ζ_{ℚ(i)}` (`rh_two_iff_QK_twins`, from `Dedekind4.rh_grh_iff_QK_twins`).
So the family `Z(w, ·)` carries the library's criteria at `w = 1` (`TwoVariableZeta.Z_one`: RH) and `w = 2`
(RH and GRH for `χ₋₄`), and fails them at `w = 4` (`TwoVariableZetaPurity.exists_zero_re_ne_two`).
-/
import Mathlib
import TwoVariableZeta
import Madelung
import WeilDedekind

open Real Complex Filter Topology Set MeasureTheory HurwitzZeta
open WeilForm WeilTest

noncomputable section

namespace TwoVariableZetaTwo

open TwoVariableZeta (Z thetaPow hasMellin hasSum_theta)

/-! ## `θ² = Σ r₂(n) e^{−πnt}` -/

lemma R_zero : GlobalTeeth.R 0 = 1 := by rw [GlobalTeeth.R_eq_pairs]; decide

/-- **`θ(t)² = Σ_{n ≥ 0} r₂(n) e^{−πnt}`**: expand the square as a sum over `ℤ²` and group by `|v|²`. -/
lemma hasSum_theta_two {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (GlobalTeeth.R n : ℝ) * rexp (-π * n * t)) (evenKernel 0 t ^ 2) := by
  set g : ℤ → ℝ := fun n => rexp (-π * (n : ℝ) ^ 2 * t) with hg
  have hθ : HasSum g (evenKernel 0 t) := hasSum_theta ht
  have g0 : 0 ≤ g := fun n => (Real.exp_pos _).le
  have h2 : HasSum (fun p : ℤ × ℤ => g p.1 * g p.2) (evenKernel 0 t * evenKernel 0 t) :=
    hθ.mul hθ (hθ.summable.mul_of_nonneg hθ.summable g0 g0)
  let N : ℤ × ℤ → ℕ := fun p => p.1.natAbs ^ 2 + p.2.natAbs ^ 2
  have hfun : (fun p : ℤ × ℤ => g p.1 * g p.2) = fun p => rexp (-π * (N p : ℝ) * t) := by
    funext p
    simp only [g, N, ← Real.exp_add, Nat.cast_add, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
    congr 1
    ring
  have hv : HasSum (fun p : ℤ × ℤ => rexp (-π * (N p : ℝ) * t)) (evenKernel 0 t ^ 2) := by
    rw [← hfun, sq]
    exact h2
  convert hv.tsum_fiberwise N using 1
  funext n
  have hset : N ⁻¹' {n} = ↑((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
      (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))) := by
    ext p
    have key : N p = n ↔ p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
      rw [← Nat.cast_inj (R := ℤ)]
      simp only [N, Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq, key]
    constructor
    · intro h
      have h1 : p.1 ^ 2 ≤ n := by nlinarith [sq_nonneg p.2]
      have h2 : p.2 ^ 2 ≤ n := by nlinarith [sq_nonneg p.1]
      have a1 := Int.natAbs_le_self_sq p.1
      have a2 := Int.natAbs_le_self_sq p.2
      rw [Int.natCast_natAbs] at a1 a2
      exact ⟨⟨abs_le.1 (a1.trans h1), abs_le.1 (a2.trans h2)⟩, h⟩
    · exact fun h => h.2
  rw [tsum_congr fun p : ↑(N ⁻¹' {n}) => show rexp (-π * (N p : ℝ) * t) = rexp (-π * n * t) by
    rw [show N p = n from p.2], hset, tsum_const, Nat.card_coe_set_eq, Set.ncard_coe_finset, nsmul_eq_mul,
    GlobalTeeth.R_eq_pairs]

/-! ## `Z(2, s)` on `Re s > 2` -/

/-- **At `w = 2`, `Z` is the completed Dedekind zeta function of `ℚ(i)`**: on `Re s > 2`,
`Z(2, s) = 2Γ_ℝ(s)ζ(s/2)L(s/2, χ₋₄)`, by Jacobi's two-square theorem. -/
theorem Z_two {s : ℂ} (hs : 2 < s.re) :
    Z 2 two_pos s =
      2 * Gammaℝ s * riemannZeta (s / 2) * DirichletCharacter.LFunction AngularFamily.χ4C (s / 2) := by
  set z := s / 2 with hz_def
  have hz : 1 < z.re := by rw [hz_def, div_ofNat_re]; linarith
  have hsum := Madelung.summable_R hz
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum
      (fun i : ℕ => if (i : ℝ) = 0 then 0 else (GlobalTeeth.R i : ℂ) * rexp (-π * i * t)) (thetaPow 2 t - 1) := by
    intro t ht
    have h := (hasSum_ofReal.2 (hasSum_theta_two ht)).update 0 0
    convert h using 1
    · funext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp
      · simp [hi]
    · simp [thetaPow, R_zero]
      ring
  have h_sum : Summable fun i : ℕ => ‖(GlobalTeeth.R i : ℂ)‖ / (i : ℝ) ^ z.re := by
    refine hsum.norm.congr fun i => ?_
    rcases eq_or_ne i 0 with rfl | hi
    · simp [Real.zero_rpow (by linarith : z.re ≠ 0)]
    · rw [LSeries.norm_term_eq, ite_eq_right hi]
  have hD := hasSum_mellin_pi_mul₀ (a := fun i : ℕ => (GlobalTeeth.R i : ℂ)) (p := fun i : ℕ => (i : ℝ))
    (F := fun t => thetaPow 2 t - 1) (s := z) (fun i => Nat.cast_nonneg i) (by linarith) hF h_sum
  rw [(hasMellin 2 two_pos (by simpa using hs)).2] at hD
  have hT : (fun i : ℕ => (π : ℂ) ^ (-z) * Gamma z * (GlobalTeeth.R i : ℂ) / ((i : ℝ) : ℂ) ^ z) =
      fun i => (π : ℂ) ^ (-z) * Gamma z * LSeries.term (fun n => (GlobalTeeth.R n : ℂ)) z i := by
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; norm_num at hz
      simp [Complex.zero_cpow hz0]
    · rw [LSeries.term_of_ne_zero hi, ofReal_natCast]
      ring
  rw [hT] at hD
  have e := hD.unique (hsum.LSeriesHasSum.mul_left _)
  rw [Madelung.lseries_R hz, Gammaℝ_def, neg_div] at *
  rw [← hz_def]
  linear_combination e / 2

/-! ## The continuation -/

lemma odd_χ4C : AngularFamily.χ4C.Odd := by
  have h : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  show AngularFamily.χ4C (-1) = -1
  simp [AngularFamily.χ4C, MulChar.ringHomComp_apply, h]

lemma completedRiemannZeta_eq {z : ℂ} (hz : 0 < z.re) : completedRiemannZeta z = Gammaℝ z * riemannZeta z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  rw [riemannZeta_def_of_ne_zero hz0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hz)]

lemma completedLFunction_eq {z : ℂ} (hz : 0 < z.re) :
    DirichletCharacter.completedLFunction AngularFamily.χ4C z =
      Gammaℝ (z + 1) * DirichletCharacter.LFunction AngularFamily.χ4C z := by
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor AngularFamily.χ4C z (Or.inr (by norm_num))
  rw [odd_χ4C.gammaFactor_def] at h
  rw [h, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))]

/-- `2Γ_ℝ(2z) = 2^z Γ_ℝ(z)Γ_ℝ(z + 1)`, from `Γ_ℝ(z)Γ_ℝ(z + 1) = Γ_ℂ(z)`. -/
lemma two_mul_Gammaℝ_two_mul (z : ℂ) : 2 * Gammaℝ (2 * z) = 2 ^ z * (Gammaℝ z * Gammaℝ (z + 1)) := by
  rw [Gammaℝ_mul_Gammaℝ_add_one, Gammaℂ_def, Gammaℝ_def, show -(2 * z) / 2 = -z by ring,
    show 2 * z / 2 = z by ring, show (2 * π : ℂ) = ((2 : ℝ) : ℂ) * (π : ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
  push_cast
  have h2 : (2 : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
  rw [cpow_neg (2 : ℂ)]
  field_simp

/-- **`Z(2, 2z) = 2^z ζ̂(z)Λ(z, χ₋₄)` off `z = 0, 1`**: the completed Dedekind zeta function of `ℚ(i)`, the
continuation of `Z_two` to the plane by the identity theorem. -/
theorem Z_two_eq {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    Z 2 two_pos (2 * z) =
      2 ^ z * completedRiemannZeta z * DirichletCharacter.completedLFunction AngularFamily.χ4C z := by
  set U : Set ℂ := ({0, 1} : Set ℂ)ᶜ with hU
  have hfin : ({0, 1} : Set ℂ).Finite := by simp
  have hUo : IsOpen U := hfin.isClosed.isOpen_compl
  have hUc : IsPreconnected U :=
    (hfin.countable.isPathConnected_compl_of_one_lt_rank (by rw [rank_real_complex]; norm_num)).isConnected
      |>.isPreconnected
  have hf : DifferentiableOn ℂ (fun z => Z 2 two_pos (2 * z)) U := by
    intro z hz
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    have hd := TwoVariableZeta.differentiableAt 2 two_pos (s := 2 * z) (mul_ne_zero two_ne_zero hz.1)
      (fun h => hz.2 (by push_cast at h; linear_combination h / 2))
    exact (hd.comp z (differentiableAt_id.const_mul (2 : ℂ))).differentiableWithinAt
  have hg : DifferentiableOn ℂ
      (fun z => 2 ^ z * completedRiemannZeta z * DirichletCharacter.completedLFunction AngularFamily.χ4C z) U := by
    intro z hz
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) z := differentiableAt_id.const_cpow (Or.inl two_ne_zero)
    have hζ : DifferentiableAt ℂ completedRiemannZeta z := differentiableAt_completedZeta hz.1 hz.2
    have hL : DifferentiableAt ℂ (DirichletCharacter.completedLFunction AngularFamily.χ4C) z :=
      (DirichletCharacter.differentiable_completedLFunction Madelung.χ4C_ne_one) z
    exact ((h2.mul hζ).mul hL).differentiableWithinAt
  have heq : (fun z => Z 2 two_pos (2 * z)) =ᶠ[𝓝 2]
      fun z => 2 ^ z * completedRiemannZeta z * DirichletCharacter.completedLFunction AngularFamily.χ4C z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hs : 2 < (2 * z).re := by simp; linarith
    rw [Z_two hs, show 2 * z / 2 = z by ring, completedRiemannZeta_eq (by linarith),
      completedLFunction_eq (by linarith)]
    linear_combination (riemannZeta z * DirichletCharacter.LFunction AngularFamily.χ4C z) *
      two_mul_Gammaℝ_two_mul z
  have h2 : (2 : ℂ) ∈ U := by
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    norm_num
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hUc h2 heq
    (by simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨h0, h1⟩)

/-! ## The zeros and the Riemann hypothesis at `w = 2` -/

/-- **In the strip `0 < Re s < 2`, `Z(2, s) = 0` exactly when `ζ(s/2) = 0` or `L(s/2, χ₋₄) = 0`.** -/
theorem Z_two_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h2 : s.re < 2) :
    Z 2 two_pos s = 0 ↔
      riemannZeta (s / 2) = 0 ∨ DirichletCharacter.LFunction AngularFamily.χ4C (s / 2) = 0 := by
  obtain ⟨z, rfl⟩ : ∃ z, s = 2 * z := ⟨s / 2, by ring⟩
  have hre : (2 * z).re = 2 * z.re := by simp
  rw [hre] at h0 h2
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; linarith
  have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at h2; linarith
  have hpos : 0 < z.re := by linarith
  rw [Z_two_eq hz0 hz1, show 2 * z / 2 = z by ring, completedRiemannZeta_eq hpos, completedLFunction_eq hpos]
  have hA : (2 : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
  have hB : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
  have hC : Gammaℝ (z + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  simp only [mul_eq_zero, hA, hB, hC, false_or]

/-- **The Riemann hypothesis for `Z(2, ·)` on its line `Re s = 1` is RH for `ζ` and GRH for `χ₋₄`**: the zeros of
`Z(2, ·)` in the strip `0 < Re s < 2` are the `2ρ` for the zeros `ρ` of `ζ` and of `L(s, χ₋₄)` with `0 < Re ρ < 1`. -/
theorem rh_two_iff :
    (∀ s : ℂ, 0 < s.re → s.re < 2 → Z 2 two_pos s = 0 → s.re = 1) ↔
      (RiemannHypothesis ∧ PsiOmega.GRH PsiOmega.chi4) := by
  constructor
  · intro h
    refine ⟨fun ρ hρ htriv _ => ?_, fun ρ hL h0 h1 => ?_⟩
    · have hnt : IsNontrivialZero ρ := ⟨hρ, htriv⟩
      have hre0 := hnt.re_pos
      have hre1 := hnt.re_lt_one
      have hs0 : 0 < (2 * ρ).re := by simp; linarith
      have hs2 : (2 * ρ).re < 2 := by simp; linarith
      have := h (2 * ρ) hs0 hs2 ((Z_two_eq_zero_iff hs0 hs2).2 (Or.inl (by rw [show 2 * ρ / 2 = ρ by ring]; exact hρ)))
      simp at this
      linarith
    · have hs0 : 0 < (2 * ρ).re := by simp; linarith
      have hs2 : (2 * ρ).re < 2 := by simp; linarith
      have := h (2 * ρ) hs0 hs2 ((Z_two_eq_zero_iff hs0 hs2).2 (Or.inr (by rw [show 2 * ρ / 2 = ρ by ring]; exact hL)))
      simp at this
      linarith
  · rintro ⟨hRH, hG⟩ s h0 h2 hz
    have hre : (s / 2).re = s.re / 2 := by simp
    rcases (Z_two_eq_zero_iff h0 h2).1 hz with h | h
    · have htriv : ¬∃ n : ℕ, s / 2 = -2 * (n + 1) := by
        rintro ⟨n, hn⟩
        have := congrArg Complex.re hn
        rw [hre] at this
        simp at this
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h1 : s / 2 ≠ 1 := fun e => by
        have := congrArg Complex.re e
        rw [hre] at this
        simp at this
        linarith
      have := hRH (s / 2) h htriv h1
      rw [hre] at this
      linarith
    · have := hG (s / 2) h (by rw [hre]; linarith) (by rw [hre]; linarith)
      rw [hre] at this
      linarith

/-- **…and so it is Weil's twin criterion for `ζ_{ℚ(i)}`** (`Dedekind4.rh_grh_iff_QK_twins`): RH for `Z(2, ·)` on its
line holds exactly when the Dedekind twin form of `ℚ(i)` is nonnegative on the twin boxes. -/
theorem rh_two_iff_QK_twins :
    (∀ s : ℂ, 0 < s.re → s.re < 2 → Z 2 two_pos s = 0 → s.re = 1) ↔
      ∀ l : ℝ, 0 ≤ l → 0 ≤ Dedekind4.QK (l + 1) (twin (box 1) l) :=
  rh_two_iff.trans Dedekind4.rh_grh_iff_QK_twins

end TwoVariableZetaTwo

#print axioms TwoVariableZetaTwo.Z_two
#print axioms TwoVariableZetaTwo.Z_two_eq
#print axioms TwoVariableZetaTwo.Z_two_eq_zero_iff
#print axioms TwoVariableZetaTwo.rh_two_iff
#print axioms TwoVariableZetaTwo.rh_two_iff_QK_twins
