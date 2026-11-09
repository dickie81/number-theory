/-
# The two-variable zeta function at `w = 4` is the zeta function of `ℙ¹`, and it has zeros off its line

Plain statement. Lagarias and Rains's `Z(w, s)` (`TwoVariableZeta.Z`) has the functional equation `s ↦ w − s`, so
its line is `Re s = w/2`. At `w = 4`, by Jacobi's four-square theorem,
`Z(4, s) = 4Γ_ℝ(s)(1 − 4^{1−s/2})ζ(s/2)ζ(s/2 − 1)` on `Re s > 4` (`TwoVariableZeta.Z_four`). With
`Γ_ℝ(z − 1)Γ_ℝ(z) = Γ_ℂ(z − 1)` this reads `Z(4, 2z) = c(z)·ζ̂(z)ζ̂(z − 1)` with `c(z) = 2^z(z − 1)(1 − 4^{1−z})/π`
entire, and both sides are holomorphic off `z = 0, 1, 2`, a connected open set; by the identity theorem the equation
holds on all of it (`Z_four_eq`). So every zero `ρ'` of `ζ̂(z)ζ̂(z − 1)`, the completed zeta function of `ℙ¹` over `ℤ`
(`PurityRational.xiP1`), gives a zero `2ρ'` of `Z(4, ·)` (`Z_four_zP1`): the `2ρ` and `2ρ + 2` for the nontrivial
zeros `ρ` of `ζ`. The `2ρ` have `0 < Re 2ρ < 2`, so `Z(4, ·)` has zeros off its line `Re s = 2` whatever the truth of
RH (`exists_zero_re_ne_two`): the Riemann hypothesis fails at `w = 4`, where the Euler product is the mixed one of
`ℙ¹` (`PurityRational`).
-/
import Mathlib
import TwoVariableZeta
import PurityRational

open Real Complex Filter Topology Set WeilForm WeilTest

noncomputable section

namespace TwoVariableZetaPurity

open TwoVariableZeta PurityRational

/-- The entire factor `c(z) = 2^z(z − 1)(1 − 4^{1−z})/π` between `Z(4, 2z)` and `ζ̂(z)ζ̂(z − 1)`. -/
def c (z : ℂ) : ℂ := 2 ^ z * (z - 1) * (1 - 4 ^ (1 - z)) / π

lemma completedRiemannZeta_eq {z : ℂ} (hz : 0 < z.re) : completedRiemannZeta z = Gammaℝ z * riemannZeta z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  rw [riemannZeta_def_of_ne_zero hz0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hz)]

/-- On `Re z > 2`, from `TwoVariableZeta.Z_four` and the Gamma factors. -/
lemma Z_four_eq_of_re {z : ℂ} (hz : 2 < z.re) : Z 4 four_pos (2 * z) = c z * xiP1 z := by
  have hs : 4 < (2 * z).re := by simp; linarith
  have hz1 : z - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [Z_four hs, show 2 * z / 2 = z by ring, xiP1, completedRiemannZeta_eq (by linarith),
    completedRiemannZeta_eq (by simp; linarith)]
  -- the Gamma factors: `Γ_ℝ(2z) = π^{−z}Γ(z)`, `Γ_ℝ(z − 1)Γ_ℝ(z) = Γ_ℂ(z − 1)`, `Γ(z) = (z − 1)Γ(z − 1)`
  have hG : Gammaℝ (z - 1) * Gammaℝ z = 2 * (2 * π) ^ (-(z - 1)) * Gamma (z - 1) := by
    rw [← Gammaℂ_def, ← Gammaℝ_mul_Gammaℝ_add_one, sub_add_cancel]
  have hR : Gammaℝ (2 * z) = π ^ (-z) * ((z - 1) * Gamma (z - 1)) := by
    rw [Gammaℝ_def, show -(2 * z) / 2 = -z by ring, show 2 * z / 2 = z by ring, ← Complex.Gamma_add_one _ hz1,
      sub_add_cancel]
  rw [hR]
  have h2π : (2 * π : ℂ) ^ (-(z - 1)) = 2 ^ (1 - z) * π ^ (1 - z) := by
    rw [show -(z - 1) = 1 - z by ring, show (2 * π : ℂ) = ((2 : ℝ) : ℂ) * (π : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
    push_cast
    ring
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have e2 : (2 : ℂ) ^ (1 - z) = 2 / 2 ^ z := by rw [cpow_sub _ _ two_ne_zero, cpow_one]
  have eπ : (π : ℂ) ^ (1 - z) = π / π ^ z := by rw [cpow_sub _ _ hπ0, cpow_one]
  have eπ' : (π : ℂ) ^ (-z) = 1 / π ^ z := by rw [cpow_neg, one_div]
  have h2z : (2 : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
  have hπz : (π : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hπ0)
  calc 4 * (π ^ (-z) * ((z - 1) * Gamma (z - 1))) * (1 - 4 ^ (1 - z)) * riemannZeta z * riemannZeta (z - 1)
      = c z * (2 * (2 * π) ^ (-(z - 1)) * Gamma (z - 1)) * riemannZeta z * riemannZeta (z - 1) := by
        rw [h2π, e2, eπ, eπ']
        unfold c
        field_simp
        ring
    _ = c z * (Gammaℝ z * riemannZeta z * (Gammaℝ (z - 1) * riemannZeta (z - 1))) := by
        rw [← hG]
        ring

lemma differentiableAt_c (z : ℂ) : DifferentiableAt ℂ c z := by
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) z := differentiableAt_id.const_cpow (Or.inl two_ne_zero)
  have h4 : DifferentiableAt ℂ (fun z : ℂ => (4 : ℂ) ^ (1 - z)) z :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl (by norm_num : (4 : ℂ) ≠ 0))
  exact (((h2.mul (differentiableAt_id.sub (differentiableAt_const _))).mul
    ((differentiableAt_const _).sub h4)).div_const _)

/-- **`Z(4, 2z) = c(z)·ζ̂(z)ζ̂(z − 1)` off `z = 0, 1, 2`**, with `c(z) = 2^z(z − 1)(1 − 4^{1−z})/π`: the continuation of
`TwoVariableZeta.Z_four` to the plane, by the identity theorem. -/
theorem Z_four_eq {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (h2 : z ≠ 2) : Z 4 four_pos (2 * z) = c z * xiP1 z := by
  set U : Set ℂ := ({0, 1, 2} : Set ℂ)ᶜ with hU
  have hfin : ({0, 1, 2} : Set ℂ).Finite := by simp
  have hUo : IsOpen U := hfin.isClosed.isOpen_compl
  have hUc : IsPreconnected U :=
    (hfin.countable.isPathConnected_compl_of_one_lt_rank (by rw [rank_real_complex]; norm_num)).isConnected
      |>.isPreconnected
  have hf : DifferentiableOn ℂ (fun z => Z 4 four_pos (2 * z)) U := by
    intro z hz
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    have hd := differentiableAt 4 four_pos (s := 2 * z) (mul_ne_zero two_ne_zero hz.1)
      (fun h => hz.2.2 (by push_cast at h; linear_combination h / 2))
    exact (hd.comp z (differentiableAt_id.const_mul (2 : ℂ))).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => c z * xiP1 z) U := by
    intro z hz
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    have hz1 : DifferentiableAt ℂ completedRiemannZeta z := differentiableAt_completedZeta hz.1 hz.2.1
    have hz2 : DifferentiableAt ℂ (fun z => completedRiemannZeta (z - 1)) z :=
      (differentiableAt_completedZeta (sub_ne_zero.2 hz.2.1) (fun h => hz.2.2 (by linear_combination h))).comp z
        (differentiableAt_id.sub (differentiableAt_const _))
    exact ((differentiableAt_c z).mul (hz1.mul hz2)).differentiableWithinAt
  have heq : (fun z => Z 4 four_pos (2 * z)) =ᶠ[𝓝 3] fun z => c z * xiP1 z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    exact Z_four_eq_of_re hz
  have h3 : (3 : ℂ) ∈ U := by
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    norm_num
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hUc h3 heq
    (by simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨h0, h1, h2⟩)

lemma re_zP1 (q : ZIdx ⊕ ZIdx) : 0 < (zP1 q).re ∧ (zP1 q).re < 2 ∧ (zP1 q).re ≠ 1 := by
  rcases q with q | q
  · have h0 := (nontrivial_zZF q).re_pos
    have h1 := (nontrivial_zZF q).re_lt_one
    simp only [zP1, Sum.elim_inl]
    exact ⟨h0, by linarith, h1.ne⟩
  · have h0 := (nontrivial_zZF q).re_pos
    have h1 := (nontrivial_zZF q).re_lt_one
    simp only [zP1, Sum.elim_inr, Complex.add_re, Complex.one_re]
    exact ⟨by linarith, by linarith, by linarith⟩

/-- **Every zero of `ℙ¹` doubled is a zero of `Z(4, ·)`**: `Z(4, 2ρ') = 0` for `ρ' = ρ` and `ρ' = ρ + 1`, `ρ` a
nontrivial zero of `ζ`. -/
theorem Z_four_zP1 (q : ZIdx ⊕ ZIdx) : Z 4 four_pos (2 * zP1 q) = 0 := by
  obtain ⟨h0, h2, h1⟩ := re_zP1 q
  rw [Z_four_eq (fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0)
    (fun h => h1 (by rw [h, Complex.one_re])) (fun h => by rw [h] at h2; norm_num at h2), xiP1_zP1, mul_zero]

/-- **The Riemann hypothesis fails for `Z(4, ·)`, whatever the truth of RH**: it has a zero off its line `Re s = 2`,
twice a nontrivial zero of `ζ`. -/
theorem exists_zero_re_ne_two : ∃ s : ℂ, Z 4 four_pos s = 0 ∧ s.re ≠ 2 := by
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  refine ⟨2 * zP1 (Sum.inl q), Z_four_zP1 _, ?_⟩
  have h1 := (nontrivial_zZF q).re_lt_one
  have e : (2 * zP1 (Sum.inl q)).re = 2 * (zetaZeroFamily q).re := by simp [zP1]
  rw [e]
  linarith

end TwoVariableZetaPurity

#print axioms TwoVariableZetaPurity.Z_four_eq
#print axioms TwoVariableZetaPurity.Z_four_zP1
#print axioms TwoVariableZetaPurity.exists_zero_re_ne_two
