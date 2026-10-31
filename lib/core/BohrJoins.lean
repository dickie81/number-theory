import Mathlib
import BohrSphere
import CubeBall
import Orthogonality
import BallTower
import DirMean
import PsiOmega
import HalfPlaneS0
import KubotaRows

/-! # The geometric picture joined to the library

This file proves joins between the geometric picture (the Bohr lift and the ball tower) and the theorems of the
library. Each runs from the library's results into the geometric picture, or between two tools. None of them proves
an open hypothesis.

* **Zero-free regions are shells around the sphere** (**`shell_of_zeroFree`**, with `norm_vF_le_norm_vF`): if `ζ ≠ 0`
  on `Re s > θ`, every nontrivial zero `ρ` has `‖v_F(θ)‖ ≤ ‖v_F(ρ)‖ ≤ ‖v_F(1 − θ)‖` for every nonempty finite set `F`
  of primes, through `PsiOmega.band_of_zeroFree`. Instances: unconditionally, strictly between the radii at `1` and
  `0` (**`shell_unconditional`**); from the Kubota–Patterson display, between the radii at `11/12` and `1/12`
  (**`shell_of_kubotaTheta`**).
* **In the limit no shell short of the sphere constrains the radius** (**`shell_radii_tendsto`**): for every `θ > ½`
  the radius at `θ` tends to `0` and the radius at `1 − θ` to `∞` over the primes below `N`. If RH fails, some zero
  pair has one Bohr vector strictly inside the sphere and one strictly outside, in every dimension, with radii
  tending to `0` and `∞` (**`zero_pair_of_not_RH`**). For the Davenport–Heilbronn function this is
  `dh_zero_pair_off_sphere` (`lib/dh/DHBohrSphere.lean`).
* **The ball tower and the Bohr lift in one identity** (**`completed_eq_sphereArea_bohr`**): for every integer
  `n ≥ 2`, `Λ(n) = (2/|S^{n−1}|)·exp(Σ_p p^{−n})·D₂(n)`, which joins `BallTower.Gammaℝ_mul_sphereArea` to the Euler
  split.
-/

open Filter Topology BohrSphere MeasureTheory Metric

namespace BohrJoins

/-! ## Part A: zero-free regions as shells around the sphere -/

/-- The radius is antitone in `Re s`. -/
lemma norm_vF_le_norm_vF {F : Finset Nat.Primes} (hF : F.Nonempty) {s s' : ℂ} (h : s.re ≤ s'.re) :
    ‖vF F s'‖ ≤ ‖vF F s‖ := by
  rcases h.lt_or_eq with h | h
  · exact (norm_vF_lt_norm_vF hF h).le
  · exact (norm_vF_eq_of_re_eq F h).ge

/-- **A zero-free half-plane is a shell around the sphere.** -/
theorem shell_of_zeroFree {θ : ℝ} (hzf : ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0)
    {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ} (hρ : WeilTest.IsNontrivialZero ρ) :
    ‖vF F θ‖ ≤ ‖vF F ρ‖ ∧ ‖vF F ρ‖ ≤ ‖vF F ((1 - θ : ℝ) : ℂ)‖ := by
  have hb := PsiOmega.band_of_zeroFree hzf hρ
  rw [abs_le] at hb
  constructor
  · exact norm_vF_le_norm_vF hF (by rw [Complex.ofReal_re]; linarith)
  · exact norm_vF_le_norm_vF hF (by rw [Complex.ofReal_re]; linarith)

/-- **Unconditionally** the nontrivial zeros lie strictly between the radii at `Re s = 1` and `Re s = 0`
(`WeilTest.IsNontrivialZero.re_lt_one`, `re_pos`). -/
theorem shell_unconditional {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ}
    (hρ : WeilTest.IsNontrivialZero ρ) : ‖vF F 1‖ < ‖vF F ρ‖ ∧ ‖vF F ρ‖ < ‖vF F 0‖ :=
  ⟨norm_vF_lt_norm_vF hF (by simpa using hρ.re_lt_one), norm_vF_lt_norm_vF hF (by simpa using hρ.re_pos)⟩

/-- From the Kubota–Patterson display (`Eis.ne_zero_of_kubotaTheta`): between the radii at `11/12`
and `1/12`. -/
theorem shell_of_kubotaTheta (hK : Eis.KubotaTheta) {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ}
    (hρ : WeilTest.IsNontrivialZero ρ) :
    ‖vF F ((11 / 12 : ℝ) : ℂ)‖ ≤ ‖vF F ρ‖ ∧ ‖vF F ρ‖ ≤ ‖vF F ((1 / 12 : ℝ) : ℂ)‖ := by
  have h := shell_of_zeroFree (θ := 11 / 12) (fun _ hs => (Eis.ne_zero_of_kubotaTheta hK hs).1) hF hρ
  norm_num at h ⊢
  exact h

/-- **In the limit no shell short of the sphere constrains the radius**: for `θ > ½` the radius at `θ` tends to
`0` and the radius at `1 − θ` to `∞` over the primes below `N`. -/
theorem shell_radii_tendsto {θ : ℝ} (hθ : 1 / 2 < θ) :
    Tendsto (fun N => ‖vF (primesLT N) (θ : ℂ)‖) atTop (𝓝 0) ∧
      Tendsto (fun N => ‖vF (primesLT N) ((1 - θ : ℝ) : ℂ)‖) atTop atTop :=
  ⟨tendsto_norm_vF_of_half_lt (by rw [Complex.ofReal_re]; exact hθ),
    tendsto_norm_vF_of_lt_half (by rw [Complex.ofReal_re]; linarith)⟩

/-- **If RH fails, some zero pair straddles the sphere**: one Bohr vector strictly inside and one strictly outside
in every dimension, with radii tending to `0` and `∞`. For the Davenport–Heilbronn function this is
`dh_zero_pair_off_sphere`. -/
theorem zero_pair_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, WeilTest.IsNontrivialZero ρ ∧ WeilTest.IsNontrivialZero (1 - ρ) ∧ 1 / 2 < ρ.re ∧
      (∀ F : Finset Nat.Primes, F.Nonempty → ‖vF F ρ‖ < 1 ∧ 1 < ‖vF F (1 - ρ)‖) ∧
      Tendsto (fun N => ‖vF (primesLT N) ρ‖) atTop (𝓝 0) ∧
      Tendsto (fun N => ‖vF (primesLT N) (1 - ρ)‖) atTop atTop := by
  obtain ⟨ρ, hre, hz⟩ : ∃ ρ : ℂ, 1 / 2 < ρ.re ∧ riemannZeta ρ = 0 := by
    by_contra hcon
    exact hRH (PsiOmega.rh_of_zeroFree_half fun ρ hρ hz => hcon ⟨ρ, hρ, hz⟩)
  have hnt : WeilTest.IsNontrivialZero ρ := by
    refine ⟨hz, ?_⟩
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re < 0 := by simp; linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have hre' : (1 - ρ).re < 1 / 2 := by rw [Complex.sub_re, Complex.one_re]; linarith
  exact ⟨ρ, hnt, PsiOmega.IsNontrivialZero.one_sub hnt, hre,
    fun F hF => ⟨(norm_vF_lt_one_iff hF).2 hre, (one_lt_norm_vF_iff hF).2 hre'⟩,
    tendsto_norm_vF_of_half_lt hre, tendsto_norm_vF_of_lt_half hre'⟩

/-! ## Part B: the ball tower -/

/-- **The ball tower and the Bohr lift in one identity**: for every integer `n ≥ 2`,
`Λ(n) = (2/|S^{n−1}|)·exp(Σ_p p^{−n})·D₂(n)`, from `BallTower.Gammaℝ_mul_sphereArea` and the Euler split. -/
theorem completed_eq_sphereArea_bohr {n : ℕ} (hn : 2 ≤ n) :
    completedRiemannZeta n = 2 / (BallTower.sphereArea n : ℂ) *
      (Complex.exp (∑' p : Nat.Primes, bohr n p) * Complex.exp (∑' p, regTerm n p)) := by
  have hre : 1 < (n : ℂ).re := by
    rw [Complex.natCast_re]; exact_mod_cast (by omega : 1 < n)
  have hS : (BallTower.sphereArea n : ℂ) ≠ 0 := by
    exact_mod_cast (BallTower.sphereArea_pos (by omega)).ne'
  have hG : Complex.Gammaℝ (n : ℂ) = 2 / (BallTower.sphereArea n : ℂ) := by
    rw [eq_div_iff hS]; exact BallTower.Gammaℝ_mul_sphereArea n (by omega)
  rw [BallTower.completed_eq_Gammaℝ_mul hre, riemannZeta_eq_exp_mul_exp hre, hG]

end BohrJoins

#print axioms BohrJoins.norm_vF_le_norm_vF
#print axioms BohrJoins.shell_of_zeroFree
#print axioms BohrJoins.shell_unconditional
#print axioms BohrJoins.shell_of_kubotaTheta
#print axioms BohrJoins.shell_radii_tendsto
#print axioms BohrJoins.zero_pair_of_not_RH
#print axioms BohrJoins.completed_eq_sphereArea_bohr
