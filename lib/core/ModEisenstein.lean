/-
# The non-holomorphic Eisenstein series of `SL(2, ℤ)`: invariance, the Epstein identity and the constant term

Milestone A of the scattering theory of the modular surface `SL(2, ℤ)\ℍ²` (B. S. Pavlov and L. D. Faddeev, 1972;
P. D. Lax and R. S. Phillips, 1976), on the side of the Dirichlet series. With `y = Im z`,
`E(z, s) = ½Σ_{(c, d) coprime}(y/|cz + d|²)^s`, the sum over `Γ_∞\SL(2, ℤ)` of `Im(γz)^s`.
* **Convergence** (`summable_norm_term`, `summable_norm_E`): absolute convergence for `Re s > 1`, by Mathlib's
  bound for the Eisenstein summands on vertical strips.
* **Invariance** (`term_smul`, `E_smul`, `epstein_smul`): `E(γz, s) = E(z, s)` for every `γ ∈ SL(2, ℤ)` and every
  `s` (as sums: `v ↦ vγ` permutes the coprime pairs), and likewise for the Epstein sum.
* **The Epstein identity** (`zeta_mul_E`, `E_eq_epstein`): `ζ(2s)E(z, s) = ½Σ_{(m, n) ≠ 0}(y/|mz + n|²)^s` for
  `Re s > 1`, by writing each nonzero pair as `k` times a coprime pair.
* **The constant term** (`integral_epstein`, `zeta_ratio_beta`, `constTerm_eq`): for `Re s > 1`,
  `∫_0^1 E(x + iy, s) dx = y^s + φ(s)y^{1−s}` with `φ = PavlovFaddeev.scatteringMatrix`, `φ(s) = Λ(2s − 1)/Λ(2s)`.
  The proof integrates the Epstein sum row by row: the row `m = 0` gives `2ζ(2s)y^s`; the row `m ≠ 0` unfolds the
  sum over `n` into `∫_ℝ (y/(m²t² + m²y²))^s dt` (`hasSum_integral_mul_add`), a Beta integral
  (`integral_rpow_sq_add`, from `KubotaBesselMellin`), and the sum over `m` gives `2ζ(2s − 1)B(½, s − ½)y^{1−s}`.
The continuation of `E` to every `s` is `ModContinuation`, and the fundamental domain and the unfolding over
`Γ_∞\SL(2, ℤ)` are `ModFD`. The Fourier expansion of `E` in Bessel functions is not built here.
-/
import Mathlib
import PavlovFaddeev
import KubotaBesselMellin

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane Matrix
open scoped MatrixGroups

noncomputable section

namespace ModEisenstein

/-! ## The summand `(y/|cz + d|²)^s` -/

/-- `|v₀z + v₁|²`. -/
def nq (z : ℍ) (v : Fin 2 → ℤ) : ℝ := Complex.normSq ((v 0 : ℂ) * z + v 1)

/-- **The summand** `(Im z/|v₀z + v₁|²)^s`. At `v = 0` it is `0^s`, which is `0` for `s ≠ 0`. -/
def term (z : ℍ) (s : ℂ) (v : Fin 2 → ℤ) : ℂ := ((z.im / nq z v : ℝ) : ℂ) ^ s

lemma nq_nonneg (z : ℍ) (v : Fin 2 → ℤ) : 0 ≤ nq z v := Complex.normSq_nonneg _

lemma nq_eq (z : ℍ) (v : Fin 2 → ℤ) : nq z v = ‖(v 0 : ℂ) * z + v 1‖ ^ 2 := Complex.normSq_eq_norm_sq _

lemma term_zero {z : ℍ} {s : ℂ} (hs : s ≠ 0) : term z s 0 = 0 := by
  simp [term, nq, Complex.zero_cpow hs]

lemma norm_term (z : ℍ) {s : ℂ} (hs : s.re ≠ 0) (v : Fin 2 → ℤ) :
    ‖term z s v‖ = (z.im / nq z v) ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_nonneg (div_nonneg z.im_pos.le (nq_nonneg z v)) hs

lemma norm_term_eq {z : ℍ} {s : ℂ} (hs : 0 < s.re) (v : Fin 2 → ℤ) :
    ‖term z s v‖ = z.im ^ s.re * ‖(v 0 : ℂ) * z + v 1‖ ^ (-(2 * s.re)) := by
  rw [norm_term z hs.ne', Real.div_rpow z.im_pos.le (nq_nonneg z v), nq_eq, div_eq_mul_inv,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Real.rpow_neg (norm_nonneg _)]
  push_cast
  ring_nf

/-- The summand is bounded by `y^σ r^{−2σ}‖v‖^{−2σ}`, uniformly on a vertical strip. -/
lemma norm_term_le_strip {z : ℍ} {s : ℂ} (hs : 0 < s.re) (v : Fin 2 → ℤ) {A B : ℝ} (hB : 0 < B)
    (hz : z ∈ verticalStrip A B) :
    ‖term z s v‖ ≤ z.im ^ s.re *
      (EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s.re)) * ‖v‖ ^ (-(2 * s.re))) := by
  rw [norm_term_eq hs]
  exact mul_le_mul_of_nonneg_left
    (EisensteinSeries.summand_bound_of_mem_verticalStrip (by linarith) v hB hz) (by positivity)

lemma summable_norm_majorant {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : Fin 2 → ℤ => ‖v‖ ^ (-(2 * s.re)) :=
  EisensteinSeries.summable_one_div_norm_rpow (by linarith)

/-- **Absolute convergence** for `Re s > 1`. -/
theorem summable_norm_term (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : Fin 2 → ℤ => ‖term z s v‖ := by
  have hz : z ∈ verticalStrip |z.re| z.im := ⟨le_rfl, le_rfl⟩
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _)
    (fun v => norm_term_le_strip (by linarith) v z.im_pos hz) ?_
  exact ((summable_norm_majorant hs).mul_left _).mul_left _

/-! ## The action of `SL(2, ℤ)` -/

/-- `cz + d` for `γ = (a, b; c, d)`. -/
def dn (γ : SL(2, ℤ)) (z : ℍ) : ℂ := (γ 1 0 : ℂ) * z + γ 1 1

lemma dn_ne_zero (γ : SL(2, ℤ)) (z : ℍ) : dn γ z ≠ 0 := by
  have h := denom_ne_zero γ z
  rwa [ModularGroup.denom_apply] at h

lemma im_smul (γ : SL(2, ℤ)) (z : ℍ) : (γ • z).im = z.im / Complex.normSq (dn γ z) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, dn]

lemma smul_lin (γ : SL(2, ℤ)) (z : ℍ) (v : Fin 2 → ℤ) :
    ((v 0 : ℂ) * ((γ • z : ℍ) : ℂ) + v 1) =
      (((v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 : ℤ) * (z : ℂ) +
        ((v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1 : ℤ)) / dn γ z := by
  have key (a b c d u w : ℂ) (hc : c * z + d ≠ 0) :
      u * ((a * z + b) / (c * z + d)) + w = ((u * a + w * c) * z + (u * b + w * d)) / (c * z + d) := by
    rw [mul_div_assoc', div_add' _ _ _ hc]
    congr 1
    ring
  have hd := dn_ne_zero γ z
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [dn, vecMul, dotProduct, Fin.sum_univ_two, algebraMap_int_eq, eq_intCast] at hd ⊢
  push_cast at hd ⊢
  exact key _ _ _ _ _ _ hd

lemma nq_smul (γ : SL(2, ℤ)) (z : ℍ) (v : Fin 2 → ℤ) :
    nq (γ • z) v = nq z (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) / Complex.normSq (dn γ z) := by
  rw [nq, smul_lin, Complex.normSq_div, nq]

/-- **The summand under `γ`**: `(Im γz/|v₀γz + v₁|²)^s = (Im z/|(vγ)₀z + (vγ)₁|²)^s`. -/
theorem term_smul (γ : SL(2, ℤ)) (z : ℍ) (s : ℂ) (v : Fin 2 → ℤ) :
    term (γ • z) s v = term z s (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have hd : Complex.normSq (dn γ z) ≠ 0 := (Complex.normSq_pos.2 (dn_ne_zero γ z)).ne'
  unfold term
  rw [nq_smul, im_smul]
  congr 2
  rcases eq_or_ne (nq z (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ))) 0 with h | h
  · simp [h]
  · field_simp

/-- `v ↦ vγ` as a bijection of `ℤ²`. -/
def vecMulEquiv (γ : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun v := v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  invFun v := v ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  left_inv v := by simp [vecMul_vecMul, Matrix.mul_adjugate]
  right_inv v := by simp [vecMul_vecMul, Matrix.adjugate_mul]

/-- The pairs `(c, d)` of coprime integers. -/
abbrev Coprime : Type := {v : Fin 2 → ℤ // IsCoprime (v 0) (v 1)}

/-- `v ↦ vγ` as a bijection of the coprime pairs. -/
def coprimeEquiv (γ : SL(2, ℤ)) : Coprime ≃ Coprime where
  toFun v := ⟨v.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ), v.2.vecMulSL γ⟩
  invFun v := ⟨v.1 ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), v.2.vecMulSL γ⁻¹⟩
  left_inv v := Subtype.ext ((vecMulEquiv γ).left_inv v.1)
  right_inv v := Subtype.ext ((vecMulEquiv γ).right_inv v.1)

/-! ## The Eisenstein series -/

/-- **The non-holomorphic Eisenstein series** `E(z, s) = ½Σ_{(c, d) = 1}(y/|cz + d|²)^s`, the sum over
`Γ_∞\SL(2, ℤ)` of `Im(γz)^s`. -/
def E (z : ℍ) (s : ℂ) : ℂ := (1 / 2 : ℂ) * ∑' v : Coprime, term z s v.1

/-- **The Epstein zeta function** of the lattice `ℤz + ℤ`, `Σ_{(m, n)} (y/|mz + n|²)^s` (the term at `0` is
`0^s = 0` for `s ≠ 0`). -/
def epstein (z : ℍ) (s : ℂ) : ℂ := ∑' v : Fin 2 → ℤ, term z s v

/-- **`SL(2, ℤ)`-invariance**, for every `s`: `E(γz, s) = E(z, s)`. -/
theorem E_smul (γ : SL(2, ℤ)) (z : ℍ) (s : ℂ) : E (γ • z) s = E z s := by
  unfold E
  congr 1
  simp_rw [term_smul]
  exact (coprimeEquiv γ).tsum_eq (fun v => term z s v.1)

/-- **`SL(2, ℤ)`-invariance of the Epstein sum**, for every `s`. -/
theorem epstein_smul (γ : SL(2, ℤ)) (z : ℍ) (s : ℂ) : epstein (γ • z) s = epstein z s := by
  unfold epstein
  simp_rw [term_smul]
  exact (vecMulEquiv γ).tsum_eq (fun v => term z s v)

/-- Absolute convergence of `E` for `Re s > 1`. -/
theorem summable_norm_E (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : Coprime => ‖term z s v.1‖ :=
  (summable_norm_term z hs).comp_injective Subtype.val_injective

/-! ## `ζ(2s)E(z, s) = ½ × Epstein` -/

lemma nq_smul_int (z : ℍ) (k : ℤ) (v : Fin 2 → ℤ) : nq z (k • v) = (k : ℝ) ^ 2 * nq z v := by
  simp only [nq, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [show (k : ℂ) * v 0 * z + k * v 1 = (k : ℂ) * (v 0 * z + v 1) by ring, Complex.normSq_mul,
    Complex.normSq_intCast]
  ring

/-- **Scaling**: the summand at `kv` is `k^{−2s}` times the summand at `v`, for `k ≥ 1`. -/
lemma term_smul_nat (z : ℍ) (s : ℂ) (n : ℕ) (v : Fin 2 → ℤ) :
    term z s (((n + 1 : ℕ) : ℤ) • v) = 1 / ((n : ℂ) + 1) ^ (2 * s) * term z s v := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : z.im / nq z (((n + 1 : ℕ) : ℤ) • v) = ((n : ℝ) + 1) ^ (-2 : ℝ) * (z.im / nq z v) := by
    rw [nq_smul_int, Real.rpow_neg hK.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    rcases eq_or_ne (nq z v) 0 with h | h
    · simp [h]
    · field_simp
  unfold term
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.rpow_nonneg hK.le _)
      (div_nonneg z.im_pos.le (nq_nonneg z v)), ← Complex.cpow_mul_ofReal_nonneg hK.le]
  congr 1
  rw [one_div, ← Complex.cpow_neg]
  push_cast
  ring_nf

/-- `(n, w) ↦ (n + 1)w`, from `ℕ × {coprime pairs}` onto `ℤ² ∖ 0`. -/
def scaleMap (p : ℕ × Coprime) : Fin 2 → ℤ := (((p.1 + 1 : ℕ) : ℤ)) • p.2.1

lemma gcd_scaleMap (p : ℕ × Coprime) : Int.gcd (scaleMap p 0) (scaleMap p 1) = p.1 + 1 := by
  simp only [scaleMap, Pi.smul_apply, smul_eq_mul, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.1 p.2.2]
  omega

lemma scaleMap_injective : Function.Injective scaleMap := by
  intro p q h
  have hn : p.1 = q.1 := by
    have := gcd_scaleMap p
    rw [h, gcd_scaleMap q] at this
    omega
  have hw : p.2 = q.2 := by
    apply Subtype.ext
    have h' : (((p.1 + 1 : ℕ) : ℤ)) • p.2.1 = (((p.1 + 1 : ℕ) : ℤ)) • q.2.1 := by
      have := h; unfold scaleMap at this; rwa [← hn] at this
    exact smul_right_injective _ (by positivity : (((p.1 + 1 : ℕ) : ℤ)) ≠ 0) h'
  exact Prod.ext hn hw

lemma mem_range_scaleMap {v : Fin 2 → ℤ} (hv : v ≠ 0) : v ∈ range scaleMap := by
  have h0 : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  have hg := Int.gcd_pos_iff.2 h0
  set d := Int.gcd (v 0) (v 1) with hd
  refine ⟨(d - 1, ⟨fun i => v i / d, ?_⟩), ?_⟩
  · exact Int.isCoprime_iff_gcd_eq_one.2 (Int.gcd_div_gcd_div_gcd hg)
  · funext i
    simp only [scaleMap, Pi.smul_apply, smul_eq_mul]
    rw [show d - 1 + 1 = d by omega, mul_comm]
    apply Int.ediv_mul_cancel
    fin_cases i
    · exact Int.gcd_dvd_left _ _
    · exact Int.gcd_dvd_right _ _

lemma hasSum_zeta_two_mul {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (2 * s)) (riemannZeta (2 * s)) := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h2]
  refine Summable.hasSum ?_
  have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 h2)
  simpa using this

/-- **The Epstein-sum identity** `ζ(2s)E(z, s) = ½Σ_{(m, n) ≠ 0}(y/|mz + n|²)^s` for `Re s > 1`. -/
theorem zeta_mul_E (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (2 * s) * E z s = (1 / 2 : ℂ) * epstein z s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hsum : HasSum (term z s) (epstein z s) := (summable_norm_term z hs).of_norm.hasSum
  have hcomp : HasSum (term z s ∘ scaleMap) (epstein z s) := by
    refine (scaleMap_injective.hasSum_iff fun v hv => ?_).2 hsum
    by_cases h : v = 0
    · rw [h, term_zero hs0]
    · exact absurd (mem_range_scaleMap h) hv
  have hprod : HasSum (fun p : ℕ × Coprime => 1 / ((p.1 : ℂ) + 1) ^ (2 * s) * term z s p.2.1)
      (riemannZeta (2 * s) * ∑' v : Coprime, term z s v.1) := by
    have h1 := hasSum_zeta_two_mul hs
    have h2 : HasSum (fun v : Coprime => term z s v.1) (∑' v : Coprime, term z s v.1) :=
      (summable_norm_E z hs).of_norm.hasSum
    have h3 : Summable fun p : ℕ × Coprime => 1 / ((p.1 : ℂ) + 1) ^ (2 * s) * term z s p.2.1 :=
      hcomp.summable.congr fun p => term_smul_nat z s p.1 p.2.1
    exact HasSum.mul (f := fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (2 * s))
      (g := fun v : Coprime => term z s v.1) h1 h2 h3
  have heq : (term z s ∘ scaleMap) = fun p : ℕ × Coprime => 1 / ((p.1 : ℂ) + 1) ^ (2 * s) * term z s p.2.1 :=
    funext fun p => term_smul_nat z s p.1 p.2.1
  rw [heq] at hcomp
  rw [hcomp.unique hprod, E]
  ring

/-- `E = Epstein/(2ζ(2s))` for `Re s > 1`. -/
theorem E_eq_epstein (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    E z s = epstein z s / (2 * riemannZeta (2 * s)) := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  have hz := riemannZeta_ne_zero_of_one_lt_re h2
  rw [eq_div_iff (mul_ne_zero two_ne_zero hz)]
  have := zeta_mul_E z hs
  linear_combination 2 * this

/-! ## One-dimensional integrals -/

/-- `G(u) = (1 + u²)^{−s}`. -/
def G (s : ℂ) (u : ℝ) : ℂ := (((1 + u ^ 2 : ℝ)) : ℂ) ^ (-s)

lemma norm_G (s : ℂ) (u : ℝ) : ‖G s u‖ = (1 + ‖u‖ ^ 2) ^ (-(2 * s.re) / 2) := by
  rw [G, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Real.norm_eq_abs, sq_abs]
  congr 1
  simp; ring

lemma continuous_G (s : ℂ) : Continuous (G s) := by
  unfold G
  refine Continuous.cpow (by fun_prop) continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.2 (by positivity)

lemma integrable_G {s : ℂ} (hs : 1 / 2 < s.re) : Integrable (G s) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s.re)
    (by simp; linarith)
  refine h.mono' (continuous_G s).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [norm_G]

/-- **`∫_ℝ (1 + u²)^{−s} du = B(½, s − ½)`** for `Re s > ½`, from `Eis.integral_one_add_sq`. -/
theorem integral_G {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ u, G s u = Complex.betaIntegral (1 / 2) (s - 1 / 2) := by
  have hi := integrable_G hs
  have hIoi : ∫ u in Ioi (0 : ℝ), G s u = (1 / 2 : ℂ) * Complex.betaIntegral (1 / 2) (s - 1 / 2) := by
    have := Eis.integral_one_add_sq 1 s
    simp only [sub_self, Complex.cpow_zero, one_mul] at this
    rw [show (1 : ℂ) / 2 = 1 / 2 from rfl] at this
    simpa [G] using this
  have hIic : ∫ u in Iic (0 : ℝ), G s u = ∫ u in Ioi (0 : ℝ), G s u := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    simp [G]
  rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn, hIic, hIoi]
  ring

/-- `(y/(t² + a²))^s = (y/a²)^s G(t/a)`. -/
lemma rpow_eq_G {a y : ℝ} (ha : 0 < a) (hy : 0 < y) (s : ℂ) (t : ℝ) :
    (((y / (t ^ 2 + a ^ 2) : ℝ)) : ℂ) ^ s = (((y / a ^ 2 : ℝ)) : ℂ) ^ s * G s (t / a) := by
  have h1 : y / (t ^ 2 + a ^ 2) = y / a ^ 2 * (1 + (t / a) ^ 2)⁻¹ := by
    field_simp
    ring
  have hp : (0 : ℝ) < 1 + (t / a) ^ 2 := by positivity
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), G,
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hp.le]; exact pi_pos.ne),
    Complex.cpow_neg]

lemma integrable_rpow_sq_add {a y : ℝ} (ha : 0 < a) (hy : 0 < y) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable fun t : ℝ => (((y / (t ^ 2 + a ^ 2) : ℝ)) : ℂ) ^ s := by
  simp_rw [rpow_eq_G ha hy]
  exact ((integrable_G hs).comp_div ha.ne').const_mul _

/-- **`∫_ℝ (y/(t² + a²))^s dt = a(y/a²)^s B(½, s − ½)`**. -/
theorem integral_rpow_sq_add {a y : ℝ} (ha : 0 < a) (hy : 0 < y) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ t : ℝ, (((y / (t ^ 2 + a ^ 2) : ℝ)) : ℂ) ^ s =
      (a : ℂ) * (((y / a ^ 2 : ℝ)) : ℂ) ^ s * Complex.betaIntegral (1 / 2) (s - 1 / 2) := by
  simp_rw [rpow_eq_G ha hy]
  rw [integral_const_mul, Measure.integral_comp_div (G s) a, integral_G hs, abs_of_pos ha,
    Complex.real_smul]
  ring

/-- **Unfolding a sum of shifts**: `Σ_n ∫_0^1 H(mx + n) dx = ∫_ℝ H` for an integrable `H` and `m ≥ 1`. -/
theorem hasSum_integral_mul_add {H : ℝ → ℂ} (hH : Integrable H) (m : ℕ) (hm : 0 < m) :
    HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..1, H (m * x + n)) (∫ t, H t) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have h1 : ∀ n : ℤ, ∫ x in (0 : ℝ)..1, H (m * x + n) =
      (m : ℂ)⁻¹ * ∑ j ∈ Finset.range m, ∫ x in (j : ℝ) + n..(j : ℝ) + n + 1, H x := by
    intro n
    rw [intervalIntegral.integral_comp_mul_add H hm' (n : ℝ), Complex.real_smul]
    push_cast
    congr 1
    have := intervalIntegral.sum_integral_adjacent_intervals (f := H) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) + n) (n := m) (fun k _ => hH.intervalIntegrable)
    simp only [Nat.cast_zero, zero_add] at this
    rw [mul_zero, zero_add, mul_one, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  simp_rw [h1]
  have h2 : HasSum (fun n : ℤ => ∑ j ∈ Finset.range m, ∫ x in (j : ℝ) + n..(j : ℝ) + n + 1, H x)
      (∑ j ∈ Finset.range m, ∫ t, H t) :=
    hasSum_sum fun j _ => hH.hasSum_intervalIntegral (j : ℝ)
  have h3 := h2.mul_left ((m : ℂ)⁻¹)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  rwa [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_mul] at h3

/-! ## The constant term -/

/-- The point `x + iy` of `ℍ`. -/
def pt (x y : ℝ) (hy : 0 < y) : ℍ := UpperHalfPlane.mk (x + y * Complex.I) (by simpa using hy)

@[simp] lemma pt_im (x : ℝ) {y : ℝ} (hy : 0 < y) : (pt x y hy).im = y := by
  simp [pt, UpperHalfPlane.im]

@[simp] lemma pt_re (x : ℝ) {y : ℝ} (hy : 0 < y) : (pt x y hy).re = x := by
  simp [pt, UpperHalfPlane.re]

lemma nq_pt (x : ℝ) {y : ℝ} (hy : 0 < y) (v : Fin 2 → ℤ) :
    nq (pt x y hy) v = ((v 0 : ℝ) * x + v 1) ^ 2 + ((v 0 : ℝ) * y) ^ 2 := by
  simp only [nq, pt, UpperHalfPlane.coe_mk, Complex.normSq_apply]
  simp
  ring

lemma pt_mem_strip {x : ℝ} (hx : |x| ≤ 1) {y : ℝ} (hy : 0 < y) : pt x y hy ∈ verticalStrip 1 y :=
  ⟨by simpa using hx, by simp⟩

lemma nq_pt_pos (x : ℝ) {y : ℝ} (hy : 0 < y) {v : Fin 2 → ℤ} (hv : v ≠ 0) : 0 < nq (pt x y hy) v := by
  rw [nq_pt]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    have : (0 : ℝ) < (v 1 : ℝ) ^ 2 := by positivity
    simp only [h0, Int.cast_zero, zero_mul, zero_add, sq (0 : ℝ), mul_zero, add_zero]
    exact this
  · have : (0 : ℝ) < ((v 0 : ℝ) * y) ^ 2 := by
      have : (v 0 : ℝ) ≠ 0 := by exact_mod_cast h0
      positivity
    nlinarith [sq_nonneg ((v 0 : ℝ) * x + v 1)]

lemma continuous_term_pt {y : ℝ} (hy : 0 < y) (s : ℂ) (v : Fin 2 → ℤ) :
    Continuous fun x : ℝ => term (pt x y hy) s v := by
  by_cases hv : v = 0
  · simp only [hv, term]
    simp only [nq, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, map_zero, div_zero]
    exact continuous_const
  · unfold term
    refine Continuous.cpow ?_ continuous_const fun x => ?_
    · simp_rw [pt_im, nq_pt]
      refine Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop) fun x => ?_)
      have := nq_pt_pos x hy hv
      rw [nq_pt] at this
      exact this.ne'
    · exact Complex.ofReal_mem_slitPlane.2 (div_pos (by simpa using hy) (nq_pt_pos x hy hv))

/-- **Termwise integration** over `0 ≤ x ≤ 1`. -/
theorem hasSum_integral_term {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v : Fin 2 → ℤ => ∫ x in (0 : ℝ)..1, term (pt x y hy) s v)
      (∫ x in (0 : ℝ)..1, epstein (pt x y hy) s) := by
  let f : (Fin 2 → ℤ) → C(ℝ, ℂ) := fun v => ⟨fun x => term (pt x y hy) s v, continuous_term_pt hy s v⟩
  have hb : ∀ v, ‖(f v).restrict (⟨uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      y ^ s.re * (EisensteinSeries.r ⟨⟨1, y⟩, hy⟩ ^ (-(2 * s.re)) * ‖v‖ ^ (-(2 * s.re))) := by
    intro v
    refine (ContinuousMap.norm_le _ (mul_nonneg (Real.rpow_nonneg hy.le _)
      (mul_nonneg (Real.rpow_nonneg (EisensteinSeries.r_pos _).le _)
        (Real.rpow_nonneg (norm_nonneg _) _)))).2 fun x => ?_
    have hx : |(x : ℝ)| ≤ 1 := by
      have h : (x : ℝ) ∈ uIcc (0 : ℝ) 1 := x.2
      rcases Set.mem_uIcc.1 h with h | h <;> rw [abs_le] <;> constructor <;> linarith [h.1, h.2]
    show ‖term (pt (x : ℝ) y hy) s v‖ ≤ _
    have := norm_term_le_strip (by linarith) v hy (pt_mem_strip hx hy)
    rwa [pt_im] at this
  have hsum : Summable fun v => ‖(f v).restrict (⟨uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun v => norm_nonneg _) hb
      (((summable_norm_majorant hs).mul_left _).mul_left _)
  exact intervalIntegral.hasSum_intervalIntegral_of_summable_norm hsum

lemma term_neg (z : ℍ) (s : ℂ) (v : Fin 2 → ℤ) : term z s (-v) = term z s v := by
  have : -v = (-1 : ℤ) • v := by simp
  rw [term, term, this, nq_smul_int]
  norm_num

/-- `((y/K²))^s = K^{−2s}y^s` for `K > 0`. -/
lemma cpow_div_sq {y K : ℝ} (hy : 0 ≤ y) (hK : 0 < K) (s : ℂ) :
    (((y / K ^ 2 : ℝ)) : ℂ) ^ s = 1 / (K : ℂ) ^ (2 * s) * (y : ℂ) ^ s := by
  have h1 : y / K ^ 2 = K ^ (-2 : ℝ) * y := by
    rw [Real.rpow_neg hK.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.rpow_nonneg hK.le _) hy,
    ← Complex.cpow_mul_ofReal_nonneg hK.le]
  congr 1
  rw [one_div, ← Complex.cpow_neg]
  push_cast
  ring_nf

lemma hasSum_zeta {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) (riemannZeta w) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
  refine Summable.hasSum ?_
  have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hw)
  simpa using this

/-- The row `m = 0`: `Σ_n (y/n²)^s = 2ζ(2s)y^s`. -/
lemma hasSum_row_zero {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ => (((y / (n : ℝ) ^ 2 : ℝ)) : ℂ) ^ s) (2 * riemannZeta (2 * s) * (y : ℂ) ^ s) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have h2 : 1 < (2 * s).re := by simp; linarith
  have hz := (hasSum_zeta h2).mul_right ((y : ℂ) ^ s)
  have hp : HasSum (fun k : ℕ => (((y / ((((k + 1 : ℕ) : ℤ)) : ℝ) ^ 2 : ℝ)) : ℂ) ^ s)
      (riemannZeta (2 * s) * (y : ℂ) ^ s) := by
    refine hz.congr_fun fun k => ?_
    rw [cpow_div_sq hy.le (by positivity)]
    push_cast; ring_nf
  have hn : HasSum (fun k : ℕ => (((y / ((-(((k : ℤ) + 1)) : ℤ) : ℝ) ^ 2 : ℝ)) : ℂ) ^ s)
      (riemannZeta (2 * s) * (y : ℂ) ^ s) := by
    refine hp.congr_fun fun k => ?_
    push_cast; ring_nf
  have := HasSum.of_add_one_of_neg_add_one (f := fun n : ℤ => (((y / (n : ℝ) ^ 2 : ℝ)) : ℂ) ^ s)
    (by simpa using hp) hn
  convert this using 1
  simp [Complex.zero_cpow hs0]
  ring

/-- `(my)((y/(my)²))^s = m^{1−2s}y^{1−s}` for `m > 0`. -/
lemma row_const {y m : ℝ} (hy : 0 < y) (hm : 0 < m) (s : ℂ) :
    ((m * y : ℝ) : ℂ) * (((y / (m * y) ^ 2 : ℝ)) : ℂ) ^ s =
      1 / (m : ℂ) ^ (2 * s - 1) * (y : ℂ) ^ (1 - s) := by
  have h1 : y / (m * y) ^ 2 = y⁻¹ / m ^ 2 := by field_simp
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [h1, cpow_div_sq (inv_nonneg.2 hy.le) hm, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact pi_pos.ne),
    Complex.cpow_sub _ _ hm', Complex.cpow_sub _ _ hy', Complex.cpow_one, Complex.cpow_one]
  push_cast
  field_simp

/-- The row `m ≥ 1`: `Σ_n ∫_0^1 (y/((mx + n)² + m²y²))^s dx = m^{1−2s}y^{1−s}B(½, s − ½)`. -/
lemma hasSum_row_pos {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..1, term (pt x y hy) s ![((k + 1 : ℕ) : ℤ), n])
      (1 / ((k : ℂ) + 1) ^ (2 * s - 1) * (y : ℂ) ^ (1 - s) * Complex.betaIntegral (1 / 2) (s - 1 / 2)) := by
  set m : ℕ := k + 1 with hm
  have hm0 : (0 : ℝ) < m := by positivity
  have ha : 0 < (m : ℝ) * y := mul_pos hm0 hy
  have hs2 : 1 / 2 < s.re := by linarith
  have hH := integrable_rpow_sq_add ha hy hs2
  have key := hasSum_integral_mul_add hH m (by omega)
  rw [integral_rpow_sq_add ha hy hs2, row_const hy hm0] at key
  have hk : ((m : ℝ) : ℂ) = (k : ℂ) + 1 := by simp [hm]
  rw [hk] at key
  refine key.congr_fun fun n => ?_
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [term, pt_im, nq_pt]
  simp

/-- `∫_0^1` of the summand at `−v` is that at `v`. -/
lemma integral_term_neg {y : ℝ} (hy : 0 < y) (s : ℂ) (v : Fin 2 → ℤ) :
    ∫ x in (0 : ℝ)..1, term (pt x y hy) s (-v) = ∫ x in (0 : ℝ)..1, term (pt x y hy) s v := by
  simp_rw [term_neg]

/-- **The integral of the Epstein sum over a period**:
`∫_0^1 Σ_{(m, n)}(y/|m(x + iy) + n|²)^s dx = 2ζ(2s)y^s + 2ζ(2s − 1)B(½, s − ½)y^{1−s}`. -/
theorem integral_epstein {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in (0 : ℝ)..1, epstein (pt x y hy) s =
      2 * riemannZeta (2 * s) * (y : ℂ) ^ s +
        2 * riemannZeta (2 * s - 1) * Complex.betaIntegral (1 / 2) (s - 1 / 2) * (y : ℂ) ^ (1 - s) := by
  set B := Complex.betaIntegral (1 / 2) (s - 1 / 2)
  set Iv : ℤ × ℤ → ℂ := fun p => ∫ x in (0 : ℝ)..1, term (pt x y hy) s ![p.1, p.2] with hI
  have htot : HasSum Iv (∫ x in (0 : ℝ)..1, epstein (pt x y hy) s) := by
    have := (hasSum_integral_term hy hs)
    rw [← (finTwoArrowEquiv ℤ).symm.hasSum_iff] at this
    exact this
  set J : ℤ → ℂ := fun m => if m = 0 then 2 * riemannZeta (2 * s) * (y : ℂ) ^ s
    else 1 / ((m.natAbs : ℂ)) ^ (2 * s - 1) * (y : ℂ) ^ (1 - s) * B with hJ
  have hJ0 : J 0 = 2 * riemannZeta (2 * s) * (y : ℂ) ^ s := by simp [hJ]
  have hJk : ∀ k : ℕ, J ((k + 1 : ℕ) : ℤ) = 1 / ((k : ℂ) + 1) ^ (2 * s - 1) * (y : ℂ) ^ (1 - s) * B ∧
      J (-((k + 1 : ℕ) : ℤ)) = 1 / ((k : ℂ) + 1) ^ (2 * s - 1) * (y : ℂ) ^ (1 - s) * B := by
    intro k
    have h1 : (((k + 1 : ℕ) : ℤ)) ≠ 0 := by omega
    have h2 : (-((k + 1 : ℕ) : ℤ)) ≠ 0 := by omega
    have e1 : (((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := by omega
    have e2 : (-((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := by omega
    simp only [hJ, h1, h2, e1, e2, reduceIte]
    push_cast
    exact ⟨rfl, rfl⟩
  have hrow : ∀ m : ℤ, HasSum (fun n => Iv (m, n)) (J m) := by
    intro m
    rcases lt_trichotomy m 0 with h | h | h
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k + 1 : ℕ) : ℤ) := ⟨(-m).toNat - 1, by omega⟩
      have hp := hasSum_row_pos hy hs k
      rw [← (Equiv.neg ℤ).hasSum_iff] at hp
      rw [(hJk k).2]
      refine hp.congr_fun fun n => ?_
      simp only [hI, Function.comp_apply, Equiv.neg_apply]
      rw [← integral_term_neg hy s]
      congr 2
    · subst h
      rw [hJ0]
      refine (hasSum_row_zero hy hs).congr_fun fun n => ?_
      simp only [hI]
      rw [intervalIntegral.integral_congr (g := fun _ => (((y / (n : ℝ) ^ 2 : ℝ)) : ℂ) ^ s)
        (fun x _ => by simp [term, nq_pt])]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = ((k + 1 : ℕ) : ℤ) := ⟨m.toNat - 1, by omega⟩
      rw [(hJk k).1]
      exact hasSum_row_pos hy hs k
  have hJsum := htot.prod_fiberwise hrow
  have h2 : 1 < (2 * s - 1).re := by simp; linarith
  have hz := (hasSum_zeta h2).mul_right ((y : ℂ) ^ (1 - s) * B)
  have hpos : HasSum (fun k : ℕ => J ((k : ℤ) + 1)) (riemannZeta (2 * s - 1) * ((y : ℂ) ^ (1 - s) * B)) := by
    refine hz.congr_fun fun k => ?_
    have := (hJk k).1
    push_cast at this
    rw [this]; ring
  have hneg : HasSum (fun k : ℕ => J (-((k : ℤ) + 1)))
      (riemannZeta (2 * s - 1) * ((y : ℂ) ^ (1 - s) * B)) := by
    refine hpos.congr_fun fun k => ?_
    have h1 := (hJk k).1
    have h2 := (hJk k).2
    push_cast at h1 h2
    rw [h1, h2]
  have hall := HasSum.of_add_one_of_neg_add_one hpos hneg
  rw [hJsum.unique hall, hJ0]
  ring

/-- `√π Γ(s − ½)ζ(2s − 1)/(Γ(s)ζ(2s)) = Λ(2s − 1)/Λ(2s)`, written with the Beta integral. -/
theorem zeta_ratio_beta {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (2 * s - 1) / riemannZeta (2 * s) * Complex.betaIntegral (1 / 2) (s - 1 / 2) =
      PavlovFaddeev.scatteringMatrix s := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  have h21 : 1 < (2 * s - 1).re := by simp; linarith
  have hz := riemannZeta_ne_zero_of_one_lt_re h2
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hB : Complex.Gamma (1 / 2) * Complex.Gamma (s - 1 / 2) =
      Complex.Gamma s * Complex.betaIntegral (1 / 2) (s - 1 / 2) := by
    have := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := 1 / 2) (t := s - 1 / 2) (by norm_num)
      (by simp; linarith)
    rw [this]; congr 2; ring
  have e1 : completedRiemannZeta (2 * s) = Complex.Gammaℝ (2 * s) * riemannZeta (2 * s) := by
    rw [riemannZeta_def_of_ne_zero (by intro h; rw [h] at h2; norm_num at h2)]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < (2 * s).re)]
  have e2 : completedRiemannZeta (2 * s - 1) = Complex.Gammaℝ (2 * s - 1) * riemannZeta (2 * s - 1) := by
    rw [riemannZeta_def_of_ne_zero (by intro h; rw [h] at h21; norm_num at h21)]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < (2 * s - 1).re)]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
  have hpis : (Real.pi : ℂ) ^ (-(2 * s) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hB' : Complex.betaIntegral (1 / 2) (s - 1 / 2) =
      Complex.Gamma (1 / 2) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s := by
    rw [hB]; field_simp
  unfold PavlovFaddeev.scatteringMatrix
  rw [e1, e2, Complex.Gammaℝ_def, Complex.Gammaℝ_def, show (2 * s - 1) / 2 = s - 1 / 2 by ring,
    show 2 * s / 2 = s by ring, show -(2 * s - 1) / 2 = -(2 * s) / 2 + 1 / 2 by ring,
    Complex.cpow_add _ _ hpi, ← Complex.Gamma_one_half_eq, hB']
  field_simp

/-- **The constant term of `E`**: `∫_0^1 E(x + iy, s) dx = y^s + φ(s)y^{1−s}` for `Re s > 1`, with
`φ = PavlovFaddeev.scatteringMatrix`, `φ(s) = Λ(2s − 1)/Λ(2s)`. -/
theorem constTerm_eq {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in (0 : ℝ)..1, E (pt x y hy) s =
      (y : ℂ) ^ s + PavlovFaddeev.scatteringMatrix s * (y : ℂ) ^ (1 - s) := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  have hz := riemannZeta_ne_zero_of_one_lt_re h2
  simp_rw [E_eq_epstein _ hs]
  rw [intervalIntegral.integral_div, integral_epstein hy hs, ← zeta_ratio_beta hs]
  field_simp

end ModEisenstein
