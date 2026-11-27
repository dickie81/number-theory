/-
# Masser's `s₂`, `E₂*` and the Kronecker limit function

The bridge between the CM side (`ThetaNorm.s2`, Masser's quasi-period invariant, and `EllipticLegendre.legendre`)
and the Eisenstein side (`ModKronecker.kron`, the Kronecker limit function of `E*(z, s)`).
* **The quasi-period `η₁` is `G₂`** (`tsum_telescope`, `hasSum_e2Summand_zetaW`, `zetaW_half_eq_G2`): for the
  lattice `ℤ + ℤτ` (`tauPair τ`), `η₁ = 2ζ_W(1/2) = ζ_W(z + 1) − ζ_W(z)`; summing the absolutely convergent series
  of `ζ_W(3/2) − ζ_W(1/2)` row by row (`c` fixed, `d` running), each row telescopes to
  `Σ_d (cτ + d)^{−2}`, Mathlib's `e2Summand c τ`, so `η₁ = Σ_c Σ_d (cτ + d)^{−2} = G₂(τ) = (π²/3)E₂(τ)`.
* **Masser's `s₂` is `(π²/3)E₂*`** (`s2_tauPair`): with Legendre's relation `η₁τ − η₂ = 2πi`,
  `s₂(ℤ + ℤτ) = (η₁τ̄ − η₂)/(τ̄ − τ) = η₁ − π/Im τ = (π²/3)(E₂(τ) − 3/(π Im τ))`.
* **`E₂*` is the `∂_τ` of the Kronecker limit function** (`hasDerivAt_kron_re`, `hasDerivAt_kron_im`,
  `wirtinger_kron`): with the Wirtinger derivative `∂_τ f = ½(∂_x f − i∂_y f)` (`wirtinger`) and Mathlib's
  `logDeriv_eta_eq_E2`, `∂_τ(−log(√y|η(τ)|²)) = −(πi/12)E₂*(τ)`.
* **The end-to-end identity** (`s2_eq_wirtinger_kron`): `s₂(ℤ + ℤτ) = 4πi·∂_τ kron(τ)`, Masser's invariant on the CM
  side is `4πi` times the `τ`-derivative of the constant term of `E*(τ, s)` at `s = 1` (Kronecker's first limit
  formula, `ModKronecker.tendsto_Estar_sub_pole`).
-/
import Mathlib
import ModKronecker
import EllipticLegendre

open Complex Real Filter Topology Set UpperHalfPlane PeriodPair ThetaNorm EisensteinSeries

noncomputable section

namespace ModMasser

/-! ## The lattice `ℤ + ℤτ` -/

/-- The period pair `(1, τ)` of the lattice `ℤ + ℤτ`, `τ ∈ ℍ`. -/
def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    refine LinearIndependent.pair_iff.2 fun s t h => ?_
    have h2 := congrArg Complex.im h
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, Complex.one_re, Complex.zero_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at h2
    have ht : t = 0 := by
      have : t * τ.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right τ.im_pos.ne'
    subst ht
    have h1 := congrArg Complex.re h
    simp at h1
    exact ⟨h1, rfl⟩

/-! ## `η₁ = G₂(τ)` -/

/-- **A telescoping series over `ℤ`**: `Σ_n (1/(w + 1 − n) − 1/(w − n)) = 0` when it converges. -/
theorem tsum_telescope (w : ℂ) (hs : Summable fun n : ℤ => 1 / (w + 1 - n) - 1 / (w - n)) :
    ∑' n : ℤ, (1 / (w + 1 - n) - 1 / (w - n)) = 0 := by
  rw [← tsum_eq_of_summable_unconditional (L := SummationFilter.symmetricIco ℤ) hs]
  refine HasSum.tsum_eq ?_
  rw [SummationFilter.hasSum_symmetricIco_int_iff]
  have e : ∀ N : ℕ, ∑ n ∈ Finset.Ico (-(N : ℤ)) N, (1 / (w + 1 - n) - 1 / (w - n)) =
      1 / ((1 : ℤ) * (w + 1) + N) - 1 / ((1 : ℤ) * (w + 1) - N) := by
    intro N
    have h := Finset.sum_Ico_int_sub N (fun n : ℤ => 1 / (w + 1 - n))
    convert h using 2 <;> push_cast <;> ring_nf
  simp_rw [e]
  simpa using (EisensteinSeries.tendsto_zero_inv_linear (w + 1) 1).sub
    (EisensteinSeries.tendsto_zero_inv_linear_sub (w + 1) 1)

/-- **The quasi-period `η₁ = 2ζ_W(1/2)` of `ℤ + ℤτ` as an iterated Eisenstein sum**:
`Σ_c Σ_d (cτ + d)^{−2} = 2ζ_W(1/2)` (each row of `ζ_W(3/2) − ζ_W(1/2)` telescopes to `e2Summand c τ`). -/
theorem hasSum_e2Summand_zetaW (τ : ℍ) :
    HasSum (fun c : ℤ => e2Summand c τ) (2 * zetaW (tauPair τ) (1 / 2)) := by
  set Λ := tauPair τ
  have hf := fun z : ℂ => (CMThetaOne.hasSumLocallyUniformly_zetaW Λ).hasSum (x := z)
  have hd := (hf (1 / 2 + 1)).sub (hf (1 / 2))
  have hz : (1 / 2 : ℂ) ∉ Λ.lattice := by
    simpa [Λ, tauPair] using Λ.ω₁_div_two_notMem_lattice
  rw [EllipticLegendre.zetaW_add_basis Λ (ω := 1) Λ.ω₁_mem_lattice (by simpa [Λ, tauPair] using
    Λ.ω₁_div_two_notMem_lattice) hz] at hd
  -- transport to `ℤ × ℤ`, rows indexed by the coefficient `c` of `τ`
  rw [← ((Equiv.prodComm ℤ ℤ).trans Λ.latticeEquivProd.toEquiv.symm).hasSum_iff] at hd
  set g : ℤ × ℤ → ℂ := fun p => 1 / ((1 / 2 - p.1 * (τ : ℂ)) + 1 - p.2) - 1 / ((1 / 2 - p.1 * (τ : ℂ)) - p.2) +
    eisSummand 2 ![p.1, p.2] τ
  have hg : HasSum g (2 * zetaW Λ (1 / 2)) := by
    refine hd.congr_fun fun p => ?_
    simp only [Function.comp, Equiv.trans_apply, Equiv.prodComm_apply, LinearEquiv.coe_toEquiv_symm]
    have hl : ((Λ.latticeEquivProd.symm p.swap : Λ.lattice) : ℂ) = p.2 + p.1 * τ := by
      rw [latticeEquiv_symm_apply]; simp [Λ, tauPair]
    erw [hl]
    simp only [g, eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
    rw [show (1 : ℂ) / 2 - p.1 * τ + 1 - p.2 = 1 / 2 + 1 - (p.2 + p.1 * τ) by ring,
      show (1 : ℂ) / 2 - p.1 * τ - p.2 = 1 / 2 - (p.2 + p.1 * τ) by ring,
      show ((p.1 : ℂ) * τ + p.2) = p.2 + p.1 * τ by ring]
    simp only [zpow_ofNat]
    ring
  refine hg.prod_fiberwise fun c => ?_
  have he := e2Summand_summable c τ
  have hb : Summable fun d : ℤ => 1 / ((1 / 2 - c * (τ : ℂ)) + 1 - d) - 1 / ((1 / 2 - c * (τ : ℂ)) - d) :=
    ((hg.summable.prod_factor c).sub he).congr fun d => by simp [g]
  have h := hb.hasSum.add he.hasSum
  rw [tsum_telescope _ hb, zero_add] at h
  exact h

/-- **`η₁ = G₂(τ)`**: the quasi-period `2ζ_W(1/2)` of `ℤ + ℤτ` is Mathlib's `G₂(τ) = Σ_c Σ_d (cτ + d)^{−2}`. -/
theorem zetaW_half_eq_G2 (τ : ℍ) : 2 * zetaW (tauPair τ) (1 / 2) = G2 τ := by
  have h := hasSum_e2Summand_zetaW τ
  simp only [G2]
  rw [tsum_eq_of_summable_unconditional h.summable, h.tsum_eq]

lemma G2_eq_E2 (τ : ℍ) : G2 τ = π ^ 2 / 3 * E2 τ := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [E2, Pi.smul_apply, smul_eq_mul, riemannZeta_two]
  field_simp
  ring

/-! ## Masser's `s₂` -/

/-- **Masser's `s₂` of `ℤ + ℤτ` is `(π²/3)E₂*(τ)`**: `s₂ = (π²/3)E₂(τ) − π/Im τ = (π²/3)(E₂(τ) − 3/(π Im τ))`,
from `η₁ = G₂(τ)` and Legendre's relation `η₁τ − η₂ = 2πi` (`EllipticLegendre.legendre`). -/
theorem s2_tauPair (τ : ℍ) : s2 (tauPair τ) = π ^ 2 / 3 * E2 τ - π / τ.im := by
  have hL := EllipticLegendre.legendre (tauPair τ) (by simpa [tauPair] using τ.im_pos)
  have h1 := zetaW_half_eq_G2 τ
  simp only [tauPair] at hL h1
  have hy : (τ.im : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hc : (starRingEnd ℂ) (τ : ℂ) - τ = -2 * Complex.I * τ.im := by
    apply Complex.ext <;> simp; ring
  have hc0 : (starRingEnd ℂ) (τ : ℂ) - τ ≠ 0 := by
    rw [hc]; simp [hy, Complex.I_ne_zero]
  rw [s2]
  simp only [tauPair, map_one, mul_one, one_mul]
  rw [← G2_eq_E2, ← h1, div_eq_iff hc0, hc]
  have e2 : 2 * zetaW (tauPair τ) ((τ : ℂ) / 2) = 2 * zetaW (tauPair τ) (1 / 2) * τ - 2 * π * Complex.I := by
    simp only [tauPair]; linear_combination -hL
  simp only [tauPair] at e2
  rw [e2]
  have hcc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * Complex.I * τ.im := by linear_combination hc
  rw [hcc]
  field_simp
  ring_nf

/-! ## `E₂*` as the `∂_τ` of the Kronecker limit function -/

open ModKronecker ComplexConjugate

/-- **The Wirtinger derivative** `∂_τ f = ½(∂_x f − i∂_y f)` of a real function `f` of `τ = x + iy`, from its two
partial derivatives along `τ + t` and `τ + it`. -/
def wirtinger (f : ℂ → ℝ) (τ : ℂ) : ℂ :=
  1 / 2 * (((deriv (fun t : ℝ => f (τ + t)) 0 : ℝ) : ℂ) -
    Complex.I * ((deriv (fun t : ℝ => f (τ + t * Complex.I)) 0 : ℝ) : ℂ))

lemma re_mul_conj_div {a b : ℂ} (ha : a ≠ 0) : (b * conj a).re / ‖a‖ ^ 2 = (b / a).re := by
  have hn : (‖a‖ : ℂ) ^ 2 ≠ 0 := by
    have : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
    exact_mod_cast pow_ne_zero 2 this
  have e : b / a = b * conj a / ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj' a]
    have hc : conj a ≠ 0 := (map_ne_zero _).2 ha
    field_simp
  rw [e, Complex.div_ofReal_re]

/-- The derivative of `t ↦ |η(τ + tv)|²` at `t = 0`: `2 Re((η′(τ)v) conj η(τ))`. -/
lemma hasDerivAt_normSq_eta (τ : ℍ) (v : ℂ) :
    HasDerivAt (fun t : ℝ => ‖ModularForm.eta (τ + t * v)‖ ^ 2)
      (2 * (deriv ModularForm.eta τ * v * conj (ModularForm.eta τ)).re) 0 := by
  have hη : HasDerivAt ModularForm.eta (deriv ModularForm.eta τ) ((τ : ℂ) + (0 : ℂ) * v) := by
    rw [zero_mul, add_zero]
    exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).hasDerivAt
  have hl : HasDerivAt (fun u : ℂ => (τ : ℂ) + u * v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const v).const_add (τ : ℂ)
  have hg := (hη.comp (0 : ℂ) hl).comp_ofReal (z := 0)
  have := hg.norm_sq
  simp only [Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero, Complex.inner] at this
  exact this

/-- **`∂_x kron(τ) = −2 Re(η′/η)(τ)`**. -/
theorem hasDerivAt_kron_re (τ : ℍ) :
    HasDerivAt (fun t : ℝ => kron (τ + t)) (-2 * (logDeriv ModularForm.eta τ).re) 0 := by
  have hη0 : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
  have hN := hasDerivAt_normSq_eta τ 1
  simp only [mul_one] at hN
  have hS : 0 < √τ.im := Real.sqrt_pos.2 τ.im_pos
  have hpos : √τ.im * ‖ModularForm.eta ((τ : ℂ) + ((0 : ℝ) : ℂ))‖ ^ 2 ≠ 0 := by
    simp only [Complex.ofReal_zero, add_zero]
    exact mul_ne_zero hS.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 hη0))
  have h := ((hN.const_mul √τ.im).log hpos).neg
  have e : (fun t : ℝ => kron ((τ : ℂ) + t)) =
      fun t : ℝ => -Real.log (√τ.im * ‖ModularForm.eta ((τ : ℂ) + t)‖ ^ 2) := by
    funext t; simp [kron]
  rw [e]
  convert h using 1
  simp only [Complex.ofReal_zero, add_zero, logDeriv_apply]
  rw [← re_mul_conj_div hη0]
  field_simp

/-- **`∂_y kron(τ) = −1/(2y) + 2 Im(η′/η)(τ)`**, `y = Im τ`. -/
theorem hasDerivAt_kron_im (τ : ℍ) :
    HasDerivAt (fun t : ℝ => kron (τ + t * Complex.I))
      (-1 / (2 * τ.im) + 2 * (logDeriv ModularForm.eta τ).im) 0 := by
  have hη0 : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
  have hN := hasDerivAt_normSq_eta τ Complex.I
  have hy := τ.im_pos
  have hS : HasDerivAt (fun t : ℝ => √(τ.im + t)) (1 / (2 * √τ.im)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_add τ.im).sqrt (by simpa using hy.ne')
    simpa using h
  have hS0 : 0 < √τ.im := Real.sqrt_pos.2 hy
  have hpos : √(τ.im + 0) * ‖ModularForm.eta ((τ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≠ 0 := by
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    exact mul_ne_zero hS0.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 hη0))
  have h := ((hS.mul hN).log hpos).neg
  have e : (fun t : ℝ => kron ((τ : ℂ) + t * Complex.I)) =
      fun t : ℝ => -Real.log (√(τ.im + t) * ‖ModularForm.eta ((τ : ℂ) + t * Complex.I)‖ ^ 2) := by
    funext t; simp [kron]
  rw [e]
  convert h using 1
  simp only [Pi.mul_apply, Complex.ofReal_zero, zero_mul, add_zero, logDeriv_apply]
  have hn : ‖ModularForm.eta τ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hη0)
  have key : (deriv ModularForm.eta τ * Complex.I * conj (ModularForm.eta τ)).re =
      -(deriv ModularForm.eta τ / ModularForm.eta τ).im * ‖ModularForm.eta τ‖ ^ 2 := by
    rw [← Complex.mul_I_re, div_mul_eq_mul_div, ← re_mul_conj_div hη0]
    field_simp
  rw [key]
  field_simp
  rw [Real.sq_sqrt hy.le]
  ring

/-- **`E₂*` is `∂_τ` of the Kronecker limit function**: `∂_τ(−log(√y|η(τ)|²)) = −(πi/12)(E₂(τ) − 3/(π Im τ))`,
from `∂_x`, `∂_y` of `kron` and Mathlib's `logDeriv_eta_eq_E2` (`η′/η = (πi/12)E₂`). -/
theorem wirtinger_kron (τ : ℍ) :
    wirtinger kron τ = -(π * Complex.I / 12) * (E2 τ - 3 / (π * τ.im)) := by
  have hy : (τ.im : ℝ) ≠ 0 := τ.im_pos.ne'
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [wirtinger, (hasDerivAt_kron_re τ).deriv, (hasDerivAt_kron_im τ).deriv, ModularForm.logDeriv_eta_eq_E2]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im, Complex.neg_re,
      Complex.neg_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    simp
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im, Complex.neg_re,
      Complex.neg_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    simp
    ring

/-- **Masser's `s₂` is `4πi ∂_τ` of the Kronecker limit function**: for the lattice `ℤ + ℤτ`,
`s₂(ℤ + ℤτ) = 4πi ∂_τ(−log(√y|η(τ)|²))`, the CM side's quasi-period invariant (`ThetaNorm.s2`) as the
`τ`-derivative of the constant term of `E*(τ, s)` at `s = 1` (`ModKronecker.tendsto_Estar_sub_pole`). -/
theorem s2_eq_wirtinger_kron (τ : ℍ) : s2 (tauPair τ) = 4 * π * Complex.I * wirtinger kron τ := by
  have hy : (τ.im : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [s2_tauPair, wirtinger_kron]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end ModMasser
