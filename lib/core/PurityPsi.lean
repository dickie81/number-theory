/-
# The kernel of `ℙ¹` from the primes: a prime-side kernel that is not positive-definite

Plain statement. `PurityRational.kerP1` is the kernel `K(r) = Σ_{ρ'} r^{ρ' − 1}/(ρ'(2 − ρ'))` over the zeros `ρ' = ρ`
and `ρ' = ρ + 1` of `ζ̂(s)ζ̂(s − 1)`, the zeta function of `ℙ¹` over `ℤ`. It is symmetric, `K(1/r) = K(r)`
(`kerP1_inv`, from the involution `ρ ↦ 1 − ρ` of the zeros), and for `x ≥ 1`, with `u = log x` and
`c₀ = 2 + γ − log 4π`,
`K(x) = cosh u·(c₀ − 1 + log π)/2 + 2 − u·sinh u − (log π)/x + A(u)/2 − cosh u·Σ_n Λ(n)/n²
  + Σ_{n ≤ x} Λ(n)(cosh u/n + cosh u/n² − (1 + n + 1/n + 1/n²)/(2x))` (`kerP1_explicit`),
where `A(u) = (1/2π)∫ H_u(r)·Re ψ_Γ(¼ + ir/2) dr` is the archimedean term (`archP1`) and `Σ_n Λ(n)/n² = −ζ′(2)/ζ(2)`.
No hypothesis. So the kernel `kerP1ψ` on the right, which is built from `Λ`, `γ`, `π` and `Γ` and does not mention the
zeros, is not positive-definite on the positive rationals (`not_posDef_psi`): a kernel from the primes, with an Euler
product and a functional equation of `ζ`'s kind behind it, and no positivity. Compare `BallPsi.rh_iff_posDef_psi`,
where the same construction for `ζ` is positive-definite exactly under RH.
* The test function. With `A_u(t) = 2cosh(u(it − ½))/((½ + it)(3/2 − it))`, the sum `K(x) + K(1/x)` is
  `Σ_ρ (A_u(t_ρ) + A_u(−t_ρ))` at `t_ρ = (ρ − ½)/i`. Subtracting `cosh u/(t² + ¼)`, whose sum over the zeros is
  `cosh u·c₀` by Hadamard's identity (`WeilForm.hadamard_zeta`), removes the poles at `t = ±i/2`: the result `H_u` is
  `B_u(t) + B_u(−t)` with `B_u` a `dslope` (`Hu`), holomorphic on `|Im t| < 3/2`, even, in the test class of
  `WeilForm.weilExplicit_zeta` (`stripTest_Hu`), with `H_u(±i/2) = 2 − u·sinh u − cosh(u)/2` (`Hu_half`).
* The transform. `∫ e^{irw}/((½ + ir)(3/2 − ir)) dr = πE(w)` with `E(w) = e^{min(−w/2, 3w/2)}`
  (`integral_exp_div`, by Fourier inversion of `E`), so
  `g(v) = ½(e^{−u/2}(E(u + v) + E(u − v)) + e^{u/2}(E(v − u) + E(−u − v))) − cosh u·e^{−|v|/2}` (`gh_Hu`).
  For `v > u` it is `cosh u·e^{−3v/2}`, not `0`, so every prime power enters: those above `x` through
  `cosh u·Σ_{n > x} Λ(n)/n²` (`prime_sum`), the pole of `1/(ρ(2 − ρ))` at `ρ = 2` seen from the prime side.
-/
import Mathlib
import PurityRational
import BallPsi

open Real Complex Finset Filter Topology MeasureTheory Set WeilForm WeilTest WeilStrip ComplexConjugate
open scoped FourierTransform

noncomputable section

namespace PurityPsi

open BallKernel BallHadamard PurityRational

/-! ## The symmetry `x ↦ 1/x` -/

/-- The involution `ρ ↦ 1 − ρ` of the nontrivial zeros, with multiplicity. -/
def flip : ZIdx ≃ ZIdx :=
  zetaEquiv.trans ((Equiv.prodCongr Equiv.boolNot (Equiv.refl _)).trans zetaEquiv.symm)

lemma zZF_flip (q : ZIdx) : zetaZeroFamily (flip q) = 1 - zetaZeroFamily q := by
  have hz : ∀ p, zetaZeroFamily (zetaEquiv.symm p) = rhoXi p := fun p => by
    rw [← rhoXi_zetaEquiv, Equiv.apply_symm_apply]
  unfold flip
  simp only [Equiv.trans_apply]
  rw [hz]
  have h : ∀ p : Bool × ZeroIdx (sqF Xi), rhoXi ((Equiv.prodCongr Equiv.boolNot (Equiv.refl _)) p) =
      1 - rhoXi p := by
    rintro ⟨b, i⟩
    cases b <;> simp [rhoXi, Equiv.boolNot] <;> ring
  rw [h, rhoXi_zetaEquiv]

/-- The term of `kerP1` at `q`. -/
def term (r : ℝ) (q : ZIdx ⊕ ZIdx) : ℂ := cexp ((zP1 q - 1) * Real.log r) / (zP1 q * (2 - zP1 q))

lemma kerP1_eq_tsum (r : ℝ) : kerP1 r = ∑' q, term r q := rfl

lemma summable_term (r : ℝ) : Summable (term r) := by
  have hb : ∀ q : ZIdx ⊕ ZIdx, ‖term r q‖ ≤ Real.exp |Real.log r| * ‖gP1 (poleP1 q)‖ := fun q => by
    have e : term r q = gP1 (poleP1 q) * cexp ((Real.log r : ℂ) * poleP1 q) := by
      unfold term
      rw [gP1_poleP1, one_div_mul_eq_div, mul_comm (Real.log r : ℂ)]
      rfl
    rw [e, norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h := abs_re_poleP1 q
    have e2 : ((Real.log r : ℂ) * poleP1 q).re = Real.log r * (poleP1 q).re := by simp
    rw [e2]
    calc Real.log r * (poleP1 q).re ≤ |Real.log r * (poleP1 q).re| := le_abs_self _
      _ = |Real.log r| * |(poleP1 q).re| := abs_mul _ _
      _ ≤ |Real.log r| * 1 := mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
      _ = |Real.log r| := mul_one _
  exact (summable_wP1.mul_left (Real.exp |Real.log r|)).of_norm_bounded hb

/-- **`K(1/r) = K(r)`**: the zeros of `ℙ¹` are symmetric about `Re s = 1`. -/
theorem kerP1_inv (r : ℝ) : kerP1 r⁻¹ = kerP1 r := by
  set e : ZIdx ⊕ ZIdx ≃ ZIdx ⊕ ZIdx := (Equiv.sumComm ZIdx ZIdx).trans (Equiv.sumCongr flip flip) with he
  rw [kerP1_eq_tsum, kerP1_eq_tsum, ← e.tsum_eq]
  refine tsum_congr fun q => ?_
  rcases q with q | q
  · simp only [he, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl, Equiv.sumCongr_apply, Sum.map_inr,
      term, zP1, Sum.elim_inl, Sum.elim_inr, zZF_flip, Real.log_inv]
    congr 1
    · congr 1; push_cast; ring
    · ring
  · simp only [he, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr, Equiv.sumCongr_apply, Sum.map_inl,
      term, zP1, Sum.elim_inl, Sum.elim_inr, zZF_flip, Real.log_inv]
    congr 1
    · congr 1; push_cast; ring
    · ring




/-- `M_u(t) = (2cosh(u(it − ½))/(3/2 − it) − cosh u)/i`. -/
def Mu (u : ℝ) (t : ℂ) : ℂ := (2 * Complex.cosh (u * (I * t - 1 / 2)) / (3 / 2 - I * t) - Real.cosh u) / I

/-- `B_u = dslope M_u (i/2)`, that is `M_u(t)/(t − i/2)`, regular at `i/2` since `M_u(i/2) = 0`. -/
def Bu (u : ℝ) : ℂ → ℂ := dslope (Mu u) (I / 2)

/-- **The test function** `H_u(t) = B_u(t) + B_u(−t)`. -/
def Hu (u : ℝ) (t : ℂ) : ℂ := Bu u t + Bu u (-t)

lemma I_mul_half : I * (I / 2) = -(1 / 2) := by
  rw [show I * (I / 2) = I ^ 2 / 2 by ring, Complex.I_sq]; ring

lemma Mu_half (u : ℝ) : Mu u (I / 2) = 0 := by
  unfold Mu
  rw [I_mul_half, show (u : ℂ) * (-(1 / 2) - 1 / 2) = -(u : ℂ) by ring, Complex.cosh_neg,
    show (3 / 2 : ℂ) - -(1 / 2) = 2 by norm_num, Complex.ofReal_cosh]
  field_simp
  ring

lemma Mu_neg_half (u : ℝ) : Mu u (-(I / 2)) = (2 - Real.cosh u) / I := by
  unfold Mu
  rw [mul_neg, I_mul_half, neg_neg, show (u : ℂ) * (1 / 2 - 1 / 2) = 0 by ring, Complex.cosh_zero,
    show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num]
  push_cast
  ring

lemma half_ne : -(I / 2) ≠ I / 2 := fun h => by
  have := congrArg Complex.im h
  simp at this
  norm_num at this

lemma Bu_eq (u : ℝ) {t : ℂ} (ht : t ≠ I / 2) : Bu u t = Mu u t / (t - I / 2) := by
  unfold Bu
  rw [dslope_of_ne _ ht, slope_def_field, Mu_half, sub_zero]

/-- Where `M_u` is regular: off `t = −3i/2`. -/
def V : Set ℂ := {t | 3 / 2 - I * t ≠ 0}

lemma isOpen_V : IsOpen V := isOpen_ne_fun (by fun_prop) continuous_const

lemma half_mem_V : I / 2 ∈ V := by
  show 3 / 2 - I * (I / 2) ≠ 0
  rw [I_mul_half]; norm_num

lemma differentiableOn_Mu (u : ℝ) : DifferentiableOn ℂ (Mu u) V := by
  intro t ht
  unfold Mu
  have hc : DifferentiableAt ℂ (fun t : ℂ => Complex.cosh (u * (I * t - 1 / 2))) t := by fun_prop
  exact ((((hc.const_mul 2).div (by fun_prop) (show (3 / 2 - I * t : ℂ) ≠ 0 from ht)).sub_const _).div_const
    _).differentiableWithinAt

lemma differentiableOn_Bu (u : ℝ) : DifferentiableOn ℂ (Bu u) V :=
  (Complex.differentiableOn_dslope (isOpen_V.mem_nhds half_mem_V)).2 (differentiableOn_Mu u)

lemma strip_sub (t : ℂ) (ht : t ∈ WeilStrip.strip (-1) 1) : t ∈ V ∧ -t ∈ V := by
  have hti : -1 ≤ t.im ∧ t.im ≤ 1 := ht
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith

lemma differentiableOn_Hu (u : ℝ) : DifferentiableOn ℂ (Hu u) (WeilStrip.strip (-1) 1) := by
  intro t ht
  have h := strip_sub t ht
  have h1 : DifferentiableAt ℂ (Bu u) t := (differentiableOn_Bu u).differentiableAt (isOpen_V.mem_nhds h.1)
  have h2 : DifferentiableAt ℂ (Bu u) (-t) :=
    (differentiableOn_Bu u).differentiableAt (isOpen_V.mem_nhds h.2)
  exact (h1.add (h2.comp t differentiableAt_id.neg)).differentiableWithinAt

lemma Hu_even (u : ℝ) (t : ℂ) : Hu u (-t) = Hu u t := by
  unfold Hu; rw [neg_neg, add_comm]


lemma rho_facts (q : ZIdx) : zetaZeroFamily q ≠ 0 ∧ 1 - zetaZeroFamily q ≠ 0 ∧ 2 - zetaZeroFamily q ≠ 0 ∧
    zetaZeroFamily q + 1 ≠ 0 := by
  have h0 := (nontrivial_zZF q).re_pos
  have h1 := (nontrivial_zZF q).re_lt_one
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have := congrArg Complex.re h; simp at this; linarith

/-- On a zero, `H_u + cosh u/(ρ(1 − ρ))` is the sum of the four terms of `K(e^u) + K(e^{−u})` at `ρ`. -/
lemma Hu_term (u : ℝ) (q : ZIdx) :
    Hu u ((zetaZeroFamily q - 1 / 2) / I) + (Real.cosh u : ℂ) * (1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))) =
      (cexp ((zetaZeroFamily q - 1) * u) + cexp ((zetaZeroFamily q - 1) * ((-u : ℝ) : ℂ))) /
        (zetaZeroFamily q * (2 - zetaZeroFamily q)) +
      (cexp ((zetaZeroFamily q + 1 - 1) * u) + cexp ((zetaZeroFamily q + 1 - 1) * ((-u : ℝ) : ℂ))) /
        ((zetaZeroFamily q + 1) * (2 - (zetaZeroFamily q + 1))) := by
  obtain ⟨h0, h1, h2, h3⟩ := rho_facts q
  set ρ := zetaZeroFamily q with hρ
  set t := (ρ - 1 / 2) / I with ht
  have hIt : I * t = ρ - 1 / 2 := by rw [ht]; field_simp
  have hne1 : t ≠ I / 2 := fun h => h0 (by
    have := congrArg (I * ·) h
    rw [hIt, I_mul_half] at this
    linear_combination this)
  have hne2 : -t ≠ I / 2 := fun h => h1 (by
    have := congrArg (I * ·) h
    rw [mul_neg, hIt, I_mul_half] at this
    linear_combination this)
  unfold Hu
  rw [Bu_eq u hne1, Bu_eq u hne2]
  unfold Mu
  rw [mul_neg, hIt]
  have e1 : t - I / 2 = ρ / I := by rw [ht]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  have e2 : -t - I / 2 = (1 - ρ) / I := by rw [ht]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  have c1 : 2 * Complex.cosh (u * (ρ - 1 / 2 - 1 / 2)) = cexp ((ρ - 1) * u) + cexp ((ρ - 1) * ((-u : ℝ) : ℂ)) := by
    rw [Complex.two_cosh]; push_cast; ring_nf
  have c2 : 2 * Complex.cosh (u * (-(ρ - 1 / 2) - 1 / 2)) =
      cexp ((ρ + 1 - 1) * u) + cexp ((ρ + 1 - 1) * ((-u : ℝ) : ℂ)) := by
    rw [Complex.two_cosh]; push_cast; ring_nf
  rw [c1, c2]
  have hI : I ≠ 0 := Complex.I_ne_zero
  have h2' : (3 / 2 : ℂ) - (ρ - 1 / 2) = 2 - ρ := by ring
  have h3' : (3 / 2 : ℂ) - -(ρ - 1 / 2) = ρ + 1 := by ring
  rw [h2', h3', show (2 : ℂ) - (ρ + 1) = 1 - ρ by ring]
  field_simp
  ring

lemma hasDerivAt_Mu (u : ℝ) (t : ℂ) (ht : 3 / 2 - I * t ≠ 0) :
    HasDerivAt (Mu u) (((2 * (Complex.sinh (u * (I * t - 1 / 2)) * (u * I))) * (3 / 2 - I * t) -
      2 * Complex.cosh (u * (I * t - 1 / 2)) * (-I)) / (3 / 2 - I * t) ^ 2 / I) t := by
  have hw : HasDerivAt (fun t : ℂ => (u : ℂ) * (I * t - 1 / 2)) (u * I) t := by
    have := ((hasDerivAt_id t).const_mul I).sub_const (1 / 2 : ℂ)
    simpa using this.const_mul (u : ℂ)
  have hc := (hw.ccosh).const_mul (2 : ℂ)
  have hg : HasDerivAt (fun t : ℂ => 3 / 2 - I * t) (-I) t := by
    simpa using ((hasDerivAt_id t).const_mul I).const_sub (3 / 2 : ℂ)
  have hq := hc.div hg ht
  exact (hq.sub_const _).div_const I

/-- `H_u(±i/2) = 2 − u sinh u − cosh(u)/2`. -/
lemma Hu_half (u : ℝ) : Hu u (I / 2) = ((2 - u * Real.sinh u - Real.cosh u / 2 : ℝ) : ℂ) := by
  have hV : (3 / 2 : ℂ) - I * (I / 2) ≠ 0 := half_mem_V
  unfold Hu
  rw [Bu_eq u half_ne, Mu_neg_half]
  unfold Bu
  rw [dslope_same, (hasDerivAt_Mu u _ hV).deriv, I_mul_half,
    show (u : ℂ) * (-(1 / 2) - 1 / 2) = -(u : ℂ) by ring, Complex.sinh_neg, Complex.cosh_neg,
    show (3 / 2 : ℂ) - -(1 / 2) = 2 by norm_num, show -(I / 2) - I / 2 = -I by ring]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma Hu_neg_half (u : ℝ) : Hu u (-(I / 2)) = ((2 - u * Real.sinh u - Real.cosh u / 2 : ℝ) : ℂ) := by
  rw [Hu_even, Hu_half]


/-- `A_u(t) = 2cosh(u(it − ½))/((½ + it)(3/2 − it))`: at `t = t_ρ` it is `(x^{ρ−1} + x^{1−ρ})/(ρ(2 − ρ))`. -/
def Ap (u : ℝ) (t : ℂ) : ℂ := 2 * Complex.cosh (u * (I * t - 1 / 2)) / ((1 / 2 + I * t) * (3 / 2 - I * t))

lemma alg_id (C₁ C₂ c a J : ℂ) (hJ : J ≠ 0) (ha : a ≠ 0) (hb : 1 - a ≠ 0) (hp : 2 - a ≠ 0) (hq : 1 + a ≠ 0) :
    (2 * C₁ / (2 - a) - c) / J / (a / J) + (2 * C₂ / (1 + a) - c) / J / ((1 - a) / J) =
      2 * C₁ / (a * (2 - a)) + 2 * C₂ / ((1 - a) * (1 + a)) - c / (a * (1 - a)) := by
  field_simp
  ring

/-- Off its four poles, `H_u(t) = A_u(t) + A_u(−t) − cosh u/(t² + ¼)`. -/
lemma Hu_eq_Ap (u : ℝ) {t : ℂ} (h1 : 1 / 2 + I * t ≠ 0) (h2 : 1 / 2 - I * t ≠ 0) (h3 : 3 / 2 - I * t ≠ 0)
    (h4 : 3 / 2 + I * t ≠ 0) : Hu u t = Ap u t + Ap u (-t) - Real.cosh u / (t ^ 2 + 1 / 4) := by
  have hne1 : t ≠ I / 2 := fun h => h1 (by rw [h, I_mul_half]; ring)
  have hne2 : -t ≠ I / 2 := fun h => h2 (by
    rw [show t = -(I / 2) by rw [← h, neg_neg], mul_neg, I_mul_half]; ring)
  unfold Hu Ap
  rw [Bu_eq u hne1, Bu_eq u hne2]
  unfold Mu
  have hI : I ≠ 0 := Complex.I_ne_zero
  have e1 : t - I / 2 = (1 / 2 + I * t) / I := by field_simp; ring_nf; rw [Complex.I_sq]; ring
  have e2 : -t - I / 2 = (1 / 2 - I * t) / I := by field_simp; ring_nf; rw [Complex.I_sq]; ring
  have e3 : t ^ 2 + 1 / 4 = (1 / 2 + I * t) * (1 / 2 - I * t) := by ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2, e3, mul_neg, show (1 / 2 : ℂ) + -(I * t) = 1 / 2 - I * t by ring,
    show (3 / 2 : ℂ) - -(I * t) = 3 / 2 + I * t by ring]
  set s := I * t with hs
  rw [show (3 / 2 : ℂ) - s = 2 - (1 / 2 + s) by ring, show (3 / 2 : ℂ) + s = 1 + (1 / 2 + s) by ring,
    show (1 / 2 : ℂ) - s = 1 - (1 / 2 + s) by ring] at *
  exact alg_id _ _ _ _ _ hI h1 h2 h3 h4

lemma Ap_conj (u r : ℝ) : conj (Ap u r) = Ap u (-r) := by
  unfold Ap
  simp only [map_div₀, map_mul, ← Complex.cosh_conj, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat, map_one]
  ring_nf

/-- `H_u` on the real line: `2 Re A_u(r) − cosh u/(r² + ¼)`. -/
def HuR (u r : ℝ) : ℝ := 2 * (Ap u r).re - Real.cosh u / (r ^ 2 + 1 / 4)

lemma ne_of_real (r : ℝ) : 1 / 2 + I * r ≠ 0 ∧ 1 / 2 - I * r ≠ 0 ∧ 3 / 2 - I * r ≠ 0 ∧ 3 / 2 + I * r ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Complex.re h <;> norm_num at this

lemma Hu_real (u r : ℝ) : Hu u r = HuR u r := by
  obtain ⟨h1, h2, h3, h4⟩ := ne_of_real r
  rw [Hu_eq_Ap u h1 h2 h3 h4, HuR, ← Ap_conj, Complex.add_conj]
  push_cast
  ring

lemma norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  have e : Complex.cosh z = (cexp z + cexp (-z)) / 2 := by rw [← Complex.two_cosh]; ring
  rw [e, norm_div, Complex.norm_two]
  have h1 : ‖cexp z‖ ≤ Real.exp |z.re| := by rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (le_abs_self _)
  have h2 : ‖cexp (-z)‖ ≤ Real.exp |z.re| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (by simp; exact neg_le_abs _)
  have := norm_add_le (cexp z) (cexp (-z))
  linarith

/-- `‖A_u(t)‖ ≤ 4e^{3|u|/2}/(1 + (Re t)²)` on the strip, for `|Re t| ≥ 1`. -/
lemma norm_Ap_le (u : ℝ) {t : ℂ} (hti : -1 ≤ t.im ∧ t.im ≤ 1) (hre : 1 ≤ |t.re|) :
    ‖Ap u t‖ ≤ 4 * Real.exp (3 / 2 * |u|) / (1 + t.re ^ 2) := by
  unfold Ap
  have hpos : 0 < 1 + t.re ^ 2 := by positivity
  have hre2 : 1 ≤ t.re ^ 2 := by nlinarith [sq_abs t.re, abs_nonneg t.re]
  have hd1 : |t.re| ≤ ‖1 / 2 + I * t‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp
  have hd2 : |t.re| ≤ ‖3 / 2 - I * t‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp
  have hden : (1 + t.re ^ 2) / 2 ≤ ‖(1 / 2 + I * t) * (3 / 2 - I * t)‖ := by
    rw [norm_mul]
    have : t.re ^ 2 ≤ ‖1 / 2 + I * t‖ * ‖3 / 2 - I * t‖ := by
      rw [← sq_abs, sq]
      exact mul_le_mul hd1 hd2 (abs_nonneg _) (norm_nonneg _)
    linarith
  have hnum : ‖2 * Complex.cosh (u * (I * t - 1 / 2))‖ ≤ 2 * Real.exp (3 / 2 * |u|) := by
    rw [norm_mul, Complex.norm_two]
    refine mul_le_mul_of_nonneg_left ((norm_cosh_le _).trans (Real.exp_le_exp.2 ?_)) (by norm_num)
    have e : ((u : ℂ) * (I * t - 1 / 2)).re = u * (-t.im - 1 / 2) := by simp
    rw [e, abs_mul]
    have : |-t.im - 1 / 2| ≤ 3 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg u]
  have hd0 : 0 < ‖(1 / 2 + I * t) * (3 / 2 - I * t)‖ := lt_of_lt_of_le (by positivity) hden
  rw [norm_div, div_le_div_iff₀ hd0 hpos]
  have hE : 0 ≤ Real.exp (3 / 2 * |u|) := (Real.exp_pos _).le
  nlinarith

/-- **`H_u` is in the test class** of `WeilForm.weilExplicit_zeta`. -/
theorem stripTest_Hu (u : ℝ) : ∃ C, StripTest (Hu u) C := by
  have hK : IsCompact (reProdIm (Icc (-1 : ℝ) 1) (Icc (-1) 1)) := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : reProdIm (Icc (-1 : ℝ) 1) (Icc (-1) 1) ⊆ WeilStrip.strip (-1) 1 := fun t ht => ht.2
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ((differentiableOn_Hu u).continuousOn.mono hsub)
  set B := 8 * Real.exp (3 / 2 * |u|) + 8 * Real.cosh u with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨max (2 * max M 0) B, ⟨differentiableOn_Hu u, fun t ht => ?_⟩⟩
  have hti : -1 ≤ t.im ∧ t.im ≤ 1 := ht
  have hpos : 0 < 1 + t.re ^ 2 := by positivity
  rcases le_or_gt |t.re| 1 with hre | hre
  · have htK : t ∈ reProdIm (Icc (-1 : ℝ) 1) (Icc (-1) 1) := ⟨abs_le.1 hre, hti⟩
    have h1 := hM t htK
    have h2 : t.re ^ 2 ≤ 1 := by nlinarith [abs_nonneg t.re, sq_abs t.re]
    rw [le_div_iff₀ hpos]
    have h3 : ‖Hu u t‖ * (1 + t.re ^ 2) ≤ max M 0 * 2 :=
      mul_le_mul (h1.trans (le_max_left _ _)) (by linarith) hpos.le (le_max_right _ _)
    linarith [le_max_left (2 * max M 0) B]
  · have hre' : 1 ≤ |t.re| := hre.le
    have h1 : 1 / 2 + I * t ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; rw [this] at hre; norm_num at hre
    have h2 : 1 / 2 - I * t ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; rw [this] at hre; norm_num at hre
    have h3 : 3 / 2 - I * t ≠ 0 := (strip_sub t ht).1
    have h4 : 3 / 2 + I * t ≠ 0 := fun h => (strip_sub t ht).2 (by
      show 3 / 2 - I * -t = 0; rw [mul_neg, sub_neg_eq_add]; exact h)
    rw [Hu_eq_Ap u h1 h2 h3 h4]
    have hA1 := norm_Ap_le u hti hre'
    have him : -1 ≤ (-t).im ∧ (-t).im ≤ 1 := by
      rw [Complex.neg_im]; constructor <;> linarith [hti.1, hti.2]
    have hre2 : 1 ≤ |(-t).re| := by rw [Complex.neg_re, abs_neg]; exact hre'
    have hA2 := norm_Ap_le u him hre2
    rw [Complex.neg_re, neg_sq] at hA2
    have hden : (1 + t.re ^ 2) / 8 ≤ ‖t ^ 2 + 1 / 4‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      have e : (t ^ 2 + 1 / 4).re = t.re ^ 2 - t.im ^ 2 + 1 / 4 := by simp [sq, Complex.mul_re]
      rw [e]
      have : t.im ^ 2 ≤ 1 := by nlinarith
      have hre2 : 1 ≤ t.re ^ 2 := by nlinarith [sq_abs t.re, abs_nonneg t.re]
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    have hd0 : 0 < ‖t ^ 2 + 1 / 4‖ := lt_of_lt_of_le (by positivity) hden
    have hC : ‖(Real.cosh u : ℂ) / (t ^ 2 + 1 / 4)‖ ≤ 8 * Real.cosh u / (1 + t.re ^ 2) := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos _).le,
        div_le_div_iff₀ hd0 hpos]
      nlinarith [Real.cosh_pos u]
    calc ‖Ap u t + Ap u (-t) - (Real.cosh u : ℂ) / (t ^ 2 + 1 / 4)‖
        ≤ ‖Ap u t‖ + ‖Ap u (-t)‖ + ‖(Real.cosh u : ℂ) / (t ^ 2 + 1 / 4)‖ := by
          refine (norm_sub_le _ _).trans ?_
          exact add_le_add (norm_add_le (Ap u t) (Ap u (-t))) le_rfl
      _ ≤ 4 * Real.exp (3 / 2 * |u|) / (1 + t.re ^ 2) + 4 * Real.exp (3 / 2 * |u|) / (1 + t.re ^ 2) +
          8 * Real.cosh u / (1 + t.re ^ 2) := by linarith
      _ = B / (1 + t.re ^ 2) := by rw [hB]; ring
      _ ≤ max (2 * max M 0) B / (1 + t.re ^ 2) :=
          div_le_div_of_nonneg_right (le_max_right _ _) hpos.le



/-- `E(w) = e^{min(−w/2, 3w/2)}`: `e^{−w/2}` for `w ≥ 0` and `e^{3w/2}` for `w ≤ 0`. -/
def ePhi (w : ℝ) : ℝ := Real.exp (min (-w / 2) (3 * w / 2))

lemma ePhi_of_nonneg {w : ℝ} (hw : 0 ≤ w) : ePhi w = Real.exp (-w / 2) := by
  unfold ePhi; rw [min_eq_left (by linarith)]

lemma ePhi_of_nonpos {w : ℝ} (hw : w ≤ 0) : ePhi w = Real.exp (3 * w / 2) := by
  unfold ePhi; rw [min_eq_right (by linarith)]

/-- `𝓕E(ξ) = 1/(3/2 − 2πiξ) + 1/(½ + 2πiξ) = 2/((½ + 2πiξ)(3/2 − 2πiξ))`. -/
theorem fourier_ePhi (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((ePhi x : ℝ) : ℂ)) ξ = 2 / ((1 / 2 + 2 * π * ξ * I) * (3 / 2 - 2 * π * ξ * I)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set a : ℂ := 3 / 2 - 2 * π * ξ * I with hadef
  set b : ℂ := -(1 / 2) - 2 * π * ξ * I with hbdef
  have ha : 0 < a.re := by simp [a]
  have hb : b.re < 0 := by simp [b]
  have hL : EqOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((ePhi v : ℝ) : ℂ))
      (fun v : ℝ => cexp (a * v)) (Iic 0) := by
    intro v hv
    simp only
    rw [ePhi_of_nonpos (mem_Iic.1 hv), smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hR : EqOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((ePhi v : ℝ) : ℂ))
      (fun v : ℝ => cexp (b * v)) (Ioi 0) := by
    intro v hv
    simp only
    rw [ePhi_of_nonneg (mem_Ioi.1 hv).le, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hiL : IntegrableOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((ePhi v : ℝ) : ℂ)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic ha 0).congr_fun hL.symm measurableSet_Iic
  have hiR : IntegrableOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((ePhi v : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hb 0).congr_fun hR.symm measurableSet_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi hiL hiR, setIntegral_congr_fun measurableSet_Iic hL,
    setIntegral_congr_fun measurableSet_Ioi hR, integral_exp_mul_complex_Iic ha,
    integral_exp_mul_complex_Ioi hb]
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hb' : (1 / 2 + 2 * π * ξ * I) = -b := by rw [hbdef]; ring
  rw [hb']
  field_simp
  rw [hadef, hbdef]
  ring

lemma ePhi_le (x : ℝ) : ePhi x ≤ Real.exp (-|x| / 2) := by
  unfold ePhi
  refine Real.exp_le_exp.2 ?_
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; exact min_le_left _ _
  · rw [abs_of_nonpos h]; exact (min_le_right _ _).trans (by linarith)

lemma continuous_ePhi : Continuous ePhi := by unfold ePhi; fun_prop

lemma norm_D_ge (y : ℝ) : 1 / 4 + y ^ 2 ≤ ‖(1 / 2 + y * I) * (3 / 2 - y * I)‖ := by
  rw [norm_mul]
  set Q := 1 / 4 + y ^ 2 with hQ
  have e1 : ‖(1 / 2 + y * I : ℂ)‖ ^ 2 = Q := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have e2 : ‖(3 / 2 - y * I : ℂ)‖ ^ 2 = Q + 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hQ0 : 0 ≤ Q := by positivity
  have hN : 0 ≤ ‖(1 / 2 + y * I : ℂ)‖ * ‖(3 / 2 - y * I : ℂ)‖ := by positivity
  have hsq : Q ^ 2 ≤ (‖(1 / 2 + y * I : ℂ)‖ * ‖(3 / 2 - y * I : ℂ)‖) ^ 2 := by
    rw [mul_pow, e1, e2]; nlinarith
  exact (pow_le_pow_iff_left₀ hQ0 hN (by norm_num)).1 hsq

/-- **`∫ e^{irw}/((½ + ir)(3/2 − ir)) dr = πE(w)`**, by Fourier inversion of `E`. -/
theorem integral_exp_div (w : ℝ) :
    ∫ r : ℝ, cexp (I * r * w) / ((1 / 2 + I * r) * (3 / 2 - I * r)) = π * ePhi w := by
  set F : ℝ → ℂ := fun x => ((ePhi x : ℝ) : ℂ) with hF
  have hFi : Integrable F := by
    have h := integrable_exp_neg_abs (c := 1 / 2) (by norm_num)
    refine (h.mono' continuous_ePhi.aestronglyMeasurable (Eventually.of_forall fun x => ?_)).ofReal
    rw [Real.norm_of_nonneg (by unfold ePhi; positivity)]
    refine (ePhi_le x).trans (le_of_eq ?_)
    congr 1; ring
  have hFc : Continuous F := continuous_ofReal.comp continuous_ePhi
  have hFF : 𝓕 F = fun ξ : ℝ => 2 / ((1 / 2 + 2 * π * (ξ : ℂ) * I) * (3 / 2 - 2 * π * (ξ : ℂ) * I)) :=
    funext fourier_ePhi
  have hP : Integrable fun ξ : ℝ => 2 / (1 / 4 + 4 * π ^ 2 * ξ ^ 2) := by
    have h := (integrable_inv_one_add_mul_sq (b := 4 * π) (by positivity)).const_mul 8
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    have : (0 : ℝ) < 1 + (4 * π * ξ) ^ 2 := by positivity
    field_simp
    ring
  have hFFi : Integrable (𝓕 F) := by
    rw [hFF]
    have hD' (ξ : ℝ) : 1 / 4 + 4 * π ^ 2 * ξ ^ 2 ≤
        ‖(1 / 2 + 2 * π * (ξ : ℂ) * I) * (3 / 2 - 2 * π * (ξ : ℂ) * I)‖ := by
      have h := norm_D_ge (2 * π * ξ)
      push_cast at h
      linarith [show (2 * π * ξ) ^ 2 = 4 * π ^ 2 * ξ ^ 2 by ring]
    have hD : ∀ ξ : ℝ, (1 / 2 + 2 * π * (ξ : ℂ) * I) * (3 / 2 - 2 * π * (ξ : ℂ) * I) ≠ 0 := fun ξ =>
      norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (hD' ξ))
    refine hP.mono' (Continuous.div continuous_const (by fun_prop) hD).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    have hd := hD' ξ
    have hQ : (0 : ℝ) < 1 / 4 + 4 * π ^ 2 * ξ ^ 2 := by positivity
    rw [norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_left (by norm_num) hQ hd
  have h := congrFun (Continuous.fourierInv_fourier_eq hFc hFi hFFi) w
  rw [Real.fourierInv_eq', hFF] at h
  simp only [RCLike.inner_apply, conj_trivial] at h
  set g : ℝ → ℂ := fun r => cexp (I * r * w) * 2 / ((1 / 2 + I * r) * (3 / 2 - I * r)) with hg
  have e1 : (fun v : ℝ => cexp (↑(2 * π * (w * v)) * I) •
      (2 / ((1 / 2 + 2 * π * (v : ℂ) * I) * (3 / 2 - 2 * π * (v : ℂ) * I)))) = fun v => g (2 * π * v) := by
    funext v
    rw [hg, smul_eq_mul]
    push_cast
    ring_nf
  rw [e1, Measure.integral_comp_mul_left g (2 * π),
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)] at h
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have h2 : ∫ r : ℝ, g r = 2 * π * F w := by
    rw [Complex.real_smul] at h
    have := congrArg (fun z => ((2 * π : ℝ) : ℂ) * z) h
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpi.ne', Complex.ofReal_one, one_mul] at this
    rw [this]; push_cast; ring
  have e2 : (fun r : ℝ => cexp (I * r * w) / ((1 / 2 + I * r) * (3 / 2 - I * r))) = fun r => g r / 2 := by
    funext r; rw [hg]; ring
  rw [e2, integral_div, h2, hF]
  push_cast
  ring


/-! ## The transform of `H_u` -/

lemma D_ne (r : ℝ) : (1 / 2 + I * r) * (3 / 2 - I * r) ≠ 0 := by
  obtain ⟨h1, -, h3, -⟩ := ne_of_real r
  exact mul_ne_zero h1 h3

lemma integrable_exp_div (w : ℝ) :
    Integrable fun r : ℝ => cexp (I * r * w) / ((1 / 2 + I * r) * (3 / 2 - I * r)) := by
  have hc : Continuous fun r : ℝ => cexp (I * r * w) / ((1 / 2 + I * r) * (3 / 2 - I * r)) :=
    Continuous.div (by fun_prop) (by fun_prop) D_ne
  refine BallPsi.integrable_cauchy.mono' hc.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have hd := norm_D_ge r
  rw [show (1 / 2 + (r : ℂ) * I) * (3 / 2 - (r : ℂ) * I) = (1 / 2 + I * r) * (3 / 2 - I * r) by ring] at hd
  have h0 : (0 : ℝ) < r ^ 2 + 1 / 4 := by positivity
  rw [norm_div, show I * (r : ℂ) * w = ((r * w : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  exact one_div_le_one_div_of_le h0 (by linarith)

/-- `A_u(r)e^{irw} = e^{−u/2}e^{ir(u + w)}/D(r) + e^{u/2}e^{ir(w − u)}/D(r)`. -/
lemma Ap_mul_exp (u r w : ℝ) : Ap u r * cexp (I * r * w) =
    (Real.exp (-u / 2) : ℂ) * (cexp (I * r * ((u + w : ℝ) : ℂ)) / ((1 / 2 + I * r) * (3 / 2 - I * r))) +
      (Real.exp (u / 2) : ℂ) * (cexp (I * r * ((w - u : ℝ) : ℂ)) / ((1 / 2 + I * r) * (3 / 2 - I * r))) := by
  unfold Ap
  rw [Complex.two_cosh]
  push_cast
  have h1 : cexp ((u : ℂ) * (I * r - 1 / 2)) * cexp (I * r * w) = cexp (-(u : ℂ) / 2) * cexp (I * r * (u + w)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have h2 : cexp (-((u : ℂ) * (I * r - 1 / 2))) * cexp (I * r * w) =
      cexp ((u : ℂ) / 2) * cexp (I * r * (w - u)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [div_mul_eq_mul_div, add_mul, h1, h2]
  ring

lemma integrable_Ap_exp (u w : ℝ) : Integrable fun r : ℝ => Ap u r * cexp (I * r * w) := by
  have e := funext fun r => Ap_mul_exp u r w
  rw [e]
  exact ((integrable_exp_div (u + w)).const_mul _).add ((integrable_exp_div (w - u)).const_mul _)

/-- **`∫ A_u(r)e^{irw} dr = π(e^{−u/2}E(u + w) + e^{u/2}E(w − u))`**. -/
lemma integral_Ap_exp (u w : ℝ) :
    ∫ r : ℝ, Ap u r * cexp (I * r * w) =
      ((π * (Real.exp (-u / 2) * ePhi (u + w) + Real.exp (u / 2) * ePhi (w - u)) : ℝ) : ℂ) := by
  have e := funext fun r => Ap_mul_exp u r w
  rw [e, integral_add ((integrable_exp_div (u + w)).const_mul _) ((integrable_exp_div (w - u)).const_mul _),
    integral_const_mul, integral_const_mul, integral_exp_div, integral_exp_div]
  push_cast
  ring

/-- **The transform of `H_u`**:
`g(v) = ½(e^{−u/2}(E(u + v) + E(u − v)) + e^{u/2}(E(v − u) + E(−u − v))) − cosh u·e^{−|v|/2}`. -/
theorem gh_Hu (u v : ℝ) :
    gh (HuR u) v = (Real.exp (-u / 2) * (ePhi (u + v) + ePhi (u - v)) +
      Real.exp (u / 2) * (ePhi (v - u) + ePhi (-v - u))) / 2 - Real.cosh u * Real.exp (-|v| / 2) := by
  unfold gh HuR
  have hA : Integrable fun r : ℝ => Ap u r * cexp (I * r * v) + Ap u r * cexp (I * r * ((-v : ℝ) : ℂ)) :=
    (integrable_Ap_exp u v).add (integrable_Ap_exp u (-v))
  have e1 : (fun r : ℝ => (2 * (Ap u r).re - Real.cosh u / (r ^ 2 + 1 / 4)) * Real.cos (r * v)) =
      fun r : ℝ => (Ap u r * cexp (I * r * v) + Ap u r * cexp (I * r * ((-v : ℝ) : ℂ))).re -
        Real.cosh u * (Real.cos (r * v) / (r ^ 2 + 1 / 4)) := by
    funext r
    have hc : cexp (I * r * v) + cexp (I * r * ((-v : ℝ) : ℂ)) = ((2 * Real.cos (r * v) : ℝ) : ℂ) := by
      rw [show I * (r : ℂ) * v = ((r * v : ℝ) : ℂ) * I by push_cast; ring,
        show I * (r : ℂ) * ((-v : ℝ) : ℂ) = -((r * v : ℝ) : ℂ) * I by push_cast; ring,
        ← Complex.two_cos, ← Complex.ofReal_cos]
      push_cast
      ring
    rw [← mul_add, hc, Complex.re_mul_ofReal]
    ring
  have hB : Integrable fun r : ℝ => Real.cosh u * (Real.cos (r * v) / (r ^ 2 + 1 / 4)) :=
    (BallPsi.integrable_cos_div v).const_mul _
  have hA' : Integrable fun r : ℝ =>
      (Ap u r * cexp (I * r * v) + Ap u r * cexp (I * r * ((-v : ℝ) : ℂ))).re := hA.re
  have hre := integral_re hA
  simp only [RCLike.re_to_complex] at hre
  rw [e1, integral_sub hA' hB, hre, integral_add (integrable_Ap_exp u v) (integrable_Ap_exp u (-v)),
    integral_const_mul, BallPsi.integral_cos_div, integral_Ap_exp, integral_Ap_exp]
  simp only [Complex.add_re, Complex.ofReal_re]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  field_simp
  ring_nf

/-! ## The prime sum -/

lemma summable_vonMangoldt_div_sq : Summable fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
  have hs : Summable fun n : ℕ => 2 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
  refine hs.of_nonneg_of_le (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h2 : Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) := Real.log_le_rpow_div hn0.le (by norm_num)
    have h3 : (n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) ^ 2 := by
      rw [← Real.rpow_add hn0, show (3 : ℝ) / 2 + 1 / 2 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    have h4 : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hn0 _
    rw [div_le_iff₀ (by positivity), ← h3]
    field_simp
    nlinarith [Real.rpow_pos_of_pos hn0 ((1 : ℝ) / 2)]

/-- **The terms of the prime sum**: `Λ(n)n^{−1/2}g(log n) = cosh u·Λ(n)/n²` plus, for `n ≤ x`,
`Λ(n)((1 + n + 1/n + 1/n²)/(2x) − cosh u/n − cosh u/n²)`. -/
lemma prime_term {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (HuR (Real.log x)) (Real.log n) =
      Real.cosh (Real.log x) * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2) +
        if n ∈ Finset.Ioc 0 ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n *
          ((1 + n + 1 / n + 1 / n ^ 2) / (2 * x) - Real.cosh (Real.log x) / n - Real.cosh (Real.log x) / n ^ 2)
        else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
  set l := Real.log n with hl
  have hl0 : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hpos)
  have hS : Real.exp (L / 2) = Real.sqrt x := BallPsi.exp_log_half hx0
  have hs : Real.exp (l / 2) = Real.sqrt n := BallPsi.exp_log_half hn0
  have hSpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hxS : x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx0.le).symm
  have hns : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt hn0.le).symm
  set S := Real.sqrt x
  set t := Real.sqrt n
  have hc : Real.cosh L = (S ^ 2 + (S ^ 2)⁻¹) / 2 := by
    rw [Real.cosh_eq, show L = L / 2 + L / 2 by ring, Real.exp_add, hS, show -(L / 2 + L / 2) = -(L / 2) + -(L / 2)
      by ring, Real.exp_add, Real.exp_neg, hS]
    ring
  rw [gh_Hu, abs_of_nonneg hl0]
  have eA : Real.exp (-L / 2) = S⁻¹ := by rw [neg_div, Real.exp_neg, hS]
  have eB : Real.exp (-l / 2) = t⁻¹ := by rw [neg_div, Real.exp_neg, hs]
  rw [ePhi_of_nonneg (by linarith : 0 ≤ L + l), ePhi_of_nonpos (by linarith : -l - L ≤ 0), eA, hS, eB]
  have e1 : Real.exp (-(L + l) / 2) = S⁻¹ * t⁻¹ := by
    rw [show -(L + l) / 2 = -(L / 2) + -(l / 2) by ring, Real.exp_add, Real.exp_neg, Real.exp_neg, hS, hs]
  have e2 : Real.exp (3 * (-l - L) / 2) = S⁻¹ ^ 3 * t⁻¹ ^ 3 := by
    rw [show 3 * (-l - L) / 2 = -(L / 2) + -(L / 2) + -(L / 2) + (-(l / 2) + -(l / 2) + -(l / 2)) by ring]
    simp only [Real.exp_add, Real.exp_neg, hS, hs]
    ring
  rw [e1, e2]
  by_cases hnx : n ∈ Finset.Ioc 0 ⌊x⌋₊
  · have hnx' : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).1 (Finset.mem_Ioc.1 hnx).2
    have hlL : l ≤ L := Real.log_le_log hn0 hnx'
    rw [ite_eq_left hnx, ePhi_of_nonneg (by linarith : 0 ≤ L - l), ePhi_of_nonpos (by linarith : l - L ≤ 0)]
    have e3 : Real.exp (-(L - l) / 2) = S⁻¹ * t := by
      rw [show -(L - l) / 2 = -(L / 2) + l / 2 by ring, Real.exp_add, Real.exp_neg, hS, hs]
    have e4 : Real.exp (3 * (l - L) / 2) = S⁻¹ ^ 3 * t ^ 3 := by
      rw [show 3 * (l - L) / 2 = -(L / 2) + -(L / 2) + -(L / 2) + (l / 2 + l / 2 + l / 2) by ring]
      simp only [Real.exp_add, Real.exp_neg, hS, hs]
      ring
    rw [e3, e4, hc, hxS, hns]
    field_simp
    ring
  · have hnx' : x < n := by
      by_contra h
      exact hnx (Finset.mem_Ioc.2 ⟨hpos, (Nat.le_floor_iff hx0.le).2 (not_lt.1 h)⟩)
    have hlL : L < l := Real.log_lt_log hx0 hnx'
    rw [ite_eq_right hnx, ePhi_of_nonpos (by linarith : L - l ≤ 0), ePhi_of_nonneg (by linarith : 0 ≤ l - L)]
    have e3 : Real.exp (3 * (L - l) / 2) = S ^ 3 * t⁻¹ ^ 3 := by
      rw [show 3 * (L - l) / 2 = L / 2 + L / 2 + L / 2 + (-(l / 2) + -(l / 2) + -(l / 2)) by ring]
      simp only [Real.exp_add, Real.exp_neg, hS, hs]
      ring
    have e4 : Real.exp (-(l - L) / 2) = S * t⁻¹ := by
      rw [show -(l - L) / 2 = L / 2 + -(l / 2) by ring, Real.exp_add, Real.exp_neg, hS, hs]
    rw [e3, e4, hc, hns]
    field_simp
    ring

/-- **The prime sum**: `Σ_n Λ(n)n^{−1/2}g(log n) = cosh u·Σ_n Λ(n)/n² +
Σ_{n ≤ x} Λ(n)((1 + n + 1/n + 1/n²)/(2x) − cosh u/n − cosh u/n²)`. -/
lemma prime_sum {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (HuR (Real.log x)) (Real.log n) =
      Real.cosh (Real.log x) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 +
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
          ((1 + n + 1 / n + 1 / n ^ 2) / (2 * x) - Real.cosh (Real.log x) / n - Real.cosh (Real.log x) / n ^ 2) := by
  rw [tsum_congr (prime_term hx)]
  have h1 := summable_vonMangoldt_div_sq.mul_left (Real.cosh (Real.log x))
  have h2 : Summable fun n : ℕ => if n ∈ Finset.Ioc 0 ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n *
      ((1 + n + 1 / n + 1 / n ^ 2) / (2 * x) - Real.cosh (Real.log x) / n - Real.cosh (Real.log x) / n ^ 2)
      else 0 := summable_of_ne_finset_zero fun n hn => ite_eq_right hn
  rw [h1.tsum_add h2, tsum_mul_left, tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) fun n hn => ite_eq_right hn]
  congr 1
  exact Finset.sum_congr rfl fun n hn => ite_eq_left hn

/-! ## The explicit formula -/

/-- The archimedean term `(1/2π)∫ H_u(r)·Re ψ(¼ + ir/2) dr`. -/
def archP1 (u : ℝ) : ℝ := 1 / (2 * π) * ∫ r, HuR u r * psiRe r

/-- Weil's explicit formula for `H_u` (`WeilForm.weilExplicit_zeta`). -/
lemma weil_Hu (u : ℝ) : WeilExplicit zetaZeroFamily (Hu u) (HuR u) := by
  obtain ⟨C, hC⟩ := stripTest_Hu u
  exact weilExplicit_zeta hC (Hu_even u) (Hu_real u)

/-- The terms of `K(x)` and of `K(1/x)`, zero by zero. -/
lemma hasSum_two (x : ℝ) : HasSum (fun q : ZIdx => (term x (Sum.inl q) + term x (Sum.inr q)) +
    (term x⁻¹ (Sum.inl q) + term x⁻¹ (Sum.inr q))) (kerP1 x + kerP1 x⁻¹) := by
  have h (y : ℝ) : HasSum (fun q : ZIdx => term y (Sum.inl q) + term y (Sum.inr q)) (kerP1 y) := by
    have h1 : Summable (term y ∘ Sum.inl) := (summable_term y).comp_injective Sum.inl_injective
    have h2 : Summable (term y ∘ Sum.inr) := (summable_term y).comp_injective Sum.inr_injective
    rw [kerP1_eq_tsum, Summable.tsum_sum h1 h2]
    exact h1.hasSum.add h2.hasSum
  exact (h x).add (h x⁻¹)

/-- **The explicit formula for the kernel of `ℙ¹`, through the primes**: for `x ≥ 1`, with `u = log x` and
`c₀ = 2 + γ − log 4π`,
`K(x) = cosh u·(c₀ − 1 + log π)/2 + 2 − u·sinh u − (log π)/x + A(u)/2 − cosh u·Σ_n Λ(n)/n²
  + Σ_{n ≤ x} Λ(n)(cosh u/n + cosh u/n² − (1 + n + 1/n + 1/n²)/(2x))`, with `A` the archimedean term `archP1`.
No hypothesis. -/
theorem kerP1_explicit {x : ℝ} (hx : 1 ≤ x) :
    kerP1 x = ((Real.cosh (Real.log x) * (2 + eulerMascheroniConstant - Real.log (4 * π) - 1 + Real.log π) / 2 +
      2 - Real.log x * Real.sinh (Real.log x) - Real.log π / x + archP1 (Real.log x) / 2 -
      Real.cosh (Real.log x) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 +
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
        (Real.cosh (Real.log x) / n + Real.cosh (Real.log x) / n ^ 2 - (1 + n + 1 / n + 1 / n ^ 2) / (2 * x)) :
        ℝ) : ℂ) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hW := (weil_Hu L).2
  have hH := hadamard_zeta.mul_left ((Real.cosh L : ℝ) : ℂ)
  have hsum := hW.add hH
  have e : (fun q : ZIdx => Hu L ((zetaZeroFamily q - 1 / 2) / I) + ((Real.cosh L : ℝ) : ℂ) *
      (1 / (zetaZeroFamily q * (1 - zetaZeroFamily q)))) = fun q : ZIdx =>
      (term x (Sum.inl q) + term x (Sum.inr q)) + (term x⁻¹ (Sum.inl q) + term x⁻¹ (Sum.inr q)) := by
    funext q
    rw [Hu_term L q]
    simp only [term, zP1, Sum.elim_inl, Sum.elim_inr, Real.log_inv, ← hL]
    push_cast
    ring
  rw [e] at hsum
  have h2 := (hasSum_two x).unique hsum
  rw [kerP1_inv, Hu_half, Hu_neg_half, prime_sum hx, gh_Hu, abs_zero, neg_zero, zero_div, Real.exp_zero,
    add_zero, sub_zero, zero_sub, ePhi_of_nonneg hL0, ePhi_of_nonpos (by linarith : -L ≤ 0)] at h2
  have hE1 : Real.exp (-L / 2) * Real.exp (-L / 2) = x⁻¹ := by
    rw [← Real.exp_add, show -L / 2 + -L / 2 = -L by ring, Real.exp_neg, hL, Real.exp_log hx0]
  have hE2 : Real.exp (L / 2) * Real.exp (3 * -L / 2) = x⁻¹ := by
    rw [← Real.exp_add, show L / 2 + 3 * -L / 2 = -L by ring, Real.exp_neg, hL, Real.exp_log hx0]
  have hg0 : (Real.exp (-L / 2) * (Real.exp (-L / 2) + Real.exp (-L / 2)) +
      Real.exp (L / 2) * (Real.exp (3 * -L / 2) + Real.exp (3 * -L / 2))) / 2 - Real.cosh L * 1 =
      2 * x⁻¹ - Real.cosh L := by
    rw [mul_add, mul_add, hE1, hE2]; ring
  rw [hg0, ← hL] at h2
  unfold archP1
  have hsplit : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
      (Real.cosh L / n + Real.cosh L / n ^ 2 - (1 + n + 1 / n + 1 / n ^ 2) / (2 * x)) =
      -∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
        ((1 + n + 1 / n + 1 / n ^ 2) / (2 * x) - Real.cosh L / n - Real.cosh L / n ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [show kerP1 x = (kerP1 x + kerP1 x) / 2 by ring, h2, hsplit]
  push_cast
  ring

/-! ## A kernel from the primes alone -/

/-- **The kernel of `ℙ¹` built from the primes**: the right side of `kerP1_explicit` at `y = max(x, 1/x)`. -/
def kerP1ψ (x : ℝ) : ℂ :=
  ((Real.cosh (Real.log (max x x⁻¹)) * (2 + eulerMascheroniConstant - Real.log (4 * π) - 1 + Real.log π) / 2 +
    2 - Real.log (max x x⁻¹) * Real.sinh (Real.log (max x x⁻¹)) - Real.log π / max x x⁻¹ +
    archP1 (Real.log (max x x⁻¹)) / 2 -
    Real.cosh (Real.log (max x x⁻¹)) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 +
    ∑ n ∈ Finset.Ioc 0 ⌊max x x⁻¹⌋₊, ArithmeticFunction.vonMangoldt n *
      (Real.cosh (Real.log (max x x⁻¹)) / n + Real.cosh (Real.log (max x x⁻¹)) / n ^ 2 -
        (1 + n + 1 / n + 1 / n ^ 2) / (2 * max x x⁻¹)) : ℝ) : ℂ)

lemma kerP1_eq_kerP1ψ {x : ℝ} (hx : 0 < x) : kerP1 x = kerP1ψ x := by
  unfold kerP1ψ
  rcases le_total 1 x with h | h
  · rw [max_eq_left ((inv_le_one_of_one_le₀ h).trans h)]
    exact kerP1_explicit h
  · have h' : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 h
    rw [max_eq_right (h.trans h'), ← kerP1_inv x]
    exact kerP1_explicit h'

/-- **A kernel from the primes that is not positive-definite**: `kerP1ψ`, built from `Λ`, `γ`, `π`, `Σ Λ(n)/n²`
and the archimedean term, without the zeros, is not positive-definite on the positive rationals. No hypothesis: it is
the kernel of `ℙ¹` (`kerP1_eq_kerP1ψ`), which has the Euler product and the functional equation, and its zeros off
the line (`PurityRational.not_posDef`). -/
theorem not_posDef_psi : ¬ PosDefQ kerP1ψ := fun h =>
  not_posDef ((BallPsi.posDefQ_congr fun _ hx => kerP1_eq_kerP1ψ hx).2 h)

end PurityPsi

#print axioms PurityPsi.kerP1_inv
#print axioms PurityPsi.kerP1_explicit
#print axioms PurityPsi.not_posDef_psi
