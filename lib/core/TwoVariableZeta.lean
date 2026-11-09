/-
# The two-variable zeta function of Lagarias and Rains

Plain statement. For `w > 0` the `w`-th power of the theta function `θ(t) = Σ_{n ∈ ℤ} e^{−πn²t}` satisfies
`θ(1/t)^w = t^{w/2}θ(t)^w` and `θ(t)^w → 1` faster than any power of `t`, so it is a weak FE-pair of weight `w/2`
(`thetaPowFEPair`). Its completed Mellin transform `Z(w, s) = ½Λ(s/2)` (`Z`) is the zeta function of two variables of
J. C. Lagarias and E. Rains ("On a two-variable zeta function for number fields", Ann. Inst. Fourier 53 (2003), (1.5)),
which G. van der Geer and R. Schoof built from the Arakelov divisors of `ℚ`:
* `Z(w, w − s) = Z(w, s)` (`functional_equation`), and `Z(w, ·)` is holomorphic off `s = 0` and `s = w`
  (`differentiableAt`);
* on `Re s > w`, `2Z(w, s)` is the Mellin transform `∫₀^∞ (θ(t)^w − 1) t^{s/2} dt/t` (`hasMellin`);
* `w = 1`: `Z(1, s) = ζ̂(s) = π^{−s/2}Γ(s/2)ζ(s)` (`Z_one`);
* `w = 4`: `θ(t)⁴ = Σ_{n ≥ 0} r₄(n)e^{−πnt}`, and by Jacobi's four-square theorem (`JacobiFourSquares.r4_eq`)
  `Σ_{n ≥ 1} r₄(n)n^{−z} = 8(1 − 4^{1−z})ζ(z)ζ(z − 1)`, so on `Re s > 4`
  `Z(4, s) = 4Γ_ℝ(s)(1 − 4^{1−s/2})ζ(s/2)ζ(s/2 − 1)` (`Z_four`): in the variable `z = s/2`, the zeta function
  `ζ(z)ζ(z − 1)` of `ℙ¹` over `ℤ` (`PurityRational`) with its Euler factor at `2` changed. Lagarias and Rains find
  Euler products only at `w = 0, 1, 2, 4, 8`.
The proof of `Z_four` expands `θ⁴` as a sum over `ℤ⁴` grouped by `|v|²`, takes the Mellin transform term by term
(Mathlib's `hasSum_mellin_pi_mul₀`), and writes `Σ_{d ∣ n, 4 ∤ d} d` as the Dirichlet convolution of `d ↦ d·[4 ∤ d]`
with `1`.
-/
import Mathlib
import JacobiFourSquares
open Real Complex Filter Topology Asymptotics Set MeasureTheory HurwitzZeta
open scoped LSeries.notation

noncomputable section

namespace TwoVariableZeta

/-! ## `θ^w` is a weak FE-pair of weight `w/2` -/

/-- `θ(t) = Σ_{n ∈ ℤ} e^{−πn²t}`, Mathlib's `evenKernel 0`, as a sum over `ℤ`. -/
lemma hasSum_theta {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => rexp (-π * (n : ℝ) ^ 2 * t)) (evenKernel 0 t) := by
  simpa using hasSum_int_evenKernel 0 ht

/-- `θ(t) ≥ 1`, its `n = 0` term, for `t > 0`. -/
lemma one_le_theta {t : ℝ} (ht : 0 < t) : 1 ≤ evenKernel 0 t := by
  simpa using le_hasSum (hasSum_theta ht) 0 fun j _ => (Real.exp_pos _).le

/-- **Jacobi's transformation** `θ(1/x) = x^{1/2} θ(x)`. -/
lemma theta_inv {x : ℝ} (hx : 0 < x) : evenKernel 0 (1 / x) = x ^ (1 / 2 : ℝ) * evenKernel 0 x := by
  have h := evenKernel_functional_equation 0 x
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  rw [h, ← mul_assoc, mul_one_div_cancel (Real.rpow_pos_of_pos hx _).ne', one_mul]

/-- `θ(t)^w`, as a complex-valued function of `t`. -/
def thetaPow (w t : ℝ) : ℂ := ((evenKernel 0 t ^ w : ℝ) : ℂ)

lemma locallyIntegrableOn_thetaPow {w : ℝ} (hw : 0 < w) : LocallyIntegrableOn (thetaPow w) (Ioi 0) :=
  (continuous_ofReal.comp_continuousOn ((continuousOn_evenKernel 0).rpow_const
    fun _ _ => Or.inr hw.le)).locallyIntegrableOn measurableSet_Ioi

lemma thetaPow_inv {w x : ℝ} (hx : x ∈ Ioi 0) :
    thetaPow w (1 / x) = ((1 : ℂ) * ((x ^ (w / 2) : ℝ) : ℂ)) • thetaPow w x := by
  have hx' : 0 < x := hx
  simp only [thetaPow, one_mul, smul_eq_mul, ← ofReal_mul]
  congr 1
  rw [theta_inv hx', Real.mul_rpow (Real.rpow_nonneg hx'.le _) (by linarith [one_le_theta hx']),
    ← Real.rpow_mul hx'.le, one_div_mul_eq_div]

/-- `θ(t)^w − 1` decays faster than any power of `t`. -/
lemma isBigO_thetaPow_sub {w : ℝ} (r : ℝ) : (thetaPow w · - 1) =O[atTop] (· ^ r) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  simp only [ite_true] at hO
  have hexp : Tendsto (fun t : ℝ => rexp (-p * t)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
  have hθ : Tendsto (evenKernel 0) atTop (𝓝 1) := tendsto_sub_nhds_zero_iff.1 (hO.trans_tendsto hexp)
  have hd := ((Real.hasDerivAt_rpow_const (p := w) (x := 1) (Or.inl one_ne_zero)).isBigO_sub).comp_tendsto hθ
  refine (isBigO_ofReal_left.mpr
    (hd.trans (hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO))).congr_left fun t => ?_
  simp [thetaPow, Real.one_rpow]

/-- **`θ^w` is a weak FE-pair** of weight `w/2` and root number `1`, its own dual, with constant term `1` at both
ends. -/
def thetaPowFEPair (w : ℝ) (hw : 0 < w) : WeakFEPair ℂ where
  f := thetaPow w
  g := thetaPow w
  k := w / 2
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_thetaPow hw
  hg_int := locallyIntegrableOn_thetaPow hw
  hk := half_pos hw
  hε := one_ne_zero
  h_feq _ hx := thetaPow_inv hx
  hf_top := isBigO_thetaPow_sub
  hg_top := isBigO_thetaPow_sub

lemma thetaPowFEPair_symm (w : ℝ) (hw : 0 < w) : (thetaPowFEPair w hw).symm = thetaPowFEPair w hw := by
  unfold thetaPowFEPair WeakFEPair.symm
  congr 1
  exact inv_one

/-! ## The two-variable zeta function -/

/-- **The two-variable zeta function of Lagarias and Rains**, `Z(w, s) = ½ Λ(s/2)` for the FE-pair `θ^w`: the
regularised Mellin transform `½ ∫₀^∞ θ(t)^w t^{s/2} dt/t`. -/
def Z (w : ℝ) (hw : 0 < w) (s : ℂ) : ℂ := (thetaPowFEPair w hw).Λ (s / 2) / 2

/-- **The functional equation** `Z(w, w − s) = Z(w, s)`. -/
theorem functional_equation (w : ℝ) (hw : 0 < w) (s : ℂ) : Z w hw (w - s) = Z w hw s := by
  have h := (thetaPowFEPair w hw).functional_equation (s / 2)
  rw [thetaPowFEPair_symm] at h
  have hk : (((thetaPowFEPair w hw).k : ℝ) : ℂ) - s / 2 = (w - s) / 2 := by
    simp only [thetaPowFEPair]; push_cast; ring
  unfold Z
  rw [← hk, h]
  simp [thetaPowFEPair]

/-- `Z(w, ·)` is holomorphic away from its poles `s = 0` and `s = w`. -/
theorem differentiableAt (w : ℝ) (hw : 0 < w) {s : ℂ} (h0 : s ≠ 0) (hw' : s ≠ w) :
    DifferentiableAt ℂ (Z w hw) s := by
  have h1 : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have h2 : s / 2 ≠ (((thetaPowFEPair w hw).k : ℝ) : ℂ) := by
    simp only [thetaPowFEPair]; push_cast
    intro h; exact hw' (by linear_combination 2 * h)
  have h3 : DifferentiableAt ℂ (fun x : ℂ => x / 2) s := differentiableAt_id.div_const (2 : ℂ)
  exact (((thetaPowFEPair w hw).differentiableAt_Λ (Or.inl h1) (Or.inl h2)).comp s h3).div_const (2 : ℂ)

/-- **On `Re s > w`, `2Z(w, s)` is the Mellin transform** `∫₀^∞ (θ(t)^w − 1) t^{s/2} dt/t`. -/
theorem hasMellin (w : ℝ) (hw : 0 < w) {s : ℂ} (hs : w < s.re) :
    HasMellin (fun t => thetaPow w t - 1) (s / 2) (2 * Z w hw s) := by
  have h := (thetaPowFEPair w hw).hasMellin (s := s / 2) (by
    simp only [thetaPowFEPair, div_ofNat_re]; linarith)
  have e : (2 : ℂ) * Z w hw s = (thetaPowFEPair w hw).Λ (s / 2) := by unfold Z; ring
  rw [e]
  exact h

lemma thetaPowFEPair_one : thetaPowFEPair 1 one_pos = hurwitzEvenFEPair 0 := by
  unfold thetaPowFEPair hurwitzEvenFEPair
  congr 1
  · funext t; simp [thetaPow]
  · funext t; simp [thetaPow, evenKernel_eq_cosKernel_of_zero]
  · norm_num

/-- **At `w = 1`, `Z` is the completed Riemann zeta function** `ζ̂(s) = π^{−s/2}Γ(s/2)ζ(s)`. -/
theorem Z_one (s : ℂ) : Z 1 one_pos s = completedRiemannZeta s := by
  rw [Z, thetaPowFEPair_one]
  rfl

/-! ## `w = 4`: Jacobi's four-square theorem -/

open JacobiFourSquares

/-- **`θ(t)^4 = Σ_{n ≥ 0} r₄(n) e^{−πnt}`**: expand the fourth power as a sum over `ℤ⁴` and group by `|v|²`. -/
lemma hasSum_theta_four {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (r4 n : ℝ) * rexp (-π * n * t)) (evenKernel 0 t ^ 4) := by
  set g : ℤ → ℝ := fun n => rexp (-π * (n : ℝ) ^ 2 * t) with hg
  have hθ : HasSum g (evenKernel 0 t) := hasSum_theta ht
  have g0 : 0 ≤ g := fun n => (Real.exp_pos _).le
  have h2 : HasSum (fun p : ℤ × ℤ => g p.1 * g p.2) (evenKernel 0 t * evenKernel 0 t) :=
    hθ.mul hθ (hθ.summable.mul_of_nonneg hθ.summable g0 g0)
  have g2 : 0 ≤ fun p : ℤ × ℤ => g p.1 * g p.2 := fun p => mul_nonneg (g0 _) (g0 _)
  have h4 := h2.mul h2 (h2.summable.mul_of_nonneg h2.summable g2 g2)
  let e : (Fin 4 → ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) :=
    { toFun := fun v => ((v 0, v 1), (v 2, v 3))
      invFun := fun q => ![q.1.1, q.1.2, q.2.1, q.2.2]
      left_inv := fun v => by ext i; fin_cases i <;> rfl
      right_inv := fun q => rfl }
  let N : (Fin 4 → ℤ) → ℕ := fun v => ∑ i, (v i).natAbs ^ 2
  have hN (v : Fin 4 → ℤ) : (∑ i, (v i : ℝ) ^ 2) = (N v : ℝ) := by
    simp only [N, Nat.cast_sum, Nat.cast_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hfun : (fun q : (ℤ × ℤ) × (ℤ × ℤ) => g q.1.1 * g q.1.2 * (g q.2.1 * g q.2.2)) ∘ e =
      fun v => rexp (-π * (N v : ℝ) * t) := by
    funext v
    show g (v 0) * g (v 1) * (g (v 2) * g (v 3)) = _
    simp only [g, ← Real.exp_add, ← hN, Fin.sum_univ_four]
    congr 1
    ring
  have hv : HasSum (fun v : Fin 4 → ℤ => rexp (-π * (N v : ℝ) * t)) (evenKernel 0 t ^ 4) := by
    rw [← hfun, show evenKernel 0 t ^ 4 = evenKernel 0 t * evenKernel 0 t * (evenKernel 0 t * evenKernel 0 t)
      by ring]
    exact e.hasSum_iff.2 h4
  convert hv.tsum_fiberwise N using 1
  funext n
  have hset : N ⁻¹' {n} = ↑((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter
      (fun v => ∑ i, v i ^ 2 = (n : ℤ))) := by
    ext v
    have key : N v = n ↔ ∑ i, v i ^ 2 = (n : ℤ) := by
      rw [← Nat.cast_inj (R := ℤ)]
      simp only [N, Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Fintype.mem_piFinset,
      Finset.mem_Icc, Set.mem_ofPred_eq, key]
    constructor
    · intro h
      refine ⟨fun i => ?_, h⟩
      have hle : v i ^ 2 ≤ n := h ▸ Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      have habs := Int.natAbs_le_self_sq (v i)
      rw [Int.natCast_natAbs] at habs
      exact abs_le.1 (habs.trans hle)
    · exact fun h => h.2
  rw [tsum_congr fun v : ↑(N ⁻¹' {n}) => show rexp (-π * (N v : ℝ) * t) = rexp (-π * n * t) by
    rw [show N v = n from v.2], hset, tsum_const, Nat.card_coe_set_eq, Set.ncard_coe_finset, nsmul_eq_mul]
  rfl

/-- `d` for `4 ∤ d`, `0` for `4 ∣ d`: so that `σ₄ = χ₄ ⍟ 1`. -/
def chi4 (d : ℕ) : ℂ := if 4 ∣ d then 0 else d

lemma sigma4_eq : (fun n => (sigma4 n : ℂ)) = chi4 ⍟ 1 := by
  funext n
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => chi4 a), sigma4, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : 4 ∣ d <;> simp [chi4, h]

lemma LSeriesSummable_natCast {z : ℂ} (hz : 2 < z.re) : LSeriesSummable (fun n : ℕ => (n : ℂ)) z :=
  LSeriesSummable_of_le_const_mul_rpow (x := 2) hz ⟨1, fun n _ => by norm_num⟩

lemma LSeries_natCast {z : ℂ} (hz : 2 < z.re) : LSeries (fun n : ℕ => (n : ℂ)) z = riemannZeta (z - 1) := by
  rw [← LSeries_one_eq_riemannZeta (by simp; linarith), LSeries, LSeries]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Pi.one_apply]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have e : (n : ℂ) ^ z = (n : ℂ) ^ (z - 1) * n := by
      conv_lhs => rw [show z = z - 1 + 1 by ring]
      rw [Complex.cpow_add _ _ hn', Complex.cpow_one]
    have hc : (n : ℂ) ^ (z - 1) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn]
    rw [e]; field_simp

lemma LSeries_dvd_four {z : ℂ} (hz : 2 < z.re) :
    LSeries (fun n : ℕ => if 4 ∣ n then (n : ℂ) else 0) z = 4 ^ (1 - z) * riemannZeta (z - 1) := by
  rw [← LSeries_natCast hz, LSeries, LSeries, ← tsum_mul_left,
    ← Function.Injective.tsum_eq (g := fun m : ℕ => 4 * m) (mul_right_injective₀ four_ne_zero)]
  · congr 1
    funext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have h4m : 4 * m ≠ 0 := mul_ne_zero four_ne_zero hm
      rw [LSeries.term_of_ne_zero h4m, LSeries.term_of_ne_zero hm, ite_eq_left (dvd_mul_right 4 m),
        Nat.cast_mul, natCast_mul_natCast_cpow, Complex.cpow_sub _ _ (by norm_num), Complex.cpow_one]
      have h4 : ((4 : ℕ) : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff]
      have hmz : (m : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hm]
      push_cast at h4 ⊢
      field_simp
  · intro n hn
    by_cases h : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · exact absurd (by simp [LSeries.term_def, h]) hn

lemma LSeriesSummable_dvd_four {z : ℂ} (hz : 2 < z.re) :
    LSeriesSummable (fun n : ℕ => if 4 ∣ n then (n : ℂ) else 0) z :=
  LSeriesSummable_of_le_const_mul_rpow (x := 2) hz ⟨1, fun n _ => by split_ifs <;> norm_num⟩

lemma chi4_eq : chi4 = (fun n : ℕ => (n : ℂ)) - fun n : ℕ => if 4 ∣ n then (n : ℂ) else 0 := by
  funext n
  by_cases h : 4 ∣ n <;> simp [chi4, h]

/-- **`Σ σ₄(n) n^{−z} = (1 − 4^{1−z}) ζ(z) ζ(z − 1)`** on `Re z > 2`. -/
lemma LSeries_sigma4 {z : ℂ} (hz : 2 < z.re) :
    LSeriesSummable (fun n => (sigma4 n : ℂ)) z ∧
      LSeries (fun n => (sigma4 n : ℂ)) z = (1 - 4 ^ (1 - z)) * riemannZeta z * riemannZeta (z - 1) := by
  have hchi : LSeriesSummable chi4 z := chi4_eq ▸ (LSeriesSummable_natCast hz).sub (LSeriesSummable_dvd_four hz)
  have hone : LSeriesSummable 1 z := LSeriesSummable_one_iff.2 (by linarith)
  refine ⟨sigma4_eq ▸ hchi.convolution hone, ?_⟩
  rw [sigma4_eq, LSeries_convolution' hchi hone, chi4_eq,
    LSeries_sub (LSeriesSummable_natCast hz) (LSeriesSummable_dvd_four hz), LSeries_natCast hz,
    LSeries_dvd_four hz, LSeries_one_eq_riemannZeta (by linarith)]
  ring

/-- **At `w = 4`, `Z` is the zeta function of `ℙ¹` over `ℤ` with its Euler factor at `2` changed**: on `Re s > 4`,
`Z(4, s) = 4 Γ_ℝ(s) (1 − 4^{1 − s/2}) ζ(s/2) ζ(s/2 − 1)`, by Jacobi's four-square theorem. -/
theorem Z_four {s : ℂ} (hs : 4 < s.re) :
    Z 4 four_pos s =
      4 * Gammaℝ s * (1 - 4 ^ (1 - s / 2)) * riemannZeta (s / 2) * riemannZeta (s / 2 - 1) := by
  set z := s / 2 with hz_def
  have hz : 2 < z.re := by rw [hz_def, div_ofNat_re]; linarith
  obtain ⟨hsig, hL⟩ := LSeries_sigma4 hz
  -- the Dirichlet coefficients of `θ⁴ − 1`
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i : ℕ => if (i : ℝ) = 0 then 0 else (r4 i : ℂ) * rexp (-π * i * t))
      (thetaPow 4 t - 1) := by
    intro t ht
    have h := (hasSum_ofReal.2 (hasSum_theta_four ht)).update 0 0
    convert h using 1
    · funext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp
      · simp [hi]
    · simp [thetaPow, r4_zero]
      ring
  have h_sum : Summable fun i : ℕ => ‖(r4 i : ℂ)‖ / (i : ℝ) ^ z.re := by
    refine (hsig.norm.mul_left 8).congr fun i => ?_
    rcases eq_or_ne i 0 with rfl | hi
    · simp [Real.zero_rpow (by linarith : z.re ≠ 0)]
    · rw [LSeries.norm_term_eq, ite_eq_right hi, r4_eq hi]
      push_cast
      rw [norm_mul, mul_div_assoc]
      norm_num
  have hD := hasSum_mellin_pi_mul₀ (a := fun i : ℕ => (r4 i : ℂ)) (p := fun i : ℕ => (i : ℝ))
    (F := fun t => thetaPow 4 t - 1) (s := z) (fun i => Nat.cast_nonneg i) (by linarith) hF h_sum
  rw [(hasMellin 4 four_pos (by simpa using hs)).2] at hD
  have hT : (fun i : ℕ => (π : ℂ) ^ (-z) * Gamma z * (r4 i : ℂ) / ((i : ℝ) : ℂ) ^ z) =
      fun i => (π : ℂ) ^ (-z) * Gamma z * (8 * LSeries.term (fun n => (sigma4 n : ℂ)) z i) := by
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; norm_num at hz
      simp [Complex.zero_cpow hz0]
    · rw [LSeries.term_of_ne_zero hi, r4_eq hi, ofReal_natCast]
      push_cast
      ring
  rw [hT] at hD
  have e := hD.unique ((hsig.LSeriesHasSum.mul_left 8).mul_left _)
  rw [hL, Gammaℝ_def, neg_div] at *
  rw [← hz_def]
  linear_combination e / 2

end TwoVariableZeta

#print axioms TwoVariableZeta.functional_equation
#print axioms TwoVariableZeta.differentiableAt
#print axioms TwoVariableZeta.hasMellin
#print axioms TwoVariableZeta.Z_one
#print axioms TwoVariableZeta.Z_four
