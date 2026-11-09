/-
# The two-variable zeta function at `w = 8`: Jacobi's eight squares, and zeros off the line

Plain statement. `θ(t)⁸ = Σ_{n ≥ 0} r₈(n)e^{−πnt}` (`hasSum_theta_eight`), and by Jacobi's eight-square theorem
(`JacobiEightSquares.r8_eq`) `r₈(n) = 16 f₈(n)` with `f₈(n) = Σ_{d ∣ n} (−1)^{n+d} d³` for `n ≥ 1`. As
`(−1)^{n+d} = −1` exactly when `d` is odd and `n/d` even, `f₈ = d³ ⍟ 1 − 2 (d³[2 ∤ d] ⍟ [2 ∣ ·])` (`f8_eq`), so
`Σ_{n ≥ 1} f₈(n)n^{−z} = (1 − 2^{1−z} + 2^{4−2z})ζ(z)ζ(z − 3)` on `Re z > 4` (`LSeries_f8`). Hence on `Re s > 8`
  `Z(8, s) = 8Γ_ℝ(s)(1 − 2^{1−s/2} + 2^{4−s})ζ(s/2)ζ(s/2 − 3)`   (`Z_eight`),
the Euler product of Lagarias and Rains at `w = 8`. With `Γ_ℝ(2z) = π^{−z}Γ(z)`, `Γ_ℝ(z) = Γ_ℝ(z − 2)(z − 2)/(2π)` and
`Γ_ℝ(z − 3)Γ_ℝ(z − 2) = Γ_ℂ(z − 3)` this reads `Z(8, 2z) = c₈(z)·ζ̂(z)ζ̂(z − 3)` with
`c₈(z) = 2^z(z − 1)(z − 3)(1 − 2^{1−z} + 2^{4−2z})/π²` entire (`c8`), and by the identity theorem the equation holds
off `z = 0, 1, 3, 4` (`Z_eight_eq`). So `Z(8, 2ρ) = 0` for every nontrivial zero `ρ` of `ζ`, and `0 < Re 2ρ < 2`:
`Z(8, ·)` has zeros off its line `Re s = 4` whatever the truth of RH (`exists_zero_re_ne_four`), as `Z(4, ·)` does
(`TwoVariableZetaPurity.exists_zero_re_ne_two`).
-/
import Mathlib
import TwoVariableZeta
import TwoVariableZetaPurity
import JacobiEightSquares

open Real Complex Filter Topology Set MeasureTheory HurwitzZeta
open scoped LSeries.notation

noncomputable section

namespace TwoVariableZetaEight

open TwoVariableZeta JacobiEightSquares WeilForm WeilTest

lemma eight_pos : (0 : ℝ) < 8 := by norm_num

/-! ## `θ⁸` as a Dirichlet series -/

/-- **`θ(t)^8 = Σ_{n ≥ 0} r₈(n) e^{−πnt}`**: expand the eighth power as a sum over `ℤ⁸` and group by `|v|²`. -/
lemma hasSum_theta_eight {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (r8 n : ℝ) * rexp (-π * n * t)) (evenKernel 0 t ^ 8) := by
  set g : ℤ → ℝ := fun n => rexp (-π * (n : ℝ) ^ 2 * t) with hg
  have hθ : HasSum g (evenKernel 0 t) := hasSum_theta ht
  have g0 : 0 ≤ g := fun n => (Real.exp_pos _).le
  have h2 : HasSum (fun p : ℤ × ℤ => g p.1 * g p.2) (evenKernel 0 t * evenKernel 0 t) :=
    hθ.mul hθ (hθ.summable.mul_of_nonneg hθ.summable g0 g0)
  have g2 : 0 ≤ fun p : ℤ × ℤ => g p.1 * g p.2 := fun p => mul_nonneg (g0 _) (g0 _)
  have h4 := h2.mul h2 (h2.summable.mul_of_nonneg h2.summable g2 g2)
  have g4 : 0 ≤ fun q : (ℤ × ℤ) × (ℤ × ℤ) => g q.1.1 * g q.1.2 * (g q.2.1 * g q.2.2) :=
    fun q => mul_nonneg (g2 _) (g2 _)
  have h8 := h4.mul h4 (h4.summable.mul_of_nonneg h4.summable g4 g4)
  let e : (Fin 8 → ℤ) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) × ((ℤ × ℤ) × (ℤ × ℤ)) :=
    { toFun := fun v => (((v 0, v 1), (v 2, v 3)), ((v 4, v 5), (v 6, v 7)))
      invFun := fun q => ![q.1.1.1, q.1.1.2, q.1.2.1, q.1.2.2, q.2.1.1, q.2.1.2, q.2.2.1, q.2.2.2]
      left_inv := fun v => by ext i; fin_cases i <;> rfl
      right_inv := fun q => rfl }
  let N : (Fin 8 → ℤ) → ℕ := fun v => ∑ i, (v i).natAbs ^ 2
  have hN (v : Fin 8 → ℤ) : (∑ i, (v i : ℝ) ^ 2) = (N v : ℝ) := by
    simp only [N, Nat.cast_sum, Nat.cast_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hfun : (fun q : ((ℤ × ℤ) × (ℤ × ℤ)) × ((ℤ × ℤ) × (ℤ × ℤ)) =>
      g q.1.1.1 * g q.1.1.2 * (g q.1.2.1 * g q.1.2.2) * (g q.2.1.1 * g q.2.1.2 * (g q.2.2.1 * g q.2.2.2))) ∘ e =
      fun v => rexp (-π * (N v : ℝ) * t) := by
    funext v
    show g (v 0) * g (v 1) * (g (v 2) * g (v 3)) * (g (v 4) * g (v 5) * (g (v 6) * g (v 7))) = _
    simp only [g, ← Real.exp_add, ← hN, Fin.sum_univ_eight]
    congr 1
    ring
  have hv : HasSum (fun v : Fin 8 → ℤ => rexp (-π * (N v : ℝ) * t)) (evenKernel 0 t ^ 8) := by
    rw [← hfun, show evenKernel 0 t ^ 8 = evenKernel 0 t * evenKernel 0 t * (evenKernel 0 t * evenKernel 0 t) *
      (evenKernel 0 t * evenKernel 0 t * (evenKernel 0 t * evenKernel 0 t)) by ring]
    exact e.hasSum_iff.2 h8
  convert hv.tsum_fiberwise N using 1
  funext n
  have hset : N ⁻¹' {n} = ↑((Fintype.piFinset fun _ : Fin 8 => Finset.Icc (-(n : ℤ)) n).filter
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

/-! ## The Dirichlet series of `r₈` -/

/-- `Σ_{d ∣ n} (−1)^{n+d} d³`, so that `r₈(n) = 16 f₈(n)` for `n ≥ 1` (`JacobiEightSquares.r8_eq`). -/
def f8 (n : ℕ) : ℂ := ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℂ) ^ 3

/-- `d³` for odd `d`, `0` for even `d`. -/
def oddCube (n : ℕ) : ℂ := if 2 ∣ n then 0 else (n : ℂ) ^ 3

/-- `n ↦ n^k` on the even `n`, `0` on the odd ones. -/
def evenPow (k n : ℕ) : ℂ := if 2 ∣ n then (n : ℂ) ^ k else 0

/-- `f₈ = d³ ⍟ 1 − 2 (oddCube ⍟ [2 ∣ ·])`: `(−1)^{n+d} = −1` exactly when `d` is odd and `n/d` even. -/
lemma f8_eq : f8 = (fun n : ℕ => (n : ℂ) ^ 3) ⍟ 1 - (2 : ℂ) • (oddCube ⍟ evenPow 0) := by
  funext n
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LSeries.convolution_def, Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => (a : ℂ) ^ 3),
    Nat.sum_divisorsAntidiagonal (fun a b => oddCube a * evenPow 0 b), Finset.mul_sum, f8,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
  rw [he, Nat.mul_div_cancel_left _ (Nat.pos_of_mem_divisors hd), pow_add, pow_mul, oddCube, evenPow]
  rcases Nat.even_or_odd d with h | h
  · rw [h.neg_one_pow, ite_eq_left h.two_dvd]
    ring
  · rw [h.neg_one_pow, ite_eq_right (Nat.not_even_iff_odd.mpr h ∘ even_iff_two_dvd.mpr)]
    rcases Nat.even_or_odd e with h' | h'
    · rw [h'.neg_one_pow, ite_eq_left h'.two_dvd]
      ring
    · rw [h'.neg_one_pow, ite_eq_right (Nat.not_even_iff_odd.mpr h' ∘ even_iff_two_dvd.mpr)]
      ring

lemma LSeriesSummable_pow (k : ℕ) {z : ℂ} (hz : k + 1 < z.re) :
    LSeriesSummable (fun n : ℕ => (n : ℂ) ^ k) z :=
  LSeriesSummable_of_le_const_mul_rpow (x := k + 1) hz ⟨1, fun n _ => by
    rw [norm_pow, Complex.norm_natCast, one_mul, add_sub_cancel_right, Real.rpow_natCast]⟩

lemma LSeries_pow (k : ℕ) {z : ℂ} (hz : k + 1 < z.re) :
    LSeries (fun n : ℕ => (n : ℂ) ^ k) z = riemannZeta (z - k) := by
  rw [← LSeries_one_eq_riemannZeta (by simp; linarith), LSeries, LSeries]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Pi.one_apply]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have e : (n : ℂ) ^ z = (n : ℂ) ^ (z - k) * (n : ℂ) ^ k := by
      conv_lhs => rw [show z = z - k + k by ring]
      rw [Complex.cpow_add _ _ hn', Complex.cpow_natCast]
    have hc : (n : ℂ) ^ (z - k) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn]
    have hk : (n : ℂ) ^ k ≠ 0 := pow_ne_zero _ hn'
    rw [e]
    field_simp

lemma LSeriesSummable_evenPow (k : ℕ) {z : ℂ} (hz : k + 1 < z.re) : LSeriesSummable (evenPow k) z :=
  LSeriesSummable_of_le_const_mul_rpow (x := k + 1) hz ⟨1, fun n _ => by
    unfold evenPow
    split_ifs
    · rw [norm_pow, Complex.norm_natCast, one_mul, add_sub_cancel_right, Real.rpow_natCast]
    · rw [norm_zero]; positivity⟩

lemma LSeries_evenPow (k : ℕ) {z : ℂ} (hz : k + 1 < z.re) :
    LSeries (evenPow k) z = 2 ^ ((k : ℂ) - z) * riemannZeta (z - k) := by
  rw [← LSeries_pow k hz, LSeries, LSeries, ← tsum_mul_left,
    ← Function.Injective.tsum_eq (g := fun m : ℕ => 2 * m) (mul_right_injective₀ two_ne_zero)]
  · congr 1
    funext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have h2m : 2 * m ≠ 0 := mul_ne_zero two_ne_zero hm
      rw [LSeries.term_of_ne_zero h2m, LSeries.term_of_ne_zero hm, evenPow, ite_eq_left (dvd_mul_right 2 m),
        Nat.cast_mul, natCast_mul_natCast_cpow, Complex.cpow_sub _ _ (by norm_num), Complex.cpow_natCast]
      have h2 : ((2 : ℕ) : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff]
      have hmz : (m : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hm]
      push_cast at h2 ⊢
      field_simp
      ring
  · intro n hn
    by_cases h : 2 ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · exact absurd (by simp [LSeries.term_def, evenPow, h]) hn

lemma oddCube_eq : oddCube = (fun n : ℕ => (n : ℂ) ^ 3) - evenPow 3 := by
  funext n
  by_cases h : 2 ∣ n <;> simp [oddCube, evenPow, h]

/-- **`Σ f₈(n) n^{−z} = (1 − 2^{1−z} + 2^{4−2z}) ζ(z) ζ(z − 3)`** on `Re z > 4`. -/
lemma LSeries_f8 {z : ℂ} (hz : 4 < z.re) :
    LSeriesSummable f8 z ∧
      LSeries f8 z = (1 - 2 ^ (1 - z) + 2 ^ (4 - 2 * z)) * riemannZeta z * riemannZeta (z - 3) := by
  have h3 : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ 3) z := LSeriesSummable_pow 3 (by push_cast; linarith)
  have hone : LSeriesSummable 1 z := LSeriesSummable_one_iff.2 (by linarith)
  have hodd : LSeriesSummable oddCube z :=
    oddCube_eq ▸ h3.sub (LSeriesSummable_evenPow 3 (by push_cast; linarith))
  have hev : LSeriesSummable (evenPow 0) z := LSeriesSummable_evenPow 0 (by push_cast; linarith)
  have hA := h3.convolution hone
  have hB := (hodd.convolution hev).smul (2 : ℂ)
  refine ⟨f8_eq ▸ hA.sub hB, ?_⟩
  rw [f8_eq, LSeries_sub hA hB, LSeries_smul, LSeries_convolution' h3 hone, LSeries_convolution' hodd hev,
    oddCube_eq, LSeries_sub h3 (LSeriesSummable_evenPow 3 (by push_cast; linarith)),
    LSeries_pow 3 (by push_cast; linarith), LSeries_evenPow 3 (by push_cast; linarith),
    LSeries_evenPow 0 (by push_cast; linarith), LSeries_one_eq_riemannZeta (by linarith)]
  push_cast
  rw [sub_zero, show (1 : ℂ) - z = 1 + (0 - z) by ring, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one,
    show (4 : ℂ) - 2 * z = 1 + ((3 - z) + (0 - z)) by ring, Complex.cpow_add _ _ two_ne_zero,
    Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  ring

/-! ## `w = 8`: Jacobi's eight-square theorem -/

/-- **At `w = 8`, `Z` is a product of two zeta functions with the Euler factor at `2` changed**: on `Re s > 8`,
`Z(8, s) = 8 Γ_ℝ(s) (1 − 2^{1 − s/2} + 2^{4 − s}) ζ(s/2) ζ(s/2 − 3)`, by Jacobi's eight-square theorem. -/
theorem Z_eight {s : ℂ} (hs : 8 < s.re) :
    Z 8 eight_pos s =
      8 * Gammaℝ s * (1 - 2 ^ (1 - s / 2) + 2 ^ (4 - s)) * riemannZeta (s / 2) * riemannZeta (s / 2 - 3) := by
  set z := s / 2 with hz_def
  have hz : 4 < z.re := by rw [hz_def, div_ofNat_re]; linarith
  obtain ⟨hsig, hL⟩ := LSeries_f8 hz
  have hr8 : ∀ i ≠ 0, (r8 i : ℂ) = 16 * f8 i := fun i hi => by
    rw [f8]
    exact_mod_cast r8_eq hi
  -- the Dirichlet coefficients of `θ⁸ − 1`
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i : ℕ => if (i : ℝ) = 0 then 0 else (r8 i : ℂ) * rexp (-π * i * t))
      (thetaPow 8 t - 1) := by
    intro t ht
    have h := (hasSum_ofReal.2 (hasSum_theta_eight ht)).update 0 0
    convert h using 1
    · funext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp
      · simp [hi]
    · simp [thetaPow, r8_zero]
      ring
  have h_sum : Summable fun i : ℕ => ‖(r8 i : ℂ)‖ / (i : ℝ) ^ z.re := by
    refine (hsig.norm.mul_left 16).congr fun i => ?_
    rcases eq_or_ne i 0 with rfl | hi
    · simp [Real.zero_rpow (by linarith : z.re ≠ 0)]
    · rw [LSeries.norm_term_eq, ite_eq_right hi, hr8 i hi, norm_mul, mul_div_assoc]
      norm_num
  have hD := hasSum_mellin_pi_mul₀ (a := fun i : ℕ => (r8 i : ℂ)) (p := fun i : ℕ => (i : ℝ))
    (F := fun t => thetaPow 8 t - 1) (s := z) (fun i => Nat.cast_nonneg i) (by linarith) hF h_sum
  rw [(hasMellin 8 eight_pos (by simpa using hs)).2] at hD
  have hT : (fun i : ℕ => (π : ℂ) ^ (-z) * Gamma z * (r8 i : ℂ) / ((i : ℝ) : ℂ) ^ z) =
      fun i => (π : ℂ) ^ (-z) * Gamma z * (16 * LSeries.term f8 z i) := by
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; norm_num at hz
      simp [Complex.zero_cpow hz0]
    · rw [LSeries.term_of_ne_zero hi, hr8 i hi, ofReal_natCast]
      ring
  rw [hT] at hD
  have e := hD.unique ((hsig.LSeriesHasSum.mul_left 16).mul_left _)
  rw [hL, Gammaℝ_def, neg_div] at *
  rw [← hz_def, show (4 : ℂ) - s = 4 - 2 * z by rw [hz_def]; ring]
  linear_combination e / 2

/-! ## The continuation and the zeros off the line -/

/-- The entire factor `c₈(z) = 2^z (z − 1)(z − 3)(1 − 2^{1−z} + 2^{4−2z})/π²` between `Z(8, 2z)` and
`ζ̂(z)ζ̂(z − 3)`. -/
def c8 (z : ℂ) : ℂ := 2 ^ z * (z - 1) * (z - 3) * (1 - 2 ^ (1 - z) + 2 ^ (4 - 2 * z)) / π ^ 2

/-- On `Re z > 4`, from `Z_eight` and the Gamma factors. -/
lemma Z_eight_eq_of_re {z : ℂ} (hz : 4 < z.re) :
    Z 8 eight_pos (2 * z) = c8 z * (completedRiemannZeta z * completedRiemannZeta (z - 3)) := by
  have hs : 8 < (2 * z).re := by simp; linarith
  have hne : ∀ a : ℂ, a.re < z.re → z - a ≠ 0 := fun a ha h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [Z_eight hs, show 2 * z / 2 = z by ring, TwoVariableZetaPurity.completedRiemannZeta_eq (by linarith),
    TwoVariableZetaPurity.completedRiemannZeta_eq (by simp; linarith)]
  -- `Γ_ℝ(2z) = π^{−z}Γ(z)`, `Γ(z) = (z − 1)(z − 2)(z − 3)Γ(z − 3)`, `Γ_ℝ(z) = Γ_ℝ(z − 2)(z − 2)/(2π)` and
  -- `Γ_ℝ(z − 3)Γ_ℝ(z − 2) = Γ_ℂ(z − 3)`
  have hR : Gammaℝ (2 * z) = π ^ (-z) * ((z - 1) * ((z - 2) * ((z - 3) * Gamma (z - 3)))) := by
    have e1 := Complex.Gamma_add_one _ (hne 1 (by simp; linarith))
    have e2 := Complex.Gamma_add_one _ (hne 2 (by simp; linarith))
    have e3 := Complex.Gamma_add_one _ (hne 3 (by simp; linarith))
    rw [sub_add_cancel] at e1
    rw [show z - 2 + 1 = z - 1 by ring] at e2
    rw [show z - 3 + 1 = z - 2 by ring] at e3
    rw [Gammaℝ_def, show -(2 * z) / 2 = -z by ring, show 2 * z / 2 = z by ring, e1, e2, e3]
  have hA : Gammaℝ z = Gammaℝ (z - 2) * (z - 2) / 2 / π := by
    rw [← Gammaℝ_add_two (hne 2 (by simp; linarith)), sub_add_cancel]
  have hG : Gammaℝ (z - 3) * Gammaℝ (z - 2) = 2 * (2 * π) ^ (-(z - 3)) * Gamma (z - 3) := by
    rw [← Gammaℂ_def, ← Gammaℝ_mul_Gammaℝ_add_one, show z - 3 + 1 = z - 2 by ring]
  have h2π : (2 * π : ℂ) ^ (-(z - 3)) = 2 ^ (3 - z) * π ^ (3 - z) := by
    rw [show -(z - 3) = 3 - z by ring, show (2 * π : ℂ) = ((2 : ℝ) : ℂ) * (π : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
    push_cast
    ring
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have e2 : (2 : ℂ) ^ (3 - z) = 8 / 2 ^ z := by
    rw [cpow_sub _ _ two_ne_zero, show (3 : ℂ) = (3 : ℕ) by norm_num, cpow_natCast]
    norm_num
  have eπ : (π : ℂ) ^ (3 - z) = π ^ 3 / π ^ z := by
    rw [cpow_sub _ _ hπ0, show (3 : ℂ) = (3 : ℕ) by norm_num, cpow_natCast]
  have eπ' : (π : ℂ) ^ (-z) = 1 / π ^ z := by rw [cpow_neg, one_div]
  have h2z : (2 : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
  have hπz : (π : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hπ0)
  rw [hR, hA]
  calc 8 * (π ^ (-z) * ((z - 1) * ((z - 2) * ((z - 3) * Gamma (z - 3))))) *
          (1 - 2 ^ (1 - z) + 2 ^ (4 - 2 * z)) * riemannZeta z * riemannZeta (z - 3)
      = c8 z * ((z - 2) / 2 / π * (2 * (2 * π) ^ (-(z - 3)) * Gamma (z - 3))) * riemannZeta z *
          riemannZeta (z - 3) := by
        rw [h2π, e2, eπ, eπ']
        unfold c8
        field_simp
    _ = c8 z * (Gammaℝ (z - 2) * (z - 2) / 2 / π * riemannZeta z * (Gammaℝ (z - 3) * riemannZeta (z - 3))) := by
        rw [← hG]
        ring

lemma differentiableAt_c8 (z : ℂ) : DifferentiableAt ℂ c8 z := by
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) z := differentiableAt_id.const_cpow (Or.inl two_ne_zero)
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - z)) z :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)
  have h4 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (4 - 2 * z)) z :=
    ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)).const_cpow (Or.inl two_ne_zero)
  exact ((((h2.mul (differentiableAt_id.sub (differentiableAt_const _))).mul
    (differentiableAt_id.sub (differentiableAt_const _))).mul (((differentiableAt_const _).sub h1).add h4)).div_const _)

/-- **`Z(8, 2z) = c₈(z)·ζ̂(z)ζ̂(z − 3)` off `z = 0, 1, 3, 4`**, with
`c₈(z) = 2^z (z − 1)(z − 3)(1 − 2^{1−z} + 2^{4−2z})/π²` entire: the continuation of `Z_eight` to the plane, by the
identity theorem. -/
theorem Z_eight_eq {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (h3 : z ≠ 3) (h4 : z ≠ 4) :
    Z 8 eight_pos (2 * z) = c8 z * (completedRiemannZeta z * completedRiemannZeta (z - 3)) := by
  set U : Set ℂ := ({0, 1, 3, 4} : Set ℂ)ᶜ with hU
  have hfin : ({0, 1, 3, 4} : Set ℂ).Finite := by simp
  have hUo : IsOpen U := hfin.isClosed.isOpen_compl
  have hUc : IsPreconnected U :=
    (hfin.countable.isPathConnected_compl_of_one_lt_rank (by rw [rank_real_complex]; norm_num)).isConnected
      |>.isPreconnected
  have hf : DifferentiableOn ℂ (fun z => Z 8 eight_pos (2 * z)) U := by
    intro z hz
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    have hd := differentiableAt 8 eight_pos (s := 2 * z) (mul_ne_zero two_ne_zero hz.1)
      (fun h => hz.2.2.2 (by push_cast at h; linear_combination h / 2))
    exact (hd.comp z (differentiableAt_id.const_mul (2 : ℂ))).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => c8 z * (completedRiemannZeta z * completedRiemannZeta (z - 3))) U := by
    intro z hz
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    have hz1 : DifferentiableAt ℂ completedRiemannZeta z := differentiableAt_completedZeta hz.1 hz.2.1
    have hz2 : DifferentiableAt ℂ (fun z => completedRiemannZeta (z - 3)) z :=
      (differentiableAt_completedZeta (sub_ne_zero.2 hz.2.2.1) (fun h => hz.2.2.2 (by linear_combination h))).comp z
        (differentiableAt_id.sub (differentiableAt_const _))
    exact ((differentiableAt_c8 z).mul (hz1.mul hz2)).differentiableWithinAt
  have heq : (fun z => Z 8 eight_pos (2 * z)) =ᶠ[𝓝 5]
      fun z => c8 z * (completedRiemannZeta z * completedRiemannZeta (z - 3)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (4 : ℝ) < (5 : ℂ).re by norm_num)] with z hz
    exact Z_eight_eq_of_re hz
  have h5 : (5 : ℂ) ∈ U := by
    simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    norm_num
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hUc h5 heq
    (by simp only [hU, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨h0, h1, h3, h4⟩)

/-- **The Riemann hypothesis fails for `Z(8, ·)`, whatever the truth of RH**: it vanishes at `2ρ` for every
nontrivial zero `ρ` of `ζ`, off its line `Re s = 4`. -/
theorem exists_zero_re_ne_four : ∃ s : ℂ, Z 8 eight_pos s = 0 ∧ s.re ≠ 4 := by
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  have h0 := (nontrivial_zZF q).re_pos
  have h1 := (nontrivial_zZF q).re_lt_one
  set ρ := zetaZeroFamily q
  have hne : ∀ a : ℝ, 1 ≤ a → ρ ≠ a := fun a ha h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  refine ⟨2 * ρ, ?_, ?_⟩
  · rw [Z_eight_eq (fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0)
      (by exact_mod_cast hne 1 le_rfl) (by exact_mod_cast hne 3 (by norm_num))
      (by exact_mod_cast hne 4 (by norm_num)), PurityRational.completedRiemannZeta_eq_zero (nontrivial_zZF q),
      zero_mul, mul_zero]
  · have e : (2 * ρ).re = 2 * ρ.re := by simp
    rw [e]
    linarith

end TwoVariableZetaEight

#print axioms TwoVariableZetaEight.LSeries_f8
#print axioms TwoVariableZetaEight.Z_eight
#print axioms TwoVariableZetaEight.Z_eight_eq
#print axioms TwoVariableZetaEight.exists_zero_re_ne_four
