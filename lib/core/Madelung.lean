/-
# The Madelung constant of the square lattice

Plain statement. Put the charge `(−1)^{m+k}` at each point `(m, k) ≠ 0` of `ℤ²`, as in a plane of rock salt. Grouped by
the shells `m² + k² = n`, on which `(−1)^{m+k} = (−1)^n`, the potential at the origin is the Dirichlet series
`S(s) = Σ_{n ≥ 1} (−1)^n r₂(n) n^{−s}` at `s = 1/2`, where `r₂(n) = GlobalTeeth.R n` counts the points of `ℤ²` on the
shell. For `Re s > 1`,

  `S(s) = −4(1 − 2^{1−s}) ζ(s) L(s, χ₋₄)`   (`lseries_coeff`),

and the right side is holomorphic on `ℂ ∖ {1}` (`differentiableOn_rhs`), so it is the continuation of `S` there. Its
value at `s = 1/2`, `−4(1 − √2) ζ(1/2) L(1/2, χ₋₄) ≈ −1.6155`, is minus the Madelung constant of the square lattice:
the electrostatic energy of one ion of a two-dimensional ionic crystal, in units of `e²/a`, as the continuation defines
it. The numerical value is a remark, not a theorem.

The proof: Jacobi's `r₂(n) = 4 Σ_{d ∣ n} χ₋₄(d)` (`GlobalTeeth.two_sq_count`) makes `Σ r₂(n) n^{−s} = 4 ζ(s) L(s, χ₋₄)`
(`AngularFamily.member_zero_eq`), and `r₂(2m) = r₂(m)` (`GlobalTeeth.R_two_mul`) makes the even terms `2^{−s}` times the
whole sum. The identity is classical; no source was read for this file.
-/
import AngularFamily

open Complex GlobalTeeth AngularFamily
open scoped LSeries.notation

noncomputable section

namespace Madelung

/-- The alternating sum of the square lattice, shell by shell: `(−1)^n r₂(n)`. -/
def coeff (n : ℕ) : ℂ := (-1) ^ n * (R n : ℂ)

lemma R_eq (n : ℕ) : (R n : ℂ) = 4 * angularCoeff 0 n := by
  simp only [angularCoeff, mul_zero, pow_zero, div_one, Finset.sum_const, nsmul_eq_mul, mul_one, R]
  ring

lemma summable_R {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n ↦ (R n : ℂ)) s := by
  have hc := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ4C hs).convolution
    (LSeriesSummable_one_iff.mpr hs)
  have ha : LSeriesSummable (angularCoeff 0) s :=
    (LSeriesSummable_congr s fun {n} hn ↦ coeff_eq_convolution hn).2 hc
  have h4 : (fun n ↦ (R n : ℂ)) = (4 : ℂ) • angularCoeff 0 := funext fun n ↦ R_eq n
  rw [h4]
  exact ha.smul 4

/-- `Σ r₂(n) n^{−s} = 4 ζ(s) L(s, χ₋₄)` on `Re s > 1`. -/
lemma lseries_R {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (R n : ℂ)) s = 4 * (riemannZeta s * DirichletCharacter.LFunction χ4C s) := by
  have h4 : (fun n ↦ (R n : ℂ)) = (4 : ℂ) • angularCoeff 0 := funext fun n ↦ R_eq n
  rw [h4, LSeries_smul]
  exact congrArg (4 * ·) (member_zero_eq hs)

/-- **The alternating lattice sum of the square lattice** on `Re s > 1`:
`Σ_{n ≥ 1} (−1)^n r₂(n) n^{−s} = −4(1 − 2^{1−s}) ζ(s) L(s, χ₋₄)`. -/
theorem lseries_coeff {s : ℂ} (hs : 1 < s.re) :
    LSeries coeff s = -4 * (1 - 2 ^ (1 - s)) * riemannZeta s * DirichletCharacter.LFunction χ4C s := by
  set t : ℕ → ℂ := LSeries.term (fun n ↦ (R n : ℂ)) s with ht
  have hR : Summable t := summable_R hs
  have heven : ∀ k : ℕ, t (2 * k) = 2 ^ (-s) * t k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [ht]
    · rw [ht, LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega), R_two_mul, Nat.cast_mul,
        natCast_mul_natCast_cpow, cpow_neg]
      have h2 : (2 : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
      have hk' : (k : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hk.ne'))
      push_cast
      field_simp
  have hceven : ∀ k : ℕ, LSeries.term coeff s (2 * k) = 2 ^ (-s) * t k := by
    intro k
    rw [← heven k]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [ht]
    · rw [ht, LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega), coeff, pow_mul]
      simp
  have hcodd : ∀ k : ℕ, LSeries.term coeff s (2 * k + 1) = -t (2 * k + 1) := by
    intro k
    rw [ht, LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega), coeff, pow_succ, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul, neg_mul, neg_div]
  have hse : Summable fun k ↦ t (2 * k) := hR.comp_injective fun a b h ↦ by omega
  have hso : Summable fun k ↦ t (2 * k + 1) := hR.comp_injective fun a b h ↦ by omega
  have hsplitR : ∑' k, t (2 * k) + ∑' k, t (2 * k + 1) = LSeries (fun n ↦ (R n : ℂ)) s :=
    tsum_even_add_odd hse hso
  have hsplitC : ∑' k, LSeries.term coeff s (2 * k) + ∑' k, LSeries.term coeff s (2 * k + 1) = LSeries coeff s :=
    tsum_even_add_odd ((hR.mul_left (2 ^ (-s))).congr fun k ↦ (hceven k).symm)
      (hso.neg.congr fun k ↦ (hcodd k).symm)
  have hL : ∑' k, t k = LSeries (fun n ↦ (R n : ℂ)) s := rfl
  rw [tsum_congr heven, tsum_mul_left, hL] at hsplitR
  rw [tsum_congr hceven, tsum_congr hcodd, tsum_mul_left, tsum_neg, hL] at hsplitC
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [cpow_sub _ _ two_ne_zero, cpow_one, cpow_neg, div_eq_mul_inv]
  rw [← hsplitC, h2]
  linear_combination (-1 : ℂ) * hsplitR + (2 * 2 ^ (-s) - 1) * lseries_R hs

lemma χ4C_ne_one : χ4C ≠ 1 := by
  intro h
  have h3 : χ4C ((3 : ℕ) : ZMod 4) = -1 := by
    rw [χ4C_apply, ZMod.χ₄_nat_three_mod_four (by norm_num)]
    norm_num
  have hu : IsUnit ((3 : ℕ) : ZMod 4) := (ZMod.isUnit_iff_coprime 3 4).2 (by norm_num)
  rw [h, MulChar.one_apply hu] at h3
  norm_num at h3

/-- **The continuation**: the right side of `lseries_coeff` is holomorphic on `ℂ ∖ {1}`. -/
theorem differentiableOn_rhs :
    DifferentiableOn ℂ (fun s ↦ -4 * (1 - 2 ^ (1 - s)) * riemannZeta s * DirichletCharacter.LFunction χ4C s)
      {1}ᶜ := by
  intro s hs
  have hz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have hL : DifferentiableAt ℂ (DirichletCharacter.LFunction χ4C) s :=
    DirichletCharacter.differentiable_LFunction χ4C_ne_one s
  have hc : DifferentiableAt ℂ (fun s : ℂ ↦ (2 : ℂ) ^ (1 - s)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)
  exact ((((differentiableAt_const _).mul ((differentiableAt_const _).sub hc)).mul hz).mul hL).differentiableWithinAt

end Madelung
