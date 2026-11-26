import WeylZForm
import GramVolume

/-!
# The slope of the standard lattice `Δ_std`: a lower bound for `det Gzb`

Part VI of the exact slope bound (F) (S1–S4), for an antitone weight `λ` of shape `ν = natW λ`, with
`|ν| = Σ_{ρ,b} ν_{ρ,b}`, `r = |ZIdx| = dim ∇(ν)` (`card_ZIdx`) and `n` the rank. Write `d! = ∏_p d_p!` (`fact`) for a
monomial `d`, `κ = ⟨hw_ν, hw_ν⟩` (`HermForms.kappa`), `Gzb = (⟨zb_i, zb_j⟩/κ)` for the Gram matrix of the `ℤ`-basis
`zb` of `∇_ℤ`, and `Γ = Gzb⁻¹` (`WeylZForm`). The coordinates of `Δ_std` are the dual basis, of Gram matrix `Γ`, so
`μ_arch(Δ_std) = −log det Γ/r`; we show `log det Γ ≤ 3·r·|ν|·log n`, that is `μ_arch(Δ_std) ≥ −3|ν| log n`
(`log_det_Γ_le`).

**Monomial factorials** (S2). A monomial `d` of a polynomial in `∇(ν)` has column weight `ν`: column `(ρ, b)` has
degree `ν_{ρ,b}`, spread over the `n` rows (`sum_col_of_mem_nabla`). So `d! ≤ ∏_{ρ,b} ν_{ρ,b}!` (`fact_le_of_col`, as
`∏_i a_i! ∣ (Σ_i a_i)!`) and `∏_{ρ,b} ν_{ρ,b}! ≤ d!·n^{|ν|}` (`prod_le_fact_mul_of_col`): a multinomial coefficient
with `n` parts of total `N` is at most `n^N`, one term of `(1 + ⋯ + 1)^N` (`factorial_sum_le`). For the monomials of
the bideterminants this is `prod_div_le_fact`.

**The bound on `κ`** (S3). `κ = Σ_d hw_d²·d! ≤ ∏ν!·Σ_d hw_d² ≤ ∏ν!·ℓ¹(hw)²`, with `ℓ¹(P) = Σ_d |P_d|` (`l1norm`).
The norm `ℓ¹` is subadditive and submultiplicative (`l1norm_mul_le`, monomial by monomial), a minor of size `s + 1`
has `ℓ¹ ≤ (s+1)! ≤ n^{s+1}` (`l1norm_minor_le`: it is a sum of `(s+1)!` signed products of variables), and `hw_ν` is
a product of `mult_{ρ,s}` leading minors of size `s + 1`, with `Σ_s (s+1)·mult_{ρ,s} = |ν_ρ|` (`sum_succ_mul_mult`,
from `sum_mult`). So `ℓ¹(hw) ≤ n^{|ν|}` (`l1norm_hw_le`) and `κ ≤ ∏ν!·n^{2|ν|}` (`kappa_le`). The hook formula is not
needed.

**`det Gzb` from below** (S1, `det_Gzb_ge`). Let `S` be the set of monomials of the bideterminants (`bidetMonos`): it
contains the supports of the `zb`. Let `E` be the integer `r × S` matrix of the coefficients of the `zb`, and
`D = diag(d!)`, so that `κ·Gzb = E·D·Eᵀ`. If `0 ≤ m ≤ d!` on `S`, then `E·D·Eᵀ − m·E·Eᵀ = E·(D − m)·Eᵀ` is positive
semidefinite, and `det` is monotone in the Loewner order (`GramVolume.det_le_det`): `κ^r·det Gzb ≥ m^r·det(E·Eᵀ)`.
Finally `E·Eᵀ` is a positive definite integer matrix (the `zb` are independent over `ℝ`, `linearIndependent_zbK`), so
`det(E·Eᵀ)` is a positive integer, at least `1`. Cauchy–Binet is not needed.

**Assembly** (S4, `log_det_Γ_le`). With `m = ∏ν!/n^{|ν|}` (S2) and S3, `det Gzb ≥ (m/κ)^r ≥ n^{−3r|ν|}`, so
`log det Γ = −log det Gzb ≤ 3·r·|ν|·log n`. The degenerate cases need no separate treatment: for `n = 0` also
`|ν| = 0` (`pow_sum_natW_pos`), and `r = 0` gives empty determinants.
-/

namespace WeylFock

open MvPolynomial HermForms Finset

open scoped Matrix Nat

noncomputable section

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ}

/-! ## S2: factorials of the monomials of column weight `ν` -/

section Factorial

/-- The multinomial bound: `(Σ_a f_a)! ≤ (∏_a f_a!)·n^{Σ_a f_a}` for `f : Fin n → ℕ`. The multinomial coefficient is
one term of the expansion of `n^{Σ f} = (1 + ⋯ + 1)^{Σ f}`. -/
theorem factorial_sum_le (f : Fin n → ℕ) : (∑ a, f a)! ≤ (∏ a, (f a)!) * n ^ ∑ a, f a := by
  rw [← Nat.multinomial_spec]
  refine Nat.mul_le_mul_left _ ?_
  have h := sum_pow_eq_sum_piAntidiag univ (fun _ : Fin n => (1 : ℕ)) (∑ a, f a)
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.cast_id] at h
  rw [h]
  exact single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
    (mem_piAntidiag.2 ⟨rfl, by simp⟩)

omit [DecidableEq Φ] in
/-- `d! = ∏_{ρ,b} ∏_a d_{ρ,a,b}!`, column by column. -/
theorem prod_factorial_eq (d : Φ × Fin n × Fin n →₀ ℕ) :
    ∏ p, (d p)! = ∏ ρ, ∏ b, ∏ a, (d (ρ, a, b))! := by
  simp only [Fintype.prod_prod_type]
  exact prod_congr rfl fun ρ _ => prod_comm

/-- A monomial of a polynomial in `∇(ν)` has column weight `ν`: `Σ_a d_{ρ,a,b} = ν_{ρ,b}`. -/
theorem sum_col_of_mem_nabla {ν : Φ → Fin n → ℕ} {P : Pol Φ n ℚ} (hP : P ∈ nabla ℚ ν)
    {d : Φ × Fin n × Fin n →₀ ℕ} (hd : d ∈ P.support) (ρ : Φ) (b : Fin n) : ∑ a, d (ρ, a, b) = ν ρ b := by
  rw [← weight_colW_apply, (mem_nabla_iff.1 hP).1 (mem_support_iff.1 hd)]

omit [DecidableEq Φ] in
/-- **S3, per monomial.** A monomial of column weight `ν` has `d! ≤ ∏_{ρ,b} ν_{ρ,b}!`. -/
theorem fact_le_of_col {ν : Φ → Fin n → ℕ} {d : Φ × Fin n × Fin n →₀ ℕ}
    (hd : ∀ ρ b, ∑ a, d (ρ, a, b) = ν ρ b) : ∏ p, (d p)! ≤ ∏ ρ, ∏ b, (ν ρ b)! := by
  rw [prod_factorial_eq]
  refine prod_le_prod fun ρ _ => prod_le_prod fun b _ => ?_
  rw [← hd ρ b]
  exact Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum _ _)

omit [DecidableEq Φ] in
/-- **S2, per monomial.** A monomial of column weight `ν` has `∏_{ρ,b} ν_{ρ,b}! ≤ d!·n^{|ν|}`: column `(ρ, b)` has
degree `ν_{ρ,b}` spread over `n` rows (`factorial_sum_le`). -/
theorem prod_le_fact_mul_of_col {ν : Φ → Fin n → ℕ} {d : Φ × Fin n × Fin n →₀ ℕ}
    (hd : ∀ ρ b, ∑ a, d (ρ, a, b) = ν ρ b) :
    ∏ ρ, ∏ b, (ν ρ b)! ≤ (∏ p, (d p)!) * n ^ ∑ ρ, ∑ b, ν ρ b := by
  rw [prod_factorial_eq, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_le_prod fun ρ _ => ?_
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_le_prod fun b _ => ?_
  rw [← hd ρ b]
  exact factorial_sum_le _

end Factorial

/-! ## S3: the `ℓ¹` norm and the bound on `κ` -/

section L1

/-- The `ℓ¹` norm `Σ_d |P_d|` of a rational polynomial. -/
def l1norm (P : Pol Φ n ℚ) : ℚ := ∑ d ∈ P.support, |P.coeff d|

omit [Fintype Φ] [DecidableEq Φ] in
/-- The `ℓ¹` norm, summed over any finite set containing the support. -/
theorem l1norm_eq_sum {P : Pol Φ n ℚ} {S : Finset (Φ × Fin n × Fin n →₀ ℕ)} (hS : P.support ⊆ S) :
    l1norm P = ∑ d ∈ S, |P.coeff d| :=
  sum_subset hS fun d _ hd => by rw [notMem_support_iff.1 hd, abs_zero]

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹ ≥ 0`. -/
theorem l1norm_nonneg (P : Pol Φ n ℚ) : 0 ≤ l1norm P := sum_nonneg fun _ _ => abs_nonneg _

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹(c·x^d) = |c|`. -/
theorem l1norm_monomial (d : Φ × Fin n × Fin n →₀ ℕ) (c : ℚ) : l1norm (monomial d c) = |c| := by
  classical
  rw [l1norm_eq_sum support_monomial_subset, sum_singleton]
  simp

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹` is subadditive. -/
theorem l1norm_add_le (P Q : Pol Φ n ℚ) : l1norm (P + Q) ≤ l1norm P + l1norm Q := by
  classical
  rw [l1norm_eq_sum support_add, l1norm_eq_sum subset_union_left, l1norm_eq_sum subset_union_right,
    ← sum_add_distrib]
  exact sum_le_sum fun d _ => by rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact abs_add_le _ _

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹` of a finite sum. -/
theorem l1norm_sum_le {ι : Type*} (s : Finset ι) (P : ι → Pol Φ n ℚ) :
    l1norm (∑ i ∈ s, P i) ≤ ∑ i ∈ s, l1norm (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1norm]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (l1norm_add_le _ _).trans (add_le_add le_rfl ih)

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹` is submultiplicative: expand both factors into monomials. -/
theorem l1norm_mul_le (P Q : Pol Φ n ℚ) : l1norm (P * Q) ≤ l1norm P * l1norm Q := by
  have e : P * Q = ∑ a ∈ P.support, ∑ b ∈ Q.support, monomial (a + b) (P.coeff a * Q.coeff b) := by
    conv_lhs => rw [P.as_sum, Q.as_sum, sum_mul_sum]
    simp only [monomial_mul_monomial]
  calc l1norm (P * Q) ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support, |P.coeff a| * |Q.coeff b| := by
        rw [e]
        refine (l1norm_sum_le _ _).trans (sum_le_sum fun a _ => (l1norm_sum_le _ _).trans (le_of_eq ?_))
        exact sum_congr rfl fun b _ => by rw [l1norm_monomial, abs_mul]
    _ = l1norm P * l1norm Q := by rw [l1norm, l1norm, sum_mul_sum]

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹(1) = 1`. -/
theorem l1norm_one : l1norm (1 : Pol Φ n ℚ) = 1 := by
  rw [← C_1, C_apply, l1norm_monomial, abs_one]

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹` of a finite product. -/
theorem l1norm_prod_le {ι : Type*} (s : Finset ι) (P : ι → Pol Φ n ℚ) :
    l1norm (∏ i ∈ s, P i) ≤ ∏ i ∈ s, l1norm (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1norm_one]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (l1norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (l1norm_nonneg _))

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹` of a power. -/
theorem l1norm_pow_le (P : Pol Φ n ℚ) (k : ℕ) : l1norm (P ^ k) ≤ l1norm P ^ k := by
  simpa using l1norm_prod_le (range k) fun _ => P

omit [Fintype Φ] [DecidableEq Φ] in
/-- `ℓ¹(z·P) = |z|·ℓ¹(P)` for `z ∈ ℤ`. -/
theorem l1norm_zsmul (z : ℤ) (P : Pol Φ n ℚ) : l1norm (z • P) = |(z : ℚ)| * l1norm P := by
  rw [l1norm_eq_sum support_smul, l1norm, mul_sum]
  exact sum_congr rfl fun d _ => by rw [coeff_smul, zsmul_eq_mul, abs_mul]

omit [Fintype Φ] [DecidableEq Φ] in
/-- A minor of size `s + 1` has `ℓ¹ ≤ (s+1)!`: it is a sum of `(s+1)!` signed products of variables. -/
theorem l1norm_minor_le (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) :
    l1norm (minor τ s I : Pol Φ n ℚ) ≤ (s + 1)! := by
  rw [minor, Matrix.det_apply]
  refine (l1norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _σ : Equiv.Perm (Fin (s + 1)), (1 : ℚ) := sum_le_sum fun σ _ => ?_
    _ = (s + 1)! := by simp [Fintype.card_perm]
  rw [Units.smul_def, l1norm_zsmul, ← Int.cast_abs, Int.isUnit_iff_abs_eq.1 (Equiv.Perm.sign σ).isUnit,
    Int.cast_one, one_mul]
  refine (l1norm_prod_le _ _).trans (le_of_eq ?_)
  refine prod_eq_one fun i _ => ?_
  simp only [Matrix.submatrix_apply, xMat, Matrix.of_apply]
  exact (l1norm_monomial _ 1).trans abs_one

/-- `Σ_s (s+1)·mult_{τ,s} = |ν_τ|`: column `b` meets `ν_b` leading minors (`sum_mult`). -/
theorem sum_succ_mul_mult {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) (τ : Φ) :
    ∑ s : Fin n, ((s : ℕ) + 1) * mult (ν τ) s = ∑ b, ν τ b := by
  have h : ∀ b, ν τ b = ∑ s : Fin n, mult (ν τ) s * if (b : ℕ) ≤ s then 1 else 0 := fun b => by
    conv_lhs => rw [← sum_mult hν]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single τ (fun σ _ h => by simp [Ne.symm h]) (by simp)]
    simp only [↓reduceIte]
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  have hI : ({b | (b : ℕ) ≤ s} : Finset (Fin n)) = Iic s := by
    ext b
    simp
  rw [← mul_sum, sum_boole, Nat.cast_id, hI, Fin.card_Iic, mul_comm]

/-- `ℓ¹(hw_ν) ≤ n^{|ν|}`: `hw_ν` is a product of `mult_{τ,s}` minors of size `s + 1`, each of `ℓ¹ ≤ n^{s+1}`. -/
theorem l1norm_hw_le {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    l1norm (hw ℚ ν) ≤ (n : ℚ) ^ ∑ ρ, ∑ b, ν ρ b := by
  rw [hw]
  refine (l1norm_prod_le _ _).trans ?_
  calc _ ≤ ∏ τ, ∏ s : Fin n, ((n : ℚ) ^ ((s : ℕ) + 1)) ^ mult (ν τ) s :=
        prod_le_prod₀ (fun _ _ => l1norm_nonneg _) fun τ _ => (l1norm_prod_le _ _).trans
          (prod_le_prod₀ (fun _ _ => l1norm_nonneg _) fun s _ => (l1norm_pow_le _ _).trans
            (pow_le_pow_left₀ (l1norm_nonneg _) ((l1norm_minor_le τ s _).trans (by
              exact_mod_cast (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left s.isLt _))) _))
    _ = _ := by
      simp only [← pow_mul, prod_pow_eq_pow_sum, sum_succ_mul_mult hν]

/-- **S3.** `κ ≤ (∏_{ρ,b} ν_{ρ,b}!)·n^{2|ν|}`: `κ = Σ_d hw_d²·d!` with `d! ≤ ∏ν!` (`fact_le_of_col`), and
`Σ_d hw_d² ≤ ℓ¹(hw)² ≤ n^{2|ν|}` (`l1norm_hw_le`). -/
theorem kappa_le (lam : Φ → Fin n → ℤ) (hlam : ∀ ρ, Antitone (lam ρ)) :
    kappa lam ≤ (∏ ρ, ∏ b, ((natW (lam ρ) b)! : ℚ)) * ((n : ℚ) ^ ∑ ρ, ∑ b, natW (lam ρ) b) ^ 2 := by
  have hν : ∀ σ, Antitone (natW (lam σ)) := fun σ => natW_antitone (hlam σ)
  set P := hw ℚ fun ρ => natW (lam ρ)
  set F := ∏ ρ, ∏ b, ((natW (lam ρ) b)! : ℚ)
  have hl := l1norm_hw_le hν
  have hF : ∀ d ∈ P.support, (fact d : ℚ) ≤ F := fun d hd => by
    have := fact_le_of_col (sum_col_of_mem_nabla (hw_mem_nabla hν) hd)
    simp only [fact, F]
    exact_mod_cast this
  rw [kappa, fock_eq_sum_right (subset_refl _)]
  calc ∑ d ∈ P.support, P.coeff d * P.coeff d * fact d ≤ ∑ d ∈ P.support, |P.coeff d| * (l1norm P * F) :=
        sum_le_sum fun d hd => by
          rw [← abs_mul_abs_self, mul_assoc]
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (hF d hd) (prod_nonneg fun _ _ => by positivity)
            (l1norm_nonneg _)) (abs_nonneg _)
          exact single_le_sum (f := fun d => |P.coeff d|) (fun _ _ => abs_nonneg _) hd
    _ = l1norm P * (l1norm P * F) := by rw [← sum_mul, l1norm]
    _ ≤ (n : ℚ) ^ (∑ ρ, ∑ b, natW (lam ρ) b) * ((n : ℚ) ^ (∑ ρ, ∑ b, natW (lam ρ) b) * F) := by
        have hF0 : 0 ≤ F := prod_nonneg fun _ _ => prod_nonneg fun _ _ => by positivity
        exact mul_le_mul hl (mul_le_mul_of_nonneg_right hl hF0) (mul_nonneg (l1norm_nonneg _) hF0)
          ((l1norm_nonneg _).trans hl)
    _ = _ := by ring

end L1

/-! ## S1: `det Gzb` from below, and S4 -/

section Gram

variable (lam : Φ → Fin n → ℤ)

omit [DecidableEq Φ] in
/-- `n^{|ν|} > 0` (for `n = 0`, `|ν| = 0`). -/
theorem pow_sum_natW_pos : (0 : ℝ) < (n : ℝ) ^ ∑ ρ, ∑ b, natW (lam ρ) b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact pow_pos (Nat.cast_pos.2 hn) _

/-- **S2.** Every monomial `d` of a bideterminant of shape `ν = natW λ` has `∏_{ρ,b} ν_{ρ,b}!/n^{|ν|} ≤ d!`
(`prod_le_fact_mul_of_col`: the bideterminant lies in `∇(ν)`, so `d` has column weight `ν`). -/
theorem prod_div_le_fact (hlam : ∀ ρ, Antitone (lam ρ)) {d : Φ × Fin n × Fin n →₀ ℕ}
    (hd : d ∈ bidetMonos ℚ fun ρ => natW (lam ρ)) :
    (∏ ρ, ∏ b, ((natW (lam ρ) b)! : ℝ)) / (n : ℝ) ^ (∑ ρ, ∑ b, natW (lam ρ) b) ≤ fact d := by
  obtain ⟨rows, -, hd⟩ := mem_biUnion.1 hd
  have h := prod_le_fact_mul_of_col
    (sum_col_of_mem_nabla (bidet_mem_nabla (fun σ => natW_antitone (hlam σ)) rows) hd)
  rw [div_le_iff₀ (pow_sum_natW_pos lam)]
  simp only [fact]
  exact_mod_cast h

/-- **S1.** If `0 ≤ m ≤ d!` for every monomial `d` of a bideterminant, then `m^r ≤ κ^r·det Gzb`, `r = |ZIdx|`.
Write `κ·Gzb = E·D·Eᵀ`, with `E` the integer coefficient matrix of the `zb` on these monomials and `D = diag(d!)`;
then `E·D·Eᵀ − m·E·Eᵀ = E·(D − m)·Eᵀ` is positive semidefinite, so `det(E·D·Eᵀ) ≥ m^r·det(E·Eᵀ)`
(`GramVolume.det_le_det`), and `det(E·Eᵀ) ≥ 1` is a positive integer: `E·Eᵀ` is positive definite, as the `zb` are
independent over `ℝ` (`linearIndependent_zbK`). -/
theorem det_Gzb_ge (hlam : ∀ ρ, Antitone (lam ρ)) {m : ℝ} (hm : 0 ≤ m)
    (hmS : ∀ d ∈ bidetMonos ℚ (fun ρ => natW (lam ρ)), m ≤ fact d) :
    m ^ Fintype.card (ZIdx lam) ≤
      (kappa lam : ℝ) ^ Fintype.card (ZIdx lam) * ((Gzb lam).map (algebraMap ℚ ℝ)).det := by
  classical
  set S := bidetMonos ℚ fun ρ => natW (lam ρ)
  have hsupp : ∀ j, (zb lam j).support ⊆ S := fun j d hd =>
    mem_bidetMonos (fun σ => natW_antitone (hlam σ)) (zb_mem_nabla hlam j) (mem_support_iff.1 hd)
  choose z hz using fun i (d : S) => RingHom.mem_range.1 (coeff_zb_mem lam i d)
  set Z : Matrix (ZIdx lam) S ℤ := Matrix.of z
  set E : Matrix (ZIdx lam) S ℝ := Z.map (Int.castRingHom ℝ)
  set D : Matrix S S ℝ := Matrix.diagonal fun d => (fact (d : Φ × Fin n × Fin n →₀ ℕ) : ℝ)
  have hEt : Eᴴ = Eᵀ := Matrix.conjTranspose_eq_transpose_of_trivial E
  -- `κ·Gzb = E·D·Eᵀ`
  have hG : (kappa lam : ℝ) • (Gzb lam).map (algebraMap ℚ ℝ) = E * D * Eᵀ := by
    ext i j
    have hf : fockWith (RingHom.id ℚ) (zb lam i) (zb lam j) =
        ∑ d : S, (z i d : ℚ) * z j d * fact (d : Φ × Fin n × Fin n →₀ ℕ) := by
      rw [fock_eq_sum_right (hsupp j), ← sum_coe_sort S]
      exact sum_congr rfl fun d _ => by rw [← hz i d, ← hz j d]; rfl
    have hκ : (kappa lam : ℝ) ≠ 0 := by exact_mod_cast (kappa_pos lam).ne'
    rw [Matrix.smul_apply, Matrix.map_apply, Gzb, smul_eq_mul, map_div₀, hf, eq_ratCast, eq_ratCast,
      mul_div_cancel₀ _ hκ, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Rat.cast_sum]
    exact sum_congr rfl fun x _ => by simp [E, D, Z, fact]; ring
  -- `det(E·Eᵀ) ≥ 1`
  have hker : ∀ v : ZIdx lam → ℝ, v ᵥ* E = 0 → v = 0 := fun v hv => by
    have hP : ∑ i, v i • zbK ℝ lam i = 0 := by
      ext d
      rw [coeff_sum]
      show _ = (0 : ℝ)
      by_cases hd : d ∈ S
      · have := congrFun hv ⟨d, hd⟩
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
        rw [← this]
        refine sum_congr rfl fun i _ => ?_
        simp [zbK, coeff_map, E, Z, ← hz i ⟨d, hd⟩]
      · exact sum_eq_zero fun i _ => by
          rw [coeff_smul, zbK, coeff_map, notMem_support_iff.1 fun h => hd (hsupp i h), map_zero, smul_zero]
    funext i
    exact Fintype.linearIndependent_iff.1 (linearIndependent_zbK ℝ lam) v hP i
  have hinj : Function.Injective E.vecMul := fun u w huw =>
    sub_eq_zero.1 (hker _ (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 huw))
  have hpos : 0 < (E * Eᵀ).det := by
    rw [← hEt]
    exact (Matrix.PosDef.mul_conjTranspose_self E hinj).det_pos
  have hint : (E * Eᵀ).det = ((Z * Zᵀ).det : ℝ) := by
    have h : E * Eᵀ = (Int.castRingHom ℝ).mapMatrix (Z * Zᵀ) := by
      rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rw [h, ← RingHom.map_det]
    rfl
  have hEE : 1 ≤ (E * Eᵀ).det := by
    rw [hint] at hpos ⊢
    have := Int.cast_pos.1 hpos
    exact_mod_cast (show (1 : ℤ) ≤ _ by omega)
  -- the Loewner order
  have hA : (m • (E * Eᵀ)).PosSemidef := by
    rw [← hEt]
    exact (Matrix.posSemidef_self_mul_conjTranspose E).smul hm
  have hBA : (E * D * Eᵀ - m • (E * Eᵀ)).PosSemidef := by
    have h1 : (Matrix.diagonal fun d : S => (fact (d : Φ × Fin n × Fin n →₀ ℕ) : ℝ) - m).PosSemidef :=
      Matrix.PosSemidef.diagonal fun d => sub_nonneg.2 (hmS d d.2)
    have h2 : Matrix.diagonal (fun d : S => (fact (d : Φ × Fin n × Fin n →₀ ℕ) : ℝ) - m) = D - m • 1 := by
      ext a b
      by_cases h : a = b
      · subst h
        simp [D]
      · simp [D, h]
    have := h1.mul_mul_conjTranspose_same E
    rwa [hEt, h2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at this
  have key := GramVolume.det_le_det hA hBA
  rw [Matrix.det_smul, ← hG, Matrix.det_smul] at key
  exact (le_mul_of_one_le_right (pow_nonneg hm _) hEE).trans key

/-- **S4.** `log det Γ ≤ 3·r·|ν|·log n`, with `r = |ZIdx|` and `|ν| = Σ_{ρ,b} ν_{ρ,b}`: equivalently
`log det Gzb ≥ −3·r·|ν|·log n`, that is `μ_arch(Δ_std) = −log det Γ/r ≥ −3|ν| log n`. By S1 with
`m = ∏ν!/n^{|ν|}` (S2) and `κ ≤ ∏ν!·n^{2|ν|}` (S3), `det Gzb ≥ (m/κ)^r ≥ n^{−3r|ν|}`. -/
theorem log_det_Γ_le (hlam : ∀ ρ, Antitone (lam ρ)) :
    Real.log ((Γ lam).map (algebraMap ℚ ℝ)).det ≤
      3 * Fintype.card (ZIdx lam) * ((∑ ρ, ∑ b, natW (lam ρ) b : ℕ) : ℝ) * Real.log n := by
  have hF : (0 : ℝ) < ∏ ρ, ∏ b, ((natW (lam ρ) b)! : ℝ) := prod_pos fun _ _ => prod_pos fun _ _ => by positivity
  have hP := pow_sum_natW_pos lam
  have hκ : (0 : ℝ) < kappa lam := by exact_mod_cast kappa_pos lam
  have h1 := det_Gzb_ge lam hlam (div_nonneg hF.le hP.le) fun d hd => prod_div_le_fact lam hlam hd
  have h3 : (kappa lam : ℝ) ≤
      (∏ ρ, ∏ b, ((natW (lam ρ) b)! : ℝ)) * ((n : ℝ) ^ ∑ ρ, ∑ b, natW (lam ρ) b) ^ 2 := by
    exact_mod_cast kappa_le lam hlam
  set r := Fintype.card (ZIdx lam)
  set g := ((Gzb lam).map (algebraMap ℚ ℝ)).det
  set N := ∑ ρ, ∑ b, natW (lam ρ) b
  set F := ∏ ρ, ∏ b, ((natW (lam ρ) b)! : ℝ)
  have hg : 0 < g := pos_of_mul_pos_right ((pow_pos (div_pos hF hP) r).trans_le h1) (pow_nonneg hκ.le r)
  have key : (((n : ℝ) ^ N) ^ 3)⁻¹ ^ r ≤ g := by
    have e : (((n : ℝ) ^ N) ^ 3)⁻¹ = (F / (n : ℝ) ^ N) / (F * ((n : ℝ) ^ N) ^ 2) := by
      field_simp [hF.ne', hP.ne']
    rw [e, div_pow, div_le_iff₀ (by positivity), mul_comm g]
    exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hκ.le h3 r) hg.le)
  have hΓ : ((Γ lam).map (algebraMap ℚ ℝ)).det = g⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← Matrix.det_mul, ← Matrix.map_mul, Γ_mul_Gzb, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]
  have hlog := Real.log_le_log (by positivity) key
  simp only [Real.log_pow, Real.log_inv, Nat.cast_ofNat] at hlog
  rw [hΓ, Real.log_inv]
  linarith

end Gram

end

end WeylFock
