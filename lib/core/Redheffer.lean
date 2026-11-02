/-
# Redheffer's matrix inside Smith's lattice: `det R_n = M(n)`

Plain statement. Index `1, …, n` by `Fin n` (`i ↦ i + 1`). Let `E(i, j) = [i ∣ j]` be the divisibility matrix and
`R(i, j) = [j = 1 or i ∣ j]` Redheffer's matrix, which is `E` with its first column replaced by ones, a rank-one change.
* `det E = 1` (`det_E`): `E` is unitriangular.
* `Σ_{m ≤ K} M(K/m) = 1` for `K ≥ 1` (`sum_mertens_div`), so the vector `c_j = M(n/j)` solves `E c = 1`
  (`E_mulVec_c`), and by Cramer's rule **`det R_n = M(n)`** (`det_redheffer`), Mertens' function
  `M(n) = Σ_{k ≤ n} μ(k)` (`mertens`).
* The integral form `R·diag(φ)·Rᵀ` is positive semidefinite, and its determinant is `M(n)²·∏_{k ≤ n} φ(k)`
  (`det_gram_redheffer`); Smith's gcd matrix is `Eᵀ·diag(φ)·E` with determinant `∏ φ(k)` (`det_smith`).
So `M(n)²` is the ratio of the covolumes of two explicit positive integral forms, Smith's and Redheffer's.
-/
import Mathlib
import SmithLattice

open Finset Matrix ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Redheffer

/-- Mertens' function `M(n) = Σ_{k ≤ n} μ(k)`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Ioc 0 n, μ k

lemma swap2 (g : ℕ → ℤ) (K : ℕ) :
    ∑ a ∈ Ioc 0 K, ∑ k ∈ Ioc 0 (K / a), g k = ∑ k ∈ Ioc 0 K, ((K / k : ℕ) : ℤ) * g k := by
  have h1 : ∀ a ∈ Ioc 0 K, Ioc 0 (K / a) = (Ioc 0 K).filter (fun k => a * k ≤ K) := by
    intro a ha
    have ha0 := (mem_Ioc.1 ha).1
    ext k
    simp only [mem_Ioc, mem_filter, Nat.le_div_iff_mul_le ha0]
    constructor
    · rintro ⟨hk, h⟩; exact ⟨⟨hk, le_trans (Nat.le_mul_of_pos_left k ha0) (by rw [mul_comm]; exact h)⟩,
        by rw [mul_comm]; exact h⟩
    · rintro ⟨⟨hk, -⟩, h⟩; exact ⟨hk, by rw [mul_comm]; exact h⟩
  rw [sum_congr rfl fun a ha => by rw [h1 a ha], ]
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk0 := (mem_Ioc.1 hk).1
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  congr 2
  have : (Ioc 0 K).filter (fun a => a * k ≤ K) = Ioc 0 (K / k) := by
    ext a
    simp only [mem_Ioc, mem_filter, Nat.le_div_iff_mul_le hk0]
    constructor
    · rintro ⟨⟨ha, -⟩, h⟩; exact ⟨ha, h⟩
    · rintro ⟨ha, h⟩; exact ⟨⟨ha, le_trans (Nat.le_mul_of_pos_right a hk0) h⟩, h⟩
  rw [this, Nat.card_Ioc, Nat.sub_zero]

/-- **`Σ_{m ≤ K} M(K/m) = 1`** for `K ≥ 1`. -/
theorem sum_mertens_div {K : ℕ} (hK : 1 ≤ K) : ∑ a ∈ Ioc 0 K, mertens (K / a) = 1 := by
  unfold mertens
  rw [swap2]
  exact SmithLattice.mertens_identity hK

lemma sum_fin_succ {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ∑ j : Fin n, f ((j : ℕ) + 1) = ∑ m ∈ Ioc 0 n, f m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, sum_Ioc_succ_top (Nat.zero_le n)]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]

/-- The divisibility matrix `E(i, j) = [i ∣ j]`. -/
def E (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

/-- **`det E = 1`.** -/
theorem det_E (n : ℕ) : (E n).det = 1 := by
  rw [det_of_isUpperTriangular]
  · simp [E]
  · intro i j hij
    have hij' : (j : ℕ) < i := hij
    simp only [E, ite_eq_right_iff, one_ne_zero, imp_false]
    intro h
    have := Nat.le_of_dvd (Nat.succ_pos _) h
    omega

/-- `c_j = M(n/j)`. -/
def c (n : ℕ) : Fin n → ℤ := fun j => mertens (n / ((j : ℕ) + 1))

theorem E_mulVec_c (n : ℕ) : E n *ᵥ c n = fun _ => 1 := by
  funext i
  have hi : (i : ℕ) + 1 ≤ n := i.2
  simp only [mulVec, dotProduct, E, c, ite_mul, one_mul, zero_mul]
  rw [sum_fin_succ n (fun m => if (i : ℕ) + 1 ∣ m then mertens (n / m) else 0), ← sum_filter]
  set d := (i : ℕ) + 1
  have hd : 0 < d := Nat.succ_pos _
  have himg : (Ioc 0 n).filter (d ∣ ·) = (Ioc 0 (n / d)).image (d * ·) := by
    ext m
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨hm, hmn⟩, a, rfl⟩
      refine ⟨a, ⟨Nat.pos_of_mul_pos_left hm, ?_⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le hd, mul_comm]; exact hmn
    · rintro ⟨a, ⟨ha, han⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd ha, ?_⟩, dvd_mul_right _ _⟩
      rw [Nat.le_div_iff_mul_le hd, mul_comm] at han; exact han
  rw [himg, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h]
  simp_rw [← Nat.div_div_eq_div_mul]
  exact sum_mertens_div ((Nat.one_le_div_iff hd).2 hi)

/-- Redheffer's matrix `R(i, j) = [j = 1 or i ∣ j]`. -/
def R (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if j = 0 ∨ (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

lemma R_eq (n : ℕ) : R n = (E (n + 1)).updateCol 0 (fun _ => 1) := by
  ext i j
  simp only [R, E, updateCol_apply]
  by_cases hj : j = 0 <;> simp [hj]

/-- **Redheffer's theorem: `det R_n = M(n)`** (with `n + 1` for `n`). -/
theorem det_redheffer (n : ℕ) : (R n).det = mertens (n + 1) := by
  rw [R_eq, ← cramer_apply]
  have hE := det_E (n + 1)
  have hinj : ∀ x : Fin (n + 1) → ℤ, (E (n + 1)).adjugate *ᵥ (E (n + 1) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, adjugate_mul, hE, one_smul, one_mulVec]
  have h1 := mulVec_cramer (E (n + 1)) (fun _ => 1)
  rw [hE, one_smul] at h1
  have h1' := h1.trans (E_mulVec_c (n + 1)).symm
  have h2 := congrArg ((E (n + 1)).adjugate *ᵥ ·) h1'
  simp only [hinj] at h2
  rw [h2]
  simp [c]

/-- **The determinant of Redheffer's form**: `det(R·diag(φ)·Rᵀ) = M(n)²·∏_{k ≤ n} φ(k)`. -/
theorem det_gram_redheffer (n : ℕ) :
    (R n * diagonal (fun k : Fin (n + 1) => ((Nat.totient ((k : ℕ) + 1) : ℕ) : ℤ)) * (R n)ᵀ).det =
      mertens (n + 1) ^ 2 * ∏ k : Fin (n + 1), ((Nat.totient ((k : ℕ) + 1) : ℕ) : ℤ) := by
  rw [det_mul, det_mul, det_transpose, det_diagonal, det_redheffer]
  ring

/-- **Smith's determinant**: `det(Eᵀ·diag(φ)·E) = ∏_{k ≤ n} φ(k)`. -/
theorem det_smith (n : ℕ) :
    ((E n)ᵀ * diagonal (fun k : Fin n => ((Nat.totient ((k : ℕ) + 1) : ℕ) : ℤ)) * E n).det =
      ∏ k : Fin n, ((Nat.totient ((k : ℕ) + 1) : ℕ) : ℤ) := by
  rw [det_mul, det_mul, det_transpose, det_diagonal, det_E]
  ring

/-- **`Eᵀ·diag(φ)·E` is the gcd matrix.** -/
theorem smith_entry (n : ℕ) (i j : Fin n) :
    ((E n)ᵀ * diagonal (fun k : Fin n => ((Nat.totient ((k : ℕ) + 1) : ℕ) : ℤ)) * E n) i j =
      (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℤ) := by
  simp only [Matrix.mul_apply, transpose_apply, diagonal_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true,
    E, ite_mul, one_mul, zero_mul]
  simp only [mul_one]
  rw [sum_fin_succ n (fun d => if d ∣ (j : ℕ) + 1 then (if d ∣ (i : ℕ) + 1 then ((Nat.totient d : ℕ) : ℤ) else 0)
    else 0)]
  have hi : (i : ℕ) + 1 ≤ n := i.2
  have hg : 0 < Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _)
  rw [← Nat.sum_totient (Nat.gcd _ _), Nat.cast_sum]
  simp_rw [← ite_and]
  rw [← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, mem_Ioc, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨-, hdj, hdi⟩; exact ⟨⟨hdi, hdj⟩, hg.ne'⟩
  · rintro ⟨⟨hdi, hdj⟩, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdi (Nat.succ_pos _), (Nat.le_of_dvd (Nat.succ_pos _) hdi).trans hi⟩, hdj, hdi⟩

/-- The trivial bound `|M(n)| ≤ n`. -/
theorem abs_mertens_le (n : ℕ) : |mertens n| ≤ n := by
  unfold mertens
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Ioc 0 n, |(μ k : ℤ)| ≤ ∑ _k ∈ Ioc 0 n, (1 : ℤ) :=
        sum_le_sum fun k _ => abs_moebius_le_one
    _ = n := by simp

end Redheffer

#print axioms Redheffer.det_E
#print axioms Redheffer.sum_mertens_div
#print axioms Redheffer.det_redheffer
#print axioms Redheffer.det_gram_redheffer
#print axioms Redheffer.det_smith
#print axioms Redheffer.smith_entry
#print axioms Redheffer.abs_mertens_le
