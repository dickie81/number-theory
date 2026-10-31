import ShortSieveCertAsym
import ShortSieveCertBuch

/-!
# The standard nodes of the certificate

A standard node has `k` primes and one rough item, sifted by the last prime: Li's terms `S(A_{p₁⋯p_k}, p_k)` before
any role reversal. Its coordinates are the primes' exponents (`stdRows`), its items in canonical order are the primes
`x_0, …, x_{k−1}` and the rough item `S_k = DEN − Σ_j x_j − H` (`stdItems`), and Buchstab's step on its rough item is
the standard node with one more prime (`buchRows_std`).

* `itemsOK_std`: the items' forms are `DEN` times their exponents.
* `buchRows_std`: the rows of a Buchstab child of a standard node are standard.
-/

open Finset Real

namespace ShortSieveCert

open ShortSieveNode

/-- The rows of a standard node: the coordinate `j < k` is the exponent of the prime `j`. -/
def stdRows (k : ℕ) : Rows k 1 := fun j t => Sum.elim (fun a => if a.val = j then 1 else 0) (fun _ => 0) t

/-- The form of the coordinate `j`. -/
def unitLF (j : ℕ) : LF := ⟨0, List.replicate j 0 ++ [1], 0⟩

/-- The items of a standard node in canonical order: the primes, then the rough item `S_k = DEN − Σ_j x_j − H`. -/
def stdItems (k : ℕ) : List LF := (List.range k).map unitLF ++ [⟨DEN, List.replicate k (-1), -1⟩]

theorem val_unitLF (j : ℕ) (X : ℕ → ℝ) (H : ℝ) : (unitLF j).val X H = X j := by
  simp [unitLF, LF.val, dotR_unit]

theorem dotR_replicate_neg_one : ∀ (k : ℕ) (X : ℕ → ℝ), dotR (List.replicate k (-1)) X = -∑ j ∈ range k, X j
  | 0, _ => by simp [dotR]
  | k + 1, X => by
    rw [List.replicate_succ, dotR, dotR_replicate_neg_one k, sum_range_succ']
    push_cast
    ring

theorem cX_std {k : ℕ} (α : Fin k ⊕ Fin 1 → ℝ) (j : Fin k) : cX (stdRows k) α j = DEN * α (Sum.inl j) := by
  unfold cX stdRows
  congr 1
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_zero, zero_mul, sum_const_zero, add_zero]
  rw [sum_eq_single j (fun a _ ha => by simp [Fin.val_ne_of_ne ha]) (fun h => absurd (mem_univ _) h)]
  simp

/-- **The items of a standard node** are `DEN` times their exponents at the coordinates and slack of any `α`. -/
theorem itemsOK_std (k : ℕ) : ItemsOK (stdRows k) (stdItems k) := by
  refine ⟨by simp [stdItems], fun t α => ?_⟩
  rcases t with a | i
  · -- a prime
    have hget : (stdItems k).getD (canon (Sum.inl a : Fin k ⊕ Fin 1)) LF.zero = unitLF a := by
      simp only [canon, Sum.elim_inl, stdItems]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_left (by simp)]
      simp
    rw [hget, val_unitLF, cX_std]
  · -- the rough item
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    have hget : (stdItems k).getD (canon (Sum.inr 0 : Fin k ⊕ Fin 1)) LF.zero =
        ⟨DEN, List.replicate k (-1), -1⟩ := by
      simp only [canon, Sum.elim_inr, Fin.val_zero, add_zero, stdItems]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
      simp
    rw [hget]
    unfold LF.val cH
    rw [dotR_replicate_neg_one]
    have e : ∑ j ∈ range k, cX (stdRows k) α j = DEN * ∑ a : Fin k, α (Sum.inl a) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => cX (stdRows k) α j), mul_sum]
      exact sum_congr rfl fun a _ => cX_std α a
    rw [e, Fintype.sum_sum_type, Fin.sum_univ_one]
    push_cast
    ring

/-- **The Buchstab child of a standard node is standard**: its rows are `stdRows (k + 1)`. -/
theorem buchRows_std (k : ℕ) : buchRows (stdRows k) 0 k = stdRows (k + 1) := by
  funext j t
  unfold buchRows stdRows
  rcases t with a | i
  · simp only [Sum.elim_inl]
    by_cases hj : j = k
    · subst hj
      simp only [ite_true]
      by_cases ha : a = Fin.last j
      · subst ha; simp
      · rw [ite_eq_right ha, ite_eq_right]
        intro h
        exact ha (Fin.ext (by simpa using h))
    · rw [ite_eq_right hj]
      induction a using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Sum.elim_inr, Fin.val_last]
        rw [ite_eq_right (Ne.symm hj)]
      | cast a =>
        simp only [Fin.lastCases_castSucc, Fin.val_castSucc]
  · simp

end ShortSieveCert

#print axioms ShortSieveCert.itemsOK_std
#print axioms ShortSieveCert.buchRows_std
