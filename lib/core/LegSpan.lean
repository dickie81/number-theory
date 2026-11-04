import Mathlib
import WeilOdd

/-! # Polynomials on `[−1/2, 1/2]` are finite Legendre mode sums `hx N x y`; polynomial antiderivatives -/

namespace LegSpan

open Polynomial Real Finset WeilPlanch WeilModes WeilOdd

lemma sL_natDegree (n : ℕ) : (sL n).natDegree = n := by
  unfold sL; rw [natDegree_map_eq_of_injective (RingHom.injective_int _)]; simp

lemma sL_degree' (n : ℕ) : (sL n).degree = n := by
  unfold sL; rw [degree_map_eq_of_injective (RingHom.injective_int _)]; exact degree_shiftedLegendre n

lemma sL_ne (n : ℕ) : sL n ≠ 0 := by
  intro h; have := sL_degree' n; rw [h] at this; simp at this

lemma span (D : ℕ) : ∀ r : ℝ[X], r.degree < D →
    ∃ c : ℕ → ℝ, ∀ y, r.eval y = ∑ n ∈ range D, c n * (sL n).eval y := by
  induction D with
  | zero =>
    intro r hr
    have : r = 0 := by simpa using hr
    exact ⟨0, fun y => by simp [this]⟩
  | succ D ih =>
    intro r hr
    set a := r.coeff D / (sL D).coeff D
    have hl : (sL D).coeff D ≠ 0 := by
      have := leadingCoeff_ne_zero.2 (sL_ne D); rwa [leadingCoeff, sL_natDegree] at this
    obtain ⟨c, hc⟩ := ih (r - C a * sL D) (by
      rw [degree_lt_iff_coeff_zero]
      intro k hk
      rw [coeff_sub, coeff_C_mul]
      rcases eq_or_lt_of_le hk with h | h
      · subst h; unfold a; field_simp; ring
      · have h1 : r.coeff k = 0 := by
          rw [degree_lt_iff_coeff_zero] at hr; exact hr k (by exact_mod_cast h)
        have h2 : (sL D).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by rw [sL_natDegree]; exact h)
        rw [h1, h2]; ring)
    refine ⟨fun n => if n = D then a else c n, fun y => ?_⟩
    rw [sum_range_succ]; simp only [ite_true]
    have : ∑ n ∈ range D, (if n = D then a else c n) * (sL n).eval y = ∑ n ∈ range D, c n * (sL n).eval y :=
      sum_congr rfl fun n hn => by rw [ite_eq_right (ne_of_lt (mem_range.1 hn))]
    rw [this, ← hc]; simp

lemma sum_even_odd (a : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ range (2 * M), a n = ∑ i ∈ range M, a (2 * i) + ∑ i ∈ range M, a (2 * i + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]; ring

/-- the cut of a function to `[−1/2, 1/2]` -/
noncomputable def cutp (φ : ℝ → ℝ) (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then φ u else 0

/-- **Every polynomial cut to `[−1/2, 1/2]` is a Legendre mode sum `hx N x y`.** -/
theorem poly_hx (p : ℝ[X]) : ∃ N x y, hx N x y = cutp (fun u => p.eval u) := by
  obtain ⟨c, hc⟩ := span (p.natDegree + 1) (p.comp (X - C (1 / 2))) (by
    calc _ ≤ ((p.comp (X - C (1/2))).natDegree : WithBot ℕ) := degree_le_natDegree
      _ < _ := by
        rw [natDegree_comp]; simp only [natDegree_X_sub_C, mul_one]; exact_mod_cast Nat.lt_succ_self _)
  set D := p.natDegree + 1
  set d : ℕ → ℝ := fun n => if n < D then c n / Real.sqrt (2 * n + 1) else 0
  refine ⟨D, fun i => d (2 * i), fun i => d (2 * i + 1), ?_⟩
  funext u
  unfold hx fx gx cutp
  rw [← sum_even_odd (fun n => d n * legT n u) D]
  split_ifs with hu
  · have e1 : p.eval u = (p.comp (X - C (1/2))).eval (u + 1/2) := by simp
    show _ = p.eval u
    rw [e1, hc]
    rw [show 2 * D = D + D by ring, sum_range_add]
    have z : ∑ n ∈ range D, d (D + n) * legT (D + n) u = 0 :=
      sum_eq_zero fun n _ => by simp [d]
    rw [z, add_zero]
    refine sum_congr rfl fun n hn => ?_
    have hn' := mem_range.1 hn
    simp only [d, ite_eq_left hn', legT, ite_eq_left hu, aeval_eq]
    have : 0 < Real.sqrt (2 * n + 1) := Real.sqrt_pos.2 (by positivity)
    field_simp
  · refine sum_eq_zero fun n _ => ?_
    simp only [legT, ite_eq_right hu, mul_zero]

/-! ## antiderivative -/

noncomputable def anti (q : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ range (q.natDegree + 1), C (q.coeff i / (i + 1)) * X ^ (i + 1)

lemma derivative_anti (q : ℝ[X]) : derivative (anti q) = q := by
  unfold anti
  rw [derivative_sum]
  conv_rhs => rw [as_sum_range_C_mul_X_pow q]
  refine sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul_X_pow]
  congr 1
  · congr 1; push_cast; field_simp

lemma hasDerivAt_anti (q : ℝ[X]) (x : ℝ) : HasDerivAt (fun y => (anti q).eval y) (q.eval x) x := by
  have := (anti q).hasDerivAt x; rwa [derivative_anti] at this

end LegSpan
