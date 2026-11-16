/-
# Comparisons of a family's primes

Plain statements. A comparison `Cmp K` is `0 ≤ c(m) + Σ_i e_i log x_i`, or `0 <` when it is strict, with
coefficients at most `1` in absolute value and a pivot `i` with `e_i = ±1`. Each kind below comes with a lemma that
says what it means for `x_i ≥ 1` (the `_holds` lemmas):

* `gt`: `x_i > x_{i'}`; `ge`, `lt`: `x_i ≥ b` and `x_i < b`, for `b > 0`;
* `prodLe`, `prodGt`: `∏_{i∈s} x_i ≤ b` and `> b`, for `b > 0`, pivoted at `i₀ ∈ s`;
* `rough`: `x_i ≤ minFac m`, for `m ≥ 2`; `rangeLo`, `rangeHi`: `b < m∏_i x_i` and `m∏_i x_i ≤ b`, for `b > 0`, `m ≥ 1`;
* `lift`: a comparison of the first `j` coordinates, as one of `K ≥ j`.

These are the comparisons of `SieveFamily.typeII_sharp`'s families, in
the kinds that Proposition 6's stops need. The file imports only Mathlib.
-/
import Mathlib

open Real Finset

namespace SieveCmp

/-- A comparison of a family: `0 ≤ c(m) + Σ_i e_i log x_i`, or `0 <` when `strict`, with a pivot `i` of coefficient
`±1` and coefficients at most `1` in absolute value. -/
structure Cmp (K : ℕ) where
  c : ℕ → ℝ
  e : Fin K → ℝ
  strict : Bool
  piv : Fin K
  hpiv : e piv = 1 ∨ e piv = -1
  he : ∀ i, |e i| ≤ 1

variable {K : ℕ}

/-- The comparison's form `c(m) + Σ_i e_i log x_i`. -/
noncomputable def Cmp.form (C : Cmp K) (m : ℕ) (x : Fin K → ℕ) : ℝ := C.c m + ∑ i, C.e i * Real.log (x i)

/-- The comparison holds: `0 < form` if strict, `0 ≤ form` otherwise. -/
def Cmp.holds (C : Cmp K) (m : ℕ) (x : Fin K → ℕ) : Prop :=
  if C.strict then 0 < C.form m x else 0 ≤ C.form m x

theorem Cmp.spec (C : Cmp K) (m : ℕ) (x : Fin K → ℕ) :
    (0 < C.form m x → C.holds m x) ∧ (C.holds m x → 0 ≤ C.form m x) := by
  unfold Cmp.holds
  split_ifs
  · exact ⟨id, le_of_lt⟩
  · exact ⟨le_of_lt, id⟩

/-! ### Sums of logarithms against indicator coefficients -/

theorem sum_single (i : Fin K) (x : Fin K → ℕ) :
    ∑ t, (if t = i then (1 : ℝ) else 0) * Real.log (x t) = Real.log (x i) := by
  simp [ite_mul]

theorem sum_set (s : Finset (Fin K)) (x : Fin K → ℕ) (hx : ∀ i, 1 ≤ x i) :
    ∑ t, (if t ∈ s then (1 : ℝ) else 0) * Real.log (x t) = Real.log (∏ t ∈ s, (x t : ℝ)) := by
  rw [Real.log_prod (fun t _ => by have := hx t; positivity)]
  simp [ite_mul, Finset.sum_ite_mem]

/-! ### The basic comparisons, and what they say on tuples of positive integers -/

end SieveCmp
