/-
# Tuples of distinct primes in cells, sorted

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The terms of a tree are sums over the strictly decreasing tuples of primes of a box of cells
(`SieveAd.famB`). The tuples of a reversed term are not in order: the primes of `r'` and those of the chain each
decrease, with nothing between the two. A tuple of distinct numbers is a strictly decreasing tuple in exactly one
order of its entries, so a sum over such tuples is a sum over the orders of sums over boxes.

* `famU q bx`: the tuples of distinct primes up to `N₂` with `x^{lo_i/DEN} ≤ p_i < x^{hi_i/DEN}`, in any order.
* `existsUnique_sort`: for an injective tuple `w` there is exactly one permutation `σ` with `w ∘ σ` strictly
  decreasing.
* `sum_famU_eq`: **a sum over the tuples of `famU q bx` that satisfy a condition `P` is the sum over the
  permutations `σ` of the sums over the tuples `z` of the box `bx ∘ σ` with `P (z ∘ σ⁻¹)`**, of the function at
  `z ∘ σ⁻¹`. `sum_famU_eq_at`: the same with the route as a variable.

The file imports `SieveAdTree.lean`.
-/
import SieveAdTree

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-- For an injective tuple there is exactly one order of its entries in which it strictly decreases. -/
theorem existsUnique_sort {k : ℕ} {w : Fin k → ℕ} (hw : Function.Injective w) :
    ∃! σ : Equiv.Perm (Fin k), StrictAnti (w ∘ σ) := by
  refine ⟨Tuple.sort (fun i => OrderDual.toDual (w i)), ?_, ?_⟩
  · intro i j hij
    have hmono := Tuple.monotone_sort (fun i => OrderDual.toDual (w i))
    have hle : w (Tuple.sort (fun i => OrderDual.toDual (w i)) j) ≤
        w (Tuple.sort (fun i => OrderDual.toDual (w i)) i) := hmono hij.le
    have hne : w (Tuple.sort (fun i => OrderDual.toDual (w i)) j) ≠
        w (Tuple.sort (fun i => OrderDual.toDual (w i)) i) := fun h =>
      hij.ne' ((Equiv.injective _) (hw h))
    exact lt_of_le_of_ne hle hne
  · intro τ hτ
    have hσ : StrictAnti (w ∘ Tuple.sort (fun i => OrderDual.toDual (w i))) := by
      intro i j hij
      have hmono := Tuple.monotone_sort (fun i => OrderDual.toDual (w i))
      have hle : w (Tuple.sort (fun i => OrderDual.toDual (w i)) j) ≤
          w (Tuple.sort (fun i => OrderDual.toDual (w i)) i) := hmono hij.le
      have hne : w (Tuple.sort (fun i => OrderDual.toDual (w i)) j) ≠
          w (Tuple.sort (fun i => OrderDual.toDual (w i)) i) := fun h =>
        hij.ne' ((Equiv.injective _) (hw h))
      exact lt_of_le_of_ne hle hne
    have h := Tuple.unique_antitone hτ.antitone hσ.antitone
    exact Equiv.ext fun i => hw (congrFun h i)

variable [Route]

/-- The tuples of distinct primes up to `N₂` in the cells of `bx`, in any order. -/
noncomputable def famU (q : ℕ) {k : ℕ} (bx : Fin k → Cell) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => SieveTypeIIU.primesLe (N2 q)).filter fun rt =>
    Function.Injective rt ∧ ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN)

theorem mem_famU {q k : ℕ} {bx : Fin k → Cell} {rt : Fin k → ℕ} :
    rt ∈ famU q bx ↔ (∀ i, rt i ≤ N2 q ∧ (rt i).Prime) ∧ Function.Injective rt ∧
      ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN) := by
  rw [famU, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [SieveTypeIIU.mem_primesLe]

/-- **A sum over tuples of distinct primes in cells, by the orders of their entries.** For a condition `P` and a
function `F` of a tuple: the sum of `F` over the tuples of `famU q bx` that satisfy `P` is the sum over the
permutations `σ` of the sums, over the strictly decreasing tuples `z` of the box `bx ∘ σ` with `P (z ∘ σ⁻¹)`, of
`F (z ∘ σ⁻¹)`. -/
theorem sum_famU_eq (q : ℕ) {k : ℕ} (bx : Fin k → Cell) (P : (Fin k → ℕ) → Prop) (F : (Fin k → ℕ) → ℝ) :
    ∑ w ∈ (famU q bx).filter P, F w =
      ∑ σ : Equiv.Perm (Fin k), ∑ z ∈ (famB q (bx ∘ σ)).filter (fun z => P (z ∘ σ.symm)), F (z ∘ σ.symm) := by
  have hin : ∀ σ : Equiv.Perm (Fin k),
      ∑ z ∈ (famB q (bx ∘ σ)).filter (fun z => P (z ∘ σ.symm)), F (z ∘ σ.symm) =
        ∑ w ∈ ((famU q bx).filter P).filter (fun w => StrictAnti (w ∘ σ)), F w := by
    intro σ
    refine Finset.sum_nbij' (fun z => z ∘ σ.symm) (fun w => w ∘ σ) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨hz, hP⟩ := hz
      obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hz
      rw [Finset.mem_filter, Finset.mem_filter, mem_famU]
      refine ⟨⟨⟨fun i => hp (σ.symm i), hsa.injective.comp σ.symm.injective, fun i => ?_⟩, hP⟩, ?_⟩
      · have := hc (σ.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        exact this
      · have e : (z ∘ σ.symm) ∘ σ = z := by
          funext i
          simp only [Function.comp_apply, Equiv.symm_apply_apply]
        rw [e]
        exact hsa
    · intro w hw
      rw [Finset.mem_filter, Finset.mem_filter, mem_famU] at hw
      obtain ⟨⟨⟨hp, -, hc⟩, hP⟩, hsa⟩ := hw
      rw [Finset.mem_filter, mem_famB]
      refine ⟨⟨fun i => hp (σ i), hsa, fun i => hc (σ i)⟩, ?_⟩
      have e : (w ∘ σ) ∘ σ.symm = w := by
        funext i
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
      rw [e]
      exact hP
    · intro z _
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    · intro w _
      funext i
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    · intro z _
      rfl
  have hin2 : ∀ σ : Equiv.Perm (Fin k),
      ∑ w ∈ ((famU q bx).filter P).filter (fun w => StrictAnti (w ∘ σ)), F w =
        ∑ w ∈ (famU q bx).filter P, if StrictAnti (w ∘ σ) then F w else 0 := fun σ => Finset.sum_filter _ _
  rw [Finset.sum_congr rfl fun σ _ => (hin σ).trans (hin2 σ), Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter, mem_famU] at hw
  obtain ⟨σ₀, hσ₀, huniq⟩ := existsUnique_sort hw.1.2.1
  rw [Finset.sum_eq_single σ₀]
  · rw [ite_eq_left hσ₀]
  · intro τ _ hτ
    rw [ite_eq_right fun h => hτ (huniq τ h)]
  · intro h
    exact absurd (Finset.mem_univ σ₀) h

omit [Route] in
/-- **A sum over tuples of distinct primes in cells, by the orders of their entries, for any route**:
`sum_famU_eq` with the route as a variable. -/
theorem sum_famU_eq_at (Rt : Route) (q : ℕ) {k : ℕ} (bx : Fin k → Cell) (P : (Fin k → ℕ) → Prop)
    (F : (Fin k → ℕ) → ℝ) :
    ∑ w ∈ (@famU Rt q k bx).filter P, F w =
      ∑ σ : Equiv.Perm (Fin k), ∑ z ∈ (@famB Rt q k (bx ∘ σ)).filter (fun z => P (z ∘ σ.symm)), F (z ∘ σ.symm) :=
  @sum_famU_eq Rt q k bx P F

end SieveAd

#print axioms SieveAd.sum_famU_eq_at
