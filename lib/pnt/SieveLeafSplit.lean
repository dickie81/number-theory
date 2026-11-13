/-
# The large leaves of a family split in three: two by the paper's lemma, one by the estimate in two variables

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

A family of leaves `x` (tuples of primes under comparisons, split into the blocks `S` and `Sᶜ`, `d₁ = ∏_S x` and
`d₂ = ∏_{Sᶜ} x`) whose box straddles the region of the paper's Lemma 4.3 is cut in three by two more comparisons:
`d₁ ≤ X₁`; `d₁ > X₁` and `d₂ ≤ X₂`; and `d₁ > X₁`, `d₂ > X₂`. The first two are bounded by `LeavesOK` (the paper's
lemma), each with its own exponents `a`, `b`, and the third by any bound of its term (the estimate in two variables,
`SieveLeafTwo.leaf2_bound`, in the use of this file).

Plain statements. `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋` and `w = ⌈q^{ε_w}⌉`.

* `large_leaves_le3`: for a family with at most `J₀ − 2` comparisons, none of them constant, `S` and `Sᶜ` nonempty,
  the forms of its comparisons and of the four cuts at most `Λ₀ log q`, its tuples strictly decreasing with entries at
  least `w`, the sizes of `LeavesOK` with `(a₁, b₁)` where `d₁ ≤ X₁` and with `(a₂, b₂)` where `d₁ > X₁` and
  `d₂ ≤ X₂`, and the term of the rest at most `q^{L−δ}/φ(q)`: the family's term is at most
  `ζ_k(…)·Σ_x 1/∏x + 3q^{L−δ}/φ(q)`.

The file imports `SieveP6ib.lean` (`SieveP6ib.sum_RTg_cmp`, a family split by one comparison).
-/
import SieveP6ib

open Real Finset SieveFamily SieveTree SieveChain SieveP6Chain

namespace SieveLeafSplit

open Classical

/-- A tuple of a family with a comparison added is a tuple of the family. -/
theorem mem_of_mem_append {K Y : ℕ} {Ω Ω' : List (GCmp K)} {x : Fin K → ℕ} (hx : x ∈ RTg K Y (Ω ++ Ω')) :
    x ∈ RTg K Y Ω ∧ ∀ C ∈ Ω', C.holds 0 x := by
  rw [SieveP6Tree.RTg_append] at hx
  exact Finset.mem_filter.1 hx

/-- A cut `∏_{i∈I} x_i ≤ b` or `b < ∏_{i∈I} x_i` on a nonempty `I` is not constant. -/
theorem gUp_nz {K : ℕ} {I : Finset (Fin K)} (hI : I.Nonempty) (b : ℝ) (st : Bool) : ∃ i, (gUp I b st).e i ≠ 0 := by
  obtain ⟨i, hi⟩ := hI
  exact ⟨i, by simp [gUp, hi]⟩

theorem gDown_nz {K : ℕ} {I : Finset (Fin K)} (hI : I.Nonempty) (b : ℝ) (st : Bool) :
    ∃ i, (gDown I b st).e i ≠ 0 := by
  obtain ⟨i, hi⟩ := hI
  exact ⟨i, by simp [gDown, hi]⟩

set_option maxHeartbeats 800000 in
/-- **The large leaves of a family, split in three.** The part with `d₁ ≤ X₁` by `LeavesOK` at `(a₁, b₁)`, the part
with `d₁ > X₁` and `d₂ ≤ X₂` by `LeavesOK` at `(a₂, b₂)`, and the part with `d₁ > X₁` and `d₂ > X₂` by the bound
`hE` of its term. -/
theorem large_leaves_le3 {q : ℕ} {a' : ZMod q} {L a₁ b₁ a₂ b₂ δ' εw Λ₀ C₀ δ : ℝ} {k J₀ Kmax : ℕ}
    (hok₁ : SieveP6TreeLeaves.LeavesOK q a' L a₁ b₁ δ' εw Λ₀ C₀ δ k J₀ Kmax)
    (hok₂ : SieveP6TreeLeaves.LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δ k J₀ Kmax) {K : ℕ} (S : Finset (Fin K))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hK₁ : S.card ≤ Kmax) (hK₂ : Sᶜ.card ≤ Kmax) (Ω : List (GCmp K))
    (hlen : Ω.length + 2 ≤ J₀) (hnz : ∀ C ∈ Ω, ∃ i, C.e i ≠ 0) {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hform : ∀ C ∈ Ω ++ [gUp S X₁ false, gDown S X₁ true, gUp Sᶜ X₂ false],
      ∀ x : Fin K → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) → C.form 0 x ≤ Λ₀ * Real.log q)
    (hreg : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i)
    (hgeo₁ : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S, (x i : ℝ) ≤ X₁ →
      ((∏ i ∈ S, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₁) ∧
      ((∏ i ∈ S, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Sᶜ, x i : ℕ) : ℝ) ^ 2 ≤
        (q : ℝ) ^ (L - b₁) ∧
      (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ))
    (hgeo₂ : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, X₁ < ∏ i ∈ S, (x i : ℝ) → ∏ i ∈ Sᶜ, (x i : ℝ) ≤ X₂ →
      ((∏ i ∈ S, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
      ((∏ i ∈ S, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Sᶜ, x i : ℕ) : ℝ) ^ 2 ≤
        (q : ℝ) ^ (L - b₂) ∧
      (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ))
    (hZ0 : 0 ≤ SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))))
    (hE : ‖∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gDown S X₁ true, gDown Sᶜ X₂ true]),
        ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊, dw q a' n *
          (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) :
    ‖∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊, dw q a' n *
        (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) *
        ∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, x i : ℕ) : ℝ) +
      3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  set G : (Fin K → ℕ) → ℂ := fun x => ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂, dw q a' n *
    (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0) with hG
  set R : (Fin K → ℕ) → ℝ := fun x => 1 / ((∏ i, x i : ℕ) : ℝ) with hR
  set Z := SieveProp6.zeta C₀ k * (((N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) / (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ)))
    with hZ
  set Ω₁ := Ω ++ [gUp S X₁ false] with hΩ₁
  set Ω' := Ω ++ [gDown S X₁ true] with hΩ'
  set Ω₂ := Ω' ++ [gUp Sᶜ X₂ false] with hΩ₂
  have hΩ₃ : Ω' ++ [gDown Sᶜ X₂ true] = Ω ++ [gDown S X₁ true, gDown Sᶜ X₂ true] := by
    rw [hΩ', List.append_assoc]
    rfl
  -- the three parts
  have hsplit : ∀ F : (Fin K → ℕ) → ℂ, ∑ x ∈ RTg K N₂ Ω, F x =
      ∑ x ∈ RTg K N₂ Ω₁, F x + ∑ x ∈ RTg K N₂ Ω₂, F x +
        ∑ x ∈ RTg K N₂ (Ω ++ [gDown S X₁ true, gDown Sᶜ X₂ true]), F x := by
    intro F
    rw [SieveP6ib.sum_RTg_cmp Ω S hX₁ F, SieveP6ib.sum_RTg_cmp Ω' Sᶜ hX₂ F, hΩ₃, add_assoc]
  have hsplitR : ∑ x ∈ RTg K N₂ Ω, R x =
      ∑ x ∈ RTg K N₂ Ω₁, R x + ∑ x ∈ RTg K N₂ Ω₂, R x +
        ∑ x ∈ RTg K N₂ (Ω ++ [gDown S X₁ true, gDown Sᶜ X₂ true]), R x := by
    rw [SieveP6ib.sum_RTg_cmp Ω S hX₁ R, SieveP6ib.sum_RTg_cmp Ω' Sᶜ hX₂ R, hΩ₃, add_assoc]
  have hR0 : 0 ≤ ∑ x ∈ RTg K N₂ (Ω ++ [gDown S X₁ true, gDown Sᶜ X₂ true]), R x :=
    Finset.sum_nonneg fun x _ => by rw [hR]; positivity
  -- the first part, by `LeavesOK` at `(a₁, b₁)`
  have h₁ : ‖∑ x ∈ RTg K N₂ Ω₁, G x‖ ≤ Z * ∑ x ∈ RTg K N₂ Ω₁, R x + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
    refine SieveP6TreeLeaves.large_leaves_le hok₁ S hK₁ hK₂ Ω₁ (by rw [hΩ₁, List.length_append]; simp; omega)
      ?_ ?_ ?_ ?_
    · intro C hC
      rcases List.mem_append.1 hC with h | h
      · exact hnz C h
      · rw [List.mem_singleton.1 h]; exact gUp_nz hS _ _
    · intro C hC x hx
      rcases List.mem_append.1 hC with h | h
      · exact hform C (List.mem_append_left _ h) x hx
      · rw [List.mem_singleton.1 h]
        exact hform _ (List.mem_append_right _ (by simp)) x hx
    · intro x hx
      exact hreg x (mem_of_mem_append hx).1
    · intro x hx
      obtain ⟨hxΩ, hC⟩ := mem_of_mem_append hx
      have hx1 := SieveP6Tree.one_le_of_mem_RTg hxΩ
      have hle := hC _ (List.mem_singleton_self _)
      rw [gUp_holds _ hX₁ false 0 hx1] at hle
      simp only [Bool.false_eq_true, ite_false] at hle
      exact hgeo₁ x hxΩ hle
  -- the second part, by `LeavesOK` at `(a₂, b₂)`
  have h₂ : ‖∑ x ∈ RTg K N₂ Ω₂, G x‖ ≤ Z * ∑ x ∈ RTg K N₂ Ω₂, R x + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
    refine SieveP6TreeLeaves.large_leaves_le hok₂ S hK₁ hK₂ Ω₂
      (by rw [hΩ₂, hΩ', List.length_append, List.length_append]; simp; omega) ?_ ?_ ?_ ?_
    · intro C hC
      rcases List.mem_append.1 hC with h | h
      · rcases List.mem_append.1 h with h' | h'
        · exact hnz C h'
        · rw [List.mem_singleton.1 h']; exact gDown_nz hS _ _
      · rw [List.mem_singleton.1 h]; exact gUp_nz hSc _ _
    · intro C hC x hx
      rcases List.mem_append.1 hC with h | h
      · rcases List.mem_append.1 h with h' | h'
        · exact hform C (List.mem_append_left _ h') x hx
        · rw [List.mem_singleton.1 h']
          exact hform _ (List.mem_append_right _ (by simp)) x hx
      · rw [List.mem_singleton.1 h]
        exact hform _ (List.mem_append_right _ (by simp)) x hx
    · intro x hx
      exact hreg x (mem_of_mem_append (mem_of_mem_append hx).1).1
    · intro x hx
      obtain ⟨hx', hC₂⟩ := mem_of_mem_append hx
      obtain ⟨hxΩ, hC₁⟩ := mem_of_mem_append hx'
      have hx1 := SieveP6Tree.one_le_of_mem_RTg hxΩ
      have hlt := hC₁ _ (List.mem_singleton_self _)
      rw [gDown_holds _ hX₁ true 0 hx1] at hlt
      simp only [ite_true] at hlt
      have hle := hC₂ _ (List.mem_singleton_self _)
      rw [gUp_holds _ hX₂ false 0 hx1] at hle
      simp only [Bool.false_eq_true, ite_false] at hle
      exact hgeo₂ x hxΩ hlt hle
  -- together
  have hE' : ‖∑ x ∈ RTg K N₂ (Ω ++ [gDown S X₁ true, gDown Sᶜ X₂ true]), G x‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := hE
  have hZsum : Z * ∑ x ∈ RTg K N₂ Ω₁, R x + Z * ∑ x ∈ RTg K N₂ Ω₂, R x ≤ Z * ∑ x ∈ RTg K N₂ Ω, R x := by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hZ0
    rw [hsplitR]
    linarith
  show ‖∑ x ∈ RTg K N₂ Ω, G x‖ ≤ Z * ∑ x ∈ RTg K N₂ Ω, R x + 3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ))
  rw [hsplit G]
  have hn1 := norm_add_le (∑ x ∈ RTg K N₂ Ω₁, G x + ∑ x ∈ RTg K N₂ Ω₂, G x)
    (∑ x ∈ RTg K N₂ (Ω ++ [gDown S X₁ true, gDown Sᶜ X₂ true]), G x)
  have hn2 := norm_add_le (∑ x ∈ RTg K N₂ Ω₁, G x) (∑ x ∈ RTg K N₂ Ω₂, G x)
  linarith

/-! ### The leaves of a tree, each size by the paper's lemma or split in three -/

open SieveP6TreeLeaves SieveP6Split

/-- The leaves of size `s` split in three (`large_leaves_le3`): `I_s` and its complement nonempty, the cuts
`1 ≤ X₁, X₂ ≤ q^{Λ₁}`, the sizes of `LeavesOK` at `(a, b)` on the large leaves with `d₁ ≤ X₁` and at `(a₂, b₂)` on those
with `d₁ > X₁` and `d₂ ≤ X₂`, and the term of the large leaves with `d₁ > X₁` and `d₂ > X₂` at most `q^{L−δ}/φ(q)`. -/
def Split3 (q : ℕ) (a' : ZMod q) (L a b a₂ b₂ δ' εw Λ₁ δ : ℝ) (k : ℕ) {j : ℕ} (Ω : List (GCmp j))
    (S₀ : Finset (Fin j)) (I : ∀ s, Finset (Fin (j + s))) (E : ℝ) (z₀ s : ℕ) : Prop :=
  (I s).Nonempty ∧ (I s)ᶜ.Nonempty ∧ ∃ X₁ X₂ : ℝ, 1 ≤ X₁ ∧ 1 ≤ X₂ ∧ Real.log X₁ ≤ Λ₁ * Real.log q ∧
    Real.log X₂ ≤ Λ₁ * Real.log q ∧
    (∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) → ∏ i ∈ I s, (x i : ℝ) ≤ X₁ →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b)) ∧
    (∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) → X₁ < ∏ i ∈ I s, (x i : ℝ) → ∏ i ∈ (I s)ᶜ, (x i : ℝ) ≤ X₂ →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b₂)) ∧
    ‖∑ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
        [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) ++ [gDown (I s) X₁ true, gDown (I s)ᶜ X₂ true]),
      ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)

set_option maxHeartbeats 1600000 in
/-- **The leaves of a tree, each size by the paper's lemma or split in three.** `SieveP6TreeLeaves.tree_leaves_le`
with, at each size `s < s_max`, either the sizes of `LeavesOK` at `(a, b)` or at `(a₂, b₂)` on its large leaves or their
split in three
(`Split3`, with `LeavesOK` at `(a, b)` and `(a₂, b₂)` on two parts and a bound of the third), and two more comparisons
in the budget: the bound is the same with `3s_max·q^{L−δ}/φ(q)` in place of `s_max·q^{L−δ}/φ(q)`. -/
theorem tree_leaves_le3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {L a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δ : ℝ}
    {k J₀ Kmax : ℕ} (hok : LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax)
    (hok₂ : LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δ k J₀ Kmax) {j : ℕ} (Ω : List (GCmp j))
    (S₀ : Finset (Fin j)) (I : ∀ s, Finset (Fin (j + s))) {E : ℝ} (hE : 0 < E) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀) (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hsmax : E ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hK : j + smax ≤ Kmax)
    (hlen : Ω.length + smax * smax + 2 * smax + 4 ≤ J₀) (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log E ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i)
    (hcase : ∀ s < smax, (∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b)) ∨ (∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b₂)) ∨
      Split3 q a' L a b a₂ b₂ δ' εw Λ₁ δ k Ω S₀ I E z₀ s)
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (N : ℕ) :
    ‖∑ s ∈ range N, (-1 : ℂ) ^ s *
        ∑ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * (3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ))) := by
  obtain ⟨hJw, -, -⟩ := SieveProp6.Jw_spec hw2
  have hw1 : 1 ≤ ⌈(q : ℝ) ^ εw⌉₊ := by omega
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hw1' : (1 : ℝ) ≤ ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast hw1
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hlogw : 0 < Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Real.log_pos (by exact_mod_cast hw2)
  have hNN : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
    have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast hN
    linarith
  have hN₂1 : (1 : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
  have hlogN₂ : 0 ≤ Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) := Real.log_nonneg hN₂1
  have hζ0 := SieveProp6.zeta_nonneg hC₀ k
  have hrem0 := SieveProp6.rem_nonneg (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k
  have hX0 : (0 : ℝ) < (q : ℝ) ^ (L - 1 - δ') := by linarith
  have he0 : 0 ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by positivity
  -- the entries of a leaf
  have hleaf : ∀ s, ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      StrictAnti x ∧ ∀ i, (x i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ x i := by
    intro s x hx
    have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
    obtain ⟨hΩ1, ⟨hanti, hblk⟩, -⟩ :=
      (SieveP6Tree.leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
    have hprime : ∀ i, (x i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
    obtain ⟨ha, hz⟩ := hreg _ (fun i => hprime _) hΩ1
    refine ⟨SieveP6Tree.strictAnti_chain (j := j) (t := s) ha hanti (fun i => by exact_mod_cast hz i)
      (fun u => (hblk u).1), fun i => ⟨hprime i, ?_⟩⟩
    induction i using Fin.addCases with
    | left i => exact le_trans hwz (hz i)
    | right u => exact_mod_cast (hblk u).2
  refine (norm_sum_sizes_le' (smax := smax) (b := fun s => (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) -
      ⌊(q : ℝ) ^ L⌋₊) / (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
      ∑ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
        1 / ((∏ i, x i : ℕ) : ℝ) + 3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)))
    (fun s => by simp) (fun s => by positivity) (fun s hs => ?_) (fun s hs => ?_)).trans ?_
  · obtain ⟨Zh, hZh⟩ : ∃ Zh, Zh = SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
        (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) := ⟨_, rfl⟩
    have hZh0 : 0 ≤ Zh := by rw [hZh]; positivity
    have hZ2 : 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
        (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) = 2 * Zh := by rw [hZh]; ring
    obtain ⟨rm, hrm⟩ : ∃ rm, rm = SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k :=
      ⟨_, rfl⟩
    have hrm0 : 0 ≤ rm := by rw [hrm]; exact hrem0
    rw [hZ2, ← hrm]
    -- the small leaves and the large ones
    rw [← Finset.sum_filter_add_sum_filter_not (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
      (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)) (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))]
    rw [← Finset.sum_filter_add_sum_filter_not (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
      (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)) (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))
      (fun x => 1 / ((∏ i, x i : ℕ) : ℝ))]
    refine (norm_add_le _ _).trans ?_
    have hsm := small_leaves_le ha' ((RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
      (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
        (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))) hw2
      (fun x hx => (hleaf s x (Finset.mem_filter.1 hx).1).2) hJw hN hC₀ hC hk hk1 hkC
    rw [hZ2, ← hrm] at hsm
    have hcard : (((RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
        (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))).card : ℝ) ≤
        (q : ℝ) ^ (L - 1 - δ') * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
          (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
            (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      have hp : (0 : ℝ) < ((∏ i, x i : ℕ) : ℝ) := by
        have := SieveP6Leaves.one_le_prod fun i => ((hleaf s x hx1).2 i).1
        exact_mod_cast (by omega : 0 < ∏ i, x i)
      rw [mul_one_div, le_div_iff₀ hp]
      push_cast at hx2 ⊢
      linarith
    have hlg : ‖∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
        (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
          dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
        Zh * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
          (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) +
          3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
      rw [filter_large_eq _ hX0]
      rcases SieveP6Split.RTg_nz (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
          [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) with h | h
      · rw [h, Finset.sum_empty, Finset.sum_empty, norm_zero, mul_zero, zero_add]
        linarith
      · rw [h, hZh]
        have hK1 : (I s).card ≤ Kmax :=
          le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; omega)
        have hK2 : (I s)ᶜ.card ≤ Kmax :=
          le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; omega)
        have hlen' : ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
              fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0)).length + 2 ≤ J₀ := by
          refine (Nat.add_le_add_right (List.length_filter_le _ _) 2).trans ?_
          have h1 := length_Pblock_le j s (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (z₀ : ℝ)
          have h2 : s * s + 2 * s ≤ smax * smax + 2 * smax := by nlinarith
          simp only [SieveP6Tree.leafCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega
        have hnz' : ∀ C ∈ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0)),
            ∃ i, C.e i ≠ 0 :=
          fun C hC => of_decide_eq_true (List.mem_filter.1 hC).2
        have hcΩ := leafCmps_c_le (j := j) (Ω := Ω) (S₀ := S₀) (E := E) (w := (⌈(q : ℝ) ^ εw⌉₊ : ℝ))
          (z₀ := (z₀ : ℝ)) (X := (q : ℝ) ^ (L - 1 - δ')) (s := s) (B := Λ₁ * Real.log q) (by positivity) hc hlz hlE
          hw1' hX
        have hform' : ∀ C ∈ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0)),
            ∀ x : Fin (j + s) → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) → C.form 0 x ≤ Λ₀ * Real.log q := by
          intro C hC x hx
          have h1 := SieveP6Split.form_le C 0 (fun i => (hx i).1) (Y := (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ))
            (fun i => by exact_mod_cast (hx i).2)
          have h2 := hcΩ C (List.mem_filter.1 hC).1
          have h3 : ((j + s : ℕ) : ℝ) * Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤
              (j + smax) * Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlogN₂
            push_cast
            have : (s : ℝ) ≤ smax := by exact_mod_cast hs.le
            linarith
          linarith
        have hreg' : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
            StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i := by
          intro x hx
          rw [← h, ← filter_large_eq _ hX0] at hx
          have hx' := (Finset.mem_filter.1 hx).1
          exact ⟨(hleaf s x hx').1, fun i => ((hleaf s x hx').2 i).2⟩
        -- a tuple of the large leaves, as a leaf with `∏x > X`
        have hlarge : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
            [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
            x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s) ∧
              (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) := by
          intro x hx
          rw [← h, ← filter_large_eq _ hX0] at hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
          exact ⟨hx1, not_le.1 hx2⟩
        rcases hcase s hs with hgeo | hgeo | ⟨hne, hnec, X₁, X₂, hX₁1, hX₂1, hlX₁, hlX₂, hgA, hgB, hEs⟩
        · have hgeo' : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
              [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
            intro x hx
            obtain ⟨hx1, hlt⟩ := hlarge x hx
            obtain ⟨g1, g2⟩ := hgeo x hx1 hlt
            exact ⟨g1, g2, hlt.le⟩
          refine (large_leaves_le hok (I s) hK1 hK2 _ (by omega) hnz' hform' hreg' hgeo').trans ?_
          linarith
        · have hgeo' : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
              [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b₂) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
            intro x hx
            obtain ⟨hx1, hlt⟩ := hlarge x hx
            obtain ⟨g1, g2⟩ := hgeo x hx1 hlt
            exact ⟨g1, g2, hlt.le⟩
          refine (large_leaves_le hok₂ (I s) hK1 hK2 _ (by omega) hnz' hform' hreg' hgeo').trans ?_
          linarith
        · have hX₁ : (0 : ℝ) < X₁ := by linarith
          have hX₂ : (0 : ℝ) < X₂ := by linarith
          have hcut : ∀ C ∈ [gUp (I s) X₁ false, gDown (I s) X₁ true, gUp (I s)ᶜ X₂ false],
              C.c 0 ≤ Λ₁ * Real.log q := by
            intro C hC
            have h0 : 0 ≤ Λ₁ * Real.log q := by positivity
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
            rcases hC with rfl | rfl | rfl
            · exact hlX₁
            · show -Real.log X₁ ≤ _
              have := Real.log_nonneg hX₁1
              linarith
            · exact hlX₂
          have hform'' : ∀ C ∈ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
              [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))) ++
              [gUp (I s) X₁ false, gDown (I s) X₁ true, gUp (I s)ᶜ X₂ false],
              ∀ x : Fin (j + s) → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
                C.form 0 x ≤ Λ₀ * Real.log q := by
            intro C hC x hx
            rcases List.mem_append.1 hC with hC | hC
            · exact hform' C hC x hx
            · have h1 := SieveP6Split.form_le C 0 (fun i => (hx i).1) (Y := (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ))
                (fun i => by exact_mod_cast (hx i).2)
              have h2 := hcut C hC
              have h3 : ((j + s : ℕ) : ℝ) * Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤
                  (j + smax) * Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ hlogN₂
                push_cast
                have : (s : ℝ) ≤ smax := by exact_mod_cast hs.le
                linarith
              linarith
          have hgeoA : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
              [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
              ∏ i ∈ I s, (x i : ℝ) ≤ X₁ →
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
            intro x hx hle
            obtain ⟨hx1, hlt⟩ := hlarge x hx
            obtain ⟨g1, g2⟩ := hgA x hx1 hlt hle
            exact ⟨g1, g2, hlt.le⟩
          have hgeoB : ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
              [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))),
              X₁ < ∏ i ∈ I s, (x i : ℝ) → ∏ i ∈ (I s)ᶜ, (x i : ℝ) ≤ X₂ →
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
              ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b₂) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
            intro x hx hlt₁ hle₂
            obtain ⟨hx1, hlt⟩ := hlarge x hx
            obtain ⟨g1, g2⟩ := hgB x hx1 hlt hlt₁ hle₂
            exact ⟨g1, g2, hlt.le⟩
          have hfam : RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ (((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
              [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp (j + s) => decide (∃ i, C.e i ≠ 0))) ++
              [gDown (I s) X₁ true, gDown (I s)ᶜ X₂ true]) =
              RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊ ((SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s ++
              [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) ++ [gDown (I s) X₁ true, gDown (I s)ᶜ X₂ true]) := by
            rw [SieveP6Tree.RTg_append, ← h, ← SieveP6Tree.RTg_append]
          have hZ0' : 0 ≤ SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
              (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) := by rw [← hZh]; exact hZh0
          exact SieveLeafSplit.large_leaves_le3 hok hok₂ (I s) hne hnec hK1 hK2 _ hlen' hnz' hX₁ hX₂ hform'' hreg'
            hgeoA hgeoB hZ0' (by rw [hfam]; exact hEs)
    have h3 := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 2 * rm)
    have h4 : 0 ≤ Zh * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
          (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
      mul_nonneg hZh0 (Finset.sum_nonneg fun x _ => by positivity)
    have h5 : 0 ≤ rm * (q : ℝ) ^ (L - 1 - δ') * ∑ x ∈ (RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ E ⌈(q : ℝ) ^ εw⌉₊ z₀ s)).filter
          (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg hrm0 hX0.le) (Finset.sum_nonneg fun x _ => by positivity)
    nlinarith [hsm, hlg, h3, h4, h5]
  · refine Finset.sum_eq_zero fun x hx => ?_
    exfalso
    have hx1 := SieveP6Tree.one_le_of_mem_RTg hx
    obtain ⟨-, ⟨-, hblk⟩, hlo⟩ := (SieveP6Tree.leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
    rw [SieveP6Tree.prod_idxAll] at hlo
    have h1 : (1 : ℝ) ≤ ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := Finset.one_le_prod₀ fun i _ => by exact_mod_cast hx1 _
    have h2 : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd j u) : ℝ) := by
      calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ s = ∏ _u : Fin s, (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => (hblk u).2
    have h3 : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ s := pow_le_pow_right₀ hw1' hs
    have h4 : 0 ≤ ∏ u : Fin s, (x (Fin.natAdd j u) : ℝ) := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    have h5 := mul_le_mul h1 (le_refl (∏ u : Fin s, (x (Fin.natAdd j u) : ℝ))) h4 (by linarith)
    linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h := sum_leaves_inv_le Ω S₀ E hw1 hwz hz₀ smax
    have hZR : 0 ≤ 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
        (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ') := by
      positivity
    exact add_le_add (mul_le_mul_of_nonneg_left h hZR) le_rfl


end SieveLeafSplit
