/-
# The leaves of a family cut in three, for any family

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveLeafSplit.tree_leaves_le3` cuts the leaves of each size of Buchstab's tree in three, for the families of
`SieveP6Tree.leafCmps`. The comparison with the rest among the tree's primes (`SieveFill`) has a second tree, whose
leaves are families of `SieveFillTree.leafCmpsL`. This file states the cut for any family of tuples.

Plain statements. `RTg` is `SieveChain`'s; `LeavesOK` `SieveP6TreeLeaves`'s; `LeavesE` `SieveLeafTwo`'s.

* `Split3F`: `SieveLeafSplit.Split3` for a family `Ω` of `K`-tuples and a set `I` of their indices: `I` and its
  complement not empty, cuts `1 ≤ X₁, X₂ ≤ q^{Λ₁}`, the sizes of `LeavesOK` at `(a, b)` on the large tuples with
  `∏_I x ≤ X₁`, at `(a₂, b₂)` on those with `∏_I x > X₁` and `∏_{Iᶜ} x ≤ X₂`, and the term of the others at most
  `q^{L−δ}/φ(q)`.
* `family_leaves_le3`: **a family's leaves by the paper's lemma at `(a, b)` or at `(a₂, b₂)`, or cut in three**:
  `SieveGap.family_leaves_le` with the large tuples by `SieveP6TreeLeaves.large_leaves_le` at either pair or by
  `SieveLeafSplit.large_leaves_le3`, at the cost `3q^{L−δ}/φ(q)` in place of `q^{L−δ}/φ(q)`.
* `cases3_of_bounds`: **the three cases from bounds of the two sides**: for a family whose tuples have entries at
  least `w = ⌈q^{εw}⌉`, `∏_I x ≤ 4q^{D₁}` and `∏_{Iᶜ} x ≤ 4q^{D₂}`, with the sizes of `LeavesOK` at `(a, b)` for
  `(pA, D₂)` and at `(a₂, b₂)` for `(D₁, th)`, and `LeavesE` on boxes `(AE, BE] ∋ ∏_I x`, `(ArE, BrE] ∋ ∏_{Iᶜ} x` with
  `AE ≤ q^{pA}`, `4q^{D₁} < BE + 1`, `ArE ≤ q^{th}`, `4q^{D₂} < BrE + 1`: its large tuples are by the paper's lemma at
  `(a, b)` (when `I` is empty), at `(a₂, b₂)` (when `Iᶜ` is), or cut in three at `q^{pA}` and `q^{th}` (`Split3F`).

The file imports `SieveGap.lean`, `SieveLeafSplit.lean` and `SieveLeafTwo.lean`.
-/
import SieveGap
import SieveLeafSplit
import SieveLeafTwo

open Real Finset SieveFamily SieveTree SieveChain SieveP6Chain SieveP6Split SieveP6TreeLeaves

namespace SieveLeafFam3

open Classical

/-- `SieveLeafSplit.Split3` for a family `Ω` of `K`-tuples and a set `I` of their indices. -/
def Split3F (q : ℕ) (a' : ZMod q) (L a b a₂ b₂ δ' εw Λ₁ δ : ℝ) (k : ℕ) {K : ℕ} (Ω : List (GCmp K))
    (I : Finset (Fin K)) : Prop :=
  I.Nonempty ∧ Iᶜ.Nonempty ∧ ∃ X₁ X₂ : ℝ, 1 ≤ X₁ ∧ 1 ≤ X₂ ∧ Real.log X₁ ≤ Λ₁ * Real.log q ∧
    Real.log X₂ ≤ Λ₁ * Real.log q ∧
    (∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) → ∏ i ∈ I, (x i : ℝ) ≤ X₁ →
        ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b)) ∧
    (∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) → X₁ < ∏ i ∈ I, (x i : ℝ) → ∏ i ∈ Iᶜ, (x i : ℝ) ≤ X₂ →
        ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b₂)) ∧
    ‖∑ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) ++
        [gDown I X₁ true, gDown Iᶜ X₂ true]),
      ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)

set_option maxHeartbeats 1600000 in
/-- **A family's leaves by the paper's lemma at `(a, b)` or at `(a₂, b₂)`, or cut in three.**
`SieveGap.family_leaves_le` with its large tuples by `LeavesOK` at `(a, b)` or at `(a₂, b₂)`, or split in three
(`Split3F`), at the cost `3q^{L−δ}/φ(q)` in place of `q^{L−δ}/φ(q)`. -/
theorem family_leaves_le3 {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {L a b a₂ b₂ δ' εw Λ₀ Λ₁ C₀ δ : ℝ}
    {k J₀ Kmax : ℕ} (hok : LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax)
    (hok₂ : LeavesOK q a' L a₂ b₂ δ' εw Λ₀ C₀ δ k J₀ Kmax) {j : ℕ} (Ω : List (GCmp j))
    (S₁ : Finset (Fin j)) (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hK : j ≤ Kmax) (hlen : Ω.length + 3 ≤ J₀)
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + j * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i)
    (hcase : (∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b)) ∨
      (∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
        ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b₂)) ∨
      Split3F q a' L a b a₂ b₂ δ' εw Λ₁ δ k Ω S₁)
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ∑ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, x i : ℕ) : ℝ) +
        3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  obtain ⟨hJw, -, -⟩ := SieveProp6.Jw_spec hw2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hlogw : 0 < Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Real.log_pos (by exact_mod_cast hw2)
  have hNN : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
    have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast hN
    linarith
  have hζ0 := SieveProp6.zeta_nonneg hC₀ k
  have hrem0 := SieveProp6.rem_nonneg (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k
  have hX0 : (0 : ℝ) < (q : ℝ) ^ (L - 1 - δ') := by linarith
  have he0 : 0 ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by positivity
  -- the entries of a chain are primes
  have hprime : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∀ i, (x i).Prime := fun x hx i =>
    (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
  obtain ⟨Zh, hZh⟩ : ∃ Zh, Zh = SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) := ⟨_, rfl⟩
  have hZh0 : 0 ≤ Zh := by rw [hZh]; positivity
  have hZ2 : 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) = 2 * Zh := by rw [hZh]; ring
  obtain ⟨rm, hrm⟩ : ∃ rm, rm = SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k :=
    ⟨_, rfl⟩
  have hrm0 : 0 ≤ rm := by rw [hrm]; exact hrem0
  rw [hZ2, ← hrm]
  -- the small chains and the large ones
  rw [← Finset.sum_filter_add_sum_filter_not (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω)
    (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))]
  rw [← Finset.sum_filter_add_sum_filter_not (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω)
    (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')) (fun x => 1 / ((∏ i, x i : ℕ) : ℝ))]
  refine (norm_add_le _ _).trans ?_
  have hsm := small_leaves_le ha' ((RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
      (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))) hw2
    (fun x hx i => ⟨hprime x (Finset.mem_filter.1 hx).1 i, (hreg x (Finset.mem_filter.1 hx).1).2 i⟩) hJw hN hC₀ hC
    hk hk1 hkC
  rw [hZ2, ← hrm] at hsm
  have hcard : (((RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
      (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ'))).card : ℝ) ≤
      (q : ℝ) ^ (L - 1 - δ') * ∑ x ∈ (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
          (fun x => ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hp : (0 : ℝ) < ((∏ i, x i : ℕ) : ℝ) := by
      have := SieveP6Leaves.one_le_prod fun i => hprime x hx1 i
      exact_mod_cast (by omega : 0 < ∏ i, x i)
    rw [mul_one_div, le_div_iff₀ hp]
    push_cast at hx2 ⊢
    linarith
  have hlg : ‖∑ x ∈ (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
      (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      Zh * ∑ x ∈ (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
        (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) +
        3 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
    rw [filter_large_eq _ hX0]
    rcases SieveP6Split.RTg_nz j ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) with h | h
    · rw [h, Finset.sum_empty, Finset.sum_empty, norm_zero, mul_zero, zero_add]
      linarith
    · rw [h, hZh]
      have hK1 : S₁.card ≤ Kmax := le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; exact hK)
      have hK2 : S₁ᶜ.card ≤ Kmax := le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; exact hK)
      have hlen' : ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          fun C : GCmp j => decide (∃ i, C.e i ≠ 0)).length + 2 ≤ J₀ := by
        refine (Nat.add_le_add_right (List.length_filter_le _ _) 2).trans ?_
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hnz' : ∀ C ∈ (Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          (fun C : GCmp j => decide (∃ i, C.e i ≠ 0)), ∃ i, C.e i ≠ 0 :=
        fun C hC => of_decide_eq_true (List.mem_filter.1 hC).2
      have hcΩ : ∀ C ∈ Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true], C.c 0 ≤ Λ₁ * Real.log q := by
        intro C hC
        rcases List.mem_append.1 hC with hC | hC
        · exact hc C hC
        · rw [List.mem_singleton] at hC
          subst hC
          have h1 : 0 ≤ Real.log ((q : ℝ) ^ (L - 1 - δ')) := Real.log_nonneg hX
          have h2 : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
          show -Real.log ((q : ℝ) ^ (L - 1 - δ')) ≤ Λ₁ * Real.log q
          linarith
      have hform' : ∀ C ∈ (Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          (fun C : GCmp j => decide (∃ i, C.e i ≠ 0)),
          ∀ x : Fin j → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) → C.form 0 x ≤ Λ₀ * Real.log q := by
        intro C hC x hx
        have h1 := SieveP6Split.form_le C 0 (fun i => (hx i).1) (Y := (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ))
          (fun i => by exact_mod_cast (hx i).2)
        have h2 := hcΩ C (List.mem_filter.1 hC).1
        linarith
      have hreg' : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))), StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i := by
        intro x hx
        rw [← h, ← filter_large_eq _ hX0] at hx
        exact hreg x (Finset.mem_filter.1 hx).1
      -- a tuple of the large leaves, as a member with `∏x > X`
      have hlarge : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))),
          x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω ∧ (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) := by
        intro x hx
        rw [← h, ← filter_large_eq _ hX0] at hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
        exact ⟨hx1, not_le.1 hx2⟩
      rcases hcase with hgeo | hgeo | ⟨hne, hnec, X₁, X₂, hX₁1, hX₂1, hlX₁, hlX₂, hgA, hgB, hEs⟩
      · have hgeo' : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))),
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
          intro x hx
          obtain ⟨hx1, hlt⟩ := hlarge x hx
          obtain ⟨g1, g2⟩ := hgeo x hx1 hlt
          exact ⟨g1, g2, hlt.le⟩
        refine (large_leaves_le hok S₁ hK1 hK2 _ (by omega) hnz' hform' hreg' hgeo').trans ?_
        linarith
      · have hgeo' : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))),
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b₂) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
          intro x hx
          obtain ⟨hx1, hlt⟩ := hlarge x hx
          obtain ⟨g1, g2⟩ := hgeo x hx1 hlt
          exact ⟨g1, g2, hlt.le⟩
        refine (large_leaves_le hok₂ S₁ hK1 hK2 _ (by omega) hnz' hform' hreg' hgeo').trans ?_
        linarith
      · have hX₁ : (0 : ℝ) < X₁ := by linarith
        have hX₂ : (0 : ℝ) < X₂ := by linarith
        have hcut : ∀ C ∈ [gUp S₁ X₁ false, gDown S₁ X₁ true, gUp S₁ᶜ X₂ false],
            C.c 0 ≤ Λ₁ * Real.log q := by
          intro C hC
          have h0 : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
          rcases hC with rfl | rfl | rfl
          · exact hlX₁
          · show -Real.log X₁ ≤ _
            have := Real.log_nonneg hX₁1
            linarith
          · exact hlX₂
        have hform'' : ∀ C ∈ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter (fun C : GCmp j => decide (∃ i,
            C.e i ≠ 0))) ++
            [gUp S₁ X₁ false, gDown S₁ X₁ true, gUp S₁ᶜ X₂ false],
            ∀ x : Fin j → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) → C.form 0 x ≤ Λ₀ * Real.log q := by
          intro C hC x hx
          rcases List.mem_append.1 hC with hC | hC
          · exact hform' C hC x hx
          · have h1 := SieveP6Split.form_le C 0 (fun i => (hx i).1) (Y := (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ))
              (fun i => by exact_mod_cast (hx i).2)
            have h2 := hcut C hC
            linarith
        have hgeoA : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
            (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))),
            ∏ i ∈ S₁, (x i : ℝ) ≤ X₁ →
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
          intro x hx hle
          obtain ⟨hx1, hlt⟩ := hlarge x hx
          obtain ⟨g1, g2⟩ := hgA x hx1 hlt hle
          exact ⟨g1, g2, hlt.le⟩
        have hgeoB : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
            (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))),
            X₁ < ∏ i ∈ S₁, (x i : ℝ) → ∏ i ∈ S₁ᶜ, (x i : ℝ) ≤ X₂ →
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
              ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
                ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b₂) ∧
              (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
          intro x hx hlt₁ hle₂
          obtain ⟨hx1, hlt⟩ := hlarge x hx
          obtain ⟨g1, g2⟩ := hgB x hx1 hlt hlt₁ hle₂
          exact ⟨g1, g2, hlt.le⟩
        have hfam : RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
            (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))) ++
            [gDown S₁ X₁ true, gDown S₁ᶜ X₂ true]) =
            RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) ++
              [gDown S₁ X₁ true, gDown S₁ᶜ X₂ true]) := by
          rw [SieveP6Tree.RTg_append, ← h, ← SieveP6Tree.RTg_append]
        have hZ0' : 0 ≤ SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
            (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) := by rw [← hZh]; exact hZh0
        exact SieveLeafSplit.large_leaves_le3 hok hok₂ S₁ hne hnec hK1 hK2 _ hlen' hnz' hX₁ hX₂ hform'' hreg'
          hgeoA hgeoB hZ0' (by rw [hfam]; exact hEs)
  have h3 := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 2 * rm)
  have h4 : 0 ≤ Zh * ∑ x ∈ (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
      (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
    mul_nonneg hZh0 (Finset.sum_nonneg fun x _ => by positivity)
  have h5 : 0 ≤ rm * (q : ℝ) ^ (L - 1 - δ') * ∑ x ∈ (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
      (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
    mul_nonneg (mul_nonneg hrm0 hX0.le) (Finset.sum_nonneg fun x _ => by positivity)
  nlinarith [hsm, hlg, h3, h4, h5]

set_option maxHeartbeats 800000 in
/-- **The three cases from bounds of the two sides.** For a family of `K`-tuples whose members have entries at least
`w = ⌈q^{εw}⌉`, `∏_I x ≤ 4q^{D₁}` and `∏_{Iᶜ} x ≤ 4q^{D₂}`, with the sizes of `LeavesOK` at `(a, b)` for
`(pA, D₂)` and at `(a₂, b₂)` for `(D₁, th)`, and `LeavesE` on boxes with `AE ≤ q^{pA}`, `4q^{D₁} < BE + 1`,
`ArE ≤ q^{th}` and `4q^{D₂} < BrE + 1`: the large tuples have the sizes at `(a, b)` (when `I` is empty), at
`(a₂, b₂)` (when its complement is), or are cut in three at `q^{pA}` and `q^{th}`. -/
theorem cases3_of_bounds {q : ℕ} [NeZero q] {a' : ZMod q} {L a b a₂ b₂ δ' εw Λ₁ δl c pA th D₁ D₂ : ℝ}
    {k J₀E K₀E AE BE ArE BrE : ℕ}
    (hokE : SieveLeafTwo.LeavesE q a' L Λ₁ δl J₀E K₀E ⌈(q : ℝ) ^ εw⌉₊ AE BE ArE BrE) {K : ℕ} (Ω : List (GCmp K))
    (I : Finset (Fin K)) (hK : K ≤ K₀E) (hlen : Ω.length + 3 ≤ J₀E) (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ'))
    (hbd : ∀ x : Fin K → ℕ, (∀ i, (x i).Prime) → (∀ C ∈ Ω, C.holds 0 x) →
      (∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i) ∧ ∏ i ∈ I, (x i : ℝ) ≤ 4 * (q : ℝ) ^ D₁ ∧
        ∏ i ∈ Iᶜ, (x i : ℝ) ≤ 4 * (q : ℝ) ^ D₂)
    (hwpow : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c)
    (hpA : 0 ≤ pA) (hpAΛ : pA ≤ Λ₁) (hth : 0 ≤ th) (hthΛ : th ≤ Λ₁)
    (hszA₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - pA - c))
    (hszA₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - pA - 2 * D₂ - c))
    (hszB₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂ - D₁ - c))
    (hszB₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b₂ - D₁ - 2 * th - c))
    (hAE : (AE : ℝ) ≤ (q : ℝ) ^ pA) (hBE : 4 * (q : ℝ) ^ D₁ < BE + 1)
    (hArE : (ArE : ℝ) ≤ (q : ℝ) ^ th) (hBrE : 4 * (q : ℝ) ^ D₂ < BrE + 1) :
    (∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
          ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) ^ 2 ≤
            (q : ℝ) ^ (L - b)) ∨
      (∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
          ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) ^ 2 ≤
            (q : ℝ) ^ (L - b₂)) ∨
      Split3F q a' L a b a₂ b₂ δ' εw Λ₁ δl k Ω I := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hw0 : (0 : ℝ) ≤ ⌈(q : ℝ) ^ εw⌉₊ := Nat.cast_nonneg _
  have hX₁ : (1 : ℝ) ≤ (q : ℝ) ^ pA := Real.one_le_rpow hq1 hpA
  have hX₂ : (1 : ℝ) ≤ (q : ℝ) ^ th := Real.one_le_rpow hq1 hth
  have hmem : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (∀ i, (x i).Prime) ∧ ∀ C ∈ Ω, C.holds 0 x := fun x hx =>
    ⟨fun i => (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2,
      (Finset.mem_filter.1 hx).2⟩
  -- the first part's sizes, `∏_I x ≤ q^{pA}`, and the second's, `∏_{Iᶜ} x ≤ q^{th}`
  have hA : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i,
      x i : ℕ) : ℝ) → ∏ i ∈ I, (x i : ℝ) ≤ (q : ℝ) ^ pA →
      ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
          ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) ^ 2 ≤
            (q : ℝ) ^ (L - b) := by
    intro x hx _ hle
    obtain ⟨-, -, hIc'⟩ := hbd x (hmem x hx).1 (hmem x hx).2
    push_cast
    exact SieveP6ib.leaf_sizes_num hq0 (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) (by linarith) hIc' hw0
      hwpow hszA₁ hszA₂
  have hB : ∀ x ∈ RTg K ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i,
      x i : ℕ) : ℝ) → ∏ i ∈ Iᶜ, (x i : ℝ) ≤ (q : ℝ) ^ th →
      ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a₂) ∧
          ((∏ i ∈ I, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) ^ 2 ≤
            (q : ℝ) ^ (L - b₂) := by
    intro x hx _ hle
    obtain ⟨-, hI', -⟩ := hbd x (hmem x hx).1 (hmem x hx).2
    push_cast
    exact SieveP6ib.leaf_sizes_num hq0 (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) hI' (by linarith) hw0
      hwpow hszB₁ hszB₂
  -- a side with no index: all the tuples in the first part, or all in the second
  by_cases h1 : I.Nonempty
  swap
  · left
    intro x hx hlt
    refine hA x hx hlt ?_
    rw [Finset.not_nonempty_iff_eq_empty.1 h1, Finset.prod_empty]
    exact hX₁
  by_cases h2 : Iᶜ.Nonempty
  swap
  · right
    left
    intro x hx hlt
    refine hB x hx hlt ?_
    rw [Finset.not_nonempty_iff_eq_empty.1 h2, Finset.prod_empty]
    exact hX₂
  right
  right
  refine ⟨h1, h2, (q : ℝ) ^ pA, (q : ℝ) ^ th, hX₁, hX₂, ?_, ?_, fun x hx hlt hle => hA x hx hlt hle,
    fun x hx hlt _ hle => hB x hx hlt hle, ?_⟩
  · rw [Real.log_rpow hq0]
    exact mul_le_mul_of_nonneg_right hpAΛ hlogq
  · rw [Real.log_rpow hq0]
    exact mul_le_mul_of_nonneg_right hthΛ hlogq
  -- the third part, by `LeavesE`
  have hlen' : ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) ++
      [gDown I ((q : ℝ) ^ pA) true, gDown Iᶜ ((q : ℝ) ^ th) true]).length ≤ J₀E := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  refine hokE K hK I Iᶜ _ disjoint_compl_right h2 hlen' ?_ ?_
  · intro C hC
    have h0 : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
    rcases List.mem_append.1 hC with hC | hC
    · rcases List.mem_append.1 hC with hC | hC
      · exact hc C hC
      · rw [List.mem_singleton] at hC
        subst hC
        show -Real.log ((q : ℝ) ^ (L - 1 - δ')) ≤ _
        have := Real.log_nonneg hX
        linarith
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
      rcases hC with rfl | rfl
      · show -Real.log ((q : ℝ) ^ pA) ≤ _
        have := Real.log_nonneg hX₁
        linarith
      · show -Real.log ((q : ℝ) ^ th) ≤ _
        have := Real.log_nonneg hX₂
        linarith
  · intro x hprime hholds
    have hx1 : ∀ i, 1 ≤ x i := fun i => (hprime i).one_lt.le
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true] at hholds
    obtain ⟨⟨hΩ, -⟩, hcut₁, hcut₂⟩ := hholds
    obtain ⟨hwx, hI', hIc'⟩ := hbd x hprime hΩ
    rw [gDown_holds _ (by linarith) true 0 hx1] at hcut₁ hcut₂
    simp only [ite_true] at hcut₁ hcut₂
    refine ⟨hwx, ?_, ?_, ?_, ?_⟩
    · have : (AE : ℝ) < ((∏ i ∈ I, x i : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((∏ i ∈ I, x i : ℕ) : ℝ) < (BE : ℝ) + 1 := by push_cast; linarith
      exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
    · have : (ArE : ℝ) < ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) < (BrE : ℝ) + 1 := by push_cast; linarith
      exact Nat.lt_succ_iff.1 (by exact_mod_cast this)

end SieveLeafFam3
