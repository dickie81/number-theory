/-
# Brun's sieve at a fixed level on a family of chains

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `GCmp`, `RTg` are `SieveChain`'s; `LeavesOK`, `large_leaves_le`, `small_leaves_le` are
`SieveP6TreeLeaves`'s; `rough z n` is `SieveTree`'s; `zeta`, `rem` and `Jw` are `SieveProp6`'s. `N₁ = ⌊q^L⌋`,
`N₂ = ⌊2q^L⌋` and `w = ⌈q^{εw}⌉`.

Harman's comparison evaluates `Σ_r S(A_r, z₀)` by a tree over the primes between a level `w` and `z₀`, and its
leaves, the terms `S(A_d, w)`, by Brun's sieve: `SieveP6TreeLeaves.tree_leaves_le`. There the level falls as the
error asked for shrinks. Here there is no tree and the level is fixed: the family's own terms at the level `w`.

* `family_leaves_le`: for a family `RTg j N₂ Ω` of strictly decreasing chains with entries at least `w ≥ 2`, split
  into the blocks `S₁` and `S₁ᶜ` with the sizes of `SieveP6Leaves.leaves_chain` at the chains with `∏x > q^{L−1−δ'}`:
  `|Σ_x (S(A_x, w) − S(B_x, w)/φ(q))|` is at most
  `(2ζ(k)(N₂ − N₁)/(φ(q) log w) + 2·rem·q^{L−1−δ'})·Σ_x 1/∏x + q^{L−δ}/φ(q)`.
  The chains with `∏x ≤ q^{L−1−δ'}` by `small_leaves_le`, the others by `large_leaves_le` after the comparisons that
  are constant are dropped.

With the sums of `1/p` over the ranges at most `3` (`SieveRanges.rng_sum_le_three`), `ζ(k)` is a number, and the
bound is the cost of a term at the least level that a sieve without the window sifts to.

The file imports `SieveP6LeavesWide.lean` and `SieveRangeSum.lean`.
-/
import SieveP6LeavesWide
import SieveRangeSum

open Real Finset SieveFamily SieveTree SieveChain SieveP6Chain SieveP6Split SieveP6TreeLeaves

namespace SieveGap

open Classical

/-- **A family of chains at a fixed level.** At `w = ⌈q^{εw}⌉ ≥ 2`, for a family `RTg j N₂ Ω` of strictly
decreasing tuples with entries at least `w` (at most `J₀ − 1` comparisons, with `m`-parts at most `Λ₁ log q`, and
`Λ₁ log q + j log N₂ ≤ Λ₀ log q`), whose chains with `∏x > q^{L−1−δ'}` split into the blocks `S₁` and `S₁ᶜ` with the
sizes of `leaves_chain`: the terms at the level `w` total at most
`(2ζ(k)(N₂ − N₁)/(φ(q) log w) + 2·rem·q^{L−1−δ'})·Σ_x 1/∏x + q^{L−δ}/φ(q)`. -/
theorem family_leaves_le {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {L a b δ' εw Λ₀ Λ₁ C₀ δ : ℝ}
    {k J₀ Kmax : ℕ} (hok : LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax) {j : ℕ} (Ω : List (GCmp j))
    (S₁ : Finset (Fin j)) (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hK : j ≤ Kmax) (hlen : Ω.length + 1 ≤ J₀)
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + j * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i)
    (hgeo : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
      ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
      ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
        (q : ℝ) ^ (L - b))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ∑ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, x i : ℕ) : ℝ) +
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
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
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
    rw [filter_large_eq _ hX0]
    rcases SieveP6Split.RTg_nz j ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]) with h | h
    · rw [h, Finset.sum_empty, Finset.sum_empty, norm_zero, mul_zero, zero_add]
      exact he0
    · rw [h, hZh]
      have hK1 : S₁.card ≤ Kmax := le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; exact hK)
      have hK2 : S₁ᶜ.card ≤ Kmax := le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin]; exact hK)
      have hlen' : ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          fun C : GCmp j => decide (∃ i, C.e i ≠ 0)).length ≤ J₀ := by
        refine (List.length_filter_le _ _).trans ?_
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
      have hgeo' : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ ((Ω ++ [gDown univ ((q : ℝ) ^ (L - 1 - δ')) true]).filter
          (fun C : GCmp j => decide (∃ i, C.e i ≠ 0))),
          ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
          ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) *
            ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) ∧
          (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, x i : ℕ) : ℝ) := by
        intro x hx
        rw [← h, ← filter_large_eq _ hX0] at hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
        have hlt := not_le.1 hx2
        obtain ⟨g1, g2⟩ := hgeo x hx1 hlt
        exact ⟨g1, g2, hlt.le⟩
      exact large_leaves_le hok S₁ hK1 hK2 _ hlen' hnz' hform' hreg' hgeo'
  have h3 := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 2 * rm)
  have h4 : 0 ≤ Zh * ∑ x ∈ (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
      (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
    mul_nonneg hZh0 (Finset.sum_nonneg fun x _ => by positivity)
  have h5 : 0 ≤ rm * (q : ℝ) ^ (L - 1 - δ') * ∑ x ∈ (RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω).filter
      (fun x => ¬ ((∏ i, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (L - 1 - δ')), 1 / ((∏ i, x i : ℕ) : ℝ) :=
    mul_nonneg (mul_nonneg hrm0 hX0.le) (Finset.sum_nonneg fun x _ => by positivity)
  nlinarith [hsm, hlg, h3, h4, h5]

end SieveGap

#print axioms SieveGap.family_leaves_le
