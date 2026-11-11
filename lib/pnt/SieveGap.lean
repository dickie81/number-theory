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

/-- **Brun's sieve at a fixed level, for a family in boxes, at large `q`.** Let `L > 2`, a level `εw > 0` and an
even `k ≥ 4`, with `(2k + 7)εw < δ' ≤ 1/16`, `s ≥ 0` and `5δ' + s ≤ L − 2`. Let `hi` bound the exponents of a
family's entries and `S₁` split them into two blocks with
`Σ_{S₁} hi + (2k + 4)εw + 5δ' + s < L − 1` and `Σ_{S₁} hi + 2Σ_{S₁ᶜ} hi + (2k + 4)εw < L + s`. There are `δ > 0`
and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: for the `j`-tuples of primes up to `⌊2q^L⌋` that satisfy at
most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q`) forcing them strictly decreasing with
`⌈q^{εw}⌉ ≤ rt_i ≤ q^{hi_i}`, the terms at the level `w = ⌈q^{εw}⌉` in `A` minus the comparison set total at most
`2ζ(k)(N₂ − N₁)/(φ(q) log w)·Σ_{rt} 1/∏rt + q^{L−δ}/φ(q)`, with `ζ(k) = SieveProp6.zeta 3 k`. -/
theorem gap_at {L : ℝ} (hL2 : 2 < L) (j J₀ : ℕ) {Λ₁ εw δ' s : ℝ} (hΛ₁ : 0 ≤ Λ₁) (hεw : 0 < εw)
    (hεwL : εw ≤ L + 1) {k : ℕ} (hk : Even k) (hk4 : 4 ≤ k) (hlvl : ((2 * k + 7 : ℕ) : ℝ) * εw < δ')
    (hδ16 : δ' ≤ 1 / 16) (hs : 0 ≤ s) (hsL : 5 * δ' + s ≤ L - 2) (hi : Fin j → ℝ) (S₁ : Finset (Fin j))
    (h1 : ∑ i ∈ S₁, hi i + ((2 * k + 4 : ℕ) : ℝ) * εw + 5 * δ' + s < L - 1)
    (h2 : ∑ i ∈ S₁, hi i + 2 * ∑ i ∈ S₁ᶜ, hi i + ((2 * k + 4 : ℕ) : ℝ) * εw < L + s) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ Ω : List (GCmp j), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ rt i) ∧ ∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) →
      ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
          dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
        2 * SieveProp6.zeta 3 k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
            (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) *
          ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) +
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  have hL0 : 0 < L := by linarith
  have hδ'0 : 0 < δ' := lt_of_le_of_lt (by positivity) hlvl
  have hk4' : (4 : ℝ) ≤ k := by exact_mod_cast hk4
  have hkC : 2 * (3 : ℝ) ^ 2 ≤ ((k : ℝ) + 1) * (k + 2) := by nlinarith
  obtain ⟨c₄, hc₄⟩ : ∃ c₄ : ℝ, c₄ = ((2 * k + 4 : ℕ) : ℝ) * εw := ⟨_, rfl⟩
  obtain ⟨c₇, hc₇⟩ : ∃ c₇ : ℝ, c₇ = ((2 * k + 7 : ℕ) : ℝ) * εw := ⟨_, rfl⟩
  rw [← hc₄] at h1 h2
  rw [← hc₇] at hlvl
  have hc₄7 : c₄ ≤ c₇ := by
    rw [hc₄, hc₇]
    refine mul_le_mul_of_nonneg_right ?_ hεw.le
    push_cast
    linarith
  have hεwk : (2 * (k : ℝ) + 4) * εw ≤ 1 / 16 := by
    have : (2 * (k : ℝ) + 4) * εw = c₄ := by rw [hc₄]; push_cast; ring
    rw [this]
    linarith
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = ∑ i ∈ S₁, hi i := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℝ, D₂ = ∑ i ∈ S₁ᶜ, hi i := ⟨_, rfl⟩
  rw [← hD₁] at h1 h2
  rw [← hD₂] at h2
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : ℝ, g₁ = L - 1 - (5 * δ' + s) - D₁ - c₄ := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : ℝ, g₂ = L + s - D₁ - 2 * D₂ - c₄ := ⟨_, rfl⟩
  obtain ⟨g₃, hg₃⟩ : ∃ g₃ : ℝ, g₃ = δ' - c₇ := ⟨_, rfl⟩
  have hg₁0 : 0 < g₁ := by rw [hg₁]; linarith
  have hg₂0 : 0 < g₂ := by rw [hg₂]; linarith
  have hg₃0 : 0 < g₃ := by rw [hg₃]; linarith
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = (Real.log (L + 1) - Real.log εw + 1) ^ j := ⟨_, rfl⟩
  have hlogpos : 0 ≤ Real.log (L + 1) - Real.log εw + 1 := by
    have := Real.log_le_log hεw hεwL
    linarith
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁def]; exact pow_nonneg hlogpos j
  -- the leaves
  obtain ⟨δ₃, hδ₃, q₁, hq₁⟩ := SieveP6LeavesWide.leavesOK_wide hL2 (a := 5 * δ' + s) (c := s) (δ' := δ')
    (κ := 4 * δ') (εw := εw) (Λ₀ := Λ₁ + j * (L + 1)) hδ'0.le hsL (by positivity) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) hεw (by positivity) j (J₀ + 1) (C₀ := 3) (by norm_num)
    (fun A hA => SieveRanges.rng_sum_le_three hA) hk (by omega) hkC hεwk
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₃ (g₃ / 2) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    have : 0 < min δ₃ (g₃ / 2) := lt_min hδ₃ (by linarith)
    linarith
  have hδ3 : 2 * δ ≤ δ₃ := by rw [hδdef]; linarith [min_le_left δ₃ (g₃ / 2)]
  have hδ4 : 2 * δ ≤ g₃ / 2 := by rw [hδdef]; linarith [min_le_right δ₃ (g₃ / 2)]
  -- the conditions that hold for large `q`
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 3 ≤ x ∧ 2 ≤ x ^ εw ∧
      ∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ (L + 1 : ℝ)), 1 / (p : ℝ) ≤ Real.log (L + 1) - Real.log εw + 1 ∧
      (2 : ℝ) ^ (2 * k + 4) ≤ x ^ g₁ ∧ (2 : ℝ) ^ (2 * k + 4) ≤ x ^ g₂ ∧
      24 * 2 ^ (2 * k + 7) * K₁ ≤ x ^ (g₃ / 2) ∧ 2 ≤ x ^ δ :=
    (Filter.eventually_ge_atTop 3).and (((tendsto_rpow_atTop hεw).eventually_ge_atTop _).and
      ((SieveRough.evLe_sum_inv hεw hεwL 1 one_pos).and
      (((tendsto_rpow_atTop hg₁0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hg₂0).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith : 0 < g₃ / 2)).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop hδ0).eventually_ge_atTop _))))))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨δ, hδ0, max q₁ ⌈x₀⌉₊, ?_⟩
  intro q _ hq a ha Ω hΩlen hΩc hΩ
  have hqx : x₀ ≤ (q : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right _ _).trans hq)
  obtain ⟨hx3, hxw, hM2, hG1, hG2, hG3, hGδ⟩ := hx₀ q hqx
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hw : (q : ℝ) ^ εw ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Nat.le_ceil _
  have hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊ := by
    have : (2 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := hxw.trans hw
    exact_mod_cast this
  have hw1 : (1 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := by
    have : (2 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := by exact_mod_cast hw2
    linarith
  have hw0 : (0 : ℝ) < (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := by linarith
  have hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (q : ℝ) ^ εw by positivity)
    linarith
  have hwpow : ∀ n : ℕ, (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ n ≤ 2 ^ n * (q : ℝ) ^ ((n : ℝ) * εw) := by
    intro n
    calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ n ≤ (2 * (q : ℝ) ^ εw) ^ n := pow_le_pow_left₀ hw0.le hwle n
      _ = 2 ^ n * ((q : ℝ) ^ εw) ^ n := mul_pow _ _ _
      _ = 2 ^ n * (q : ℝ) ^ ((n : ℝ) * εw) := by
        rw [← Real.rpow_natCast ((q : ℝ) ^ εw) n, ← Real.rpow_mul hq0.le, mul_comm εw (n : ℝ)]
  have hxL1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 hL0.le
  have hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := Nat.floor_mono (by linarith)
  have hN₂le : (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have h2L : 2 * (q : ℝ) ^ L < (q : ℝ) ^ (L + 1 : ℝ) := by
    have hX0 : 0 < (q : ℝ) ^ L := by positivity
    rw [Real.rpow_add hq0, Real.rpow_one]
    have := mul_lt_mul_of_pos_left (show (2 : ℝ) < q by linarith) hX0
    linarith
  have hN₂1 : (1 : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by
    have : 1 ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hlogN₂ : Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ (L + 1) * Real.log q := by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log (by linarith) (hN₂le.trans h2L.le)
  have hΛ : Λ₁ * Real.log q + j * Real.log (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) ≤ (Λ₁ + j * (L + 1)) * Real.log q := by
    have h := mul_le_mul_of_nonneg_left hlogN₂ (Nat.cast_nonneg (α := ℝ) j)
    have e : (Λ₁ + j * (L + 1)) * Real.log q = Λ₁ * Real.log q + j * ((L + 1) * Real.log q) := by ring
    rw [e]
    linarith
  have hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ') := Real.one_le_rpow hq1 (by linarith)
  -- the chains
  have hprime : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∀ i, rt i ≤ ⌊2 * (q : ℝ) ^ L⌋₊ ∧ (rt i).Prime :=
    fun rt hrt i => SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)
  have hreg : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, StrictAnti x ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ x i := by
    intro x hx
    obtain ⟨h1', h2', -⟩ := hΩ x (fun i => (hprime x hx i).2) (Finset.mem_filter.1 hx).2
    exact ⟨h1', h2'⟩
  have hprodle : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∀ T : Finset (Fin j),
      ((∏ i ∈ T, x i : ℕ) : ℝ) ≤ (q : ℝ) ^ (∑ i ∈ T, hi i) := by
    intro x hx T
    obtain ⟨-, -, h3'⟩ := hΩ x (fun i => (hprime x hx i).2) (Finset.mem_filter.1 hx).2
    rw [Nat.cast_prod, Real.rpow_sum_of_pos hq0]
    exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => h3' i
  have hgeo : ∀ x ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
      ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - (5 * δ' + s)) ∧
      ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
        (q : ℝ) ^ (L - -s) := by
    intro x hx _
    have hA := hprodle x hx S₁
    have hB := hprodle x hx S₁ᶜ
    rw [← hD₁] at hA
    rw [← hD₂] at hB
    have hW := hwpow (2 * k + 4)
    rw [← hc₄] at hW
    have hA0 : (0 : ℝ) ≤ ((∏ i ∈ S₁, x i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) ≤ ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hWW : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ g₁ * (q : ℝ) ^ c₄ :=
      hW.trans (mul_le_mul_of_nonneg_right hG1 (by positivity))
    have hWW2 : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ g₂ * (q : ℝ) ^ c₄ :=
      hW.trans (mul_le_mul_of_nonneg_right hG2 (by positivity))
    constructor
    · calc ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4)
          ≤ (q : ℝ) ^ D₁ * ((q : ℝ) ^ g₁ * (q : ℝ) ^ c₄) :=
            mul_le_mul hA hWW (by positivity) (by positivity)
        _ = (q : ℝ) ^ (L - 1 - (5 * δ' + s)) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, hg₁]
          congr 1
          ring
    · have hB2 : ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2 ≤ ((q : ℝ) ^ D₂) ^ 2 := pow_le_pow_left₀ hB0 hB 2
      calc ((∏ i ∈ S₁, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ S₁ᶜ, x i : ℕ) : ℝ) ^ 2
          ≤ (q : ℝ) ^ D₁ * ((q : ℝ) ^ g₂ * (q : ℝ) ^ c₄) * ((q : ℝ) ^ D₂) ^ 2 :=
            mul_le_mul (mul_le_mul hA hWW2 (by positivity) (by positivity)) hB2 (by positivity) (by positivity)
        _ = (q : ℝ) ^ (L - -s) := by
          rw [← Real.rpow_natCast ((q : ℝ) ^ D₂) 2, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0,
            ← Real.rpow_add hq0, ← Real.rpow_add hq0, hg₂]
          congr 1
          push_cast
          ring
  have hmain := family_leaves_le ha (hq₁ q ((le_max_left _ _).trans hq) a ha) Ω S₁ hw2 (le_refl j)
    (by omega : Ω.length + 1 ≤ J₀ + 1) hΛ₁ hΩc hΛ hX hN hreg hgeo (by norm_num : (0 : ℝ) ≤ 3)
    (fun A hA => SieveRanges.rng_sum_le_three hA) hk (by omega) hkC
  -- the sum of `1/∏rt`
  have hsRT : ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ K₁ := by
    refine (SieveProp6.sum_RT_inv_le (s := SieveRough.primesIn ((q : ℝ) ^ εw) ((q : ℝ) ^ (L + 1 : ℝ))) ?_).trans ?_
    · intro rt hrt
      rw [Fintype.mem_piFinset]
      intro i
      rw [SieveRough.mem_primesIn]
      refine ⟨(hprime rt hrt i).2, hw.trans (by exact_mod_cast (hreg rt hrt).2 i), ?_⟩
      have h1' : (rt i : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast (hprime rt hrt i).1
      linarith
    · rw [hK₁def]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => by positivity) hM2 j
  have hS0 : 0 ≤ ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) :=
    Finset.sum_nonneg fun rt _ => by positivity
  -- the remainder
  obtain ⟨hJw, hJ2, hJ3⟩ := SieveProp6.Jw_spec hw2
  have hrem : SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k ≤
      12 * (2 ^ (2 * k + 7) * (q : ℝ) ^ c₇) := by
    refine (SieveProp6.rem_le hw1 _ k).trans ?_
    rw [Real.rpow_natCast]
    have hW7 := hwpow (2 * k + 7)
    rw [← hc₇] at hW7
    have h0 : (0 : ℝ) ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) := by positivity
    have hJ0 : (0 : ℝ) ≤ (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊ : ℝ) + 1 := by positivity
    calc ((SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊ : ℝ) + 1) * 2 ^ SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊ *
          (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4)
        ≤ (3 * (⌈(q : ℝ) ^ εw⌉₊ : ℝ)) * (4 * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ 2) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hJ3 hJ2 (by positivity) (by positivity)) h0
      _ = 12 * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 7) := by ring
      _ ≤ 12 * (2 ^ (2 * k + 7) * (q : ℝ) ^ c₇) := mul_le_mul_of_nonneg_left hW7 (by norm_num)
  have hremterm : 2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k *
      (q : ℝ) ^ (L - 1 - δ') * ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - g₃ / 2) := by
    have hrem0 := SieveProp6.rem_nonneg (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k
    have hXp : (0 : ℝ) < (q : ℝ) ^ (L - 1 - δ') := by positivity
    calc 2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k *
          (q : ℝ) ^ (L - 1 - δ') * ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)
        ≤ 2 * (12 * (2 ^ (2 * k + 7) * (q : ℝ) ^ c₇)) * (q : ℝ) ^ (L - 1 - δ') * K₁ :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrem (by norm_num)) hXp.le) hsRT hS0
            (by positivity)
      _ = (24 * 2 ^ (2 * k + 7) * K₁) * ((q : ℝ) ^ c₇ * (q : ℝ) ^ (L - 1 - δ')) := by ring
      _ ≤ (q : ℝ) ^ (g₃ / 2) * ((q : ℝ) ^ c₇ * (q : ℝ) ^ (L - 1 - δ')) :=
          mul_le_mul_of_nonneg_right hG3 (by positivity)
      _ = (q : ℝ) ^ (-1 : ℝ) * (q : ℝ) ^ (L - g₃ / 2) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0, hg₃]
          congr 1
          ring
      _ ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - g₃ / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Real.rpow_neg_one]
          exact inv_anti₀ hφ hφq
  -- the two errors
  have herr : (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - g₃ / 2) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃) ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
    have hφi : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
    have e1 : (q : ℝ) ^ (L - g₃ / 2) ≤ (q : ℝ) ^ (L - 2 * δ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have e2 : (q : ℝ) ^ (L - δ₃) ≤ (q : ℝ) ^ (L - 2 * δ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have e3 : 2 * (q : ℝ) ^ (L - 2 * δ) ≤ (q : ℝ) ^ (L - δ) := by
      calc 2 * (q : ℝ) ^ (L - 2 * δ) ≤ (q : ℝ) ^ δ * (q : ℝ) ^ (L - 2 * δ) :=
            mul_le_mul_of_nonneg_right hGδ (by positivity)
        _ = (q : ℝ) ^ (L - δ) := by rw [← Real.rpow_add hq0]; congr 1; ring
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) hφi
  refine hmain.trans ?_
  rw [add_mul]
  linarith

end SieveGap

#print axioms SieveGap.family_leaves_le
#print axioms SieveGap.gap_at
