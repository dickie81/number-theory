/-
# The comparison in two variables with the rest among the tree's primes, at one modulus

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoP6.prop6_two_core` evaluates `Σ_r S(A_r, z₀)` over a family of chains by Buchstab's tree over the primes
below `z₀`, stopped when the first variable's product enters its window; the rest of the estimate in two variables
is a product of the family's own primes. This file is for a family with no such primes: a stop of that tree is not
evaluated but sifted further, by the tree below its last prime (`SieveFillTree.tree_last`), whose primes are the
rest, until their product reaches a threshold.

Plain statements. `GCmp`, `RTg` are `SieveChain`'s; `leafCmpsL`, `stopCmpsL` `SieveFillTree`'s; `ChainOK2`
`SieveTwoP6`'s; `LeavesOK` `SieveP6TreeLeaves`'s; `rough z n` and `primesIco w z` `SieveTree`'s; `zeta`, `rem` and `Jw`
`SieveProp6`'s. `L` is a route's (`SieveRoute.Route`), `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋` and `w = ⌈q^{εw}⌉`.

* `leaves_last_le`: the leaves of the tree below the last entry, by `SieveGap.family_leaves_le` at each size.
* `stops_last_le`: the stops of the tree below the last entry at `E = Ar + 1`, by `ChainOK2`: the first variable is
  the family's, on a set `S` with `A < ∏_S rt ≤ B`, and the rest is the tree's block, in `(Ar, (Ar + 1)z_b)` when
  the family's last entries are at most `z_b`.
* `last_pattern_le`: **a family sifted at its last entry, with the first variable in its window**: the two
  together.
* `stops_rest_le`: the stops of a tree from the level `z₀` with the rule `Ar + 1 ≤ ∏P`, by `ChainOK2` with the
  tree's block as the rest and the first variable the family's.
* `sum_stops_inv_le`: over the stops of a tree, `Σ 1/d ≤ (Σ_{rt} 1/r)∏_{p∈[w,z₀)}(1 + 1/p)`.
* `leaf_blocks2_le`, `sizes_of_blocks`: the sizes of the two blocks of a leaf with two blocks of new primes.
* `fill_below_ib`: **a family below the window.** The tree to the window; its leaves by
  `SieveP6TreeLeaves.tree_leaves_le`, and each of its stops by `last_pattern_le`.
* `fill_window_ib`: **a family in the window.** The tree with the rule `Ar + 1 ≤ ∏P` from the level `z₀`; its
  leaves by `tree_leaves_le` and its stops by `stops_rest_le`.
* `prop6_fill_core`: **the comparison at one `q`.** For a family in boxes `q^{lo_i} ≤ rt_i ≤ q^{hi_i}`, strictly
  decreasing with entries at least `z₀`, with `(P₁ + 1)z₀ ≤ P₂`, `(Ar + 1)z₀ ≤ Br`, `q^{Σ_{S₀} hi} ≤ P₂`,
  `P₁ + 1 ≤ 4q^t·q^{Σ_{S₀} lo}` and `4q^t·z₀·(Ar + 1) ≤ 4q^T`: the family splits by `c = ∏_{S₀} rt ≤ P₁` and
  `P₁ < c`, and `|Σ_r (S(A_r, z₀) − S(B_r, z₀)/φ(q))|` is at most the leaves' main term and remainder, with the
  sums of `1/d` over them at most `(Σ_{rt} 1/r)∏_{[w,z₀)}(1 + 1/p)·(1 + ∏_{[w,N₂]}(1 + 1/p))`, plus
  `(2s_max + s_max²)q^{L−δ₃}/φ(q) + (s_max² + s_max)q^{L−δ₁}/φ(q)`.

The file imports `SieveTwoP6.lean`, `SieveGap.lean` and `SieveFillTree.lean`.
-/
import SieveTwoP6
import SieveGap
import SieveFillTree

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain SieveP6Tree SieveP6ib SieveTwoP6
  SieveFillTree

namespace SieveFill

open Classical

variable [Route]

/-! ### The leaves of the tree below the last entry -/

/-- **The leaves of the tree below the last entry.** At `w = ⌈q^{εw}⌉ ≥ 2`, with the rule `E ≤ ∏P`,
`1 < E ≤ w^{s_max}`: for a family `RTg (k′ + 1) N₂ Ω` of strictly decreasing tuples with entries at least `w`, split
each leaf `x` of size `s` with `∏x > X = q^{L−1−δ'}` into the blocks `I_s` and `I_sᶜ` with the sizes of
`leaves_chain`. Then the leaves (with the signs `(−1)^s`) total at most
`(2ζ(k)(N₂ − N₁)/(φ(q) log w) + 2·rem·X)(Σ_{rt} 1/r)∏_{p∈[w,N₂]}(1 + 1/p) + s_max·q^{L−δ}/φ(q)`. -/
theorem leaves_last_le {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δ E : ℝ}
    {k J₀ Kmax : ℕ} (hok : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δ k J₀ Kmax) {k' : ℕ}
    (Ω : List (GCmp (k' + 1))) (I : ∀ s, Finset (Fin (k' + 1 + s))) {smax : ℕ} (hE : 1 < E)
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwY : ⌈(q : ℝ) ^ εw⌉₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hsmax : E ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hK : k' + 1 + smax ≤ Kmax)
    (hlen : Ω.length + smax * smax + 3 * smax + 2 ≤ J₀) (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hlE : Real.log E ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((k' + 1 + smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ ∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ rt i)
    (hgeo : ∀ s < smax, ∀ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (leafCmpsL Ω E ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (N : ℕ) :
    ‖∑ s ∈ range N, (-1 : ℂ) ^ s *
        ∑ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
            (leafCmpsL Ω E ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a' n * (if (∏ i, x i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ))) +
        smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  set w := ⌈(q : ℝ) ^ εw⌉₊ with hwdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hZ0 : (0 : ℝ) < ((N₂ + 1 : ℕ) : ℝ) := by positivity
  have hE0 : (0 : ℝ) < E := by linarith
  have hB : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
  obtain ⟨Mc, hMcdef⟩ : ∃ Mc : ℝ, Mc = 2 * SieveProp6.zeta C₀ k * (((N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (w : ℝ))) +
        2 * SieveProp6.rem (w : ℝ) (SieveProp6.Jw w) k * (q : ℝ) ^ (L - 1 - δ') := ⟨_, rfl⟩
  have hMc : 0 ≤ Mc := by
    rw [hMcdef]
    have hN' : (0 : ℝ) ≤ (N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
      have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ N₂ := by exact_mod_cast hN
      linarith
    have hlw : 0 ≤ Real.log (w : ℝ) := Real.log_nonneg hw1
    exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.zeta_nonneg hC₀ k))
      (div_nonneg hN' (mul_nonneg (Nat.cast_nonneg _) hlw)))
      (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _))
  rw [← hMcdef]
  have he : 0 ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by positivity
  -- the members of a family of leaves
  have hmem : ∀ s, ∀ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
      (StrictAnti x ∧ ∀ i, w ≤ x i) ∧ ∏ u : Fin s, (x (Fin.natAdd (k' + 1) u) : ℝ) < E ∧
        ∀ u : Fin s, (w : ℝ) ≤ x (Fin.natAdd (k' + 1) u) := by
    intro s x hx
    have hx1 := one_le_of_mem_RTg hx
    have hprime : ∀ i, (x i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
    obtain ⟨⟨hΩ1, ⟨hanti, hblk⟩, hlt⟩, hbelow⟩ :=
      (leafCmpsL_holds Ω hE0 hw0 hZ0 hx1).1 (Finset.mem_filter.1 hx).2
    obtain ⟨ha, hent⟩ := hreg _ (fun i => hprime _) hΩ1
    refine ⟨⟨strictAnti_chainL ha hanti hbelow, fun i => ?_⟩, hlt, fun u => (hblk u).2⟩
    induction i using Fin.addCases with
    | left i => exact hent i
    | right u => exact_mod_cast (hblk u).2
  -- each size
  have hsize : ∀ s < smax, ‖∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
      ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂, dw q a' n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0)‖ ≤
        Mc * ∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s), 1 / ((∏ i, x i : ℕ) : ℝ) +
          (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
    intro s hs
    have hss : s * s + 3 * s ≤ smax * smax + 3 * smax := by nlinarith
    have hlen' := length_leafCmpsL_le Ω E (w : ℝ) ((N₂ + 1 : ℕ) : ℝ) s
    have hΛs : Λ₁ * Real.log q + ((k' + 1 + s : ℕ) : ℝ) * Real.log (N₂ : ℝ) ≤ Λ₀ * Real.log q := by
      have h1 : ((k' + 1 + s : ℕ) : ℝ) ≤ ((k' + 1 + smax : ℕ) : ℝ) := by exact_mod_cast (by omega)
      have h2 : 0 ≤ Real.log (N₂ : ℝ) := Real.log_natCast_nonneg N₂
      have := mul_le_mul_of_nonneg_right h1 h2
      linarith
    rw [hMcdef]
    exact SieveGap.family_leaves_le ha' hok (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s) (I s) hw2 (by omega)
      (by omega) hΛ₁ (leafCmpsL_c_le hB hc hlZ hlE hw1) hΛs hX hN (fun x hx => (hmem s x hx).1) (hgeo s hs)
      hC₀ hC hk hk1 hkC
  refine (SieveP6TreeLeaves.norm_sum_sizes_le'
    (b := fun s => Mc * ∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
      1 / ((∏ i, x i : ℕ) : ℝ) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ))
    (fun s => by simp) (fun s => add_nonneg (mul_nonneg hMc (Finset.sum_nonneg fun x _ => by positivity)) he)
    hsize (fun s hs => ?_)).trans ?_
  · refine Finset.sum_eq_zero fun x hx => ?_
    exfalso
    obtain ⟨-, hlt, hge⟩ := hmem s x hx
    have h2 : (w : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd (k' + 1) u) : ℝ) := by
      calc (w : ℝ) ^ s = ∏ _u : Fin s, (w : ℝ) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => hge u
    have h3 : (w : ℝ) ^ smax ≤ (w : ℝ) ^ s := pow_le_pow_right₀ hw1 hs
    linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsub : ∑ s ∈ range smax, ∑ x ∈ RTg (k' + 1 + s) N₂ (leafCmpsL Ω E w ((N₂ + 1 : ℕ) : ℝ) s),
        1 / ((∏ i, x i : ℕ) : ℝ) ≤
          (∑ rt ∈ RTg (k' + 1) N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco w (N₂ + 1), (1 + 1 / (p : ℝ)) := by
      refine le_trans (Finset.sum_le_sum fun s _ => ?_)
        (SieveP6TreeLeaves.sum_leaves_inv_le Ω ∅ E (by omega) hwY le_rfl smax)
      rw [leafCmpsL, RTg_append]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => by positivity
    have := mul_le_mul_of_nonneg_left hsub hMc
    linarith

/-! ### The stops of the tree below the last entry -/

/-- **The stops of the tree below the last entry.** Let `ChainOK2` hold for the windows `(A, B]` and `(Ar, Br]`,
with `(Ar + 1)z_b ≤ Br` and `Ar + 1 ≤ w^{s_max}`, `1 ≤ w`, `q^{e₀} ≤ w`, `k′ + 1 + s_max ≤ K₀`,
`|Ω| + s_max² + 3s_max + 2 ≤ J₀`, and the comparisons' `m`-parts, `log(N₂ + 1)` and `log(Ar + 1)` at most
`Λ₁ log q`; let the tuples satisfying `Ω` be strictly decreasing with entries at least `w`, last entry at most `z_b`
and `A < ∏_{i∈S} rt_i ≤ B`. Then the stops of the tree below the last entry at `E = Ar + 1`, whose rest is the
tree's block, total at most `s_max·q^{L−δ}/φ(q)`. -/
theorem stops_last_le {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B Ar Br : ℕ}
    (hok : ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br) {k' : ℕ} (Ω : List (GCmp (k' + 1)))
    (S : Finset (Fin (k' + 1))) {w zb smax : ℕ} (hw : 1 ≤ w) (hwq : (q : ℝ) ^ e₀ ≤ w)
    (hAB : (Ar + 1) * zb ≤ Br) (hsmax : (Ar : ℝ) + 1 ≤ (w : ℝ) ^ smax) (hK : k' + 1 + smax ≤ K₀)
    (hJ : Ω.length + smax * smax + 3 * smax + 2 ≤ J₀) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, w ≤ rt i) ∧ rt (Fin.last k') ≤ zb ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B)
    (N : ℕ) :
    ‖∑ s ∈ range N, (-1 : ℂ) ^ (s + 1) *
        ∑ x ∈ RTg (k' + 1 + (s + 1)) ⌊2 * (q : ℝ) ^ L⌋₊
            (stopCmpsL Ω ((Ar : ℝ) + 1) w ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, x i) ∣ n ∧ rough (x (Fin.natAdd (k' + 1) (Fin.last s))) n then 1 else 0)‖ ≤
      smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  have hb : 0 ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by positivity
  have hE : (0 : ℝ) < (Ar : ℝ) + 1 := by positivity
  have hE1 : (1 : ℝ) ≤ (Ar : ℝ) + 1 := by linarith [(Nat.cast_nonneg Ar : (0 : ℝ) ≤ Ar)]
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hZ0 : (0 : ℝ) < ((N₂ + 1 : ℕ) : ℝ) := by positivity
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hBnn : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
  refine norm_sum_sizes_le hb (fun s => by simp) (fun s hs => ?_) (fun s hs => ?_)
  · refine hok (k' + 1 + s) (by omega) (S.map (Fin.castAddEmb (s + 1)))
      ((univ : Finset (Fin (s + 1))).map (Fin.natAddEmb (k' + 1)))
      (stopCmpsL Ω ((Ar : ℝ) + 1) w ((N₂ + 1 : ℕ) : ℝ) s) ?_ (Finset.univ_nonempty.map) ?_ ?_ ?_
    · refine disjoint_of_val fun a ha b hb => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ha
      obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hb
      show (i : ℕ) < k' + 1 + u
      have := i.isLt
      omega
    · have h1 := length_stopCmpsL_le Ω ((Ar : ℝ) + 1) (w : ℝ) ((N₂ + 1 : ℕ) : ℝ) s
      have h2 : (s + 1) * (s + 1) + 3 * (s + 1) ≤ smax * smax + 3 * smax := by nlinarith
      omega
    · exact stopCmpsL_c_le hBnn hc hlZ hlA hE1 hw1
    · intro x hx hΩ
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      obtain ⟨⟨hΩ1, ⟨hanti, hblk⟩, hlo, hhi⟩, hbelow⟩ := (stopCmpsL_holds Ω hE hw0 hZ0 hx1).1 hΩ
      obtain ⟨ha, hent, hzb, hAlo, hBhi⟩ := hreg _ (fun i => hx _) hΩ1
      have hentall : ∀ i : Fin (k' + 1 + (s + 1)), (w : ℝ) ≤ x i := fun i => by
        induction i using Fin.addCases with
        | left i => exact_mod_cast hent i
        | right u => exact (hblk u).2
      have hP' : ∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc) ≤ Ar := by
        have h1 : ((∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc) : ℕ) : ℝ) < ((Ar + 1 : ℕ) : ℝ) := by
          push_cast
          exact hlo
        have h2 : ∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc) < Ar + 1 := by exact_mod_cast h1
        omega
      have hall : ∏ u : Fin (s + 1), x (Fin.natAdd (k' + 1) u) =
          (∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc)) * x (Fin.natAdd (k' + 1) (Fin.last s)) :=
        Fin.prod_univ_castSucc _
      have hlastb : x (Fin.natAdd (k' + 1) (Fin.last s)) ≤ zb := by
        have := hbelow (Fin.last s)
        omega
      refine ⟨strictAnti_chainL ha hanti hbelow, fun i => le_trans hwq (hentall i), ?_, ?_, ?_, ?_⟩
      · rw [Finset.prod_map]
        exact hAlo
      · rw [Finset.prod_map]
        exact hBhi
      · rw [Finset.prod_map]
        have h1 : ((Ar + 1 : ℕ) : ℝ) ≤ ((∏ u : Fin (s + 1), x (Fin.natAdd (k' + 1) u) : ℕ) : ℝ) := by
          push_cast
          exact hhi
        have h2 : Ar + 1 ≤ ∏ u : Fin (s + 1), x (Fin.natAdd (k' + 1) u) := by exact_mod_cast h1
        exact Nat.lt_of_succ_le h2
      · rw [Finset.prod_map]
        show ∏ u : Fin (s + 1), x (Fin.natAdd (k' + 1) u) ≤ Br
        rw [hall]
        calc (∏ u : Fin s, x (Fin.natAdd (k' + 1) u.castSucc)) * x (Fin.natAdd (k' + 1) (Fin.last s))
            ≤ Ar * zb := Nat.mul_le_mul hP' hlastb
          _ ≤ (Ar + 1) * zb := Nat.mul_le_mul_right zb (Nat.le_succ Ar)
          _ ≤ Br := hAB
  · refine Finset.sum_eq_zero fun x hx => ?_
    exfalso
    have hx1 := one_le_of_mem_RTg hx
    obtain ⟨⟨-, ⟨-, hblk⟩, hlo, -⟩, -⟩ := (stopCmpsL_holds Ω hE hw0 hZ0 hx1).1 (Finset.mem_filter.1 hx).2
    have h2 : (w : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd (k' + 1) u.castSucc) : ℝ) := by
      calc (w : ℝ) ^ s = ∏ _u : Fin s, (w : ℝ) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => (hblk u.castSucc).2
    have h3 : (w : ℝ) ^ smax ≤ (w : ℝ) ^ s := pow_le_pow_right₀ hw1 hs
    linarith

/-! ### A family sifted at its last entry -/

/-- **A family sifted at its last entry, with the first variable in its window.** For chains `rt` of length `k′ + 1`,
strictly decreasing with entries at least `w = ⌈q^{εw}⌉`, last entry at most `z_b`, and `A < ∏_{i∈S} rt_i ≤ B`: by
the tree below the last entry with the rule `Ar + 1 ≤ ∏P` (`SieveFillTree.tree_last`), the multiples of `∏rt` with no
prime factor below `rt`'s last entry are its leaves, at most `leaves_last_le`'s bound, and its stops, at most
`s_max·q^{L−δ_c}/φ(q)` (`stops_last_le`). -/
theorem last_pattern_le {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δl δc : ℝ}
    {k J₀ J₀' K₀ Kmax A B Ar Br : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {k' : ℕ} (Ω : List (GCmp (k' + 1)))
    (S : Finset (Fin (k' + 1))) (I : ∀ s, Finset (Fin (k' + 1 + s))) {zb smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwY : ⌈(q : ℝ) ^ εw⌉₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hAB : (Ar + 1) * zb ≤ Br) (hAr : 1 ≤ Ar) (hsmax : (Ar : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hKL : k' + 1 + smax ≤ Kmax) (hKC : k' + 1 + smax ≤ K₀)
    (hlenL : Ω.length + smax * smax + 3 * smax + 2 ≤ J₀) (hlenC : Ω.length + smax * smax + 3 * smax + 2 ≤ J₀')
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((k' + 1 + smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ εw⌉₊ ≤ rt i) ∧ rt (Fin.last k') ≤ zb ∧ A < ∏ i ∈ S, rt i ∧
        ∏ i ∈ S, rt i ≤ B)
    (hgeo : ∀ s < smax, ∀ x ∈ RTg (k' + 1 + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (leafCmpsL Ω ((Ar : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ))) +
        smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl)) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hE : (1 : ℝ) < (Ar : ℝ) + 1 := by
    have : (1 : ℝ) ≤ Ar := by exact_mod_cast hAr
    linarith
  have hfam : ∀ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, StrictAnti rt ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ rt (Fin.last k') :=
    fun rt hrt => by
      obtain ⟨h1, h2, -⟩ := hreg rt (fun i => (SieveTypeIIU.mem_primesLe.1
        (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2
      exact ⟨h1, h2 _⟩
  rw [tree_last (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊) (dw q a') Ω hE (by omega) hwY hfam]
  refine (norm_add_le _ _).trans ?_
  have hL := leaves_last_le ha' hokL Ω I hE hw2 hwY hsmax hKL hlenL hΛ₁ hc hlZ hlA hΛ hX hN
    (fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩) hgeo hC₀ hC hk hk1 hkC
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1)).card + 1)
  have hS := stops_last_le hq1 a' hΛ₁ hokC Ω S (by omega) (Nat.le_ceil _) hAB hsmax hKC hlenC hc hlZ hlA hreg
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1)).card + 1)
  linarith

/-! ### The stops of a tree whose rest is the tree's block -/

/-- **The stops of a tree from a level, with the tree's block as the rest.** Let `ChainOK2` hold for the windows
`(A, B]` and `(Ar, Br]`, with `(Ar + 1)z₀ ≤ Br` and `Ar + 1 ≤ w^{s_max}`, `1 ≤ w ≤ z₀`, `q^{e₀} ≤ w`,
`j + s_max ≤ K₀`, `|Ω| + s_max² + 2s_max + 2 ≤ J₀`, and the comparisons' `m`-parts, `log z₀` and `log(Ar + 1)` at
most `Λ₁ log q`; let the tuples satisfying `Ω` be strictly decreasing with entries at least `z₀` and
`A < ∏_{i∈S} rt_i ≤ B`. Then the stops of the tree with the rule `Ar + 1 ≤ ∏P` total at most `s_max·q^{L−δ}/φ(q)`:
a stop's rest is its block, in `(Ar, (Ar + 1)z₀)`, and its first variable the family's. -/
theorem stops_rest_le {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B Ar Br : ℕ}
    (hok : ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S : Finset (Fin j))
    {w z₀ smax : ℕ} (hw : 1 ≤ w) (hwq : (q : ℝ) ^ e₀ ≤ w) (hwz : w ≤ z₀)
    (hAB : (Ar + 1) * z₀ ≤ Br) (hsmax : (Ar : ℝ) + 1 ≤ (w : ℝ) ^ smax) (hK : j + smax ≤ K₀)
    (hJ : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hlz : Real.log z₀ ≤ Λ₁ * Real.log q) (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B)
    (N : ℕ) :
    ‖∑ s ∈ range N, (-1 : ℂ) ^ (s + 1) *
        ∑ x ∈ RTg (j + (s + 1)) ⌊2 * (q : ℝ) ^ L⌋₊ (stopCmps Ω ∅ ((Ar : ℝ) + 1) w z₀ s),
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, x i) ∣ n ∧ rough (x (Fin.natAdd j (Fin.last s))) n then 1 else 0)‖ ≤
      smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  have hb : 0 ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by positivity
  have hE : (0 : ℝ) < (Ar : ℝ) + 1 := by positivity
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hwz' : (w : ℝ) ≤ z₀ := by exact_mod_cast hwz
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  refine norm_sum_sizes_le hb (fun s => by simp) (fun s hs => ?_) (fun s hs => ?_)
  · refine hok (j + s) (by omega) (S.map (Fin.castAddEmb (s + 1)))
      ((univ : Finset (Fin (s + 1))).map (Fin.natAddEmb j)) (stopCmps Ω ∅ ((Ar : ℝ) + 1) w z₀ s) ?_
      (Finset.univ_nonempty.map) ?_ ?_ ?_
    · refine disjoint_of_val fun a ha b hb => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ha
      obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hb
      show (i : ℕ) < j + u
      have := i.isLt
      omega
    · have h1 := length_Pblock_le j (s + 1) (w : ℝ) (z₀ : ℝ)
      have h2 : (s + 1) * (s + 1) + 2 * (s + 1) ≤ smax * smax + 2 * smax := by nlinarith
      simp only [stopCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega
    · intro C hC
      simp only [stopCmps, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
      rcases hC with (⟨C', hC', rfl⟩ | hC) | rfl | rfl
      · exact hc C' hC'
      · exact Pblock_c_le (j := j) (s := s + 1) (by positivity) hlz hw1 C hC
      · exact hlA
      · show -Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q
        have : 0 ≤ Real.log ((Ar : ℝ) + 1) :=
          Real.log_nonneg (by linarith [(Nat.cast_nonneg Ar : (0 : ℝ) ≤ Ar)])
        nlinarith
    · intro x hx hΩ
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      obtain ⟨hΩ1, ⟨hanti, hblk⟩, hlo, hhi⟩ := (stopCmps_holds Ω ∅ hE hw0 hz0 hx1).1 hΩ
      rw [prod_idxInit, Finset.prod_empty, one_mul] at hlo
      rw [prod_idxAll, Finset.prod_empty, one_mul] at hhi
      obtain ⟨ha, hz, hAlo, hBhi⟩ := hreg _ (fun i => hx _) hΩ1
      have hent : ∀ i : Fin (j + (s + 1)), (w : ℝ) ≤ x i := fun i => by
        induction i using Fin.addCases with
        | left i => exact le_trans hwz' (by exact_mod_cast hz i)
        | right u => exact (hblk u).2
      have hP' : ∏ u : Fin s, x (Fin.natAdd j u.castSucc) ≤ Ar := by
        have h1 : ((∏ u : Fin s, x (Fin.natAdd j u.castSucc) : ℕ) : ℝ) < ((Ar + 1 : ℕ) : ℝ) := by
          push_cast
          exact hlo
        have h2 : ∏ u : Fin s, x (Fin.natAdd j u.castSucc) < Ar + 1 := by exact_mod_cast h1
        omega
      have hall : ∏ u : Fin (s + 1), x (Fin.natAdd j u) =
          (∏ u : Fin s, x (Fin.natAdd j u.castSucc)) * x (Fin.natAdd j (Fin.last s)) :=
        Fin.prod_univ_castSucc _
      have hlastb : x (Fin.natAdd j (Fin.last s)) ≤ z₀ := by
        have h1 : (x (Fin.natAdd j (Fin.last s)) : ℝ) < z₀ := (hblk (Fin.last s)).1
        have h2 : x (Fin.natAdd j (Fin.last s)) < z₀ := by exact_mod_cast h1
        omega
      refine ⟨strictAnti_chain (j := j) (t := s + 1) ha hanti (fun i => by exact_mod_cast hz i)
        (fun u => (hblk u).1), fun i => le_trans hwq (hent i), ?_, ?_, ?_, ?_⟩
      · rw [Finset.prod_map]
        exact hAlo
      · rw [Finset.prod_map]
        exact hBhi
      · rw [Finset.prod_map]
        have h1 : ((Ar + 1 : ℕ) : ℝ) ≤ ((∏ u : Fin (s + 1), x (Fin.natAdd j u) : ℕ) : ℝ) := by
          push_cast
          exact hhi
        have h2 : Ar + 1 ≤ ∏ u : Fin (s + 1), x (Fin.natAdd j u) := by exact_mod_cast h1
        exact Nat.lt_of_succ_le h2
      · rw [Finset.prod_map]
        show ∏ u : Fin (s + 1), x (Fin.natAdd j u) ≤ Br
        rw [hall]
        calc (∏ u : Fin s, x (Fin.natAdd j u.castSucc)) * x (Fin.natAdd j (Fin.last s))
            ≤ Ar * z₀ := Nat.mul_le_mul hP' hlastb
          _ ≤ (Ar + 1) * z₀ := Nat.mul_le_mul_right z₀ (Nat.le_succ Ar)
          _ ≤ Br := hAB
  · refine Finset.sum_eq_zero fun x hx => ?_
    exfalso
    have hx1 := one_le_of_mem_RTg hx
    obtain ⟨-, ⟨-, hblk⟩, hlo, -⟩ := (stopCmps_holds Ω ∅ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
    rw [prod_idxInit, Finset.prod_empty, one_mul] at hlo
    have h2 : (w : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ) := by
      calc (w : ℝ) ^ s = ∏ _u : Fin s, (w : ℝ) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => (hblk u.castSucc).2
    have h3 : (w : ℝ) ^ smax ≤ (w : ℝ) ^ s := pow_le_pow_right₀ hw1 hs
    linarith

omit [Route] in
/-- **The sums of `1/d` over the stops**: at most `(Σ_{rt} 1/r)∏_{p∈[w,z₀)}(1 + 1/p)`. -/
theorem sum_stops_inv_le {j : ℕ} (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) (E : ℝ) {Y w z₀ : ℕ} (hw : 1 ≤ w)
    (hwz : w ≤ z₀) (hz₀ : z₀ ≤ Y + 1) (M : ℕ) :
    ∑ s ∈ range M, ∑ x ∈ RTg (j + (s + 1)) Y (stopCmps Ω S₀ E w z₀ s), 1 / ((∏ i, x i : ℕ) : ℝ) ≤
      (∑ rt ∈ RTg j Y Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ)) := by
  rw [← SieveProp6.sum_leaves_inv]
  have hstep : ∀ s, ∑ x ∈ RTg (j + (s + 1)) Y (stopCmps Ω S₀ E w z₀ s), 1 / ((∏ i, x i : ℕ) : ℝ) ≤
      ∑ rt ∈ RTg j Y Ω, ∑ P ∈ (primesIco w z₀).powersetCard (s + 1),
        1 / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) := by
    intro s
    rw [stopCmps, RTg_append (j + (s + 1)) Y (Ω.map liftChain ++ Pblock j (s + 1) w z₀)]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => by positivity).trans
      (le_of_eq ?_)
    have e : ∀ x : Fin (j + (s + 1)) → ℕ, 1 / ((∏ i, x i : ℕ) : ℝ) =
        1 / (((∏ i, x (Fin.castAdd (s + 1) i)) * ∏ u, x (Fin.natAdd j u) : ℕ) : ℝ) := fun x => by
      rw [← Fin.prod_univ_add]
    rw [Finset.sum_congr rfl fun x _ => e x,
      ← sum_chain j (s + 1) Ω hw hwz hz₀ (fun rt y => 1 / (((∏ i, rt i) * ∏ u, y u : ℕ) : ℝ))]
    refine Finset.sum_congr rfl fun rt _ => ?_
    rw [sum_powersetCard_desc]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.prod_image fun u _ v _ h => (Finset.mem_filter.1 hy).2.injective h]
  refine (Finset.sum_le_sum fun s _ => hstep s).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun rt _ => ?_
  have h1 := SieveP6TreeLeaves.sum_sizes_le_powerset (primesIco w z₀) (M + 1)
    (fun P => 1 / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ)) fun P => by positivity
  rw [Finset.sum_range_succ'] at h1
  have h2 : (0 : ℝ) ≤ ∑ P ∈ (primesIco w z₀).powersetCard 0, 1 / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) :=
    Finset.sum_nonneg fun P _ => by positivity
  linarith

/-! ### The sizes of a leaf of the second tree -/

omit [Route] in
/-- **The two blocks of a leaf with two blocks of new primes are small.** For `x = (rt, y, y'')` with
`rt_i ≤ Q^{hi_i}` and `∏y·∏y'' ≤ Y₀`: the block of `S₁` (with the new primes if `eIn₁`) is at most
`Q^{Σ_{S₁} hi}·(Y₀ if eIn₁)`, and the other at most `Q^{Σ_{S₁ᶜ} hi}·(Y₀ unless eIn₁)`. -/
theorem leaf_blocks2_le {j : ℕ} (S₁ : Finset (Fin j)) (eIn₁ : Bool) {s₁ s₂ : ℕ} {x : Fin (j + s₁ + s₂) → ℕ}
    (hx : ∀ i, 1 ≤ x i) {Q : ℝ} (hQ : 0 < Q) (hi : Fin j → ℝ)
    (hrt : ∀ i, (x (Fin.castAdd s₂ (Fin.castAdd s₁ i)) : ℝ) ≤ Q ^ hi i) {Y₀ : ℝ}
    (hy : (∏ u, (x (Fin.castAdd s₂ (Fin.natAdd j u)) : ℝ)) * ∏ v, (x (Fin.natAdd (j + s₁) v) : ℝ) ≤ Y₀) :
    ∏ i ∈ Isplit (Isplit S₁ eIn₁ s₁) eIn₁ s₂, (x i : ℝ) ≤ Q ^ (∑ i ∈ S₁, hi i) * (if eIn₁ then Y₀ else 1) ∧
      ∏ i ∈ (Isplit (Isplit S₁ eIn₁ s₁) eIn₁ s₂)ᶜ, (x i : ℝ) ≤
        Q ^ (∑ i ∈ S₁ᶜ, hi i) * (if eIn₁ then 1 else Y₀) := by
  have hpos : ∀ i, (0 : ℝ) ≤ x i := fun i => Nat.cast_nonneg _
  have hx' : ∀ i : Fin (j + s₁), 1 ≤ x (Fin.castAdd s₂ i) := fun i => hx _
  have hT : ∀ T : Finset (Fin j), ∏ i ∈ T, (x (Fin.castAdd s₂ (Fin.castAdd s₁ i)) : ℝ) ≤ Q ^ (∑ i ∈ T, hi i) :=
    fun T => by
      rw [Real.rpow_sum_of_pos hQ]
      exact Finset.prod_le_prod₀ (fun i _ => hpos _) fun i _ => hrt i
  have hQ0 : ∀ T : Finset (Fin j), 0 ≤ Q ^ (∑ i ∈ T, hi i) := fun T => by positivity
  have hy1 : 0 ≤ ∏ u, (x (Fin.castAdd s₂ (Fin.natAdd j u)) : ℝ) := Finset.prod_nonneg fun u _ => hpos _
  have hy2 : 0 ≤ ∏ v, (x (Fin.natAdd (j + s₁) v) : ℝ) := Finset.prod_nonneg fun v _ => hpos _
  rw [prod_Isplit, prod_Isplit_compl _ eIn₁ hx, prod_Isplit S₁ eIn₁ (fun i => x (Fin.castAdd s₂ i)),
    prod_Isplit_compl S₁ eIn₁ hx']
  cases eIn₁
  · simp only [Bool.false_eq_true, ite_false, mul_one]
    refine ⟨hT S₁, ?_⟩
    rw [mul_assoc]
    exact mul_le_mul (hT S₁ᶜ) hy (mul_nonneg hy1 hy2) (hQ0 _)
  · simp only [ite_true, mul_one]
    refine ⟨?_, hT S₁ᶜ⟩
    rw [mul_assoc]
    exact mul_le_mul (hT S₁) hy (mul_nonneg hy1 hy2) (hQ0 _)

/-- From the bounds of a leaf's two blocks, with the new primes' product at most `4q^T`, to the sizes of
`leaves_chain`. -/
theorem sizes_of_blocks {q : ℕ} (hq0 : (0 : ℝ) < q) {K : ℕ} (I : Finset (Fin K)) (x : Fin K → ℕ) {j : ℕ}
    (S₁ : Finset (Fin j)) (eIn₁ : Bool) (hi : Fin j → ℝ) {T c a b w : ℝ} {k : ℕ} (hw0 : 0 ≤ w)
    (hwpow : w ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c)
    (hI : ∏ i ∈ I, (x i : ℝ) ≤ (q : ℝ) ^ (∑ i ∈ S₁, hi i) * (if eIn₁ then 4 * (q : ℝ) ^ T else 1))
    (hIc : ∏ i ∈ Iᶜ, (x i : ℝ) ≤ (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i) * (if eIn₁ then 1 else 4 * (q : ℝ) ^ T))
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) - c)) :
    ((∏ i ∈ I, x i : ℕ) : ℝ) * w ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
      ((∏ i ∈ I, x i : ℕ) : ℝ) * w ^ (2 * k + 4) * ((∏ i ∈ Iᶜ, x i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L - b) := by
  have hqT : 0 ≤ (q : ℝ) ^ T := by positivity
  have hI' : ∏ i ∈ I, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) := by
    refine hI.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false, mul_one, add_zero]
      linarith
    · simp only [ite_true]
      rw [Real.rpow_add hq0]
      linarith
  have hIc' : ∏ i ∈ Iᶜ, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) := by
    refine hIc.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false]
      rw [Real.rpow_add hq0]
      linarith
    · simp only [ite_true, mul_one, add_zero]
      linarith
  push_cast
  exact leaf_sizes_num hq0 (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) hI' hIc' hw0 hwpow hsz₁ hsz₂

/-! ### A family below the window -/

set_option maxHeartbeats 1600000 in
/-- **A family below the window, with the rest among the tree's primes.** The family's products
`c = ∏_{i∈S₀} rt_i` are below `E = A + 1`. By the tree with the rule `E ≤ c∏P` (`SieveP6Tree.tree_chains`): its
leaves by `SieveP6TreeLeaves.tree_leaves_le`; each of its stops, whose first variable is in `(A, B]` and which has
no rest, by `last_pattern_le`, the tree below its last prime with the rule `Ar + 1 ≤ ∏P`. A leaf of the first tree
has new primes of product at most `4q^t`, one of a second tree at most `4q^t·z₀·(Ar + 1) ≤ 4q^T`. -/
theorem fill_below_ib {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δl δc t T c : ℝ}
    {k J₀ J₀' K₀ Kmax A B Ar Br : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ S₁ : Finset (Fin j))
    (eIn₁ : Bool) (hi : Fin j → ℝ) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hAB : (A + 1) * z₀ ≤ B) (hArB : (Ar + 1) * z₀ ≤ Br) (hAr : 1 ≤ Ar)
    (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hsmr : (Ar : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + 2 * smax ≤ Kmax) (hKC : j + 2 * smax ≤ K₀)
    (hlenL : Ω.length + 2 * (smax * smax) + 5 * smax + 4 ≤ J₀)
    (hlenC : Ω.length + 2 * (smax * smax) + 5 * smax + 4 ≤ J₀') (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q) (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((j + 2 * smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        (A : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (rt i : ℝ))
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hT : 4 * (q : ℝ) ^ t * z₀ * ((Ar : ℝ) + 1) ≤ 4 * (q : ℝ) ^ T) (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) - c))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          (((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) *
            (1 + ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ)))) +
        (smax + smax * smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl)) +
        smax * smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  set w := ⌈(q : ℝ) ^ εw⌉₊ with hwdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hz1 : (1 : ℝ) ≤ z₀ := by exact_mod_cast (by omega : 1 ≤ z₀)
  have hwz' : (w : ℝ) ≤ z₀ := by exact_mod_cast hwz
  have hZ0 : (0 : ℝ) < ((N₂ + 1 : ℕ) : ℝ) := by positivity
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hEB : (0 : ℝ) < (Ar : ℝ) + 1 := by positivity
  have hAr1 : (1 : ℝ) ≤ (Ar : ℝ) + 1 := by linarith [(Nat.cast_nonneg Ar : (0 : ℝ) ≤ Ar)]
  have hBnn : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq
  have hlogN : 0 ≤ Real.log (N₂ : ℝ) := Real.log_natCast_nonneg N₂
  have hqt : 0 < (q : ℝ) ^ t := by positivity
  have hwY : w ≤ N₂ + 1 := hwz.trans hz₀
  have hwpow : (w : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
    calc (w : ℝ) ^ (2 * k + 4) ≤ (2 * (q : ℝ) ^ εw) ^ (2 * k + 4) := pow_le_pow_left₀ hw0.le hwle _
      _ = 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ εw), ← Real.rpow_mul hq0.le, ← hεwc]
          push_cast
          ring_nf
  have htT : 4 * (q : ℝ) ^ t ≤ 4 * (q : ℝ) ^ T := by
    refine le_trans ?_ hT
    have h1 : 4 * (q : ℝ) ^ t * 1 ≤ 4 * (q : ℝ) ^ t * z₀ := mul_le_mul_of_nonneg_left hz1 (by positivity)
    have h2 : 4 * (q : ℝ) ^ t * z₀ * 1 ≤ 4 * (q : ℝ) ^ t * z₀ * ((Ar : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hAr1 (by positivity)
    linarith
  have hreg' : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩
  have hfam' : ∀ rt ∈ RTg j N₂ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1 ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hrt => ⟨hfam rt hrt, (hreg' rt (fun i => (SieveTypeIIU.mem_primesLe.1
      (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2).2⟩
  obtain ⟨Mc, hMcdef⟩ : ∃ Mc : ℝ, Mc = 2 * SieveProp6.zeta C₀ k * (((N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (w : ℝ))) +
        2 * SieveProp6.rem (w : ℝ) (SieveProp6.Jw w) k * (q : ℝ) ^ (L - 1 - δ') := ⟨_, rfl⟩
  have hMc : 0 ≤ Mc := by
    rw [hMcdef]
    have hN' : (0 : ℝ) ≤ (N₂ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
      have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ N₂ := by exact_mod_cast hN
      linarith
    have hlw : 0 ≤ Real.log (w : ℝ) := Real.log_nonneg hw1
    exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.zeta_nonneg hC₀ k))
      (div_nonneg hN' (mul_nonneg (Nat.cast_nonneg _) hlw)))
      (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _))
  rw [← hMcdef]
  obtain ⟨el, hel⟩ : ∃ el : ℝ, el = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl) := ⟨_, rfl⟩
  obtain ⟨ec, hec⟩ : ∃ ec : ℝ, ec = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc) := ⟨_, rfl⟩
  have hel0 : 0 ≤ el := by rw [hel]; positivity
  have hec0 : 0 ≤ ec := by rw [hec]; positivity
  rw [← hel, ← hec]
  obtain ⟨PN, hPN⟩ : ∃ PN : ℝ, PN = ∏ p ∈ primesIco w (N₂ + 1), (1 + 1 / (p : ℝ)) := ⟨_, rfl⟩
  have hPN0 : 0 ≤ PN := by rw [hPN]; exact Finset.prod_nonneg fun p _ => by positivity
  rw [← hPN]
  rw [tree_chains (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂) (dw q a') Ω S₀ hE (by omega) hwz hz₀ hfam']
  refine (norm_add_le _ _).trans ?_
  -- the leaves of the first tree
  have hΛA : Λ₁ * Real.log q + ((j : ℝ) + smax) * Real.log (N₂ : ℝ) ≤ Λ₀ * Real.log q := by
    have h1 : (j : ℝ) + smax ≤ ((j + 2 * smax : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg smax : (0 : ℝ) ≤ smax)]
    have := mul_le_mul_of_nonneg_right h1 hlogN
    linarith
  have hLv := SieveP6TreeLeaves.tree_leaves_le ha' hokL Ω S₀ (Isplit S₁ eIn₁) hE hw2 hwz hz₀ hsmax (by omega)
    (by nlinarith) hΛ₁ hc hlz hlE hΛA hX hN hreg' (fun s _ x hx _ => by
      have hx1 := one_le_of_mem_RTg hx
      obtain ⟨hΩ1, -, halive⟩ := (leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
      have hprime : ∀ i, (x i).Prime := fun i =>
        (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
      obtain ⟨-, -, hbox, hAc⟩ := hreg _ (fun i => hprime _) hΩ1
      rw [prod_idxAll] at halive
      have hcpos : 0 < ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx1 _
      have hy : ∏ u, (x (Fin.natAdd j u) : ℝ) ≤ 4 * (q : ℝ) ^ T := by
        have h1 : (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * ∏ u, (x (Fin.natAdd j u) : ℝ) <
            (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * (4 * (q : ℝ) ^ t) := by
          calc _ < (A : ℝ) + 1 := halive
            _ ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := hAc
            _ = _ := by ring
        exact (lt_of_mul_lt_mul_left h1 hcpos.le).le.trans htT
      obtain ⟨hI, hIc⟩ := leaf_blocks_le S₁ eIn₁ hx1 hq0 hi hbox hy
      exact sizes_of_blocks hq0 _ x S₁ eIn₁ hi hw0.le hwpow hI hIc hsz₁ hsz₂) hC₀ hC hk hk1 hkC
    ((primesIco w z₀).card + 1)
  rw [← hMcdef, ← hel] at hLv
  -- the stops of the first tree, each by the tree below its last prime
  have hSt : ‖∑ s ∈ range ((primesIco w z₀).card + 1), (-1 : ℂ) ^ (s + 1) *
      ∑ x ∈ RTg (j + (s + 1)) N₂ (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s),
        ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ N₂,
          dw q a' n * (if (∏ i, x i) ∣ n ∧ rough (x (Fin.natAdd j (Fin.last s))) n then 1 else 0)‖ ≤
      Mc * (((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) * PN) +
        smax * (smax * el + smax * ec) := by
    refine (SieveP6TreeLeaves.norm_sum_sizes_le' (smax := smax)
      (b := fun s => Mc * ((∑ x ∈ RTg (j + (s + 1)) N₂ (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s),
        1 / ((∏ i, x i : ℕ) : ℝ)) * PN) + (smax * el + smax * ec))
      (fun s => by simp) (fun s => add_nonneg (mul_nonneg hMc (mul_nonneg
        (Finset.sum_nonneg fun x _ => by positivity) hPN0))
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hel0) (mul_nonneg (Nat.cast_nonneg _) hec0)))
      (fun s hs => ?_) (fun s hs => ?_)).trans ?_
    · have hss : (s + 1) * (s + 1) + 2 * (s + 1) ≤ smax * smax + 2 * smax := by nlinarith
      have hlen1 : (stopCmps Ω S₀ ((A : ℝ) + 1) (w : ℝ) (z₀ : ℝ) s).length ≤
          Ω.length + smax * smax + 2 * smax + 2 := by
        have h1 := length_Pblock_le j (s + 1) (w : ℝ) (z₀ : ℝ)
        simp only [stopCmps, List.length_append, List.length_map, List.length_cons, List.length_nil]
        omega
      have hΛs : Λ₁ * Real.log q + ((j + s + 1 + smax : ℕ) : ℝ) * Real.log (N₂ : ℝ) ≤ Λ₀ * Real.log q := by
        have h1 : ((j + s + 1 + smax : ℕ) : ℝ) ≤ ((j + 2 * smax : ℕ) : ℝ) := by exact_mod_cast (by omega)
        have := mul_le_mul_of_nonneg_right h1 hlogN
        linarith
      have H := last_pattern_le ha' hokL hokC (k' := j + s) (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s)
        (idxAll S₀ (s + 1)) (fun sB => Isplit (Isplit S₁ eIn₁ (s + 1)) eIn₁ sB) (zb := z₀) hw2 hwY hArB hAr
        hsmr (by omega) (by omega) (by omega) (by omega) hΛ₁
        (fun C hC => by
          simp only [stopCmps, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
          rcases hC with (⟨C', hC', rfl⟩ | hC) | rfl | rfl
          · exact hc C' hC'
          · exact Pblock_c_le (j := j) (s := s + 1) hBnn hlz hw1 C hC
          · exact hlE
          · show -Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q
            have : 0 ≤ Real.log ((A : ℝ) + 1) :=
              Real.log_nonneg (by linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)])
            linarith)
        hlZ hlA hΛs hX hN
        (fun x hx hΩ => by
          have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
          obtain ⟨hΩ1, ⟨hanti, hblk⟩, hlo, hhi⟩ := (stopCmps_holds Ω S₀ hE hw0 hz0 hx1).1 hΩ
          obtain ⟨ha, hz, -, -⟩ := hreg _ (fun i => hx _) hΩ1
          have hcast : ∀ I : Finset (Fin (j + (s + 1))), ((∏ i ∈ I, x i : ℕ) : ℝ) = ∏ i ∈ I, (x i : ℝ) :=
            fun I => Nat.cast_prod _ _
          have hent : ∀ i : Fin (j + (s + 1)), w ≤ x i := fun i => by
            induction i using Fin.addCases with
            | left i => exact hwz.trans (hz i)
            | right u => exact_mod_cast (hblk u).2
          have hlastb : x (Fin.natAdd j (Fin.last s)) ≤ z₀ := by
            have h1 : (x (Fin.natAdd j (Fin.last s)) : ℝ) < z₀ := (hblk (Fin.last s)).1
            have h2 : x (Fin.natAdd j (Fin.last s)) < z₀ := by exact_mod_cast h1
            omega
          refine ⟨strictAnti_chain (j := j) (t := s + 1) ha hanti (fun i => by exact_mod_cast hz i)
            (fun u => (hblk u).1), hent, hlastb, ?_, ?_⟩
          · have : (A : ℝ) + 1 ≤ ((∏ i ∈ idxAll S₀ (s + 1), x i : ℕ) : ℝ) := by rw [hcast]; exact hhi
            have : A + 1 ≤ ∏ i ∈ idxAll S₀ (s + 1), x i := by exact_mod_cast this
            exact Nat.lt_of_succ_le this
          · have hlast : (x (Fin.natAdd j (Fin.last s)) : ℝ) < z₀ := (hblk (Fin.last s)).1
            have hpos : (0 : ℝ) ≤ ∏ i ∈ idxInit S₀ s, (x i : ℝ) :=
              Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
            have h1 : ∏ i ∈ idxAll S₀ (s + 1), (x i : ℝ) < ((A : ℝ) + 1) * z₀ := by
              rw [prod_idxAll_succ]
              calc (∏ i ∈ idxInit S₀ s, (x i : ℝ)) * x (Fin.natAdd j (Fin.last s))
                  ≤ (∏ i ∈ idxInit S₀ s, (x i : ℝ)) * z₀ := mul_le_mul_of_nonneg_left hlast.le hpos
                _ < ((A : ℝ) + 1) * z₀ := mul_lt_mul_of_pos_right hlo hz0
            have h2 : (((A + 1) * z₀ : ℕ) : ℝ) ≤ B := by exact_mod_cast hAB
            push_cast at h2
            have h3 : ((∏ i ∈ idxAll S₀ (s + 1), x i : ℕ) : ℝ) < B + 1 := by rw [hcast]; linarith
            have : ∏ i ∈ idxAll S₀ (s + 1), x i < B + 1 := by exact_mod_cast h3
            exact Nat.lt_succ_iff.1 this)
        (fun sB _ x hx _ => by
          have hx1 := one_le_of_mem_RTg hx
          have hprime : ∀ i, (x i).Prime := fun i =>
            (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
          obtain ⟨⟨hΩs, -, hlt2⟩, -⟩ :=
            (leafCmpsL_holds (k' := j + s) (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s) hEB hw0 hZ0 hx1).1
              (Finset.mem_filter.1 hx).2
          have hx1' : ∀ i : Fin (j + (s + 1)), 1 ≤ x (Fin.castAdd sB i) := fun i => hx1 _
          obtain ⟨hΩ1, ⟨-, hblk1⟩, hlo, -⟩ := (stopCmps_holds Ω S₀ hE hw0 hz0 hx1').1 hΩs
          obtain ⟨-, -, hbox, hAc⟩ := hreg _ (fun i => hprime _) hΩ1
          rw [prod_idxInit] at hlo
          have hcpos : 0 < ∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ) :=
            Finset.prod_pos fun i _ => by exact_mod_cast hx1 _
          have hy' : ∏ u : Fin s, (x (Fin.castAdd sB (Fin.natAdd j u.castSucc)) : ℝ) ≤ 4 * (q : ℝ) ^ t := by
            have h1 : (∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ)) *
                ∏ u : Fin s, (x (Fin.castAdd sB (Fin.natAdd j u.castSucc)) : ℝ) <
                (∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ)) * (4 * (q : ℝ) ^ t) := by
              calc _ < (A : ℝ) + 1 := hlo
                _ ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (x (Fin.castAdd sB (Fin.castAdd (s + 1) i)) : ℝ) := hAc
                _ = _ := by ring
            exact (lt_of_mul_lt_mul_left h1 hcpos.le).le
          have hlast : (x (Fin.castAdd sB (Fin.natAdd j (Fin.last s))) : ℝ) ≤ z₀ := (hblk1 (Fin.last s)).1.le
          have hy1 : ∏ u : Fin (s + 1), (x (Fin.castAdd sB (Fin.natAdd j u)) : ℝ) ≤ 4 * (q : ℝ) ^ t * z₀ := by
            rw [Fin.prod_univ_castSucc]
            exact mul_le_mul hy' hlast (Nat.cast_nonneg _) (by positivity)
          have hy2 : ∏ v : Fin sB, (x (Fin.natAdd (j + (s + 1)) v) : ℝ) ≤ (Ar : ℝ) + 1 := hlt2.le
          have hy : (∏ u : Fin (s + 1), (x (Fin.castAdd sB (Fin.natAdd j u)) : ℝ)) *
              ∏ v : Fin sB, (x (Fin.natAdd (j + (s + 1)) v) : ℝ) ≤ 4 * (q : ℝ) ^ T :=
            (mul_le_mul hy1 hy2 (Finset.prod_nonneg fun v _ => Nat.cast_nonneg _) (by positivity)).trans hT
          obtain ⟨hI, hIc⟩ := leaf_blocks2_le S₁ eIn₁ (s₁ := s + 1) (s₂ := sB) hx1 hq0 hi hbox hy
          exact sizes_of_blocks hq0 _ x S₁ eIn₁ hi hw0.le hwpow hI hIc hsz₁ hsz₂)
        hC₀ hC hk hk1 hkC
      rw [← hMcdef, ← hel, ← hec, ← hPN] at H
      exact H.trans (le_of_eq (add_assoc _ _ _))
    · refine Finset.sum_eq_zero fun x hx => ?_
      exfalso
      have hx1 := one_le_of_mem_RTg hx
      obtain ⟨-, ⟨-, hblk⟩, hlo, -⟩ := (stopCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
      rw [prod_idxInit] at hlo
      have h1 : (1 : ℝ) ≤ ∏ i ∈ S₀, (x (Fin.castAdd (s + 1) i) : ℝ) :=
        Finset.one_le_prod₀ fun i _ => by exact_mod_cast hx1 _
      have h2 : (w : ℝ) ^ s ≤ ∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ) := by
        calc (w : ℝ) ^ s = ∏ _u : Fin s, (w : ℝ) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hw0.le) fun u _ => (hblk u.castSucc).2
      have h3 : (w : ℝ) ^ smax ≤ (w : ℝ) ^ s := pow_le_pow_right₀ hw1 hs
      have h4 : 0 ≤ ∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ) :=
        Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
      have h5 := mul_le_mul h1 (le_refl (∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ))) h4 (by linarith)
      linarith
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have hsub := sum_stops_inv_le Ω S₀ ((A : ℝ) + 1) (Y := N₂) (by omega : 1 ≤ w) hwz hz₀ smax
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsub hPN0) hMc
      linarith
  have e : Mc * (((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) *
      (1 + PN)) = Mc * ((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
        ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) +
      Mc * (((∑ rt ∈ RTg j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) * PN) := by
    ring
  rw [e]
  have e2 : ((smax : ℝ) + smax * smax) * el + (smax : ℝ) * smax * ec =
      smax * el + smax * (smax * el + smax * ec) := by ring
  linarith

/-! ### A family in the window -/

/-- **A family in the window, with the rest among the tree's primes.** The family's products
`∏_{i∈S₀} rt_i` are in `(A, B]`. By the tree with the rule `Ar + 1 ≤ ∏P` (`SieveP6Tree.tree_chains` at `S₀ = ∅`):
its leaves, whose new primes have product at most `Ar + 1 ≤ 4q^T`, by `SieveP6TreeLeaves.tree_leaves_le`; its stops,
whose rest is the tree's block, by `stops_rest_le`. -/
theorem fill_window_ib {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δl δc T c : ℝ}
    {k J₀ J₀' K₀ Kmax A B Ar Br : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ S₁ : Finset (Fin j))
    (eIn₁ : Bool) (hi : Fin j → ℝ) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hArB : (Ar + 1) * z₀ ≤ Br) (hAr : 1 ≤ Ar)
    (hsmr : (Ar : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax) (hKC : j + smax ≤ K₀)
    (hlenL : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀) (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀')
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlA : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((j : ℝ) + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧ A < ∏ i ∈ S₀, rt i ∧
        ∏ i ∈ S₀, rt i ≤ B)
    (hT : (Ar : ℝ) + 1 ≤ 4 * (q : ℝ) ^ T) (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) - c))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a' n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δl)) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δc)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hE : (0 : ℝ) < (Ar : ℝ) + 1 := by positivity
  have hwpow : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
    calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (2 * (q : ℝ) ^ εw) ^ (2 * k + 4) :=
          pow_le_pow_left₀ hw0.le hwle _
      _ = 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ εw), ← Real.rpow_mul hq0.le, ← hεwc]
          push_cast
          ring_nf
  have hreg' : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩
  have hfam' : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
      ∏ i ∈ (∅ : Finset (Fin j)), (rt i : ℝ) < (Ar : ℝ) + 1 ∧ ∀ i, z₀ ≤ rt i := fun rt hrt => by
    refine ⟨?_, (hreg' rt (fun i => (SieveTypeIIU.mem_primesLe.1
      (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2).2⟩
    rw [Finset.prod_empty]
    have : (1 : ℝ) ≤ Ar := by exact_mod_cast hAr
    linarith
  rw [tree_chains (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊) (dw q a') Ω ∅ hE (by omega) hwz hz₀ hfam']
  refine (norm_add_le _ _).trans ?_
  have hLv := SieveP6TreeLeaves.tree_leaves_le ha' hokL Ω ∅ (Isplit S₁ eIn₁) hE hw2 hwz hz₀ hsmr hKL hlenL hΛ₁ hc
    hlz hlA hΛ hX hN hreg' (fun s _ x hx _ => by
      have hx1 := one_le_of_mem_RTg hx
      obtain ⟨hΩ1, -, halive⟩ := (leafCmps_holds Ω ∅ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
      have hprime : ∀ i, (x i).Prime := fun i =>
        (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
      obtain ⟨-, -, hbox, -⟩ := hreg _ (fun i => hprime _) hΩ1
      rw [prod_idxAll, Finset.prod_empty, one_mul] at halive
      obtain ⟨hI, hIc⟩ := leaf_blocks_le S₁ eIn₁ hx1 hq0 hi hbox (halive.le.trans hT)
      exact sizes_of_blocks hq0 _ x S₁ eIn₁ hi hw0.le hwpow hI hIc hsz₁ hsz₂) hC₀ hC hk hk1 hkC
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  have hSt := stops_rest_le hq1 a' hΛ₁ hokC Ω S₀ (by omega) (Nat.le_ceil _) hwz hArB hsmr hKC hlenC hc hlz hlA
    (fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1, (hreg rt hp hΩ).2.2.2⟩)
    ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  linarith

/-! ### The comparison at one `q` -/

set_option maxHeartbeats 1600000 in
/-- **The comparison in two variables with the rest among the tree's primes, at one `q`.** The family split by
`c = ∏_{i∈S₀} rt_i` against the window `(P₁, P₂]`: at most `P₁` (`fill_below_ib`: a tree to the window, then a tree
below each stop for the rest), or above `P₁` (in the window by `hA`: `fill_window_ib`, a tree for the rest). The rest
is the product of a tree's primes from the first with product above `Ar`, so it lies in `(Ar, (Ar + 1)z₀)`. -/
theorem prop6_fill_core {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {j : ℕ} (Ω : List (GCmp j))
    (S₀ S₁ : Finset (Fin j)) (eIn₁ : Bool) (lo hi : Fin j → ℝ)
    {t T aL bL δ' εw c Λ₀ Λ₁ C₀ δ₁ δ₃ : ℝ} {k J₀C K₀ Kmax smax P₁ P₂ Ar Br z₀ : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a L aL bL δ' εw Λ₀ C₀ δ₃ k J₀C Kmax)
    (hokC : ChainOK2 q a εw Λ₁ δ₁ J₀C K₀ P₁ P₂ Ar Br)
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hΛ₁ : 0 ≤ Λ₁) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlZ : Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ + 1 : ℕ) : ℝ) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + ((j + 2 * smax : ℕ) : ℝ) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hJ : Ω.length + 1 + 2 * (smax * smax) + 5 * smax + 4 ≤ J₀C) (hK : j + 2 * smax ≤ K₀)
    (hKm : j + 2 * smax ≤ Kmax) (hP₁ : 1 ≤ P₁) (hAr : 1 ≤ Ar) (hAB : (P₁ + 1) * z₀ ≤ P₂)
    (hArB : (Ar + 1) * z₀ ≤ Br) (hsm : (P₁ : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hsmr : (Ar : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hl₁ : Real.log ((P₁ : ℝ) + 1) ≤ Λ₁ * Real.log q) (hlr : Real.log ((Ar : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hB : ∀ s : ℝ, (q : ℝ) ^ (∑ i ∈ S₀, lo i) ≤ s → (P₁ : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * s)
    (hA : (q : ℝ) ^ (∑ i ∈ S₀, hi i) ≤ P₂)
    (hT : 4 * (q : ℝ) ^ t * z₀ * ((Ar : ℝ) + 1) ≤ 4 * (q : ℝ) ^ T) (hT' : (Ar : ℝ) + 1 ≤ 4 * (q : ℝ) ^ T)
    (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - aL - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - bL - (∑ i ∈ S₁, hi i + (if eIn₁ then T else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else T)) - c))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hΩc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hΩ : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ ∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          (((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) *
            (1 + ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ)))) +
        (2 * smax + smax * smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃)) +
        (smax * smax + smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hP₁0 : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
  have hlogN : 0 ≤ Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlP₁ : Real.log (P₁ : ℝ) ≤ Λ₁ * Real.log q := (Real.log_le_log hP₁0 (by linarith)).trans hl₁
  -- the two patterns' comparisons
  have hcB : ∀ C ∈ Ω ++ [gUp S₀ (P₁ : ℝ) false], C.c 0 ≤ Λ₁ * Real.log q := by
    intro C hC
    rcases List.mem_append.1 hC with h | h
    · exact hΩc C h
    · rw [List.mem_singleton] at h
      rw [h]
      exact hlP₁
  have hcW : ∀ C ∈ Ω ++ [gDown S₀ (P₁ : ℝ) true], C.c 0 ≤ Λ₁ * Real.log q := by
    intro C hC
    rcases List.mem_append.1 hC with h | h
    · exact hΩc C h
    · rw [List.mem_singleton] at h
      rw [h]
      show -Real.log (P₁ : ℝ) ≤ Λ₁ * Real.log q
      have h1 : 0 ≤ Real.log (P₁ : ℝ) := Real.log_nonneg (by exact_mod_cast hP₁)
      have h2 := mul_nonneg hΛ₁ hlogq
      linarith
  have hpatB : ∀ {rt : Fin j → ℕ}, (∀ i, 1 ≤ rt i) → ((∀ C ∈ Ω ++ [gUp S₀ (P₁ : ℝ) false], C.holds 0 rt) ↔
      (∀ C ∈ Ω, C.holds 0 rt) ∧ ∏ i ∈ S₀, (rt i : ℝ) ≤ P₁) := by
    intro rt h1
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true, gUp_holds _ hP₁0 false 0 h1, Bool.false_eq_true, ite_false]
  have hpatW : ∀ {rt : Fin j → ℕ}, (∀ i, 1 ≤ rt i) → ((∀ C ∈ Ω ++ [gDown S₀ (P₁ : ℝ) true], C.holds 0 rt) ↔
      (∀ C ∈ Ω, C.holds 0 rt) ∧ (P₁ : ℝ) < ∏ i ∈ S₀, (rt i : ℝ)) := by
    intro rt h1
    simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true, gDown_holds _ hP₁0 true 0 h1, ite_true]
  rw [sum_RTg_cmp Ω S₀ hP₁0 (fun rt => ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
    dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0))]
  -- at most `P₁`: two trees
  have hBb := fill_below_ib ha hokL hokC (Ω ++ [gUp S₀ (P₁ : ℝ) false]) S₀ S₁ eIn₁ hi hw2 hwle hwz hz₀ hAB hArB hAr
    hsm hsmr hKm hK (by rw [List.length_append, List.length_singleton]; omega)
    (by rw [List.length_append, List.length_singleton]; omega) hΛ₁ hcB hlz hlZ hl₁ hlr hΛ hX hN
    (fun rt hp hh => by
      obtain ⟨hΩ', -⟩ := (hpatB (fun i => (hp i).one_lt.le)).1 hh
      obtain ⟨hsa, hz, hb⟩ := hΩ rt hp hΩ'
      exact ⟨hsa, hz, fun i => (hb i).2, hB _ (box_prod hq0 S₀ hb).1⟩)
    (fun rt hrt => by
      have := ((hpatB (one_le_of_mem_RTg hrt)).1 (Finset.mem_filter.1 hrt).2).2
      linarith)
    hT hεwc hsz₁ hsz₂ hC₀ hC hk hk1 hkC
  -- above `P₁`: in the window, one tree
  have hΛW : Λ₁ * Real.log q + ((j : ℝ) + smax) * Real.log ((⌊2 * (q : ℝ) ^ L⌋₊ : ℕ) : ℝ) ≤ Λ₀ * Real.log q := by
    have h1 : (j : ℝ) + smax ≤ ((j + 2 * smax : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg smax : (0 : ℝ) ≤ smax)]
    have := mul_le_mul_of_nonneg_right h1 hlogN
    linarith
  have hWb := fill_window_ib ha hokL hokC (Ω ++ [gDown S₀ (P₁ : ℝ) true]) S₀ S₁ eIn₁ hi hw2 hwle hwz hz₀ hArB hAr
    hsmr (by omega) (by omega) (by rw [List.length_append, List.length_singleton]; nlinarith)
    (by rw [List.length_append, List.length_singleton]; nlinarith) hΛ₁ hcW hlz hlr hΛW hX hN
    (fun rt hp hh => by
      obtain ⟨hΩ', hlt⟩ := (hpatW (fun i => (hp i).one_lt.le)).1 hh
      obtain ⟨hsa, hz, hb⟩ := hΩ rt hp hΩ'
      have hle : ∏ i ∈ S₀, (rt i : ℝ) ≤ P₂ := (box_prod hq0 S₀ hb).2.trans hA
      have hlt' : (P₁ : ℝ) < ((∏ i ∈ S₀, rt i : ℕ) : ℝ) := by push_cast; exact hlt
      have hle' : ((∏ i ∈ S₀, rt i : ℕ) : ℝ) ≤ P₂ := by push_cast; exact hle
      exact ⟨hsa, hz, fun i => (hb i).2, by exact_mod_cast hlt', by exact_mod_cast hle'⟩)
    hT' hεwc hsz₁ hsz₂ hC₀ hC hk hk1 hkC
  -- the two families are the parts of the family
  have hS := sum_RTg_cmp (Y := ⌊2 * (q : ℝ) ^ L⌋₊) Ω S₀ hP₁0 (fun rt => 1 / ((∏ i, rt i : ℕ) : ℝ))
  have hnn : ∀ Ω' : List (GCmp j), 0 ≤ ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω', 1 / ((∏ i, rt i : ℕ) : ℝ) :=
    fun Ω' => Finset.sum_nonneg fun rt _ => by positivity
  obtain ⟨Mc, hMcdef⟩ : ∃ Mc : ℝ, Mc = 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
      (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ') :=
    ⟨_, rfl⟩
  have hMc : 0 ≤ Mc := by
    rw [hMcdef]
    have hN' : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
      have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast hN
      linarith
    have hlw : 0 ≤ Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Real.log_nonneg (Nat.one_le_cast.2 (by omega))
    exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.zeta_nonneg hC₀ k))
      (div_nonneg hN' (mul_nonneg (Nat.cast_nonneg _) hlw)))
      (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _))
  rw [← hMcdef] at hBb hWb ⊢
  obtain ⟨Pz, hPz⟩ : ∃ Pz : ℝ, Pz = ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨PN, hPN⟩ : ∃ PN : ℝ,
      PN = ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ (⌊2 * (q : ℝ) ^ L⌋₊ + 1), (1 + 1 / (p : ℝ)) := ⟨_, rfl⟩
  have hPz0 : 0 ≤ Pz := by rw [hPz]; exact Finset.prod_nonneg fun p _ => by positivity
  have hPN0 : 0 ≤ PN := by rw [hPN]; exact Finset.prod_nonneg fun p _ => by positivity
  rw [← hPz, ← hPN] at hBb ⊢
  rw [← hPz] at hWb
  obtain ⟨SB, hSB⟩ : ∃ SB : ℝ, SB = ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gUp S₀ (P₁ : ℝ) false]),
      1 / ((∏ i, rt i : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨SW, hSW⟩ : ∃ SW : ℝ, SW = ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gDown S₀ (P₁ : ℝ) true]),
      1 / ((∏ i, rt i : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hSB, ← hSW] at hS
  rw [← hSB] at hBb
  rw [← hSW] at hWb
  rw [hS]
  have hSB0 : 0 ≤ SB := by rw [hSB]; exact hnn _
  have hSW0 : 0 ≤ SW := by rw [hSW]; exact hnn _
  refine (norm_add_le _ _).trans ?_
  have e1 : Mc * ((SB + SW) * Pz * (1 + PN)) = Mc * (SB * Pz * (1 + PN)) + Mc * (SW * Pz) +
      Mc * (SW * Pz * PN) := by ring
  have h3 : 0 ≤ Mc * (SW * Pz * PN) := mul_nonneg hMc (mul_nonneg (mul_nonneg hSW0 hPz0) hPN0)
  rw [e1]
  have e2 : (2 * (smax : ℝ) + smax * smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃)) +
      ((smax : ℝ) * smax + smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁)) =
      ((smax : ℝ) + smax * smax) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃)) +
        (smax : ℝ) * smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁)) +
        (smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃)) + smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁))) := by
    ring
  linarith

end SieveFill

#print axioms SieveFill.prop6_fill_core
