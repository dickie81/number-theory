/-
# Harman's comparison with stops in two variables, at one modulus

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveP6ib.prop6ib_core` evaluates `Σ_r S(A_r, z₀)` over a family of chains by Buchstab's tree over the primes below
`z₀`, stopped when the product `c∏P` of some of the chain's primes and the tree's enters a window of the Type II
estimate in one variable; it takes the bound for chains with a product in the window as a hypothesis (`ChainOK`).
This file is the same with a hypothesis that fits the estimate in two variables, whose zone for the first variable
depends on the rest: the bound for chains with one product in a window and the product of other primes, the rest,
in a second one.

Plain statements. `GCmp`, `RTg` are `SieveChain`'s; `gUp`, `gDown` `SieveP6Chain`'s; `LeavesOK`
`SieveP6TreeLeaves`'s; `rough z n` and `primesIco w z` `SieveTree`'s; `zeta`, `rem` and `Jw` `SieveProp6`'s. `L` is a
route's (`SieveRoute.Route`), `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋` and `w = ⌈q^{εw}⌉`.

* `ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br`: the bound `q^{L−δ}/φ(q)` for the chains of length at most `K₀ + 1`,
  strictly decreasing with entries at least `q^{e₀}`, with `A < ∏_{i∈S} rt_i ≤ B` and `Ar < ∏_{i∈Sr} rt_i ≤ Br` for
  disjoint sets `S` and `Sr ≠ ∅` of indices, sifted at their last entry.
* `root_bound2`, `root_bound2'`: a family with the first product in its window, sifted at `z₀`: one step of Buchstab's
  identity and `ChainOK2` give `2q^{L−δ}/φ(q)`.
* `stops_bound2`: the stops of the tree at `E = A + 1`, with `(A + 1)z₀ ≤ B`: a stop's first product, the chain's on
  `S₀` times the tree's primes, lies in `(A, (A + 1)z₀)`, and its rest is the chain's.
* `tree_pattern2_le`, `tree_pattern2_ib`: a family below the window, by the tree; its leaves by `LeavesOK`.
* `prop6_two_core`: **the comparison at one `q`.** For a family in boxes `q^{lo_i} ≤ rt_i ≤ q^{hi_i}`, strictly
  decreasing with entries at least `z₀`, whose rest on `Sr` lies in `(Ar, Br]`, with
  `(P₁ + 1)z₀ ≤ P₂`, `q^{Σ_{S₀} hi} ≤ P₂` and `P₁ + 1 ≤ 4q^t·q^{Σ_{S₀} lo}`: the family splits by
  `c = ∏_{S₀} rt ≤ P₁` (a tree) and `P₁ < c` (in the window), and
  `|Σ_r (S(A_r, z₀) − S(B_r, z₀)/φ(q))|` is at most the leaves' main term and remainder plus
  `s_max·q^{L−δ₃}/φ(q) + (s_max + 2)q^{L−δ₁}/φ(q)`.

The proofs are those of `SieveP6Tree.root_bound`, `stops_bound`, `SieveP6ib.tree_pattern_le` and `tree_pattern_ib`
with the rest carried along: its indices keep their places in every extension of a chain, by one prime
(`Fin.castSuccEmb`) or by a block (`Fin.castAddEmb`).

The file imports `SieveP6ib.lean`.
-/
import SieveP6ib

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain SieveP6Tree SieveP6ib

namespace SieveTwoP6

open Classical

variable [Route]

/-- **The bound for chains with two marked products**: `q^{L−δ}/φ(q)` for the chains of length at most `K₀ + 1`
cut out by at most `J₀` comparisons with `m`-parts at most `Λ₁ log q`, each strictly decreasing with entries at least
`q^{e₀}`, `A < ∏_{i∈S} rt_i ≤ B` and `Ar < ∏_{i∈Sr} rt_i ≤ Br`, for disjoint sets `S` and `Sr ≠ ∅` of indices: the
multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime factor below `rt`'s last entry, summed over `rt`. -/
def ChainOK2 (q : ℕ) (a : ZMod q) (e₀ Λ₁ δ : ℝ) (J₀ K₀ A B Ar Br : ℕ) : Prop :=
  ∀ k' ≤ K₀, ∀ (S Sr : Finset (Fin (k' + 1))) (Ω : List (GCmp (k' + 1))), Disjoint S Sr → Sr.Nonempty →
    Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
    (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B ∧
        Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br) →
    ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)

theorem ChainOK2.mono {q : ℕ} (hq : 1 ≤ q) {a : ZMod q} {e₀ Λ₁ δ δ' : ℝ} {J₀ K₀ K₀' A B Ar Br : ℕ}
    (h : ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br) (hδ : δ' ≤ δ) (hK : K₀' ≤ K₀) :
    ChainOK2 q a e₀ Λ₁ δ' J₀ K₀' A B Ar Br := by
  intro k' hk' S Sr Ω hd hne hΩ hc hreg
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine (h k' (hk'.trans hK) S Sr Ω hd hne hΩ hc hreg).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by positivity)

/-! ### A family with its first product in the window -/

/-- **A family with its first product in the window, sifted at `z₀`.** For chains `rt` (length `k′ + 1 ≤ K₀`) cut out
by at most `J₀ − 2` comparisons, each strictly decreasing with entries at least `z₀ ≥ max(1, q^{e₀})`,
`A < ∏_{i∈S} rt_i ≤ B` and `Ar < ∏_{i∈Sr} rt_i ≤ Br`: one step of Buchstab's identity and `ChainOK2` on both terms
bound the multiples of `∏rt` with no prime factor below `z₀` by `2q^{L−δ}/φ(q)`. -/
theorem root_bound2 {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B Ar Br : ℕ}
    (hok : ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br) {k' : ℕ} (hk' : k' + 1 ≤ K₀) (S Sr : Finset (Fin (k' + 1)))
    (hdisj : Disjoint S Sr) (hSr : Sr.Nonempty)
    (Ω : List (GCmp (k' + 1))) (hΩ : Ω.length + 2 ≤ J₀) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) {z₀ : ℕ}
    (hz₀ : 1 ≤ z₀) (hz₀q : (q : ℝ) ^ e₀ ≤ z₀)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B ∧
        Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br) :
    ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      2 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  set N₁ := ⌊(q : ℝ) ^ L⌋₊
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  -- one step of Buchstab's identity
  have hpt : ∀ rt ∈ RTg (k' + 1) N₂ Ω, ∀ n ∈ Finset.Ioc N₁ N₂,
      dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0) =
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) +
          ∑ p ∈ primesIco z₀ (rt (Fin.last k')), dw q a n *
            (if (∏ i, (Fin.snoc rt p : Fin (k' + 1 + 1) → ℕ) i) ∣ n ∧
              rough ((Fin.snoc rt p : Fin (k' + 1 + 1) → ℕ) (Fin.last _)) n then 1 else 0) := by
    intro rt hrt n hn
    have hprime : ∀ i, (rt i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2
    obtain ⟨hanti, hz, -⟩ := hreg rt hprime (Finset.mem_filter.1 hrt).2
    have hW : ∀ p : ℕ, p.Prime → p ∣ ∏ i, rt i → rt (Fin.last k') ≤ p := by
      intro p hp hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hp (hprime i)).1 hi]
      exact hanti.antitone (Fin.le_last i)
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hn).1; omega
    have h := SieveDecomp.buchstab_pt hn0 (hz (Fin.last k')) hW
    have hC : (if (∏ i, rt i) ∣ n ∧ rough z₀ n then (1 : ℂ) else 0) =
        (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) +
          ∑ p ∈ primesIco z₀ (rt (Fin.last k')), (if (∏ i, rt i) * p ∣ n ∧ rough p n then 1 else 0) := by
      have h' := congrArg (fun t : ℝ => (t : ℂ)) h
      simp only [Complex.ofReal_sub, Complex.ofReal_sum, apply_ite (fun t : ℝ => (t : ℂ)), Complex.ofReal_one,
        Complex.ofReal_zero] at h'
      rw [h']
      ring
    rw [hC, mul_add, Finset.mul_sum]
    simp only [SieveDecomp.prod_snoc, Fin.snoc_last]
  rw [Finset.sum_congr rfl fun rt hrt => Finset.sum_congr rfl (hpt rt hrt)]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun rt _ => Finset.sum_comm]
  rw [sum_snoc_chain hz₀ Ω (fun x => ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n *
    (if (∏ i, x i) ∣ n ∧ rough (x (Fin.last _)) n then 1 else 0))]
  refine (norm_add_le _ _).trans ?_
  have h1 := hok k' (by omega) S Sr Ω hdisj hSr (by omega) hc fun rt hp hΩ' => by
    obtain ⟨ha, hz, hlo, hhi, hrl, hrh⟩ := hreg rt hp hΩ'
    exact ⟨ha, fun i => le_trans hz₀q (by exact_mod_cast hz i), hlo, hhi, hrl, hrh⟩
  have h2 := hok (k' + 1) hk' (S.map Fin.castSuccEmb) (Sr.map Fin.castSuccEmb) (extG (z₀ : ℝ) Ω)
    ((Finset.disjoint_map _).2 hdisj) hSr.map (by rw [length_extG]; omega)
    (fun C hC => by
      simp only [extG, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
      rcases hC with ⟨C', hC', rfl⟩ | rfl | rfl
      · exact hc C' hC'
      · show (0 : ℝ) ≤ Λ₁ * Real.log q
        positivity
      · show -Real.log z₀ ≤ Λ₁ * Real.log q
        have : 0 ≤ Real.log z₀ := Real.log_nonneg (by exact_mod_cast hz₀)
        nlinarith)
    fun x hx hΩ' => by
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
      simp only [extG, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, and_true, liftChain_holds] at hΩ'
      obtain ⟨hΩ1, hlt, hge⟩ := hΩ'
      rw [gltVar_holds _ _ 0 hx1] at hlt
      rw [gDown_holds _ hz0 false 0 hx1, Finset.prod_singleton] at hge
      simp only [Bool.false_eq_true, ite_false, Nat.cast_le] at hge
      obtain ⟨ha, hz, hlo, hhi, hrl, hrh⟩ := hreg (Fin.init x) (fun i => hx _) hΩ1
      have hlast : ∀ u, x (Fin.last (k' + 1)) < Fin.init x u := fun u =>
        lt_of_lt_of_le hlt (ha.antitone (Fin.le_last u))
      have hx' : x = Fin.snoc (α := fun _ => ℕ) (Fin.init x) (x (Fin.last (k' + 1))) := (Fin.snoc_init_self x).symm
      have hprodS : ∀ T : Finset (Fin (k' + 1)), ∏ i ∈ T.map Fin.castSuccEmb, x i = ∏ i ∈ T, Fin.init x i :=
        fun T => by
          rw [Finset.prod_map]
          rfl
      refine ⟨?_, fun i => ?_, by rw [hprodS]; exact hlo, by rw [hprodS]; exact hhi, by rw [hprodS]; exact hrl,
        by rw [hprodS]; exact hrh⟩
      · rw [hx']
        exact strictAnti_snoc ha hlast
      · refine le_trans hz₀q ?_
        induction i using Fin.lastCases with
        | last => exact_mod_cast hge
        | cast i => exact_mod_cast hz i
  linarith

/-- `root_bound2` for families of any length. -/
theorem root_bound2' {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B Ar Br : ℕ}
    (hok : ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br) {j : ℕ} (hj : j ≤ K₀) (S Sr : Finset (Fin j))
    (hdisj : Disjoint S Sr) (hSr : Sr.Nonempty) (Ω : List (GCmp j)) (hΩ : Ω.length + 2 ≤ J₀)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) {z₀ : ℕ} (hz₀ : 1 ≤ z₀) (hz₀q : (q : ℝ) ^ e₀ ≤ z₀)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B ∧
        Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      2 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  cases j with
  | zero =>
    obtain ⟨i, -⟩ := hSr
    exact i.elim0
  | succ k' => exact root_bound2 hq a hΛ₁ hok (by omega) S Sr hdisj hSr Ω hΩ hc hz₀ hz₀q hreg

/-! ### The stops of a tree -/

/-- **The stops of a tree.** Let `ChainOK2` hold for the windows `(A, B]` and `(Ar, Br]`, with `(A + 1)z₀ ≤ B` and
`A + 1 ≤ w^{s_max}`, `1 ≤ w ≤ z₀`, `q^{e₀} ≤ w`, `j + s_max ≤ K₀`, `|Ω| + s_max² + 2s_max + 2 ≤ J₀`, and the
comparisons' `m`-parts, `log z₀` and `log(A + 1)` at most `Λ₁ log q`; let the tuples satisfying `Ω` be strictly
decreasing with entries at least `z₀` and `Ar < ∏_{i∈Sr} rt_i ≤ Br`, for `Sr ≠ ∅` disjoint from `S₀`. Then the stops
of the tree at `E = A + 1` total at most `s_max·q^{L−δ}/φ(q)`. -/
theorem stops_bound2 {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B Ar Br : ℕ}
    (hok : ChainOK2 q a e₀ Λ₁ δ J₀ K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ Sr : Finset (Fin j))
    (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty) {w z₀ smax : ℕ}
    (hw : 1 ≤ w) (hwq : (q : ℝ) ^ e₀ ≤ w) (hwz : w ≤ z₀) (hAB : (A + 1) * z₀ ≤ B)
    (hsmax : (A : ℝ) + 1 ≤ (w : ℝ) ^ smax) (hK : j + smax ≤ K₀) (hJ : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlA : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br)
    (N : ℕ) :
    ‖∑ s ∈ range N, (-1 : ℂ) ^ (s + 1) *
        ∑ x ∈ RTg (j + (s + 1)) ⌊2 * (q : ℝ) ^ L⌋₊ (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s),
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, x i) ∣ n ∧ rough (x (Fin.natAdd j (Fin.last s))) n then 1 else 0)‖ ≤
      smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) := by
  have hb : 0 ≤ (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by positivity
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hwz' : (w : ℝ) ≤ z₀ := by exact_mod_cast hwz
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  refine norm_sum_sizes_le hb (fun s => by simp) (fun s hs => ?_) (fun s hs => ?_)
  · refine hok (j + s) (by omega) (idxAll S₀ (s + 1)) (Sr.map (Fin.castAddEmb (s + 1)))
      (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s) ?_ hSr.map ?_ ?_ ?_
    · rw [idxAll, Finset.disjoint_union_left]
      refine ⟨(Finset.disjoint_map _).2 hdisj, (disjoint_of_val fun a ha b hb => ?_).symm⟩
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
      · show -Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q
        have : 0 ≤ Real.log ((A : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)])
        nlinarith
    · intro x hx hΩ
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      obtain ⟨hΩ1, ⟨hanti, hblk⟩, hlo, hhi⟩ := (stopCmps_holds Ω S₀ hE hw0 hz0 hx1).1 hΩ
      obtain ⟨ha, hz, hrl, hrh⟩ := hreg _ (fun i => hx _) hΩ1
      have hcast : ∀ I : Finset (Fin (j + (s + 1))), ((∏ i ∈ I, x i : ℕ) : ℝ) = ∏ i ∈ I, (x i : ℝ) :=
        fun I => Nat.cast_prod _ _
      have hent : ∀ i : Fin (j + (s + 1)), (w : ℝ) ≤ x i := fun i => by
        induction i using Fin.addCases with
        | left i => exact le_trans hwz' (by exact_mod_cast hz i)
        | right u => exact (hblk u).2
      refine ⟨strictAnti_chain (j := j) (t := s + 1) ha hanti (fun i => by exact_mod_cast hz i)
        (fun u => (hblk u).1), fun i => le_trans hwq (hent i), ?_, ?_, ?_, ?_⟩
      · have : (A : ℝ) + 1 ≤ ((∏ i ∈ idxAll S₀ (s + 1), x i : ℕ) : ℝ) := by rw [hcast]; exact hhi
        have : A + 1 ≤ ∏ i ∈ idxAll S₀ (s + 1), x i := by exact_mod_cast this
        exact Nat.lt_of_succ_le this
      · have hlast : (x (Fin.natAdd j (Fin.last s)) : ℝ) < z₀ := (hblk (Fin.last s)).1
        have hpos : (0 : ℝ) ≤ ∏ i ∈ idxInit S₀ s, (x i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
        have h1 : ∏ i ∈ idxAll S₀ (s + 1), (x i : ℝ) < ((A : ℝ) + 1) * z₀ := by
          rw [prod_idxAll_succ]
          calc (∏ i ∈ idxInit S₀ s, (x i : ℝ)) * x (Fin.natAdd j (Fin.last s))
              ≤ (∏ i ∈ idxInit S₀ s, (x i : ℝ)) * z₀ := mul_le_mul_of_nonneg_left hlast.le hpos
            _ < ((A : ℝ) + 1) * z₀ := mul_lt_mul_of_pos_right hlo hz0
        have h2 : (((A + 1) * z₀ : ℕ) : ℝ) ≤ B := by exact_mod_cast hAB
        push_cast at h2
        have h3 : ((∏ i ∈ idxAll S₀ (s + 1), x i : ℕ) : ℝ) < B + 1 := by rw [hcast]; linarith
        have : ∏ i ∈ idxAll S₀ (s + 1), x i < B + 1 := by exact_mod_cast h3
        exact Nat.lt_succ_iff.1 this
      · rw [Finset.prod_map]
        exact hrl
      · rw [Finset.prod_map]
        exact hrh
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
    have h4 : 0 ≤ ∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ) := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    have h5 := mul_le_mul h1 (le_refl (∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ))) h4 (by linarith)
    linarith

/-! ### A tree pattern -/

/-- **A tree pattern.** `SieveP6ib.tree_pattern_le` with `ChainOK2` for the stops: the family's products
`c = ∏_{i∈S₀} rt_i` are below `E = A + 1`, and its rests `∏_{i∈Sr} rt_i` in `(Ar, Br]`. -/
theorem tree_pattern2_le {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δl δc : ℝ}
    {k J₀ J₀' K₀ Kmax A B Ar Br : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ Sr : Finset (Fin j))
    (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty)
    (I : ∀ s, Finset (Fin (j + s))) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀) (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1)
    (hAB : (A + 1) * z₀ ≤ B) (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax)
    (hKC : j + smax ≤ K₀) (hlenL : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀)
    (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀') (hΛ₁ : 0 ≤ Λ₁)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br)
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hgeo : ∀ s < smax, ∀ x ∈ RTg (j + s) ⌊2 * (q : ℝ) ^ L⌋₊
        (SieveP6Tree.leafCmps Ω S₀ ((A : ℝ) + 1) ⌈(q : ℝ) ^ εw⌉₊ z₀ s),
      (q : ℝ) ^ (L - 1 - δ') < ((∏ i, x i : ℕ) : ℝ) →
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i ∈ I s, x i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i ∈ (I s)ᶜ, x i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b))
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
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hreg' : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1⟩
  have hfam' : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1 ∧ ∀ i, z₀ ≤ rt i :=
    fun rt hrt => ⟨hfam rt hrt, (hreg' rt (fun i => (SieveTypeIIU.mem_primesLe.1
      (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2) (Finset.mem_filter.1 hrt).2).2⟩
  rw [SieveP6Tree.tree_chains (Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊) (dw q a') Ω S₀ hE (by omega) hwz hz₀
    hfam']
  refine (norm_add_le _ _).trans ?_
  have hL := SieveP6TreeLeaves.tree_leaves_le ha' hokL Ω S₀ I hE hw2 hwz hz₀ hsmax hKL hlenL hΛ₁ hc hlz hlE hΛ hX
    hN hreg' hgeo hC₀ hC hk hk1 hkC ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  have hS := stops_bound2 hq1 a' hΛ₁ hokC Ω S₀ Sr hdisj hSr (by omega) (Nat.le_ceil _) hwz hAB hsmax hKC hlenC hc
    hlz hlE hreg ((primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀).card + 1)
  linarith

/-- **A tree pattern, with the sizes from the boxes.** `SieveP6ib.tree_pattern_ib` with `ChainOK2` for the stops. -/
theorem tree_pattern2_ib {q : ℕ} [NeZero q] {a' : ZMod q} (ha' : IsUnit a') {a b δ' εw Λ₀ Λ₁ C₀ δl δc t c : ℝ}
    {k J₀ J₀' K₀ Kmax A B Ar Br : ℕ} (hokL : SieveP6TreeLeaves.LeavesOK q a' L a b δ' εw Λ₀ C₀ δl k J₀ Kmax)
    (hokC : ChainOK2 q a' εw Λ₁ δc J₀' K₀ A B Ar Br) {j : ℕ} (Ω : List (GCmp j)) (S₀ Sr : Finset (Fin j))
    (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty) (S₁ : Finset (Fin j))
    (eIn₁ : Bool) (hi : Fin j → ℝ) {z₀ smax : ℕ}
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hAB : (A + 1) * z₀ ≤ B)
    (hsmax : (A : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax) (hKL : j + smax ≤ Kmax) (hKC : j + smax ≤ K₀)
    (hlenL : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀) (hlenC : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀')
    (hΛ₁ : 0 ≤ Λ₁) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlE : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        (A : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (rt i : ℝ) ∧ Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br)
    (hfam : ∀ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∏ i ∈ S₀, (rt i : ℝ) < (A : ℝ) + 1)
    (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - b - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - c))
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
  have hw0 : (0 : ℝ) < ⌈(q : ℝ) ^ εw⌉₊ := by exact_mod_cast (by omega : 0 < ⌈(q : ℝ) ^ εw⌉₊)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  have hE : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hwpow : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
    calc (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (2 * (q : ℝ) ^ εw) ^ (2 * k + 4) :=
          pow_le_pow_left₀ hw0.le hwle _
      _ = 2 ^ (2 * k + 4) * (q : ℝ) ^ c := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ εw), ← Real.rpow_mul hq0.le, ← hεwc]
          push_cast
          ring_nf
  refine tree_pattern2_le ha' hokL hokC Ω S₀ Sr hdisj hSr (Isplit S₁ eIn₁) hw2 hwz hz₀ hAB hsmax hKL hKC hlenL hlenC
    hΛ₁ hc hlz hlE hΛ hX hN
    (fun rt hp hΩ => ⟨(hreg rt hp hΩ).1, (hreg rt hp hΩ).2.1, (hreg rt hp hΩ).2.2.2.2⟩) hfam ?_ hC₀ hC hk hk1 hkC
  intro s _ x hx _
  have hx1 := one_le_of_mem_RTg hx
  obtain ⟨hΩ1, -, halive⟩ := (leafCmps_holds Ω S₀ hE hw0 hz0 hx1).1 (Finset.mem_filter.1 hx).2
  have hprime : ∀ i, (x i).Prime := fun i =>
    (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2
  obtain ⟨-, -, hbox, hAc, -⟩ := hreg _ (fun i => hprime _) hΩ1
  rw [prod_idxAll] at halive
  have hcpos : 0 < ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx1 _
  have hy : ∏ u, (x (Fin.natAdd j u) : ℝ) ≤ 4 * (q : ℝ) ^ t := by
    have h1 : (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * ∏ u, (x (Fin.natAdd j u) : ℝ) <
        (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * (4 * (q : ℝ) ^ t) := by
      calc _ < (A : ℝ) + 1 := halive
        _ ≤ 4 * (q : ℝ) ^ t * ∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ) := hAc
        _ = _ := by ring
    exact (lt_of_mul_lt_mul_left h1 hcpos.le).le
  obtain ⟨hI, hIc⟩ := leaf_blocks_le S₁ eIn₁ hx1 hq0 hi hbox hy
  have hqt : 0 ≤ (q : ℝ) ^ t := by positivity
  have hI' : ∏ i ∈ Isplit S₁ eIn₁ s, (x i : ℝ) ≤ 4 * (q : ℝ) ^ (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) := by
    refine hI.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false, mul_one, add_zero]
      linarith
    · simp only [ite_true]
      rw [Real.rpow_add hq0]
      linarith
  have hIc' : ∏ i ∈ (Isplit S₁ eIn₁ s)ᶜ, (x i : ℝ) ≤
      4 * (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) := by
    refine hIc.trans ?_
    have hS : 0 ≤ (q : ℝ) ^ (∑ i ∈ S₁ᶜ, hi i) := by positivity
    cases eIn₁
    · simp only [Bool.false_eq_true, ite_false]
      rw [Real.rpow_add hq0]
      linarith
    · simp only [ite_true, mul_one, add_zero]
      linarith
  push_cast
  exact leaf_sizes_num hq0 (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) hI' hIc' hw0.le hwpow hsz₁ hsz₂

/-! ### The comparison at one `q` -/

set_option maxHeartbeats 1600000 in
/-- **Harman's comparison with stops in two variables, at one `q`.** The family split by `c = ∏_{i∈S₀} rt_i`
against the window `(P₁, P₂]`: at most `P₁` (a tree, `tree_pattern2_ib`, its blocks small by `hB`), or above `P₁` (in
the window by `hA`: `root_bound2'`). -/
theorem prop6_two_core {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {j : ℕ} (Ω : List (GCmp j))
    (S₀ Sr S₁ : Finset (Fin j)) (hdisj : Disjoint S₀ Sr) (hSr : Sr.Nonempty) (eIn₁ : Bool) (lo hi : Fin j → ℝ)
    {t aL bL δ' εw c Λ₀ Λ₁ C₀ δ₁ δ₃ : ℝ} {k J₀C K₀ Kmax smax P₁ P₂ Ar Br z₀ : ℕ}
    (hokL : SieveP6TreeLeaves.LeavesOK q a L aL bL δ' εw Λ₀ C₀ δ₃ k J₀C Kmax)
    (hokC : ChainOK2 q a εw Λ₁ δ₁ J₀C K₀ P₁ P₂ Ar Br)
    (hw2 : 2 ≤ ⌈(q : ℝ) ^ εw⌉₊) (hwle : (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ εw) (hwz : ⌈(q : ℝ) ^ εw⌉₊ ≤ z₀)
    (hz₀ : z₀ ≤ ⌊2 * (q : ℝ) ^ L⌋₊ + 1) (hz₀q : (q : ℝ) ^ εw ≤ z₀) (hΛ₁ : 0 ≤ Λ₁)
    (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hΛ : Λ₁ * Real.log q + (j + smax) * Real.log ⌊2 * (q : ℝ) ^ L⌋₊ ≤ Λ₀ * Real.log q)
    (hX : 1 ≤ (q : ℝ) ^ (L - 1 - δ')) (hN : ⌊(q : ℝ) ^ L⌋₊ ≤ ⌊2 * (q : ℝ) ^ L⌋₊)
    (hJ : Ω.length + 1 + smax * smax + 2 * smax + 2 ≤ J₀C) (hK : j + smax + 1 ≤ K₀) (hKm : j + smax ≤ Kmax)
    (hP₁ : 1 ≤ P₁) (hAB : (P₁ + 1) * z₀ ≤ P₂) (hsm : (P₁ : ℝ) + 1 ≤ (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ smax)
    (hl₁ : Real.log ((P₁ : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hB : ∀ s : ℝ, (q : ℝ) ^ (∑ i ∈ S₀, lo i) ≤ s → (P₁ : ℝ) + 1 ≤ 4 * (q : ℝ) ^ t * s)
    (hA : (q : ℝ) ^ (∑ i ∈ S₀, hi i) ≤ P₂) (hεwc : (2 * k + 4 : ℝ) * εw = c)
    (hsz₁ : 4 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - aL - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) - c))
    (hsz₂ : 64 * 2 ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - bL - (∑ i ∈ S₁, hi i + (if eIn₁ then t else 0)) -
      2 * (∑ i ∈ S₁ᶜ, hi i + (if eIn₁ then 0 else t)) - c))
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hΩc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q)
    (hΩ : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ (∀ i, (q : ℝ) ^ lo i ≤ rt i ∧ (rt i : ℝ) ≤ (q : ℝ) ^ hi i) ∧
        Ar < ∏ i ∈ Sr, rt i ∧ ∏ i ∈ Sr, rt i ≤ Br) :
    ‖∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
      (2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ')) *
          ((∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
            ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ))) +
        smax * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₃)) +
        (smax + 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ₁)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqn : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hP₁0 : (0 : ℝ) < P₁ := by exact_mod_cast hP₁
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqn)
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
  -- at most `P₁`: a tree
  have hBb := tree_pattern2_ib ha hokL hokC (Ω ++ [gUp S₀ (P₁ : ℝ) false]) S₀ Sr hdisj hSr S₁ eIn₁ hi hw2 hwle hwz
    hz₀ hAB hsm hKm (by omega) (by rw [List.length_append, List.length_singleton]; omega)
    (by rw [List.length_append, List.length_singleton]; omega) hΛ₁ hcB hlz hl₁ hΛ hX hN
    (fun rt hp hh => by
      obtain ⟨hΩ', -⟩ := (hpatB (fun i => (hp i).one_lt.le)).1 hh
      obtain ⟨hsa, hz, hb, hrl, hrh⟩ := hΩ rt hp hΩ'
      exact ⟨hsa, hz, fun i => (hb i).2, hB _ (box_prod hq0 S₀ hb).1, hrl, hrh⟩)
    (fun rt hrt => by
      have := ((hpatB (one_le_of_mem_RTg hrt)).1 (Finset.mem_filter.1 hrt).2).2
      linarith)
    hεwc hsz₁ hsz₂ hC₀ hC hk hk1 hkC
  -- above `P₁`: in the window
  have hWb := root_bound2' hqn a hΛ₁ hokC (by omega) S₀ Sr hdisj hSr (Ω ++ [gDown S₀ (P₁ : ℝ) true])
    (by rw [List.length_append, List.length_singleton]; omega) hcW (by omega) hz₀q
    (fun rt hp hh => by
      obtain ⟨hΩ', hlt⟩ := (hpatW (fun i => (hp i).one_lt.le)).1 hh
      obtain ⟨hsa, hz, hb, hrl, hrh⟩ := hΩ rt hp hΩ'
      have hle : ∏ i ∈ S₀, (rt i : ℝ) ≤ P₂ := (box_prod hq0 S₀ hb).2.trans hA
      have hlt' : (P₁ : ℝ) < ((∏ i ∈ S₀, rt i : ℕ) : ℝ) := by push_cast; exact hlt
      have hle' : ((∏ i ∈ S₀, rt i : ℕ) : ℝ) ≤ P₂ := by push_cast; exact hle
      exact ⟨hsa, hz, by exact_mod_cast hlt', by exact_mod_cast hle', hrl, hrh⟩)
  -- the tree's family is a part of the family
  have hS := sum_RTg_cmp (Y := ⌊2 * (q : ℝ) ^ L⌋₊) Ω S₀ hP₁0 (fun rt => 1 / ((∏ i, rt i : ℕ) : ℝ))
  have hnn : ∀ Ω' : List (GCmp j), 0 ≤ ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω', 1 / ((∏ i, rt i : ℕ) : ℝ) :=
    fun Ω' => Finset.sum_nonneg fun rt _ => by positivity
  have hSle : ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ (Ω ++ [gUp S₀ (P₁ : ℝ) false]), 1 / ((∏ i, rt i : ℕ) : ℝ) ≤
      ∑ rt ∈ RTg j ⌊2 * (q : ℝ) ^ L⌋₊ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) := by
    rw [hS]
    linarith [hnn (Ω ++ [gDown S₀ (P₁ : ℝ) true])]
  have hMc : 0 ≤ 2 * SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
          (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) +
        2 * SieveProp6.rem (⌈(q : ℝ) ^ εw⌉₊ : ℝ) (SieveProp6.Jw ⌈(q : ℝ) ^ εw⌉₊) k * (q : ℝ) ^ (L - 1 - δ') := by
    have hN' : (0 : ℝ) ≤ (⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊ := by
      have : (⌊(q : ℝ) ^ L⌋₊ : ℝ) ≤ ⌊2 * (q : ℝ) ^ L⌋₊ := by exact_mod_cast hN
      linarith
    have hlw : 0 ≤ Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ) := Real.log_nonneg (Nat.one_le_cast.2 (by omega))
    exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.zeta_nonneg hC₀ k))
      (div_nonneg hN' (mul_nonneg (Nat.cast_nonneg _) hlw)))
      (mul_nonneg (mul_nonneg zero_le_two (SieveProp6.rem_nonneg _ _ k)) (Real.rpow_nonneg hq0.le _))
  have hPr : 0 ≤ ∏ p ∈ primesIco ⌈(q : ℝ) ^ εw⌉₊ z₀, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  refine (norm_add_le _ _).trans ?_
  have hmono := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSle hPr) hMc
  linarith

end SieveTwoP6

#print axioms SieveTwoP6.prop6_two_core
