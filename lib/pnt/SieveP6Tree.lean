/-
# Proposition 6 with the bilinear estimate: Buchstab's tree on a family

Plain statements. `GCmp`, `RTg` and `liftChain` are `SieveChain`'s; `gUp`, `gDown`, `gltVar` and `Pblock` are
`SieveP6Chain`'s; `rough z n` and `primesIco w z` are `SieveTree`'s. `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

* `sum_snoc_chain`: the pairs `(rt, p)`, `rt` in a family of chains and `p ∈ [z, rt_last)` prime, are the chains of
  the family extended by `extG` (`p < rt_last`, `z ≤ p`).
* `tree_split`: Buchstab's tree (`SieveTreeStop.tree_weighted_stop`) with the rule `E ≤ c∏P`, for `0 ≤ c < E`: the
  leaves are the `P ⊆ [w, z₀)` with `c∏P < E`, and the stops the `(p, P)` with `c∏P < E ≤ c∏P·p`.
* `sum_powerset_desc`, `sum_stops_by_size`: such sums over sets, by size, as sums over strictly decreasing tuples.
* `tree_chains`: **the tree on a family, as chains.** For `1 ≤ w ≤ z₀ ≤ Y + 1` and a family `RTg j Y Ω` whose tuples
  have entries at least `z₀` and `c = ∏_{i∈S₀} rt_i < E`: the multiples of `∏rt` with no prime factor below `z₀` are
  `Σ_s (−1)^s` times the leaves of size `s` (the chains of `leafCmps`, sifted at `w`) plus `Σ_s (−1)^{s+1}` times the
  stops of size `s + 1` (the chains of `stopCmps`, sifted at their last entry).
* `ChainOK`: the bound `q^{L−δ}/φ(q)` for chains of length at most `K₀ + 1` with a product in the window `(A, B]`.
  `chainOK_TL` and `chainOK_TR` give it for the lower window (`SieveChain.chainTL_bound`) and its reflection
  (`SieveChainR.chainTR_bound`).
* `root_bound`: for a family with a product in a window, sifted at `z₀`, one step of Buchstab's identity
  (`SieveDecomp.buchstab_pt`) and `ChainOK` give `2q^{L−δ}/φ(q)`.
* `stops_bound`: the stops of the tree at `E = A + 1`, with `(A + 1)z₀ ≤ B` and `A + 1 ≤ w^{s_max}`, total at most
  `s_max·q^{L−δ}/φ(q)` by `ChainOK`: a stop's product lies in `(A, (A + 1)z₀)`, and no stop has `s_max` primes below
  `z₀` before its last.

The file imports `SieveP6Chain.lean` and `SieveDecomp.lean`.
-/
import SieveP6Chain
import SieveDecomp

open Real Finset SieveFamily SieveTree SieveChain SieveRoute SieveP6Chain

namespace SieveP6Tree

open Classical

/-! ### One more prime below a chain's last entry -/

/-- One more prime `p ∈ [z, rt_last)` after a chain's primes. -/
noncomputable def extG {k' : ℕ} (z : ℝ) (Ω : List (GCmp (k' + 1))) : List (GCmp (k' + 1 + 1)) :=
  Ω.map liftChain ++ [gltVar (Fin.last k').castSucc (Fin.last (k' + 1)), gDown {Fin.last (k' + 1)} z false]

theorem length_extG {k' : ℕ} (z : ℝ) (Ω : List (GCmp (k' + 1))) : (extG z Ω).length = Ω.length + 2 := by
  simp [extG]

theorem mem_RTg_extG {k' Y z : ℕ} (hz : 1 ≤ z) {Ω : List (GCmp (k' + 1))} {x : Fin (k' + 1 + 1) → ℕ} :
    x ∈ RTg (k' + 1 + 1) Y (extG (z : ℝ) Ω) ↔
      Fin.init x ∈ RTg (k' + 1) Y Ω ∧ x (Fin.last _) ≤ Y ∧ (x (Fin.last _)).Prime ∧ z ≤ x (Fin.last _) ∧
        x (Fin.last _) < x (Fin.last k').castSucc := by
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  simp only [RTg, Finset.mem_filter, Fintype.mem_piFinset, SieveTypeIIU.mem_primesLe]
  constructor
  · rintro ⟨hx, hΩ⟩
    have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).2.one_lt.le
    simp only [extG, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true, liftChain_holds] at hΩ
    obtain ⟨hΩ1, hlt, hge⟩ := hΩ
    rw [gltVar_holds _ _ 0 hx1] at hlt
    rw [gDown_holds _ hz0 false 0 hx1, Finset.prod_singleton] at hge
    simp only [Bool.false_eq_true, ite_false, Nat.cast_le] at hge
    exact ⟨⟨fun i => hx i.castSucc, hΩ1⟩, (hx _).1, (hx _).2, hge, hlt⟩
  · rintro ⟨⟨hx, hΩ⟩, hY, hp, hge, hlt⟩
    have hxx : ∀ i, x i ≤ Y ∧ (x i).Prime := fun i => by
      induction i using Fin.lastCases with
      | last => exact ⟨hY, hp⟩
      | cast i => exact hx i
    have hx1 : ∀ i, 1 ≤ x i := fun i => (hxx i).2.one_lt.le
    refine ⟨hxx, ?_⟩
    simp only [extG, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true, liftChain_holds]
    refine ⟨hΩ, (gltVar_holds _ _ 0 hx1).2 hlt, ?_⟩
    rw [gDown_holds _ hz0 false 0 hx1, Finset.prod_singleton]
    simp only [Bool.false_eq_true, ite_false, Nat.cast_le]
    exact hge

/-- **The extension's bijection.** The pairs `(rt, p)` with `rt` in the family and `p ∈ [z, rt_last)` prime are the
chains of the extended family. -/
theorem sum_snoc_chain {M : Type*} [AddCommMonoid M] {k' Y z : ℕ} (hz : 1 ≤ z) (Ω : List (GCmp (k' + 1)))
    (G : (Fin (k' + 1 + 1) → ℕ) → M) :
    ∑ rt ∈ RTg (k' + 1) Y Ω, ∑ p ∈ primesIco z (rt (Fin.last k')), G (Fin.snoc rt p) =
      ∑ x ∈ RTg (k' + 1 + 1) Y (extG (z : ℝ) Ω), G x := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => Fin.snoc x.1 x.2) (fun x => ⟨Fin.init x, x (Fin.last _)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨rt, p⟩ h
    rw [Finset.mem_sigma] at h
    obtain ⟨hrt, hp⟩ := h
    dsimp only at hrt hp
    rw [mem_primesIco] at hp
    show (Fin.snoc rt p : Fin (k' + 1 + 1) → ℕ) ∈ _
    rw [mem_RTg_extG hz]
    have hrtY := (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1
      (Fin.last k'))).1
    simp only [Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]
    exact ⟨hrt, by omega, hp.2.2, hp.1, hp.2.1⟩
  · intro x hx
    rw [mem_RTg_extG hz] at hx
    rw [Finset.mem_sigma, mem_primesIco]
    exact ⟨hx.1, hx.2.2.2.1, hx.2.2.2.2, hx.2.2.1⟩
  · rintro ⟨rt, p⟩ _
    simp only [Fin.init_snoc, Fin.snoc_last]
  · intro x _
    simp only [Fin.snoc_init_self]
  · intro _ _
    rfl


/-! ### Buchstab's tree with the rule `E ≤ c∏P` -/

/-- **Buchstab's tree with the rule `E ≤ c∏P`.** For `1 ≤ w ≤ z₀`, `r` with every prime factor at least `z₀`, and
`0 ≤ c < E`: `Σ_{n∈C} f(n)[r ∣ n, rough z₀ n]` is the leaves' sum
`Σ_{P ⊆ [w, z₀), c∏P < E} (−1)^{|P|} Σ_{n∈C} f(n)[r∏P ∣ n, rough w n]` plus the stops' sum
`Σ_{w ≤ p < z₀} Σ_{P ⊆ (p, z₀), c∏P < E ≤ c∏P·p} (−1)^{|P|+1} Σ_{n∈C} f(n)[r∏P·p ∣ n, rough p n]`. -/
theorem tree_split (C : Finset ℕ) (f : ℕ → ℂ) {r w z₀ : ℕ} (hw : 1 ≤ w) (hwz : w ≤ z₀)
    (hr : ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p) {c E : ℝ} (hc : 0 ≤ c) (hcE : c < E) :
    ∑ n ∈ C, f n * (if r ∣ n ∧ rough z₀ n then 1 else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
          (if c * ((∏ p ∈ P, p : ℕ) : ℝ) < E then
            ∑ n ∈ C, f n * (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if c * ((∏ p' ∈ P, p' : ℕ) : ℝ) < E ∧ E ≤ c * ((∏ p' ∈ P, p' : ℕ) : ℝ) * p then
            ∑ n ∈ C, f n * (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
  let stop : Finset ℕ → Prop := fun P' => E ≤ c * ((∏ p ∈ P', p : ℕ) : ℝ)
  have hs : ¬ stop ∅ := by
    show ¬ E ≤ c * ((∏ p ∈ (∅ : Finset ℕ), p : ℕ) : ℝ)
    rw [Finset.prod_empty, Nat.cast_one, mul_one]
    exact not_le.2 hcE
  have hlo : ∀ P' : Finset ℕ, stop P' → E ≤ c * ((∏ p ∈ P', p : ℕ) : ℝ) := fun _ h => h
  have hhi : ∀ P' : Finset ℕ, E ≤ c * ((∏ p ∈ P', p : ℕ) : ℝ) → c * ((∏ p ∈ P', p : ℕ) : ℝ) < E * z₀ → stop P' :=
    fun _ h _ => h
  have hPm : ∀ {a : ℕ} {P : Finset ℕ}, P ⊆ primesIco a z₀ → w ≤ a → ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) < z₀ :=
    fun hP ha p hp => by
      have := mem_primesIco.1 (hP hp)
      exact ⟨by omega, by exact_mod_cast this.2.1⟩
  rw [SieveTreeStop.tree_weighted_stop C f hwz hr stop hs]
  congr 1
  · refine Finset.sum_congr rfl fun P hP => ?_
    have hal := SieveTreeStop.alive_iff_lt stop hc hcE hlo hhi (hPm (Finset.mem_powerset.1 hP) le_rfl)
    by_cases h : c * ((∏ p ∈ P, p : ℕ) : ℝ) < E
    · rw [ite_eq_left (hal.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hal.1 h')), ite_eq_right h]
  · refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun P hP => ?_
    have hpm := mem_primesIco.1 hp
    have hP' := Finset.mem_powerset.1 hP
    have hal := SieveTreeStop.alive_iff_lt stop hc hcE hlo hhi (hPm hP' (by omega))
    have hpP : p ∉ P := fun h => by have := mem_primesIco.1 (hP' h); omega
    by_cases h : c * ((∏ p' ∈ P, p' : ℕ) : ℝ) < E
    · have hst := SieveTreeStop.stop_insert_iff stop hc hcE hlo hhi h (by omega) (by exact_mod_cast hpm.2.1) hpP
      by_cases h2 : E ≤ c * ((∏ p' ∈ P, p' : ℕ) : ℝ) * p
      · rw [ite_eq_left ⟨hal.2 h, hst.2 h2⟩, ite_eq_left ⟨h, h2⟩]
      · rw [ite_eq_right (fun h' => h2 (hst.1 h'.2)), ite_eq_right (fun h' => h2 h'.2)]
    · rw [ite_eq_right (fun h' => h (hal.1 h'.1)), ite_eq_right (fun h' => h h'.1)]

/-- A sum over the subsets of `T` with the sign `(−1)^{|P|}`, by size, over strictly decreasing tuples. -/
theorem sum_powerset_desc (T : Finset ℕ) (g : Finset ℕ → ℂ) :
    ∑ P ∈ T.powerset, (-1 : ℂ) ^ P.card * g P =
      ∑ s ∈ range (T.card + 1), (-1 : ℂ) ^ s *
        ∑ y ∈ (Fintype.piFinset fun _ : Fin s => T).filter StrictAnti, g (Finset.univ.image y) := by
  rw [Finset.sum_powerset]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← sum_powersetCard_desc T s g, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_powersetCard.1 hP).2]

/-- A sum over `p ∈ [w, z₀)` and the subsets of the primes of `(p, z₀)` with the sign `(−1)^{|P|+1}`, by size, over
strictly decreasing tuples whose last entry is `p`. -/
theorem sum_stops_by_size {w z₀ : ℕ} (G : ℕ → Finset ℕ → ℂ) :
    ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) * G p P =
      ∑ s ∈ range ((primesIco w z₀).card + 1), (-1 : ℂ) ^ (s + 1) *
        ∑ y ∈ (Fintype.piFinset fun _ : Fin (s + 1) => primesIco w z₀).filter StrictAnti,
          G (y (Fin.last s)) (Finset.univ.image fun u : Fin s => y u.castSucc) := by
  set T := primesIco w z₀ with hT
  have hfil : ∀ p ∈ T, primesIco (p + 1) z₀ = T.filter (p < ·) := fun p hp => by
    obtain ⟨hwp, -, -⟩ := mem_primesIco.1 hp
    ext p'
    simp only [hT, mem_primesIco, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, h2, h3⟩, by omega⟩
    · rintro ⟨⟨-, h2, h3⟩, h4⟩
      exact ⟨by omega, h2, h3⟩
  have hsize : ∀ p ∈ T, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) * G p P =
      ∑ s ∈ range (T.card + 1), ∑ P ∈ (T.filter (p < ·)).powersetCard s, (-1 : ℂ) ^ (s + 1) * G p P := by
    intro p hp
    rw [hfil p hp, Finset.sum_powerset]
    have hle : (T.filter (p < ·)).card + 1 ≤ T.card + 1 := by
      have := Finset.card_filter_le T (p < ·)
      omega
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    have hzero : ∑ s ∈ Finset.Ico ((T.filter (p < ·)).card + 1) (T.card + 1),
        ∑ P ∈ (T.filter (p < ·)).powersetCard s, (-1 : ℂ) ^ (s + 1) * G p P = 0 :=
      Finset.sum_eq_zero fun s hs => by
        rw [Finset.powersetCard_eq_empty.2 (by have := (Finset.mem_Ico.1 hs).1; omega), Finset.sum_empty]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun P hP => ?_
    rw [(Finset.mem_powersetCard.1 hP).2]
  rw [Finset.sum_congr rfl hsize, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [← sum_stops_desc T s G]

/-! ### The tree's branches as chains -/

section Chains

variable {j : ℕ}

/-- The indices of `S₀` in the first block and all of the second, on `Fin (j + s)`. -/
def idxAll (S₀ : Finset (Fin j)) (s : ℕ) : Finset (Fin (j + s)) :=
  S₀.map (Fin.castAddEmb s) ∪ (univ : Finset (Fin s)).map (Fin.natAddEmb j)

/-- The indices of `S₀` in the first block and all but the last of the second, on `Fin (j + (s + 1))`. -/
def idxInit (S₀ : Finset (Fin j)) (s : ℕ) : Finset (Fin (j + (s + 1))) :=
  S₀.map (Fin.castAddEmb (s + 1)) ∪ (univ : Finset (Fin s)).map (Fin.castSuccEmb.trans (Fin.natAddEmb j))

theorem disjoint_of_val {n : ℕ} {A B : Finset (Fin n)} (h : ∀ a ∈ A, ∀ b ∈ B, (a : ℕ) < b) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  exact lt_irrefl _ (h x hxA x hxB)

theorem prod_idxAll (S₀ : Finset (Fin j)) {s : ℕ} (x : Fin (j + s) → ℕ) :
    ∏ i ∈ idxAll S₀ s, (x i : ℝ) = (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * ∏ u, (x (Fin.natAdd j u) : ℝ) := by
  have hd : Disjoint (S₀.map (Fin.castAddEmb s)) ((univ : Finset (Fin s)).map (Fin.natAddEmb j)) := by
    refine disjoint_of_val fun a ha b hb => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hb
    show (i : ℕ) < j + u
    have := i.isLt
    omega
  rw [idxAll, Finset.prod_union hd, Finset.prod_map, Finset.prod_map]
  rfl

theorem prod_idxInit (S₀ : Finset (Fin j)) {s : ℕ} (x : Fin (j + (s + 1)) → ℕ) :
    ∏ i ∈ idxInit S₀ s, (x i : ℝ) =
      (∏ i ∈ S₀, (x (Fin.castAdd (s + 1) i) : ℝ)) * ∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ) := by
  have hd : Disjoint (S₀.map (Fin.castAddEmb (s + 1)))
      ((univ : Finset (Fin s)).map (Fin.castSuccEmb.trans (Fin.natAddEmb j))) := by
    refine disjoint_of_val fun a ha b hb => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hb
    show (i : ℕ) < j + u
    have := i.isLt
    omega
  rw [idxInit, Finset.prod_union hd, Finset.prod_map, Finset.prod_map]
  rfl

theorem RTg_append (K Y : ℕ) (Ω Ω' : List (GCmp K)) :
    RTg K Y (Ω ++ Ω') = (RTg K Y Ω).filter (fun x => ∀ C ∈ Ω', C.holds 0 x) := by
  unfold RTg
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun x _ => ?_
  simp only [List.forall_mem_append]

theorem one_le_of_mem_RTg {K Y : ℕ} {Ω : List (GCmp K)} {x : Fin K → ℕ} (hx : x ∈ RTg K Y Ω) (i : Fin K) :
    1 ≤ x i :=
  (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)).2.one_lt.le

/-- The comparisons of a leaf with a block of size `s`: the family's on the first block, the block's (`Pblock`), and
`c∏y < E` with `c = ∏_{i∈S₀} rt_i`. -/
noncomputable def leafCmps (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) (E w z₀ : ℝ) (s : ℕ) : List (GCmp (j + s)) :=
  Ω.map liftChain ++ Pblock j s w z₀ ++ [gUp (idxAll S₀ s) E true]

/-- The comparisons of a stop with a block `y` of size `s + 1`: the family's on the first block, the block's, and
`c∏y' < E ≤ c∏y` with `y'` the block without its last entry. -/
noncomputable def stopCmps (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) (E w z₀ : ℝ) (s : ℕ) :
    List (GCmp (j + (s + 1))) :=
  Ω.map liftChain ++ Pblock j (s + 1) w z₀ ++ [gUp (idxInit S₀ s) E true, gDown (idxAll S₀ (s + 1)) E false]

/-- **The leaves of size `s` as chains.** -/
theorem sum_leaves_chain {M : Type*} [AddCommMonoid M] (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) {E : ℝ}
    (hE : 0 < E) {Y w z₀ : ℕ} (s : ℕ) (hw : 1 ≤ w) (hwz : w ≤ z₀) (hz₀ : z₀ ≤ Y + 1) (G : ℕ → M) :
    ∑ rt ∈ RTg j Y Ω, ∑ y ∈ (Fintype.piFinset fun _ : Fin s => primesIco w z₀).filter StrictAnti,
        (if (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u, y u : ℕ) : ℝ) < E then G ((∏ i, rt i) * ∏ u, y u) else 0) =
      ∑ x ∈ RTg (j + s) Y (leafCmps Ω S₀ E w z₀ s), G (∏ i, x i) := by
  rw [sum_chain j s Ω hw hwz hz₀ (fun rt y =>
    if (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u, y u : ℕ) : ℝ) < E then G ((∏ i, rt i) * ∏ u, y u) else 0)]
  rw [leafCmps, RTg_append (j + s) Y (Ω.map liftChain ++ Pblock j s w z₀), Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 := one_le_of_mem_RTg hx
  have hcond : (∀ C ∈ [gUp (idxAll S₀ s) E true], C.holds 0 x) ↔
      (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * ((∏ u, x (Fin.natAdd j u) : ℕ) : ℝ) < E := by
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    rw [gUp_holds _ hE true 0 hx1, prod_idxAll]
    push_cast
    simp
  have hprod : (∏ i, x (Fin.castAdd s i)) * ∏ u, x (Fin.natAdd j u) = ∏ i, x i := (Fin.prod_univ_add x).symm
  by_cases h : (∏ i ∈ S₀, (x (Fin.castAdd s i) : ℝ)) * ((∏ u, x (Fin.natAdd j u) : ℕ) : ℝ) < E
  · rw [ite_eq_left h, ite_eq_left (hcond.2 h), hprod]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hcond.1 h'))]

/-- **The stops of size `s + 1` as chains.** -/
theorem sum_stops_chain {M : Type*} [AddCommMonoid M] (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) {E : ℝ}
    (hE : 0 < E) {Y w z₀ : ℕ} (s : ℕ) (hw : 1 ≤ w) (hwz : w ≤ z₀) (hz₀ : z₀ ≤ Y + 1) (G : ℕ → ℕ → M) :
    ∑ rt ∈ RTg j Y Ω, ∑ y ∈ (Fintype.piFinset fun _ : Fin (s + 1) => primesIco w z₀).filter StrictAnti,
        (if (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) < E ∧
            E ≤ (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) * (y (Fin.last s) : ℝ) then
          G ((∏ i, rt i) * (∏ u : Fin s, y u.castSucc) * y (Fin.last s)) (y (Fin.last s)) else 0) =
      ∑ x ∈ RTg (j + (s + 1)) Y (stopCmps Ω S₀ E w z₀ s), G (∏ i, x i) (x (Fin.natAdd j (Fin.last s))) := by
  rw [sum_chain j (s + 1) Ω hw hwz hz₀ (fun rt y =>
    if (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) < E ∧
        E ≤ (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) * (y (Fin.last s) : ℝ) then
      G ((∏ i, rt i) * (∏ u : Fin s, y u.castSucc) * y (Fin.last s)) (y (Fin.last s)) else 0)]
  rw [stopCmps, RTg_append (j + (s + 1)) Y (Ω.map liftChain ++ Pblock j (s + 1) w z₀), Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 := one_le_of_mem_RTg hx
  have hall : ∏ u : Fin (s + 1), (x (Fin.natAdd j u) : ℝ) =
      (∏ u : Fin s, (x (Fin.natAdd j u.castSucc) : ℝ)) * x (Fin.natAdd j (Fin.last s)) :=
    Fin.prod_univ_castSucc _
  have hcond : (∀ C ∈ [gUp (idxInit S₀ s) E true, gDown (idxAll S₀ (s + 1)) E false], C.holds 0 x) ↔
      (∏ i ∈ S₀, (x (Fin.castAdd (s + 1) i) : ℝ)) * ((∏ u : Fin s, x (Fin.natAdd j u.castSucc) : ℕ) : ℝ) < E ∧
        E ≤ (∏ i ∈ S₀, (x (Fin.castAdd (s + 1) i) : ℝ)) *
          ((∏ u : Fin s, x (Fin.natAdd j u.castSucc) : ℕ) : ℝ) * (x (Fin.natAdd j (Fin.last s)) : ℝ) := by
    simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
    rw [gUp_holds _ hE true 0 hx1, gDown_holds _ hE false 0 hx1, prod_idxInit, prod_idxAll, hall]
    push_cast
    simp only [ite_true, mul_assoc]
  have hprod : (∏ i, x (Fin.castAdd (s + 1) i)) * (∏ u : Fin s, x (Fin.natAdd j u.castSucc)) *
      x (Fin.natAdd j (Fin.last s)) = ∏ i, x i := by
    rw [Fin.prod_univ_add x, Fin.prod_univ_castSucc (fun u => x (Fin.natAdd j u)), mul_assoc]
  by_cases h : (∏ i ∈ S₀, (x (Fin.castAdd (s + 1) i) : ℝ)) *
      ((∏ u : Fin s, x (Fin.natAdd j u.castSucc) : ℕ) : ℝ) < E ∧
        E ≤ (∏ i ∈ S₀, (x (Fin.castAdd (s + 1) i) : ℝ)) *
          ((∏ u : Fin s, x (Fin.natAdd j u.castSucc) : ℕ) : ℝ) * (x (Fin.natAdd j (Fin.last s)) : ℝ)
  · rw [ite_eq_left h, ite_eq_left (hcond.2 h), hprod]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hcond.1 h'))]

/-- **Buchstab's tree on a family, as chains.** For `1 ≤ w ≤ z₀ ≤ Y + 1` and a family `RTg j Y Ω` whose tuples have
entries at least `z₀` and `c = ∏_{i∈S₀} rt_i < E`: the multiples of `∏rt` with no prime factor below `z₀` are the
leaves of the sizes `s ≤ |[w, z₀)|`, the chains of `leafCmps` (with the sign `(−1)^s`, sifted at `w`), plus the stops,
the chains of `stopCmps` (with the sign `(−1)^{s+1}`, sifted at their last entry). -/
theorem tree_chains (C : Finset ℕ) (f : ℕ → ℂ) (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) {E : ℝ} (hE : 0 < E)
    {Y w z₀ : ℕ} (hw : 1 ≤ w) (hwz : w ≤ z₀) (hz₀ : z₀ ≤ Y + 1)
    (hfam : ∀ rt ∈ RTg j Y Ω, (∏ i ∈ S₀, (rt i : ℝ)) < E ∧ ∀ i, z₀ ≤ rt i) :
    ∑ rt ∈ RTg j Y Ω, ∑ n ∈ C, f n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0) =
      ∑ s ∈ range ((primesIco w z₀).card + 1), (-1 : ℂ) ^ s *
          ∑ x ∈ RTg (j + s) Y (leafCmps Ω S₀ E w z₀ s),
            ∑ n ∈ C, f n * (if (∏ i, x i) ∣ n ∧ rough w n then 1 else 0) +
        ∑ s ∈ range ((primesIco w z₀).card + 1), (-1 : ℂ) ^ (s + 1) *
          ∑ x ∈ RTg (j + (s + 1)) Y (stopCmps Ω S₀ E w z₀ s),
            ∑ n ∈ C, f n * (if (∏ i, x i) ∣ n ∧ rough (x (Fin.natAdd j (Fin.last s))) n then 1 else 0) := by
  set T := primesIco w z₀ with hT
  have hrt : ∀ rt ∈ RTg j Y Ω, ∑ n ∈ C, f n * (if (∏ i, rt i) ∣ n ∧ rough z₀ n then 1 else 0) =
      ∑ s ∈ range (T.card + 1), (-1 : ℂ) ^ s * ∑ y ∈ (Fintype.piFinset fun _ : Fin s => T).filter StrictAnti,
          (if (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u, y u : ℕ) : ℝ) < E then
            ∑ n ∈ C, f n * (if (∏ i, rt i) * (∏ u, y u) ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ s ∈ range (T.card + 1), (-1 : ℂ) ^ (s + 1) *
          ∑ y ∈ (Fintype.piFinset fun _ : Fin (s + 1) => T).filter StrictAnti,
            (if (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) < E ∧
                E ≤ (∏ i ∈ S₀, (rt i : ℝ)) * ((∏ u : Fin s, y u.castSucc : ℕ) : ℝ) * (y (Fin.last s) : ℝ) then
              ∑ n ∈ C, f n * (if (∏ i, rt i) * (∏ u : Fin s, y u.castSucc) * y (Fin.last s) ∣ n ∧
                rough (y (Fin.last s)) n then 1 else 0) else 0) := by
    intro rt hrt
    obtain ⟨hcE, hz⟩ := hfam rt hrt
    have hprime : ∀ i, (rt i).Prime := fun i =>
      (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hrt).1 i)).2
    have hr : ∀ p : ℕ, p.Prime → p ∣ ∏ i, rt i → z₀ ≤ p := by
      intro p hp hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hp (hprime i)).1 hi]
      exact hz i
    have hc : (0 : ℝ) ≤ ∏ i ∈ S₀, (rt i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    rw [tree_split C f hw hwz hr hc hcE, sum_powerset_desc, sum_stops_by_size]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      have hinj := (Finset.mem_filter.1 hy).2.injective
      rw [Finset.prod_image fun u _ v _ h => hinj h]
    · refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      have hinj : Function.Injective fun u : Fin s => y u.castSucc :=
        fun u v h => Fin.castSucc_injective _ ((Finset.mem_filter.1 hy).2.injective h)
      rw [Finset.prod_image fun u _ v _ h => hinj h]
  rw [Finset.sum_congr rfl hrt, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum, sum_leaves_chain Ω S₀ hE s hw hwz hz₀
      (fun d => ∑ n ∈ C, f n * (if d ∣ n ∧ rough w n then 1 else 0))]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum, sum_stops_chain Ω S₀ hE s hw hwz hz₀
      (fun d p => ∑ n ∈ C, f n * (if d ∣ n ∧ rough p n then 1 else 0))]

theorem strictAnti_append {a b : ℕ} {u : Fin a → ℕ} {v : Fin b → ℕ} (hu : StrictAnti u) (hv : StrictAnti v)
    (huv : ∀ i k, v k < u i) : StrictAnti (Fin.append u v) := by
  intro x y hxy
  induction x using Fin.addCases with
  | left i =>
    induction y using Fin.addCases with
    | left i' =>
      rw [Fin.append_left, Fin.append_left]
      exact hu (Fin.lt_def.2 (Fin.lt_def.1 hxy))
    | right k =>
      rw [Fin.append_left, Fin.append_right]
      exact huv i k
  | right k =>
    induction y using Fin.addCases with
    | left i' =>
      exfalso
      have h1 := Fin.lt_def.1 hxy
      have h2 := i'.isLt
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
      omega
    | right k' =>
      rw [Fin.append_right, Fin.append_right]
      refine hv (Fin.lt_def.2 ?_)
      have h1 := Fin.lt_def.1 hxy
      simp only [Fin.val_natAdd] at h1
      omega

theorem Pblock_c_le {j s : ℕ} {w z₀ B : ℝ} (hB : 0 ≤ B) (hz : Real.log z₀ ≤ B) (hw : 1 ≤ w) :
    ∀ C ∈ Pblock j s w z₀, C.c 0 ≤ B := by
  intro C hC
  unfold Pblock at hC
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and] at hC
  rcases hC with (hC | ⟨u, rfl⟩) | ⟨u, rfl⟩
  · obtain ⟨u, v, -, rfl⟩ := mem_ltPairs.1 hC
    show (0 : ℝ) ≤ B
    exact hB
  · show Real.log z₀ ≤ B
    exact hz
  · show -Real.log w ≤ B
    have := Real.log_nonneg hw
    linarith

/-- What the comparisons of a leaf say. -/
theorem leafCmps_holds {j : ℕ} (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) {E : ℝ} (hE : 0 < E) {w z₀ : ℝ}
    (hw : 0 < w) (hz : 0 < z₀) {s : ℕ} {x : Fin (j + s) → ℕ} (hx1 : ∀ i, 1 ≤ x i) :
    (∀ C ∈ leafCmps Ω S₀ E w z₀ s, C.holds 0 x) ↔
      (∀ C ∈ Ω, C.holds 0 (fun i => x (Fin.castAdd s i))) ∧
        (StrictAnti (fun u : Fin s => x (Fin.natAdd j u)) ∧
          ∀ u : Fin s, (x (Fin.natAdd j u) : ℝ) < z₀ ∧ w ≤ (x (Fin.natAdd j u) : ℝ)) ∧
        ∏ i ∈ idxAll S₀ s, (x i : ℝ) < E := by
  simp only [leafCmps, List.forall_mem_append, List.forall_mem_map, liftChain_holds, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true, Pblock_holds hw hz 0 hx1, gUp_holds _ hE true 0 hx1,
    ite_true, and_assoc]

/-- What the comparisons of a stop say. -/
theorem stopCmps_holds {j : ℕ} (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) {E : ℝ} (hE : 0 < E) {w z₀ : ℝ}
    (hw : 0 < w) (hz : 0 < z₀) {s : ℕ} {x : Fin (j + (s + 1)) → ℕ} (hx1 : ∀ i, 1 ≤ x i) :
    (∀ C ∈ stopCmps Ω S₀ E w z₀ s, C.holds 0 x) ↔
      (∀ C ∈ Ω, C.holds 0 (fun i => x (Fin.castAdd (s + 1) i))) ∧
        (StrictAnti (fun u : Fin (s + 1) => x (Fin.natAdd j u)) ∧
          ∀ u : Fin (s + 1), (x (Fin.natAdd j u) : ℝ) < z₀ ∧ w ≤ (x (Fin.natAdd j u) : ℝ)) ∧
        ∏ i ∈ idxInit S₀ s, (x i : ℝ) < E ∧ E ≤ ∏ i ∈ idxAll S₀ (s + 1), (x i : ℝ) := by
  simp only [stopCmps, List.forall_mem_append, List.forall_mem_map, liftChain_holds, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true, Pblock_holds hw hz 0 hx1, gUp_holds _ hE true 0 hx1,
    gDown_holds _ hE false 0 hx1, ite_true, Bool.false_eq_true, ite_false, and_assoc]

/-- The tuples of a family of leaves or stops, with the family's tuples strictly decreasing with entries at least `z₀`
and the block's entries below `z₀`, are strictly decreasing. -/
theorem strictAnti_chain {j t : ℕ} {x : Fin (j + t) → ℕ} {z₀ : ℝ} (h1 : StrictAnti (fun i => x (Fin.castAdd t i)))
    (h2 : StrictAnti (fun u => x (Fin.natAdd j u))) (h3 : ∀ i, z₀ ≤ (x (Fin.castAdd t i) : ℝ))
    (h4 : ∀ u, (x (Fin.natAdd j u) : ℝ) < z₀) : StrictAnti x := by
  have e : x = Fin.append (fun i => x (Fin.castAdd t i)) (fun u => x (Fin.natAdd j u)) :=
    (Fin.append_castAdd_natAdd (f := x)).symm
  rw [e]
  exact strictAnti_append h1 h2 fun i k => by exact_mod_cast (h4 k).trans_le (h3 i)

theorem prod_idxAll_succ (S₀ : Finset (Fin j)) {s : ℕ} (x : Fin (j + (s + 1)) → ℕ) :
    ∏ i ∈ idxAll S₀ (s + 1), (x i : ℝ) = (∏ i ∈ idxInit S₀ s, (x i : ℝ)) * x (Fin.natAdd j (Fin.last s)) := by
  rw [prod_idxAll, prod_idxInit, Fin.prod_univ_castSucc]
  ring

/-- A sum over sizes, with signs of norm at most one, whose terms are at most `b` below `s_max` and vanish from
`s_max` on, is at most `s_max·b`. -/
theorem norm_sum_sizes_le {N smax : ℕ} {b : ℝ} (hb : 0 ≤ b) {ε X : ℕ → ℂ} (hε : ∀ s, ‖ε s‖ ≤ 1)
    (hX : ∀ s < smax, ‖X s‖ ≤ b) (h0 : ∀ s, smax ≤ s → X s = 0) :
    ‖∑ s ∈ range N, ε s * X s‖ ≤ smax * b := by
  have hterm : ∀ s ∈ range N, ‖ε s * X s‖ ≤ if s < smax then b else 0 := by
    intro s _
    rw [norm_mul]
    by_cases hs : s < smax
    · rw [ite_eq_left hs]
      calc ‖ε s‖ * ‖X s‖ ≤ 1 * b := mul_le_mul (hε s) (hX s hs) (norm_nonneg _) zero_le_one
        _ = b := one_mul b
    · rw [ite_eq_right hs, h0 s (not_lt.1 hs), norm_zero, mul_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((range N).filter (· < smax)).card ≤ smax :=
    (Finset.card_le_card fun s hs => Finset.mem_range.2 (Finset.mem_filter.1 hs).2).trans (Finset.card_range smax).le
  have : (((range N).filter (· < smax)).card : ℝ) ≤ smax := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right this hb

end Chains

variable [Route]

/-! ### Chains with a product in a window, for every length up to a bound -/

/-- **Chains with a product in a window.** `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)` for the multiples `n ∈ (N₁, N₂]` of `∏rt` with
no prime factor below `rt`'s last entry, summed over a family of chains of length at most `K₀ + 1` cut out by at most
`J₀` comparisons with `m`-parts at most `Λ₁ log q`, each chain strictly decreasing, with entries at least `q^{e₀}` and
`A < ∏_{i∈S} rt_i ≤ B`. -/
def ChainOK (q : ℕ) (a : ZMod q) (e₀ Λ₁ δ : ℝ) (J₀ K₀ A B : ℕ) : Prop :=
  ∀ k' ≤ K₀, ∀ (S : Finset (Fin (k' + 1))) (Ω : List (GCmp (k' + 1))), Ω.length ≤ J₀ →
    (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
    (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B) →
    ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω, ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
        dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)

theorem ChainOK.mono {q : ℕ} (hq : 1 ≤ q) {a : ZMod q} {e₀ Λ₁ δ δ' : ℝ} {J₀ K₀ K₀' A B : ℕ}
    (h : ChainOK q a e₀ Λ₁ δ J₀ K₀ A B) (hδ : δ' ≤ δ) (hK : K₀' ≤ K₀) : ChainOK q a e₀ Λ₁ δ' J₀ K₀' A B := by
  intro k' hk' S Ω hΩ hc hreg
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine (h k' (hk'.trans hK) S Ω hΩ hc hreg).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by positivity)

/-- **The lower window for every length up to `K₀ + 1`** (`SieveChain.chainTL_bound`). -/
theorem chainOK_TL [RouteOK] (hII : TypeIIAt) {e₀ : ℝ} (he₀ : 0 < e₀) (K₀ J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ P₁ P₂ : ℕ, (q : ℝ) ^ (w₁ * L) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
        ChainOK q a e₀ Λ₁ δ J₀ K₀ P₁ P₂ := by
  induction K₀ with
  | zero =>
    obtain ⟨δ, hδ, q₀, H⟩ := chainTL_bound hII he₀ 0 J₀ hΛ₁
    refine ⟨δ, hδ, q₀, fun q _ hq a ha P₁ P₂ hP₁ hP₂ k' hk' S Ω hΩ hc hreg => ?_⟩
    obtain rfl : k' = 0 := by omega
    exact H q hq a ha S Ω P₁ P₂ hΩ hc hP₁ hP₂ hreg
  | succ K ih =>
    obtain ⟨δ₁, hδ₁, q₁, H₁⟩ := ih
    obtain ⟨δ₂, hδ₂, q₂, H₂⟩ := chainTL_bound hII he₀ (K + 1) J₀ hΛ₁
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max q₁ q₂, fun q _ hq a ha P₁ P₂ hP₁ hP₂ k' hk' S Ω hΩ hc hreg => ?_⟩
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    rcases Nat.lt_or_ge k' (K + 1) with h | h
    · exact (H₁ q (le_trans (le_max_left _ _) hq) a ha P₁ P₂ hP₁ hP₂).mono hq1 (min_le_left _ _) le_rfl k'
        (by omega) S Ω hΩ hc hreg
    · obtain rfl : k' = K + 1 := by omega
      refine (H₂ q (le_trans (le_max_right _ _) hq) a ha S Ω P₁ P₂ hΩ hc hP₁ hP₂ hreg).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
        (by linarith [min_le_right δ₁ δ₂])) (by positivity)

/-- **The reflected window for every length up to `K₀ + 1`** (`SieveChainR.chainTR_bound`). -/
theorem chainOK_TR [RouteOK] (hII : TypeIIAt) {e₀ : ℝ} (he₀ : 0 < e₀) (K₀ J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ W₀ W₁ : ℕ, W₁ ≤ ⌊(q : ℝ) ^ L⌋₊ → (q : ℝ) ^ (w₁ * L) ≤ ((⌊(q : ℝ) ^ L⌋₊ / W₁ : ℕ) : ℝ) →
        ((⌊2 * (q : ℝ) ^ L⌋₊ / (W₀ + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
        ChainOK q a e₀ Λ₁ δ J₀ K₀ W₀ W₁ := by
  induction K₀ with
  | zero =>
    obtain ⟨δ, hδ, q₀, H⟩ := SieveChainR.chainTR_bound hII he₀ 0 J₀ hΛ₁
    refine ⟨δ, hδ, q₀, fun q _ hq a ha W₀ W₁ hW hP₁ hP₂ k' hk' S Ω hΩ hc hreg => ?_⟩
    obtain rfl : k' = 0 := by omega
    exact H q hq a ha S Ω W₀ W₁ hΩ hc hreg hW hP₁ hP₂
  | succ K ih =>
    obtain ⟨δ₁, hδ₁, q₁, H₁⟩ := ih
    obtain ⟨δ₂, hδ₂, q₂, H₂⟩ := SieveChainR.chainTR_bound hII he₀ (K + 1) J₀ hΛ₁
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max q₁ q₂, fun q _ hq a ha W₀ W₁ hW hP₁ hP₂ k' hk' S Ω hΩ hc hreg => ?_⟩
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    rcases Nat.lt_or_ge k' (K + 1) with h | h
    · exact (H₁ q (le_trans (le_max_left _ _) hq) a ha W₀ W₁ hW hP₁ hP₂).mono hq1 (min_le_left _ _) le_rfl k'
        (by omega) S Ω hΩ hc hreg
    · obtain rfl : k' = K + 1 := by omega
      refine (H₂ q (le_trans (le_max_right _ _) hq) a ha S Ω W₀ W₁ hΩ hc hreg hW hP₁ hP₂).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
        (by linarith [min_le_right δ₁ δ₂])) (by positivity)

/-! ### A family with a product in a window -/

/-- **A family with a product in a window, sifted at `z₀`.** For chains `rt` (length `k′ + 1 ≤ K₀`) cut out by at
most `J₀ − 2` comparisons with `m`-parts at most `Λ₁ log q` (`Λ₁ ≥ 0`), each strictly decreasing, with entries at least
`z₀ ≥ max(1, q^{e₀})` and `A < ∏_{i∈S} rt_i ≤ B`: one step of Buchstab's identity, `S(A_r, z₀) = S(A_r, rt_last) +
Σ_{z₀ ≤ p < rt_last} S(A_{rp}, p)`, and `ChainOK` on both terms bound the multiples of `∏rt` with no prime factor below
`z₀` by `2q^{L−δ}/φ(q)`. -/
theorem root_bound {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B : ℕ}
    (hok : ChainOK q a e₀ Λ₁ δ J₀ K₀ A B) {k' : ℕ} (hk' : k' + 1 ≤ K₀) (S : Finset (Fin (k' + 1)))
    (Ω : List (GCmp (k' + 1))) (hΩ : Ω.length + 2 ≤ J₀) (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) {z₀ : ℕ}
    (hz₀ : 1 ≤ z₀) (hz₀q : (q : ℝ) ^ e₀ ≤ z₀)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ A < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ B) :
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
  have h1 := hok k' (by omega) S Ω (by omega) hc fun rt hp hΩ' => by
    obtain ⟨ha, hz, hlo, hhi⟩ := hreg rt hp hΩ'
    exact ⟨ha, fun i => le_trans hz₀q (by exact_mod_cast hz i), hlo, hhi⟩
  have h2 := hok (k' + 1) hk' (S.map Fin.castSuccEmb) (extG (z₀ : ℝ) Ω) (by rw [length_extG]; omega)
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
      obtain ⟨ha, hz, hlo, hhi⟩ := hreg (Fin.init x) (fun i => hx _) hΩ1
      have hlast : ∀ u, x (Fin.last (k' + 1)) < Fin.init x u := fun u =>
        lt_of_lt_of_le hlt (ha.antitone (Fin.le_last u))
      have hx' : x = Fin.snoc (α := fun _ => ℕ) (Fin.init x) (x (Fin.last (k' + 1))) := (Fin.snoc_init_self x).symm
      have hprodS : ∏ i ∈ S.map Fin.castSuccEmb, x i = ∏ i ∈ S, Fin.init x i := by
        rw [Finset.prod_map]
        rfl
      refine ⟨?_, fun i => ?_, by rw [hprodS]; exact hlo, by rw [hprodS]; exact hhi⟩
      · rw [hx']
        exact strictAnti_snoc ha hlast
      · refine le_trans hz₀q ?_
        induction i using Fin.lastCases with
        | last => exact_mod_cast hge
        | cast i => exact_mod_cast hz i
  linarith


/-! ### The stops of a tree -/

/-- **The stops of a tree.** Let `ChainOK` hold for the window `(A, B]`, with `(A + 1)z₀ ≤ B` and
`A + 1 ≤ w^{s_max}`, `1 ≤ w ≤ z₀`, `q^{e₀} ≤ w`, `j + s_max ≤ K₀`, `|Ω| + s_max² + 2s_max + 2 ≤ J₀`, and the
comparisons' `m`-parts, `log z₀` and `log(A + 1)` at most `Λ₁ log q`; let the tuples satisfying `Ω` be strictly
decreasing with entries at least `z₀`. Then the stops of the tree at `E = A + 1` (the chains of `stopCmps` with the
signs `(−1)^{s+1}`, sifted at their last entry) total at most `s_max·q^{L−δ}/φ(q)`. -/
theorem stops_bound {q : ℕ} (hq : 1 ≤ q) (a : ZMod q) {e₀ Λ₁ δ : ℝ} (hΛ₁ : 0 ≤ Λ₁) {J₀ K₀ A B : ℕ}
    (hok : ChainOK q a e₀ Λ₁ δ J₀ K₀ A B) {j : ℕ} (Ω : List (GCmp j)) (S₀ : Finset (Fin j)) {w z₀ smax : ℕ}
    (hw : 1 ≤ w) (hwq : (q : ℝ) ^ e₀ ≤ w) (hwz : w ≤ z₀) (hAB : (A + 1) * z₀ ≤ B)
    (hsmax : (A : ℝ) + 1 ≤ (w : ℝ) ^ smax) (hK : j + smax ≤ K₀) (hJ : Ω.length + smax * smax + 2 * smax + 2 ≤ J₀)
    (hc : ∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) (hlz : Real.log z₀ ≤ Λ₁ * Real.log q)
    (hlA : Real.log ((A : ℝ) + 1) ≤ Λ₁ * Real.log q)
    (hreg : ∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → StrictAnti rt ∧ ∀ i, z₀ ≤ rt i)
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
  · refine hok (j + s) (by omega) (idxAll S₀ (s + 1)) (stopCmps Ω S₀ ((A : ℝ) + 1) w z₀ s) ?_ ?_ ?_
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
      obtain ⟨ha, hz⟩ := hreg _ (fun i => hx _) hΩ1
      have hcast : ∀ I : Finset (Fin (j + (s + 1))), ((∏ i ∈ I, x i : ℕ) : ℝ) = ∏ i ∈ I, (x i : ℝ) :=
        fun I => Nat.cast_prod _ _
      have hent : ∀ i : Fin (j + (s + 1)), (w : ℝ) ≤ x i := fun i => by
        induction i using Fin.addCases with
        | left i => exact le_trans hwz' (by exact_mod_cast hz i)
        | right u => exact (hblk u).2
      refine ⟨strictAnti_chain (j := j) (t := s + 1) ha hanti (fun i => by exact_mod_cast hz i)
        (fun u => (hblk u).1), fun i => le_trans hwq (hent i), ?_, ?_⟩
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

end SieveP6Tree
