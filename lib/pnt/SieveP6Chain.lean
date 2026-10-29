/-
# Proposition 6 with the bilinear estimate: the branches as chains

Plain statements. `GCmp`, `RTg` and `liftChain` are `SieveChain`'s; `primesIco w z` is `SieveTree`'s; `desc s P` is the
`s`-set `P` in decreasing order (`SieveStops2.desc`).

* `gUp`, `gDown`, `gltVar`: the comparisons `∏_{i∈I} x_i < b` (or `≤ b`), `b < ∏_{i∈I} x_i` (or `b ≤`) and
  `x_j < x_i`, with what they say for `x_i ≥ 1` (`gUp_holds`, `gDown_holds`, `gltVar_holds`).
* `Pblock`, `Pblock_holds`: the comparisons of a block `y = (x_{j}, …, x_{j+s−1})` of a chain: strictly decreasing,
  each entry below `z₀` and at least `w`.
* `sum_powersetCard_desc`: a sum over the `s`-subsets of `T` is a sum over the strictly decreasing `s`-tuples of `T`.
* `sum_stops_desc`: a sum over a prime `p ∈ T` and an `s`-set `P` of the primes of `T` above `p` is a sum over the
  strictly decreasing `(s + 1)`-tuples `y` of `T`, through `p = y_s` and `P = {y_0, …, y_{s−1}}`.
* `sum_chain`: for `z₀ ≤ Y + 1`, a sum over the `j`-tuples `rt` of a region `Ω` and the strictly decreasing `s`-tuples
  `y` of primes of `[w, z₀)` is a sum over the chains `x = (rt, y)` of the region `Ω` on the first block and `Pblock`.

These put the branches of Buchstab's tree (`SieveTreeStop.tree_weighted_stop`), a tuple `rt` and a set of primes below
`z₀`, in the form of `SieveChain.chainTL_bound`, `SieveChainR.chainTR_bound` and `SieveTypeIBAsym.leaves_ib`.

The file imports `SieveChainR.lean` and `SieveTreeStop.lean`.
-/
import SieveChainR
import SieveTreeStop

open Real Finset SieveFamily SieveTree SieveChain

namespace SieveP6Chain

/-! ### Comparisons of products -/

section Cmps

variable {K : ℕ}

/-- `∏_{i∈I} x_i < b` (`st`) or `∏_{i∈I} x_i ≤ b`. -/
noncomputable def gUp (I : Finset (Fin K)) (b : ℝ) (st : Bool) : GCmp K where
  c := fun _ => Real.log b
  e := fun i => -(if i ∈ I then 1 else 0)
  strict := st
  he := fun i => by split_ifs <;> simp

/-- `b < ∏_{i∈I} x_i` (`st`) or `b ≤ ∏_{i∈I} x_i`. -/
noncomputable def gDown (I : Finset (Fin K)) (b : ℝ) (st : Bool) : GCmp K where
  c := fun _ => -Real.log b
  e := fun i => if i ∈ I then 1 else 0
  strict := st
  he := fun i => by split_ifs <;> simp

/-- `x_j < x_i`. -/
noncomputable def gltVar (i j : Fin K) : GCmp K where
  c := fun _ => 0
  e := fun t => (if t = i then 1 else 0) - (if t = j then 1 else 0)
  strict := true
  he := fun t => by split_ifs <;> simp

theorem sum_ind_log (I : Finset (Fin K)) (x : Fin K → ℕ) (hx : ∀ i, 1 ≤ x i) :
    ∑ i, (if i ∈ I then (1 : ℝ) else 0) * Real.log (x i) = Real.log (∏ i ∈ I, (x i : ℝ)) := by
  rw [Real.log_prod (fun i _ => by have := hx i; positivity)]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem gUp_holds (I : Finset (Fin K)) {b : ℝ} (hb : 0 < b) (st : Bool) (m : ℕ) {x : Fin K → ℕ}
    (hx : ∀ i, 1 ≤ x i) :
    (gUp I b st).holds m x ↔ if st then ∏ i ∈ I, (x i : ℝ) < b else ∏ i ∈ I, (x i : ℝ) ≤ b := by
  have hpos : 0 < ∏ i ∈ I, (x i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx i
  unfold GCmp.holds GCmp.form gUp
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [sum_ind_log I x hx, ← sub_eq_add_neg]
  cases st
  · simp only [Bool.false_eq_true, ite_false, sub_nonneg]
    exact Real.log_le_log_iff hpos hb
  · simp only [ite_true, sub_pos]
    exact Real.log_lt_log_iff hpos hb

theorem gDown_holds (I : Finset (Fin K)) {b : ℝ} (hb : 0 < b) (st : Bool) (m : ℕ) {x : Fin K → ℕ}
    (hx : ∀ i, 1 ≤ x i) :
    (gDown I b st).holds m x ↔ if st then b < ∏ i ∈ I, (x i : ℝ) else b ≤ ∏ i ∈ I, (x i : ℝ) := by
  have hpos : 0 < ∏ i ∈ I, (x i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hx i
  unfold GCmp.holds GCmp.form gDown
  rw [sum_ind_log I x hx, neg_add_eq_sub]
  cases st
  · simp only [Bool.false_eq_true, ite_false, sub_nonneg]
    exact Real.log_le_log_iff hb hpos
  · simp only [ite_true, sub_pos]
    exact Real.log_lt_log_iff hb hpos

theorem gltVar_holds (i j : Fin K) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (gltVar i j).holds m x ↔ x j < x i := by
  have hpos : ∀ t, (0 : ℝ) < x t := fun t => by exact_mod_cast hx t
  unfold GCmp.holds GCmp.form gltVar
  simp only [ite_true, zero_add, sub_mul, Finset.sum_sub_distrib, gsum_single, sub_pos]
  rw [Real.log_lt_log_iff (hpos _) (hpos _), Nat.cast_lt]

end Cmps

/-! ### The block of a chain below `z₀` -/

section Block

open Classical

/-- `y_v < y_u` for `u < v`, on the block `y = (x_{j}, …, x_{j+s−1})`. -/
noncomputable def ltPairs (j s : ℕ) : List (GCmp (j + s)) :=
  (List.finRange s).flatMap fun u => (List.finRange s).filterMap fun v =>
    if u < v then some (gltVar (Fin.natAdd j u) (Fin.natAdd j v)) else none

theorem mem_ltPairs {j s : ℕ} {C : GCmp (j + s)} :
    C ∈ ltPairs j s ↔ ∃ u v : Fin s, u < v ∧ gltVar (Fin.natAdd j u) (Fin.natAdd j v) = C := by
  unfold ltPairs
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨u, v, hv⟩
    by_cases huv : u < v
    · rw [ite_eq_left huv] at hv
      exact ⟨u, v, huv, Option.some_inj.1 hv⟩
    · rw [ite_eq_right huv] at hv
      exact absurd hv (by simp)
  · rintro ⟨u, v, huv, rfl⟩
    exact ⟨u, v, by rw [ite_eq_left huv]⟩

theorem length_ltPairs_le (j s : ℕ) : (ltPairs j s).length ≤ s * s := by
  unfold ltPairs
  rw [List.length_flatMap]
  calc ((List.finRange s).map fun u => ((List.finRange s).filterMap fun v =>
        if u < v then some (gltVar (Fin.natAdd j u) (Fin.natAdd j v)) else none).length).sum
      ≤ ((List.finRange s).map fun _ => s).sum := by
        apply List.sum_le_sum
        intro u _
        exact (List.length_filterMap_le _ _).trans (by simp)
    _ = s * s := by simp

theorem ltPairs_holds {j s : ℕ} (m : ℕ) {x : Fin (j + s) → ℕ} (hx : ∀ i, 1 ≤ x i) :
    (∀ C ∈ ltPairs j s, C.holds m x) ↔ StrictAnti (fun u : Fin s => x (Fin.natAdd j u)) := by
  constructor
  · intro h u v huv
    exact (gltVar_holds _ _ m hx).1 (h _ (mem_ltPairs.2 ⟨u, v, huv, rfl⟩))
  · intro h C hC
    obtain ⟨u, v, huv, rfl⟩ := mem_ltPairs.1 hC
    exact (gltVar_holds _ _ m hx).2 (h huv)

/-- The comparisons of the block `y = (x_{j}, …, x_{j+s−1})` of a chain on `Fin (j + s)`: strictly decreasing, each
entry below `z₀` and at least `w`. -/
noncomputable def Pblock (j s : ℕ) (w z₀ : ℝ) : List (GCmp (j + s)) :=
  ltPairs j s ++ (List.finRange s).map (fun u => gUp {Fin.natAdd j u} z₀ true) ++
    (List.finRange s).map (fun u => gDown {Fin.natAdd j u} w false)

theorem length_Pblock_le (j s : ℕ) (w z₀ : ℝ) : (Pblock j s w z₀).length ≤ s * s + 2 * s := by
  unfold Pblock
  simp only [List.length_append, List.length_map, List.length_finRange]
  have := length_ltPairs_le j s
  omega

theorem Pblock_holds {j s : ℕ} {w z₀ : ℝ} (hw : 0 < w) (hz₀ : 0 < z₀) (m : ℕ) {x : Fin (j + s) → ℕ}
    (hx : ∀ i, 1 ≤ x i) :
    (∀ C ∈ Pblock j s w z₀, C.holds m x) ↔
      StrictAnti (fun u : Fin s => x (Fin.natAdd j u)) ∧ ∀ u : Fin s,
        (x (Fin.natAdd j u) : ℝ) < z₀ ∧ w ≤ (x (Fin.natAdd j u) : ℝ) := by
  have hone : ∀ u : Fin s, ∏ i ∈ ({Fin.natAdd j u} : Finset (Fin (j + s))), (x i : ℝ) = x (Fin.natAdd j u) :=
    fun u => Finset.prod_singleton _ _
  unfold Pblock
  simp only [List.forall_mem_append, List.forall_mem_map, List.mem_finRange, true_implies,
    gUp_holds _ hz₀ true m hx, gDown_holds _ hw false m hx, ite_true, Bool.false_eq_true, ite_false, hone,
    ltPairs_holds m hx]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun u => ⟨h2 u, h3 u⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun u => (h2 u).1⟩, fun u => (h2 u).2⟩

end Block

/-! ### Sets of primes as decreasing tuples -/

section Tuples

open Classical

/-- A sum over the `s`-subsets of `T` is a sum over the strictly decreasing `s`-tuples of `T`. -/
theorem sum_powersetCard_desc {M : Type*} [AddCommMonoid M] (T : Finset ℕ) (s : ℕ) (f : Finset ℕ → M) :
    ∑ Q ∈ T.powersetCard s, f Q =
      ∑ y ∈ (Fintype.piFinset fun _ : Fin s => T).filter StrictAnti, f (Finset.univ.image y) := by
  refine Finset.sum_nbij' (fun Q => SieveStops2.desc s Q) (fun y => Finset.univ.image y) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    obtain ⟨hQT, hcard⟩ := Finset.mem_powersetCard.1 hQ
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun u => hQT (SieveStops2.desc_mem hcard u), SieveStops2.desc_strictAnti hcard⟩
  · intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hy
    refine Finset.mem_powersetCard.2 ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp
      exact hy.1 u
    · rw [Finset.card_image_of_injective _ hy.2.injective, Finset.card_univ, Fintype.card_fin]
  · intro Q hQ
    exact SieveStops2.image_desc (Finset.mem_powersetCard.1 hQ).2
  · intro y hy
    exact SieveStops2.desc_image (Finset.mem_filter.1 hy).2
  · intro Q hQ
    rw [SieveStops2.image_desc (Finset.mem_powersetCard.1 hQ).2]

/-- A strictly decreasing tuple followed by an entry below all of it is strictly decreasing. -/
theorem strictAnti_snoc {s : ℕ} {d : Fin s → ℕ} (hd : StrictAnti d) {p : ℕ} (hp : ∀ u, p < d u) :
    StrictAnti (Fin.snoc (α := fun _ => ℕ) d p) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast u =>
      rw [Fin.snoc_last, Fin.snoc_castSucc]
      exact hp u
  | cast v =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.2 (Fin.le_last _))
    | cast u =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hd (Fin.castSucc_lt_castSucc_iff.1 hab)

/-- A sum over `p ∈ T` and an `s`-set `P` of the elements of `T` above `p` is a sum over the strictly decreasing
`(s + 1)`-tuples `y` of `T`, through `p = y_s` and `P = {y_0, …, y_{s−1}}`. -/
theorem sum_stops_desc {M : Type*} [AddCommMonoid M] (T : Finset ℕ) (s : ℕ) (G : ℕ → Finset ℕ → M) :
    ∑ p ∈ T, ∑ P ∈ (T.filter (p < ·)).powersetCard s, G p P =
      ∑ y ∈ (Fintype.piFinset fun _ : Fin (s + 1) => T).filter StrictAnti,
        G (y (Fin.last s)) (Finset.univ.image fun u : Fin s => y u.castSucc) := by
  rw [Finset.sum_sigma' T (fun p => (T.filter (p < ·)).powersetCard s) (fun p P => G p P)]
  refine Finset.sum_nbij' (fun t => Fin.snoc (α := fun _ => ℕ) (SieveStops2.desc s t.2) t.1)
    (fun y => ⟨y (Fin.last s), Finset.univ.image fun u : Fin s => y u.castSucc⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, P⟩ ht
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at ht
    obtain ⟨hpT, hPT, hcard⟩ := ht
    have hPmem : ∀ u, SieveStops2.desc s P u ∈ T.filter (p < ·) := fun u => hPT (SieveStops2.desc_mem hcard u)
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, strictAnti_snoc (SieveStops2.desc_strictAnti hcard)
      fun u => (Finset.mem_filter.1 (hPmem u)).2⟩
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hpT
    | cast u => rw [Fin.snoc_castSucc]; exact (Finset.mem_filter.1 (hPmem u)).1
  · intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hy
    obtain ⟨hyT, hya⟩ := hy
    have hinj : Function.Injective fun u : Fin s => y u.castSucc :=
      fun u v h => Fin.castSucc_injective _ (hya.injective h)
    simp only [Finset.mem_sigma, Finset.mem_powersetCard]
    refine ⟨hyT _, fun p hp => ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp
      exact Finset.mem_filter.2 ⟨hyT _, hya (Fin.castSucc_lt_last u)⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rintro ⟨p, P⟩ ht
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at ht
    obtain ⟨-, -, hcard⟩ := ht
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
    rw [SieveStops2.image_desc hcard]
  · intro y hy
    have hya := (Finset.mem_filter.1 hy).2
    have hsa : StrictAnti fun u : Fin s => y u.castSucc := fun u v huv =>
      hya (Fin.castSucc_lt_castSucc_iff.2 huv)
    simp only
    rw [SieveStops2.desc_image hsa]
    exact Fin.snoc_init_self y
  · rintro ⟨p, P⟩ ht
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at ht
    obtain ⟨-, -, hcard⟩ := ht
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
    rw [SieveStops2.image_desc hcard]

/-- **The branches as chains.** For `1 ≤ w ≤ z₀ ≤ Y + 1`: a sum over the `j`-tuples `rt` of the region `Ω` and the
strictly decreasing `s`-tuples `y` of primes of `[w, z₀)` is a sum over the chains `x = (rt, y)` of the region `Ω` on
the first block and `Pblock` on the second. -/
theorem sum_chain {M : Type*} [AddCommMonoid M] (j s : ℕ) (Ω : List (GCmp j)) {Y w z₀ : ℕ} (hw : 1 ≤ w)
    (hwz : w ≤ z₀) (hz₀ : z₀ ≤ Y + 1) (H : (Fin j → ℕ) → (Fin s → ℕ) → M) :
    ∑ rt ∈ RTg j Y Ω, ∑ y ∈ (Fintype.piFinset fun _ : Fin s => primesIco w z₀).filter StrictAnti, H rt y =
      ∑ x ∈ RTg (j + s) Y (Ω.map (liftChain (t := s)) ++ Pblock j s w z₀),
        H (fun i => x (Fin.castAdd s i)) (fun u => x (Fin.natAdd j u)) := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hz0 : (0 : ℝ) < z₀ := by exact_mod_cast (by omega : 0 < z₀)
  rw [← Finset.sum_product' (f := fun rt y => H rt y)]
  refine Finset.sum_nbij' (fun t => Fin.append t.1 t.2) (fun x => (fun i => x (Fin.castAdd s i),
    fun u => x (Fin.natAdd j u))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨rt, y⟩ ht
    simp only [Finset.mem_product, RTg, Finset.mem_filter, Fintype.mem_piFinset] at ht
    obtain ⟨⟨hrtY, hrtΩ⟩, hyI, hya⟩ := ht
    have hy : ∀ u, w ≤ y u ∧ y u < z₀ ∧ (y u).Prime := fun u => mem_primesIco.1 (hyI u)
    have hx1 : ∀ i, 1 ≤ Fin.append rt y i := fun i => by
      refine Fin.addCases (fun i => ?_) (fun u => ?_) i
      · rw [Fin.append_left]; exact (SieveTypeIIU.mem_primesLe.1 (hrtY i)).2.one_lt.le
      · rw [Fin.append_right]; exact (hy u).2.2.one_lt.le
    simp only [RTg, Finset.mem_filter, Fintype.mem_piFinset, List.forall_mem_append, List.forall_mem_map]
    refine ⟨fun i => ?_, fun C hC => ?_, (Pblock_holds hw0 hz0 0 hx1).2 ⟨?_, fun u => ?_⟩⟩
    · refine Fin.addCases (fun i => ?_) (fun u => ?_) i
      · rw [Fin.append_left]; exact hrtY i
      · rw [Fin.append_right]
        exact SieveTypeIIU.mem_primesLe.2 ⟨by have := (hy u).2.1; omega, (hy u).2.2⟩
    · rw [liftChain_holds]
      simp only [Fin.append_left]
      exact hrtΩ C hC
    · simp only [Fin.append_right]
      exact hya
    · simp only [Fin.append_right]
      exact ⟨by exact_mod_cast (hy u).2.1, by exact_mod_cast (hy u).1⟩
  · intro x hx
    simp only [RTg, Finset.mem_filter, Fintype.mem_piFinset, List.forall_mem_append, List.forall_mem_map] at hx
    obtain ⟨hxY, hΩ', hP⟩ := hx
    have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hxY i)).2.one_lt.le
    obtain ⟨hya, hyb⟩ := (Pblock_holds hw0 hz0 0 hx1).1 hP
    simp only [Finset.mem_product, RTg, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨⟨fun i => hxY _, fun C hC => ?_⟩, fun u => ?_, hya⟩
    · exact (liftChain_holds C 0 x).1 (hΩ' C hC)
    · obtain ⟨h1, h2⟩ := hyb u
      exact mem_primesIco.2 ⟨by exact_mod_cast h2, by exact_mod_cast h1,
        (SieveTypeIIU.mem_primesLe.1 (hxY _)).2⟩
  · rintro ⟨rt, y⟩ _
    simp only [Fin.append_left, Fin.append_right]
  · intro x _
    exact Fin.append_castAdd_natAdd
  · rintro ⟨rt, y⟩ _
    simp only [Fin.append_left, Fin.append_right]

end Tuples

end SieveP6Chain
