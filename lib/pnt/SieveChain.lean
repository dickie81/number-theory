/-
# Type II for chains of primes

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. A `GCmp` is a comparison `0 ≤ c(m) + Σ_i e_i log x_i` (or `0 <`) with coefficients in `{−1, 0, 1}` and
no designated pivot. `RTg k Y Ω` is the set of `k`-tuples of primes up to `Y` that satisfy the comparisons `Ω` at
`m = 0`. `L`, `w₁` and `w₂` are a route's parameters (`SieveRoute.Route`) with `RouteOK`, and the bounds below assume
its Type II estimate (`hII : SieveRoute.TypeIIAt`). `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

* `typeII_gcmp`, `typeII_gcmp'`: `SieveStops2.typeII_cmp` for `GCmp`s: those with a nonzero coefficient are pivoted,
  and those without one become conditions on `m`.
* `chainTU_bound` (the upper window): fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for
  `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over `RTg (k′ + 1) N₂ Ω` with at most `J₀` comparisons, whose `m`-parts
  at `m = 0` are at most `Λ₁ log q`, each such tuple having its entries at least `q^{e₀}`, its last entry least, and
  `W₀ < ∏rt ≤ W₁`. Let `W₁ ≤ N₁`, `q^{w₁L} ≤ ⌊N₁/W₁⌋` and `⌊N₂/(W₀ + 1)⌋ ≤ q^{w₂L}`. Then the multiples `n ∈ (N₁, N₂]`
  of `∏rt` with no prime factor below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.
* `chainTL_bound` (the lower window): the same for `rt` strictly decreasing, with entries at least `q^{e₀}` and
  `P₁ < ∏_{i∈S} rt_i ≤ P₂` for a set `S` of indices, where `q^{w₁L} ≤ P₁` and `P₂ ≤ q^{w₂L}`.

These evaluate the evaluable terms of the sieve's decomposition: a chain `p₁ > ⋯ > p_k` of
primes, and the rough rest of `n`. In the upper window the chain's product is the Type II variable's partner and
the rest of `n` is the variable; in the lower window `m = ∏_S rt` is the variable, and the rest of `n` with the
primes off `S` are the family's primes.

The proof:

* Upper window: `sum_cofactor_range` puts the rest of `n` in `(N₁/W₁, N₂/(W₀ + 1)]`, the comparisons `cmpsTU` (the
  region, the rest's roughness against the last prime, the range) cut out the family, and `typeII_gcmp` bounds it.
* Lower window: the rest of `n` is the product of a non-increasing tuple `y` of primes at least `rt`'s last entry
  (`sum_mult_eq`, `sum_rough_tuples`). `sum_TL_eq` regroups the pairs `(rt, y)` by `m = ∏_S rt`, a squarefree `m`
  of `Mset S P₁ P₂`, with the prime variables `x = (y, rt on Sᶜ)` and the comparisons `cmpsTL`, whose `m`-parts
  read `m`'s factors in decreasing order (`factS`). Their `m`-parts are at most `B + log m` (`cmpsTL_c_le`), and
  `typeII_gcmp'` bounds each length of `y`.

The file imports `SieveProp6.lean`.
-/
import SieveProp6

open Real Finset SieveFamily SieveTree SieveCmp SieveRoute

namespace SieveChain

/-! ### Comparisons without a designated pivot -/

/-- A comparison `0 ≤ c(m) + Σ_i e_i log x_i` (or `0 <` when `strict`) with coefficients in `{−1, 0, 1}`. -/
structure GCmp (K : ℕ) where
  c : ℕ → ℝ
  e : Fin K → ℝ
  strict : Bool
  he : ∀ i, e i = -1 ∨ e i = 0 ∨ e i = 1

variable {K : ℕ}

/-- The comparison's form `c(m) + Σ_i e_i log x_i`. -/
noncomputable def GCmp.form (C : GCmp K) (m : ℕ) (x : Fin K → ℕ) : ℝ := C.c m + ∑ i, C.e i * Real.log (x i)

/-- The comparison holds: `0 < form` if strict, `0 ≤ form` otherwise. -/
def GCmp.holds (C : GCmp K) (m : ℕ) (x : Fin K → ℕ) : Prop :=
  if C.strict then 0 < C.form m x else 0 ≤ C.form m x

/-- A comparison with a nonzero coefficient, pivoted at one of them. -/
noncomputable def GCmp.toCmp (C : GCmp K) (h : ∃ i, C.e i ≠ 0) : Cmp K where
  c := C.c
  e := C.e
  strict := C.strict
  piv := Classical.choose h
  hpiv := by
    have h1 := Classical.choose_spec h
    rcases C.he (Classical.choose h) with h2 | h2 | h2
    · exact Or.inr h2
    · exact absurd h2 h1
    · exact Or.inl h2
  he := fun i => by rcases C.he i with h | h | h <;> simp [h]

theorem GCmp.toCmp_holds (C : GCmp K) (h : ∃ i, C.e i ≠ 0) (m : ℕ) (x : Fin K → ℕ) :
    (C.toCmp h).holds m x ↔ C.holds m x := Iff.rfl

/-- With every coefficient zero, a comparison does not depend on `x`. -/
theorem GCmp.holds_of_zero (C : GCmp K) (h : ∀ i, C.e i = 0) (m : ℕ) (x y : Fin K → ℕ) :
    C.holds m x ↔ C.holds m y := by
  unfold GCmp.holds GCmp.form
  simp [h]

/-- The comparisons of a list that have a nonzero coefficient, pivoted. -/
noncomputable def pivoted (l : List (GCmp K)) : List (Cmp K) :=
  open Classical in l.filterMap (fun C => if h : ∃ i, C.e i ≠ 0 then some (C.toCmp h) else none)

theorem mem_pivoted {l : List (GCmp K)} {C' : Cmp K} :
    C' ∈ pivoted l ↔ ∃ C ∈ l, ∃ h : ∃ i, C.e i ≠ 0, C.toCmp h = C' := by
  classical
  unfold pivoted
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨C, hC, hC'⟩
    by_cases h : ∃ i, C.e i ≠ 0
    · rw [dite_eq_left h] at hC'
      exact ⟨C, hC, h, Option.some_inj.1 hC'⟩
    · rw [dite_eq_right h] at hC'
      exact absurd hC' (by simp)
  · rintro ⟨C, hC, h, rfl⟩
    exact ⟨C, hC, by rw [dite_eq_left h]⟩

theorem length_pivoted_le (l : List (GCmp K)) : (pivoted l).length ≤ l.length :=
  List.length_filterMap_le _ _

/-- A list of comparisons holds iff its pivoted part holds and its comparisons with all coefficients zero hold. -/
theorem holds_iff_pivoted (l : List (GCmp K)) (m : ℕ) (x : Fin K → ℕ) :
    (∀ C ∈ l, C.holds m x) ↔
      (∀ C' ∈ pivoted l, C'.holds m x) ∧ (∀ C ∈ l, (∀ i, C.e i = 0) → C.holds m (fun _ => 1)) := by
  constructor
  · intro h
    refine ⟨fun C' hC' => ?_, fun C hC h0 => (C.holds_of_zero h0 m x _).1 (h C hC)⟩
    obtain ⟨C, hC, hne, rfl⟩ := mem_pivoted.1 hC'
    exact (C.toCmp_holds hne m x).2 (h C hC)
  · rintro ⟨h1, h2⟩ C hC
    by_cases hne : ∃ i, C.e i ≠ 0
    · exact (C.toCmp_holds hne m x).1 (h1 _ (mem_pivoted.2 ⟨C, hC, hne, rfl⟩))
    · push Not at hne
      exact (C.holds_of_zero hne m x _).2 (h2 C hC hne)

/-! ### The basic comparisons -/

/-- A comparison taken at `m = 0`, whatever `m`. -/
def GCmp.const (C : GCmp K) : GCmp K := { C with c := fun _ => C.c 0 }

theorem GCmp.const_holds (C : GCmp K) (m : ℕ) (x : Fin K → ℕ) : C.const.holds m x ↔ C.holds 0 x := Iff.rfl

theorem gsum_single (i : Fin K) (x : Fin K → ℕ) :
    ∑ t, (if t = i then (1 : ℝ) else 0) * Real.log (x t) = Real.log (x i) := by
  simp [ite_mul]

theorem gsum_log_prod (x : Fin K → ℕ) (hx : ∀ i, 1 ≤ x i) :
    ∑ t, (1 : ℝ) * Real.log (x t) = Real.log (∏ t, (x t : ℝ)) := by
  rw [Real.log_prod (fun t _ => by have := hx t; positivity)]
  simp

/-- `x_i ≤ minFac m`. -/
noncomputable def grough (i : Fin K) : GCmp K where
  c := fun m => Real.log (Nat.minFac m)
  e := fun t => -(if t = i then 1 else 0)
  strict := false
  he := fun t => by split_ifs <;> simp

theorem grough_holds (i : Fin K) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (grough i).holds m x ↔ x i ≤ Nat.minFac m := by
  have hpos : (0 : ℝ) < x i := by exact_mod_cast hx i
  have hmf : (0 : ℝ) < Nat.minFac m := by exact_mod_cast Nat.minFac_pos m
  unfold GCmp.holds GCmp.form grough
  simp only [Bool.false_eq_true, ite_false, neg_mul, Finset.sum_neg_distrib, gsum_single, ← sub_eq_add_neg,
    sub_nonneg]
  rw [Real.log_le_log_iff hpos hmf, Nat.cast_le]

/-- `b < m∏_i x_i`. -/
noncomputable def grangeLo (b : ℝ) : GCmp K where
  c := fun m => Real.log m - Real.log b
  e := fun _ => 1
  strict := true
  he := fun _ => by simp

theorem grangeLo_holds {b : ℝ} (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (grangeLo b).holds m x ↔ b < (m : ℝ) * ∏ t, (x t : ℝ) := by
  have hpos : (0 : ℝ) < ∏ t, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold GCmp.holds GCmp.form grangeLo
  simp only [ite_true]
  rw [gsum_log_prod x hx, sub_add_eq_add_sub, ← Real.log_mul hm0.ne' hpos.ne', sub_pos]
  exact Real.log_lt_log_iff hb (mul_pos hm0 hpos)

/-- `m∏_i x_i ≤ b`. -/
noncomputable def grangeHi (b : ℝ) : GCmp K where
  c := fun m => Real.log b - Real.log m
  e := fun _ => -1
  strict := false
  he := fun _ => by simp

theorem grangeHi_holds {b : ℝ} (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (grangeHi b).holds m x ↔ (m : ℝ) * ∏ t, (x t : ℝ) ≤ b := by
  have hpos : (0 : ℝ) < ∏ t, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : ∑ t, (-1 : ℝ) * Real.log (x t) = -Real.log (∏ t, (x t : ℝ)) := by
    rw [Real.log_prod (fun t _ => by have := hx t; positivity), ← Finset.sum_neg_distrib]
    simp
  unfold GCmp.holds GCmp.form grangeHi
  simp only [Bool.false_eq_true, ite_false]
  rw [hlog, ← sub_eq_add_neg, sub_sub, ← Real.log_mul hm0.ne' hpos.ne', sub_nonneg]
  exact Real.log_le_log_iff (mul_pos hm0 hpos) hb

/-- `x_j ≤ x_i`. -/
noncomputable def ggeVar (i j : Fin K) : GCmp K where
  c := fun _ => 0
  e := fun t => (if t = i then 1 else 0) - (if t = j then 1 else 0)
  strict := false
  he := fun t => by split_ifs <;> simp

theorem ggeVar_holds (i j : Fin K) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (ggeVar i j).holds m x ↔ x j ≤ x i := by
  have hpos : ∀ t, (0 : ℝ) < x t := fun t => by exact_mod_cast hx t
  unfold GCmp.holds GCmp.form ggeVar
  simp only [Bool.false_eq_true, ite_false, zero_add, sub_mul, Finset.sum_sub_distrib, gsum_single, sub_nonneg]
  rw [Real.log_le_log_iff (hpos _) (hpos _), Nat.cast_le]

/-! ### Multiples of a number in a range -/

/-- A `p`-rough `W ∈ (W₀, W₁]` with `W₁ ≤ N₁`: its multiples in `(N₁, N₂]` that are `p`-rough are `Wk` with
`k ∈ (N₁/W₁, N₂/(W₀ + 1)]` and `p ≤ minFac k`. -/
theorem sum_cofactor_range (f : ℕ → ℂ) {W p W₀ W₁ N₁ N₂ : ℕ} (hW0 : 0 < W) (hWp : rough p W)
    (hlo : W₀ < W) (hhi : W ≤ W₁) (hW₁ : W₁ ≤ N₁) (hP₁ : 1 ≤ N₁ / W₁) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0) =
      ∑ k ∈ Finset.Ioc (N₁ / W₁) (N₂ / (W₀ + 1)),
        (if p ≤ Nat.minFac k ∧ N₁ < W * k ∧ W * k ≤ N₂ then f (W * k) else 0) := by
  rw [SieveStops1.sum_cofactor f hW0 (le_trans hhi hW₁) hWp, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  have hW10 : 0 < W₁ := lt_of_lt_of_le hW0 hhi
  constructor
  · rintro ⟨⟨hk2, -⟩, hr, h1, h2⟩
    refine ⟨⟨?_, ?_⟩, (SieveStops2.rough_iff_le_minFac hk2).1 hr, h1, h2⟩
    · rw [Nat.div_lt_iff_lt_mul hW10]
      calc N₁ < W * k := h1
        _ ≤ W₁ * k := Nat.mul_le_mul_right k hhi
        _ = k * W₁ := Nat.mul_comm _ _
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc k * (W₀ + 1) ≤ k * W := Nat.mul_le_mul_left k hlo
        _ = W * k := Nat.mul_comm _ _
        _ ≤ N₂ := h2
  · rintro ⟨⟨hk1, -⟩, hmin, h1, h2⟩
    have hk2 : 2 ≤ k := by omega
    exact ⟨⟨hk2, le_trans (Nat.le_mul_of_pos_left k hW0) h2⟩, (SieveStops2.rough_iff_le_minFac hk2).2 hmin, h1, h2⟩

open Classical in
/-- The `k`-tuples of primes up to `Y` that satisfy the comparisons `Ω` at `m = 0`. -/
noncomputable def RTg (k Y : ℕ) (Ω : List (GCmp k)) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => SieveTypeIIU.primesLe Y)).filter (fun rt => ∀ C ∈ Ω, C.holds 0 rt)

/-! ### Splitting a chain by a set of its indices -/

section Split

variable {k : ℕ} (S : Finset (Fin k))

/-- `Fin |S| ⊕ Fin |Sᶜ| ≃ Fin k`, increasing on each part. -/
def eS : Fin S.card ⊕ Fin Sᶜ.card ≃ Fin k := finSumEquivOfFinset rfl rfl

/-- The tuple with `a` on `S` and `b` on `Sᶜ`, in order. -/
def merge (a : Fin S.card → ℕ) (b : Fin Sᶜ.card → ℕ) : Fin k → ℕ := fun i => Sum.elim a b ((eS S).symm i)

variable {S}

theorem merge_inl (a : Fin S.card → ℕ) (b : Fin Sᶜ.card → ℕ) (u : Fin S.card) :
    merge S a b (eS S (Sum.inl u)) = a u := by
  simp [merge]

theorem merge_inr (a : Fin S.card → ℕ) (b : Fin Sᶜ.card → ℕ) (v : Fin Sᶜ.card) :
    merge S a b (eS S (Sum.inr v)) = b v := by
  simp [merge]

theorem merge_split (rt : Fin k → ℕ) :
    merge S (fun u => rt (eS S (Sum.inl u))) (fun v => rt (eS S (Sum.inr v))) = rt := by
  funext i
  obtain ⟨y, rfl⟩ := (eS S).surjective i
  rcases y with u | v
  · exact merge_inl _ _ u
  · exact merge_inr _ _ v

theorem eS_inl_strictMono : StrictMono (fun u : Fin S.card => eS S (Sum.inl u)) :=
  (S.orderEmbOfFin rfl).strictMono

theorem sum_split (f : Fin k → ℝ) :
    ∑ i, f i = (∑ u, f (eS S (Sum.inl u))) + ∑ v, f (eS S (Sum.inr v)) := by
  rw [← Fintype.sum_equiv (eS S) (fun y => f (eS S y)) f (fun _ => rfl), Fintype.sum_sum_type]

theorem prod_split_nat (f : Fin k → ℕ) :
    ∏ i, f i = (∏ u, f (eS S (Sum.inl u))) * ∏ v, f (eS S (Sum.inr v)) := by
  rw [← Fintype.prod_equiv (eS S) (fun y => f (eS S y)) f (fun _ => rfl), Fintype.prod_sum_type]

/-- The product over `S` is the product over the first part. -/
theorem prod_S (f : Fin k → ℕ) : ∏ i ∈ S, f i = ∏ u, f (eS S (Sum.inl u)) := by
  conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
  rw [Finset.prod_image (fun u _ v _ h => (S.orderEmbOfFin rfl).injective h)]
  rfl

end Split

/-! ### Comparisons on the full tuple, as comparisons of the lower window -/

section Transform

variable {k t : ℕ} (S : Finset (Fin k))

variable {S}

/-- A comparison of the chain, on the full tuple. -/
def liftChain (C : GCmp k) : GCmp (k + t) where
  c := fun _ => C.c 0
  e := fun i => Fin.addCases C.e (fun _ => 0) i
  strict := C.strict
  he := fun i => by
    refine Fin.addCases (fun a => ?_) (fun v => ?_) i
    · simpa using C.he _
    · simp

theorem liftChain_holds (C : GCmp k) (m : ℕ) (z : Fin (k + t) → ℕ) :
    (liftChain (t := t) C).holds m z ↔ C.holds 0 (fun i => z (Fin.castAdd t i)) := by
  unfold GCmp.holds GCmp.form liftChain
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]

end Transform

/-! ### The comparisons of the lower window -/

section TLcmps

open Classical

/-- `y` non-increasing: `y_b ≤ y_a` for `a ≤ b`, on the full tuple `(rt, y)`. -/
noncomputable def yPairs (k t : ℕ) : List (GCmp (k + t)) :=
  (List.finRange t).flatMap fun a => (List.finRange t).filterMap fun b =>
    if a ≤ b then some (ggeVar (Fin.natAdd k a) (Fin.natAdd k b)) else none

theorem mem_yPairs {k t : ℕ} {C : GCmp (k + t)} :
    C ∈ yPairs k t ↔ ∃ a b : Fin t, a ≤ b ∧ ggeVar (Fin.natAdd k a) (Fin.natAdd k b) = C := by
  unfold yPairs
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨a, b, hb⟩
    by_cases hab : a ≤ b
    · rw [ite_eq_left hab] at hb
      exact ⟨a, b, hab, Option.some_inj.1 hb⟩
    · rw [ite_eq_right hab] at hb
      exact absurd hb (by simp)
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, b, by rw [ite_eq_left hab]⟩

theorem length_yPairs_le (k t : ℕ) : (yPairs k t).length ≤ t * t := by
  unfold yPairs
  rw [List.length_flatMap]
  calc ((List.finRange t).map fun a => ((List.finRange t).filterMap fun b =>
        if a ≤ b then some (ggeVar (Fin.natAdd k a) (Fin.natAdd k b)) else none).length).sum
      ≤ ((List.finRange t).map fun _ => t).sum := by
        apply List.sum_le_sum
        intro a _
        exact (List.length_filterMap_le _ _).trans (by simp)
    _ = t * t := by simp

theorem yPairs_holds {k t : ℕ} (m : ℕ) {z : Fin (k + t) → ℕ} (hz : ∀ i, 1 ≤ z i) :
    (∀ C ∈ yPairs k t, C.holds m z) ↔ ∀ a b : Fin t, a ≤ b → z (Fin.natAdd k b) ≤ z (Fin.natAdd k a) := by
  constructor
  · intro h a b hab
    exact (ggeVar_holds _ _ m hz).1 (h _ (mem_yPairs.2 ⟨a, b, hab, rfl⟩))
  · intro h C hC
    obtain ⟨a, b, hab, rfl⟩ := mem_yPairs.1 hC
    exact (ggeVar_holds _ _ m hz).2 (h a b hab)

/-- `y` at least the chain's last entry, on the full tuple. -/
noncomputable def yLast (k' t : ℕ) : List (GCmp (k' + 1 + t)) :=
  (List.finRange t).map fun a => ggeVar (Fin.natAdd (k' + 1) a) (Fin.castAdd t (Fin.last k'))

theorem yLast_holds {k' t : ℕ} (m : ℕ) {z : Fin (k' + 1 + t) → ℕ} (hz : ∀ i, 1 ≤ z i) :
    (∀ C ∈ yLast k' t, C.holds m z) ↔ ∀ a : Fin t, z (Fin.castAdd t (Fin.last k')) ≤ z (Fin.natAdd (k' + 1) a) := by
  unfold yLast
  simp only [List.forall_mem_map, List.mem_finRange, true_implies]
  exact forall_congr' fun a => ggeVar_holds _ _ m hz

/-- The comparisons of the full tuple `(rt, y)`: the region `Ω` of `rt`, `y` non-increasing and at least `rt`'s
last entry, and the range `N₁ < ∏rt·∏y ≤ N₂`. -/
noncomputable def fullTL (k' t : ℕ) (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) : List (GCmp (k' + 1 + t)) :=
  Ω.map (liftChain (t := t)) ++ yPairs (k' + 1) t ++ yLast k' t ++ [grangeLo N₁, grangeHi N₂]

theorem length_fullTL_le (k' t : ℕ) (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) :
    (fullTL k' t Ω N₁ N₂).length ≤ Ω.length + t * t + t + 2 := by
  unfold fullTL yLast
  simp only [List.length_append, List.length_map, List.length_finRange, List.length_cons, List.length_nil]
  have := length_yPairs_le (k' + 1) t
  omega

theorem fullTL_holds {k' t : ℕ} (Ω : List (GCmp (k' + 1))) {N₁ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (rt : Fin (k' + 1) → ℕ) (y : Fin t → ℕ) (hrt : ∀ i, 1 ≤ rt i) (hy : ∀ a, 1 ≤ y a) :
    (∀ C ∈ fullTL k' t Ω N₁ N₂, C.holds 1 (Fin.append rt y)) ↔
      (∀ C ∈ Ω, C.holds 0 rt) ∧ (∀ a b : Fin t, a ≤ b → y b ≤ y a) ∧ (∀ a, rt (Fin.last k') ≤ y a) ∧
        N₁ < (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) ∧ (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) ≤ N₂ := by
  have hz : ∀ i, 1 ≤ Fin.append rt y i := fun i => by
    refine Fin.addCases (fun i => ?_) (fun a => ?_) i
    · rw [Fin.append_left]; exact hrt i
    · rw [Fin.append_right]; exact hy a
  have hprod : ∏ i, ((Fin.append rt y i : ℕ) : ℝ) = (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) := by
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  unfold fullTL
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true]
  rw [yPairs_holds 1 hz, yLast_holds 1 hz, grangeLo_holds hN₁ le_rfl hz, grangeHi_holds hN₂ le_rfl hz]
  simp only [Fin.append_left, Fin.append_right, Nat.cast_one, one_mul, hprod]
  have hlc : (∀ C ∈ Ω, (liftChain (t := t) C).holds 1 (Fin.append rt y)) ↔ ∀ C ∈ Ω, C.holds 0 rt := by
    refine forall₂_congr fun C _ => ?_
    rw [liftChain_holds]
    simp only [Fin.append_left]
  rw [hlc]
  tauto

end TLcmps

/-! ### The lower window: chains and cofactor tuples as `m = ∏_S rt` and the other primes -/

section TLsum

open Classical

end TLsum

/-! ### Multiples of a number as cofactor tuples -/

/-- The `p`-rough multiples in `(N₁, N₂]` of a `p`-rough `W > 0` are `Wk` with `k ∈ [1, N₂]` `p`-rough. -/
theorem sum_mult_eq (f : ℕ → ℂ) {W p N₁ N₂ : ℕ} (hW : 0 < W) (hWp : rough p W) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0) =
      ∑ k ∈ (Finset.Icc 1 N₂).filter (fun k => ∀ p' < p, p'.Prime → ¬ p' ∣ k),
        (if N₁ < W * k ∧ W * k ≤ N₂ then f (W * k) else 0) := by
  rw [show (∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0)) =
      ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => W ∣ n ∧ rough p n), f n by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun n => n / W) (fun k => W * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Nat.mul_div_cancel_left c hW]
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · omega
    exact ⟨⟨⟨hc1, le_trans (Nat.le_mul_of_pos_left c hW) hn2⟩,
      fun p' hp' hpp hpd => hr p' hp' hpp (dvd_mul_of_dvd_right hpd W)⟩, hn1, hn2⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨-, hr⟩, h1, h2⟩ := hk
    refine ⟨⟨h1, h2⟩, dvd_mul_right W k, fun p' hp' hpp hpd => ?_⟩
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact hWp p' hp' hpp h
    · exact hr p' hp' hpp h
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2.1
  · intro k _
    exact Nat.mul_div_cancel_left k hW
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2.1]

/-- For `z ≥ 2`, `Y ≥ 1` and `Y < z^{K+1}`, the `z`-rough `k ∈ [1, Y]` are the products of the non-increasing tuples
of at most `K` primes at least `z`, the empty tuple included. -/
theorem sum_rough_tuples {z Y : ℕ} (hz : 2 ≤ z) (hY : 1 ≤ Y) {M : Type*} [AddCommMonoid M] (G : ℕ → M) (K : ℕ)
    (hK : Y < z ^ (K + 1)) :
    ∑ k ∈ (Finset.Icc 1 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k), G k =
      ∑ t ∈ Finset.range (K + 1), ∑ y ∈ SieveRoughTuple.tuples z Y t, G (∏ a, y a) := by
  have hsplit : (Finset.Icc 1 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k) =
      insert 1 ((Finset.Icc 2 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, hr⟩
      rcases (show k = 1 ∨ 2 ≤ k by omega) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨h, h2⟩, hr⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, hr⟩)
      · exact ⟨⟨le_rfl, hY⟩, fun p _ hp hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)⟩
      · exact ⟨⟨by omega, h2⟩, hr⟩
  have h1 : (1 : ℕ) ∉ (Finset.Icc 2 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k) := by
    simp
  rw [hsplit, Finset.sum_insert h1, SieveRoughTuple.sum_rough_eq hz G K hK, SieveTypeIIR.sum_Icc_one,
    Finset.sum_range_succ', add_comm]
  congr 1
  have h0 : SieveRoughTuple.tuples z Y 0 = {fun i => i.elim0} := by
    ext y
    simp only [SieveRoughTuple.tuples, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro _
      funext i
      exact i.elim0
    · rintro rfl
      refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
      simpa using hY
  rw [h0, Finset.sum_singleton]
  simp

section TypeII

open Classical

/-- The comparisons of the upper window: the region, the cofactor's roughness and the range. -/
noncomputable def cmpsTU (k' : ℕ) (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) : List (GCmp (k' + 1)) :=
  Ω.map GCmp.const ++ [grough (Fin.last k'), grangeLo N₁, grangeHi N₂]

end TypeII

end SieveChain
