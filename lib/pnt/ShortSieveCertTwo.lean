import ShortSieveCertRev

/-!
# Buchstab's step on the last rough item of a node

The reversed nodes have two rough items, and the certificate decomposes either one by Buchstab's identity. This file
treats a node `⟨k, m + 1, s, conds⟩` with any number of rough items and decomposes its last one at the level
`x^{1/20}`; a node whose other item is to be decomposed first swaps its two items (`swapN`).

* `Inv`: the invariant of a node's conditions, its primes at least `x^{1/20}` and each rough item at least its sifting
  prime (`StdInv.inv`, `RevInv.inv` for the standard and reversed nodes).
* `lastChild`: the Buchstab child, with the condition that its last item is at least the new prime, which its terms
  satisfy (`count_last`); it keeps the invariants (`Inv.last`, `CondsOK.last`).
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveExpand ShortSieveBuch ShortSieveTree ShortSieveTypeI

open Classical

/-- The invariant of a node's conditions: its primes are at least `x^{1/20}`, and each rough item is at least its
sifting prime. -/
def Inv (N : Node) : Prop :=
  ∀ x : ℝ, 1 < x → ∀ v : (Fin N.k → ℕ) × (Fin N.m → ℕ), (∀ a, 0 < v.1 a) → (∀ i, 0 < v.2 i) →
    (∀ C ∈ N.conds, C.Holds x v.1 v.2) → (∀ a, x ^ (1 / 20 : ℝ) ≤ v.1 a) ∧ ∀ i, v.1 (N.s i) ≤ v.2 i

/-- A node's terms have primes above `x^c`, for `c < 1/20`, and rough items above `1`. -/
theorem Inv.big {N : Node} (h : Inv N) {c : ℝ} (hc1 : c < 1 / 20) :
    ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i := by
  filter_upwards [eventually_gt_atTop 1] with x hx v hv
  obtain ⟨hvp, -, hcv⟩ := mem_filter.1 hv
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hvp
  obtain ⟨h1, h2⟩ := h x hx v (fun a => (hp a).2.pos) (fun i => (hρ i).1) hcv
  have hxc : (1 : ℝ) < x ^ (1 / 20 : ℝ) := Real.one_lt_rpow hx (by norm_num)
  refine ⟨fun a => (Real.rpow_lt_rpow_of_exponent_lt hx hc1).trans_le (h1 a), fun i => ?_⟩
  have := (h1 (N.s i)).trans (Nat.cast_le.2 (h2 i))
  exact_mod_cast hxc.trans_le this

/-- More conditions keep the invariant. -/
theorem Inv.cons {k m : ℕ} {s : Fin m → Fin k} {conds : List (Cond k m)} (h : Inv ⟨k, m, s, conds⟩)
    (C : Cond k m) : Inv ⟨k, m, s, C :: conds⟩ :=
  fun x hx v hv1 hv2 hc => h x hx v hv1 hv2 fun C' h' => hc C' (List.mem_cons_of_mem _ h')

theorem StdInv.inv {k : ℕ} {conds : List (Cond (k + 1) 1)} (h : StdInv k conds) : Inv (std k conds) := by
  intro x hx v hv1 hv2 hc
  obtain ⟨h1, h2⟩ := h x hx v hv1 hv2 hc
  exact ⟨h1, fun i => by rw [Fin.fin_one_eq_zero i]; exact h2⟩

theorem RevInv.inv {k : ℕ} {conds : List (Cond (k + 1) 2)} (h : RevInv k conds) : Inv (revN k conds) := by
  intro x hx v hv1 hv2 hc
  obtain ⟨h1, h2, h3⟩ := h x hx v hv1 hv2 hc
  refine ⟨h1, fun i => ?_⟩
  induction i using Fin.lastCases with
  | last =>
    show v.1 (revS k (Fin.last 1)) ≤ v.2 (Fin.last 1)
    rw [revS, Fin.snoc_last]
    exact h3
  | cast j =>
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hj
    show v.1 (revS k (Fin.castSucc 0)) ≤ v.2 (Fin.castSucc 0)
    rw [revS, Fin.snoc_castSucc]
    exact h2

/-! ### The Buchstab child of the last item -/

/-- The child's added condition: the last item is at least the new prime, `log p_{last} − log ρ_{last} ≤ 0`. -/
noncomputable def geLast (k m : ℕ) : Cond (k + 1) (m + 1) :=
  ⟨fun j => if j = Fin.last k then 1 else 0, fun i => if i = Fin.last m then -1 else 0, fun _ => 0, false⟩

theorem holds_geLast {k m : ℕ} (x : ℝ) {v : (Fin (k + 1) → ℕ) × (Fin (m + 1) → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) : (geLast k m).Holds x v.1 v.2 ↔ v.1 (Fin.last k) ≤ v.2 (Fin.last m) := by
  unfold Cond.Holds Cond.val geLast
  simp only [Bool.false_eq_true, ↓reduceIte, ite_mul, one_mul, zero_mul, neg_mul, sum_ite_eq', mem_univ]
  rw [← sub_eq_add_neg, sub_nonpos, Real.log_le_log_iff (by exact_mod_cast hv1 _) (by exact_mod_cast hv2 _),
    Nat.cast_le]

/-- **The Buchstab child of the last item** at the level `x^{1/20}`, with the condition that its last item is at least
the new prime. -/
@[reducible] noncomputable def lastChild {k m : ℕ} (s : Fin (m + 1) → Fin k) (conds : List (Cond k (m + 1))) : Node :=
  ⟨k + 1, m + 1, Function.update (fun i => (s i).castSucc) (Fin.last m) (Fin.last k),
    geLast k m :: (conds.map (Cond.split · (Fin.last m)) ++
      [lvlCond (1 / 20) (fun _ => 0), ltCond (s (Fin.last m))])⟩

theorem pos_merge {k m : ℕ} (i₀ : Fin m) {v : (Fin (k + 1) → ℕ) × (Fin m → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) : (∀ a, 0 < (merge i₀ v).1 a) ∧ ∀ i, 0 < (merge i₀ v).2 i := by
  refine ⟨fun a => hv1 _, fun i => ?_⟩
  simp only [merge]
  by_cases hi : i = i₀
  · subst hi
    rw [Function.update_self]
    exact Nat.mul_pos (hv1 _) (hv2 _)
  · rw [Function.update_of_ne hi]
    exact hv2 i

/-- The Buchstab child's conditions at a pair: the node's at the merged pair, the level and the order. -/
theorem lastConds_facts {k m : ℕ} {s : Fin (m + 1) → Fin k} {conds : List (Cond k (m + 1))} {x : ℝ} (hx : 0 < x)
    {v : (Fin (k + 1) → ℕ) × (Fin (m + 1) → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i)
    (hc : ∀ C ∈ ((⟨k, m + 1, s, conds⟩ : Node).buch (Fin.last m) (1 / 20) (fun _ => 0)).conds, C.Holds x v.1 v.2) :
    (∀ C ∈ conds, C.Holds x (merge (Fin.last m) v).1 (merge (Fin.last m) v).2) ∧
      x ^ (1 / 20 : ℝ) ≤ v.1 (Fin.last k) ∧ v.1 (Fin.last k) < v.1 (s (Fin.last m)).castSucc := by
  have e1 : v.1 = Fin.snoc (Fin.init v.1) (v.1 (Fin.last k)) := (Fin.snoc_init_self v.1).symm
  refine ⟨fun C hC => holds_merge C _ x hv1 hv2 (hc _ (List.mem_append_left _ (List.mem_map_of_mem hC))), ?_, ?_⟩
  · have h := hc (lvlCond (1 / 20) (fun _ => 0)) (List.mem_append_right _ (by simp))
    rw [e1, holds_lvlCond (p := Fin.init v.1) _ _ hx (fun j => hv1 _) (hv1 _), lvlOf_zero, Nat.ceil_le] at h
    exact h
  · have h := hc (ltCond (s (Fin.last m))) (List.mem_append_right _ (by simp))
    rw [e1, holds_ltCond (p := Fin.init v.1) _ _ (fun j => hv1 _) (hv1 _)] at h
    exact h

/-- **The child's terms satisfy the added condition**, so the child's count is the Buchstab child's. -/
theorem count_last {k m : ℕ} {s : Fin (m + 1) → Fin k} {conds : List (Cond k (m + 1))}
    (hinv : Inv ⟨k, m + 1, s, conds⟩) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    ((⟨k, m + 1, s, conds⟩ : Node).buch (Fin.last m) (1 / 20) (fun _ => 0)).count x y =
      (lastChild s conds).count x y := by
  symm
  refine count_cons_of_implied ((⟨k, m + 1, s, conds⟩ : Node).buch (Fin.last m) (1 / 20) (fun _ => 0)) _ x y
    fun v hv hr hI => ?_
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hv
  have hv1 : ∀ a, 0 < v.1 a := fun a => (hp a).2.pos
  have hv2 : ∀ i, 0 < v.2 i := fun i => (hρ i).1
  rw [holds_geLast x hv1 hv2]
  obtain ⟨hcm, -, hlt⟩ := lastConds_facts (by linarith) hv1 hv2 hI.1
  have hlt' : v.1 (Fin.last k) < v.1 (s (Fin.last m)).castSucc := hlt
  obtain ⟨hw1, hw2⟩ := pos_merge (Fin.last m) hv1 hv2
  obtain ⟨-, hge⟩ := hinv x hx (merge (Fin.last m) v : (Fin k → ℕ) × (Fin (m + 1) → ℕ)) hw1 hw2 hcm
  have hge' := hge (Fin.last m)
  simp only [merge, Function.update_self, Fin.init] at hge'
  -- the last item is not `1`, so its least prime factor is at least the new prime
  have hρ2 : 2 ≤ v.2 (Fin.last m) := by
    by_contra h
    have h1 : v.2 (Fin.last m) = 1 := by have := (hρ (Fin.last m)).1; omega
    rw [h1, mul_one] at hge'
    omega
  have hr' := hr (Fin.last m)
  simp only [Function.update_self] at hr'
  exact ((SieveStops2.rough_iff_le_minFac hρ2).1 hr').trans (Nat.minFac_le (by omega))

/-- **The child keeps the invariant.** -/
theorem Inv.last {k m : ℕ} {s : Fin (m + 1) → Fin k} {conds : List (Cond k (m + 1))}
    (h : Inv ⟨k, m + 1, s, conds⟩) : Inv (lastChild s conds) := by
  intro x hx v hv1 hv2 hcv
  have hge := (holds_geLast x hv1 hv2).1 (hcv _ List.mem_cons_self)
  obtain ⟨hcm, hlvl, -⟩ := lastConds_facts (by linarith) hv1 hv2 fun C hC => hcv C (List.mem_cons_of_mem _ hC)
  obtain ⟨hw1, hw2⟩ := pos_merge (Fin.last m) hv1 hv2
  obtain ⟨h1, h2⟩ := h x hx (merge (Fin.last m) v) hw1 hw2 hcm
  refine ⟨fun a => ?_, fun i => ?_⟩
  · induction a using Fin.lastCases with
    | last => exact hlvl
    | cast j => exact h1 j
  · by_cases hi : i = Fin.last m
    · subst hi
      simpa using hge
    · have := h2 i
      simp only [merge, Function.update_of_ne hi, Fin.init] at this
      simpa [Function.update_of_ne hi] using this

/-- **The child's conditions are not functions of the product alone.** -/
theorem CondsOK.last {k m : ℕ} {s : Fin (m + 1) → Fin k} {conds : List (Cond k (m + 1))} (h : CondsOK conds) :
    CondsOK (lastChild s conds).conds := by
  intro C hC
  rcases List.mem_cons.1 hC with rfl | hC
  · exact ⟨Sum.inl (Fin.last k), Sum.inr (Fin.last m), by norm_num [geLast]⟩
  rcases List.mem_append.1 hC with hC | hC
  · obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    obtain ⟨u, w, huw⟩ := h C' hC'
    refine ⟨u.map Fin.castSucc id, w.map Fin.castSucc id, ?_⟩
    rcases u with a | i <;> rcases w with b | j <;> simpa [Cond.split] using huw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · exact ⟨Sum.inl (Fin.last k), Sum.inr 0, by simp [lvlCond]⟩
    · exact ⟨Sum.inl (Fin.last k), Sum.inr 0, by simp [ltCond, (Fin.castSucc_ne_last (s (Fin.last m))).symm]⟩

/-! ### The child's items -/

/-- An item's form at a pair's coordinates and slack is `DEN` times its exponent. -/
theorem ItemsOK.val_coords {k m : ℕ} {A : Rows k m} {items : List LF} (hI : ItemsOK A items) (t : Fin k ⊕ Fin m)
    (x : ℝ) (v : (Fin k → ℕ) × (Fin m → ℕ)) :
    (items.getD (canon t) LF.zero).val (coords A x v) (slack x v) = DEN * expo x v t :=
  hI.2 t (expo x v)

/-- The parent's exponents of a Buchstab child's: the new prime's joins the item `i₀`'s. -/
noncomputable def mergeE {k m : ℕ} (i₀ : Fin m) (α : Fin (k + 1) ⊕ Fin m → ℝ) : Fin k ⊕ Fin m → ℝ :=
  Sum.elim (fun a => α (Sum.inl a.castSucc)) fun i => α (Sum.inr i) + if i = i₀ then α (Sum.inl (Fin.last k)) else 0

theorem cX_buch {k m : ℕ} (A : Rows k m) (i₀ : Fin m) {d : ℕ} (α : Fin (k + 1) ⊕ Fin m → ℝ) {j : ℕ} (hj : j ≠ d) :
    cX (buchRows A i₀ d) α j = cX A (mergeE i₀ α) j := by
  unfold cX
  congr 1
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc]
  simp only [buchRows, ite_eq_right hj, Sum.elim_inl, Sum.elim_inr, Fin.lastCases_castSucc, Fin.lastCases_last,
    mergeE]
  have e : ∀ i : Fin m, (A j (Sum.inr i) : ℝ) * (α (Sum.inr i) + if i = i₀ then α (Sum.inl (Fin.last k)) else 0) =
      (A j (Sum.inr i) : ℝ) * α (Sum.inr i) +
        if i = i₀ then (A j (Sum.inr i₀) : ℝ) * α (Sum.inl (Fin.last k)) else 0 := fun i => by
    split_ifs with h
    · subst h; ring
    · ring
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_ite_eq' univ i₀, ite_eq_left (mem_univ i₀)]
  ring

theorem cX_buch_new {k m : ℕ} (A : Rows k m) (i₀ : Fin m) (d : ℕ) (α : Fin (k + 1) ⊕ Fin m → ℝ) :
    cX (buchRows A i₀ d) α d = DEN * α (Sum.inl (Fin.last k)) := by
  unfold cX
  congr 1
  rw [Fintype.sum_sum_type]
  simp [buchRows]

theorem cH_buch {k m : ℕ} (i₀ : Fin m) (α : Fin (k + 1) ⊕ Fin m → ℝ) : cH α = cH (mergeE i₀ α) := by
  unfold cH
  congr 2
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc]
  simp only [mergeE, Sum.elim_inl, Sum.elim_inr]
  rw [sum_add_distrib, sum_ite_eq' univ i₀, ite_eq_left (mem_univ i₀)]
  ring

/-- A form on the coordinates below `d` has the same value at a child's exponents as at its parent's. -/
theorem val_buch {k m : ℕ} (A : Rows k m) (i₀ : Fin m) {d : ℕ} (α : Fin (k + 1) ⊕ Fin m → ℝ) {L : LF}
    (hL : L.c.length ≤ d) :
    L.val (cX (buchRows A i₀ d) α) (cH α) = L.val (cX A (mergeE i₀ α)) (cH (mergeE i₀ α)) := by
  unfold LF.val
  rw [cH_buch i₀ α, dotR_congr L.c fun j hj => cX_buch A i₀ α (by omega)]

/-- The item at the position `p` of the Buchstab child of the last item, in canonical order: the primes', the new
prime's coordinate `d`, the other items', and the last item's less the new prime's. -/
def lastItemF (items : List LF) (k m d p : ℕ) : LF :=
  if p < k then items.getD p LF.zero
  else if p = k then unitLF d
  else if p < k + m + 1 then items.getD (p - 1) LF.zero
  else (items.getD (k + m) LF.zero).add ((unitLF d).smul (-1))

/-- The items of the Buchstab child of the last item, in canonical order. -/
def lastItems (items : List LF) (k m d : ℕ) : List LF := List.ofFn fun p : Fin (k + m + 2) => lastItemF items k m d p

theorem getD_lastItems {items : List LF} {k m d p : ℕ} (hp : p < k + m + 2) :
    (lastItems items k m d).getD p LF.zero = lastItemF items k m d p := by
  rw [lastItems, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hp), List.getElem_ofFn]

theorem length_getD_le {items : List LF} {d : ℕ} (hfit : ∀ L ∈ items, L.c.length ≤ d) (p : ℕ) :
    (items.getD p LF.zero).c.length ≤ d := by
  rcases lt_or_ge p items.length with hp | hp
  · rw [List.getD_eq_getElem _ _ hp]
    exact hfit _ (List.getElem_mem hp)
  · rw [List.getD_eq_default _ _ hp]
    simp [LF.zero]

/-- **The child's items** are `DEN` times their exponents. -/
theorem itemsOK_last {k m : ℕ} {A : Rows k (m + 1)} {items : List LF} (hI : ItemsOK A items) {d : ℕ}
    (hfit : ∀ L ∈ items, L.c.length ≤ d) : ItemsOK (buchRows A (Fin.last m) d) (lastItems items k m d) := by
  refine ⟨by simp only [lastItems, List.length_ofFn]; ring, fun t α => ?_⟩
  rcases t with a | i
  · induction a using Fin.lastCases with
    | last =>
      rw [show canon (Sum.inl (Fin.last k) : Fin (k + 1) ⊕ Fin (m + 1)) = k from rfl, getD_lastItems (by omega),
        lastItemF, ite_eq_right (lt_irrefl k), ite_eq_left rfl, val_unitLF, cX_buch_new]
    | cast a =>
      rw [show canon (Sum.inl a.castSucc : Fin (k + 1) ⊕ Fin (m + 1)) = a from rfl, getD_lastItems (by omega),
        lastItemF, ite_eq_left a.isLt, val_buch A _ α (length_getD_le hfit _)]
      exact hI.2 (Sum.inl a) (mergeE (Fin.last m) α)
  · induction i using Fin.lastCases with
    | last =>
      rw [show canon (Sum.inr (Fin.last m) : Fin (k + 1) ⊕ Fin (m + 1)) = k + 1 + m from rfl,
        getD_lastItems (by omega), lastItemF, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), LF.val_add, LF.val_smul, val_unitLF, cX_buch_new,
        val_buch A _ α (length_getD_le hfit _)]
      have h := hI.2 (Sum.inr (Fin.last m)) (mergeE (Fin.last m) α)
      rw [show canon (Sum.inr (Fin.last m) : Fin k ⊕ Fin (m + 1)) = k + m from rfl] at h
      have e : mergeE (Fin.last m) α (Sum.inr (Fin.last m)) = α (Sum.inr (Fin.last m)) + α (Sum.inl (Fin.last k)) := by
        simp [mergeE]
      rw [h, e]
      push_cast
      ring
    | cast i =>
      rw [show canon (Sum.inr i.castSucc : Fin (k + 1) ⊕ Fin (m + 1)) = k + 1 + i from rfl,
        getD_lastItems (by omega), lastItemF, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega), show k + 1 + (i : ℕ) - 1 = k + i by omega, val_buch A _ α (length_getD_le hfit _)]
      have h := hI.2 (Sum.inr i.castSucc) (mergeE (Fin.last m) α)
      rw [show canon (Sum.inr i.castSucc : Fin k ⊕ Fin (m + 1)) = k + i from rfl] at h
      have e : mergeE (Fin.last m) α (Sum.inr i.castSucc) = α (Sum.inr i.castSucc) := by
        simp [mergeE, Fin.castSucc_ne_last]
      rw [h, e]

/-! ### The Type I term and the decision -/

/-- The Type I term of Buchstab's step on the last item: the other items sifted as in the node, the last free of
primes below `x^{1/20}`, the term's cofactor. -/
@[reducible] noncomputable def lastT {k m : ℕ} (s : Fin (m + 1) → Fin k) (conds : List (Cond k (m + 1))) : TNode :=
  ⟨k, m, fun i => s i.castSucc, 1 / 20, conds⟩

theorem lastT_toJ {k m : ℕ} (s : Fin (m + 1) → Fin k) (conds : List (Cond k (m + 1))) :
    (lastT s conds).toJ = (⟨k, m + 1, s, conds⟩ : Node).toJ (Fin.last m) (1 / 20) (fun _ => 0) := by
  simp only [TNode.toJ, Node.toJ, lastT]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp [Fin.castSucc_ne_last]

/-- The roles of a node's primes and items other than the last in its Type I term: their labels. -/
def lastRole {k m : ℕ} (labels : List ℕ) (hlt3 : ∀ t : Fin k ⊕ Fin m, labels.getD (canon t) 0 < 3) :
    Fin k ⊕ Fin m → Fin 3 := fun t => ⟨labels.getD (canon t) 0, hlt3 t⟩

/-- The Type I term's group exponents are the node's, the last item in group `3`. -/
theorem tExp_last {k m : ℕ} (s : Fin (m + 1) → Fin k) (conds : List (Cond k (m + 1))) {labels : List ℕ}
    (hlt4 : ∀ t : Fin k ⊕ Fin (m + 1), labels.getD (canon t) 0 < 4) (h3 : labels.getD (k + m) 0 = 3)
    (hlt3 : ∀ t : Fin k ⊕ Fin m, labels.getD (canon t) 0 < 3) (x : ℝ) (w : (Fin k → ℕ) × (Fin (m + 1) → ℕ))
    (i : Fin 3) :
    tExp (lastT s conds) (lastRole labels hlt3) x w i = grpExp (grpOf labels 4 hlt4) ⟨i, by omega⟩ (expo x w) := by
  unfold tExp grpExp
  rw [sum_filter, sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc (n := m)]
  have hl : (grpOf labels 4 hlt4 (Sum.inr (Fin.last m)) = ⟨i, by omega⟩) ↔ False := by
    simp only [grpOf, canon, Sum.elim_inr, Fin.val_last, h3, Fin.mk.injEq, iff_false]
    omega
  rw [ite_eq_right (hl.1 ·), add_zero]
  congr 1
  · refine sum_congr rfl fun a _ => ?_
    simp only [lastRole, grpOf, canon, Sum.elim_inl, Fin.ext_iff, expo]
  · refine sum_congr rfl fun j _ => ?_
    simp only [lastRole, grpOf, canon, Sum.elim_inr, Fin.ext_iff, expo, Fin.val_castSucc]

/-- **A box passing the Type I check lies in Li's regions**: at the last item's Type I term's pairs near `x`, with the
margin `1/(100 DEN)`. -/
theorem typeIReg_of_checkL {k m : ℕ} {s : Fin (m + 1) → Fin k} {conds : List (Cond k (m + 1))}
    {A : Rows k (m + 1)} {items : List LF} (hI : ItemsOK A items) {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound ⟨k, m + 1, s, conds⟩ A E Γ B) (hE : 0 < E) (hfit : ∀ L ∈ items, L.c.length ≤ B.length)
    {acts : List LF} (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length)
    {labels : List ℕ} {kind : ℕ} (hcheck : typeICheck items (k + m) E B acts labels kind = true) :
    ∃ (role : Fin k ⊕ Fin m → Fin 3) (kd : Bool), (kd = false → ∀ t, role t ≠ 2) ∧
      ∀ᶠ x in atTop, ∀ w ∈ (lastT s conds).terms x, x / 2 < (prodP w : ℝ) → (prodP w : ℝ) ≤ x →
        TypeIReg (21 / 40) (1 / (400 * DEN)) kd (tExp (lastT s conds) role x w) ∧
          tExp (lastT s conds) role x w 0 + tExp (lastT s conds) role x w 1 + tExp (lastT s conds) role x w 2 ≤
            1 - 1 / (400 * DEN) := by
  obtain ⟨hl, h3, hall⟩ := labels_of_check hcheck
  rw [hI.1] at hl hall
  have hlt3 : ∀ t : Fin k ⊕ Fin m, labels.getD (canon t) 0 < 3 := by
    rintro (a | j)
    · exact lt_of_lt_of_le (hall a (by omega) (by omega)) (by split_ifs <;> norm_num)
    · exact lt_of_lt_of_le (hall (k + j) (by omega) (by omega)) (by split_ifs <;> norm_num)
  have hlt4 : ∀ t : Fin k ⊕ Fin (m + 1), labels.getD (canon t) 0 < 4 := by
    rintro (a | j)
    · exact (hlt3 (Sum.inl a)).trans (by norm_num)
    · induction j using Fin.lastCases with
      | last =>
        show labels.getD (k + m) 0 < 4
        rw [h3]
        norm_num
      | cast j => exact (hlt3 (Sum.inr j)).trans (by norm_num)
  refine ⟨lastRole labels hlt3, decide (kind ≠ 1), fun hkd t => ?_, ?_⟩
  · have hk1 : kind = 1 := by simpa using hkd
    rcases t with a | j
    · have := hall a (by omega) (by omega)
      rw [ite_eq_left hk1] at this
      simp only [lastRole, ne_eq, Fin.ext_iff, Fin.val_two, canon, Sum.elim_inl]
      omega
    · have := hall (k + j) (by omega) (by omega)
      rw [ite_eq_left hk1] at this
      simp only [lastRole, ne_eq, Fin.ext_iff, Fin.val_two, canon, Sum.elim_inr]
      omega
  filter_upwards [abs_slack_le hE k (m + 1), eventually_gt_atTop 1] with x hsl hx1 w hw h1 h2
  obtain ⟨hwp, -, hc⟩ := mem_filter.1 hw
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hwp
  have hw1 : ∀ a, 0 < w.1 a := fun a => (hp a).2.pos
  have hw2 : ∀ i, 0 < w.2 i := fun i => (hρ i).1
  have hH := hsl w hw1 hw2 (by linarith) (by linarith)
  obtain ⟨hB, hΓ⟩ := h x hx1 w hw1 hw2 hc hH
  refine typeIReg_core hfit hfa hcheck (inBoxC_of_inBox hB) hH (fun g hg => ?_) fun i => ?_
  · obtain ⟨c, hc', rfl⟩ := hacts g hg
    exact Con.val_le (hΓ c hc')
  · rw [tExp_last s conds hlt4 h3 hlt3]
    exact val_grpLF_eq hI hl hlt4 ⟨i, by omega⟩ (expo x w)

/-- **Buchstab's step on the last item.** On a sound node whose box passes the Type I check with the last item as the
cofactor, Buchstab's identity at the level `x^{1/20}` leaves a Type I term, asymptotic by Li's Lemmas 3.1 and 3.2,
and the child: the node is `OK` for `σ` with the child's loss for `−σ`. -/
theorem Sound.OK_of_decL {k m : ℕ} {s : Fin (m + 1) → Fin k} {conds : List (Cond k (m + 1))}
    {A : Rows k (m + 1)} {items : List LF} (hI : ItemsOK A items) {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound ⟨k, m + 1, s, conds⟩ A E Γ B) (hE : 0 < E) (hk : 0 < k) (hinv : Inv ⟨k, m + 1, s, conds⟩)
    (hcond : CondsOK conds) (hfit : ∀ L ∈ items, L.c.length ≤ B.length) {acts : List LF}
    (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length) {labels : List ℕ} {kind : ℕ}
    (hcheck : typeICheck items (k + m) E B acts labels kind = true) {c ρ σ L : ℝ} (hc : 0 < c) (hc1 : c < 1 / 20)
    (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hσ : |σ| ≤ 1) (hLi31 : ShortSieveLi.LiLemma31 (21 / 40) (1 / 10) ρ)
    (hLi32 : ShortSieveLi.LiLemma32 (21 / 40) (1 / 10) ρ)
    (hG : OK (21 / 40) ρ (-σ) (fun x y => ((lastChild s conds).count x y : ℝ)) L) :
    OK (21 / 40) ρ σ (fun x y => ((⟨k, m + 1, s, conds⟩ : Node).count x y : ℝ)) L := by
  have hθρ : (21 / 40 : ℝ) ≤ 1 - ρ := by linarith
  -- the level is at most the last item's sifting prime
  have hlvl : ∀ x : ℝ, 1 < x → ∀ v ∈ pairs k (m + 1) ⌊x⌋₊, (∀ C ∈ conds, C.Holds x v.1 v.2) →
      lvlOf (1 / 20) (fun _ => 0) x v.1 ≤ v.1 (s (Fin.last m)) := by
    intro x hx v hv hcv
    obtain ⟨hp, hρ'⟩ := mem_pairs.1 hv
    obtain ⟨h2, -⟩ := hinv x hx v (fun a => (hp a).2.pos) (fun i => (hρ' i).1) hcv
    rw [lvlOf_zero, Nat.ceil_le]
    exact h2 _
  -- the child
  have hG' : OK (21 / 40) ρ (-σ) (fun x y =>
      (((⟨k, m + 1, s, conds⟩ : Node).buch (Fin.last m) (1 / 20) (fun _ => 0)).count x y : ℝ)) L := by
    refine OK_congr ?_ hθρ hG
    filter_upwards [eventually_gt_atTop 1] with x hx y _ _
    rw [count_last hinv hx y]
  -- the Type I term
  have hJ : Asym (21 / 40) ρ (fun x y =>
      (((⟨k, m + 1, s, conds⟩ : Node).toJ (Fin.last m) (1 / 20) (fun _ => 0)).count x y : ℝ)) := by
    obtain ⟨role, kd, hrole, hreg⟩ := typeIReg_of_checkL hI h hE hfit hacts hfa hcheck
    have hbigT : ∀ᶠ x in atTop, ∀ w ∈ (lastT s conds).terms x, (∀ a, x ^ c < w.1 a) ∧
        ∀ i : Fin (lastT s conds).m, 1 < w.2 i.castSucc := by
      filter_upwards [eventually_gt_atTop 1] with x hx w hw
      obtain ⟨hwp, -, hcw⟩ := mem_filter.1 hw
      obtain ⟨hp, hρ'⟩ := mem_pairs.1 hwp
      obtain ⟨h1, h2⟩ := hinv x hx w (fun a => (hp a).2.pos) (fun i => (hρ' i).1) hcw
      have hxc : (1 : ℝ) < x ^ (1 / 20 : ℝ) := Real.one_lt_rpow hx (by norm_num)
      refine ⟨fun a => (Real.rpow_lt_rpow_of_exponent_lt hx hc1).trans_le (h1 a), fun i => ?_⟩
      have := (h1 (s i.castSucc)).trans (Nat.cast_le.2 (h2 i.castSucc))
      exact_mod_cast hxc.trans_le this
    have hrel := abs_count_sub_le_typeI (lastT s conds) hk hc (by linarith) hρ hρc
      (show (0 : ℝ) < 1 / 20 by norm_num) (show 12 * ρ < (1 / 20 : ℝ) by linarith)
      (show (1 / 20 : ℝ) ≤ 2 * (21 / 40) - 1 by norm_num) (by norm_num) (by norm_num)
      (div_pos one_pos (mul_pos (by norm_num) DEN_pos)) hLi31 hLi32 hcond hbigT role kd hrole hreg
    rw [lastT_toJ] at hrel
    refine asym_of_rel hrel ?_
    -- the comparison interval: the node's count plus the child's
    obtain ⟨CN, hCN0, hCN⟩ := ShortSieveLi.count_B_le ⟨k, m + 1, s, conds⟩ hc (by linarith) hρ hρc
      (hinv.big hc1)
    obtain ⟨CG, hCG0, hCG⟩ := ShortSieveLi.count_B_le (lastChild s conds) hc (by linarith) hρ hρc
      (hinv.last.big hc1)
    refine ⟨CN + CG, by positivity, ?_⟩
    filter_upwards [hCN, hCG, eventually_gt_atTop 1] with x h1 h2 hx
    rw [count_buchstab (⟨k, m + 1, s, conds⟩ : Node) (Fin.last m) (1 / 20) (fun _ => 0) (by linarith) _
      (hlvl x hx), count_last hinv hx]
    push_cast
    have e : (CN + CG) * x ^ (1 - ρ) / Real.log x =
        CN * x ^ (1 - ρ) / Real.log x + CG * x ^ (1 - ρ) / Real.log x := by ring
    rw [e]
    exact add_le_add h1 h2
  exact OK_of_buch (⟨k, m + 1, s, conds⟩ : Node) (Fin.last m) (1 / 20) (fun _ => 0)
    ((eventually_gt_atTop 1).mono fun x hx => hlvl x hx) hθρ hσ hJ hG'

/-! ### The child's coordinates -/

/-- The largest value of a form on the box with `|H| ≤ E`. -/
def LF.maxB (L : LF) (B : Box) (E : ℤ) : ℤ := -((L.smul (-1)).min B E)

theorem LF.le_maxB (L : LF) {B : Box} (hlen : L.c.length ≤ B.length) {E : ℤ} {X : ℕ → ℝ} (hX : InBox B X) {H : ℝ}
    (hH : |H| ≤ E) : L.val X H ≤ L.maxB B E := by
  have h := (L.smul (-1)).min_le (by simpa [LF.smul] using hlen) hX hH
  rw [LF.val_smul] at h
  unfold LF.maxB
  push_cast at h ⊢
  linarith

theorem expo_merge_eq {k m : ℕ} (i₀ : Fin m) (x : ℝ) {v : (Fin (k + 1) → ℕ) × (Fin m → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) : expo x (merge i₀ v) = mergeE i₀ (expo x v) := by
  funext t
  rw [expo_merge i₀ x hv1 hv2]
  rcases t with a | i
  · rfl
  · simp only [Sum.elim_inr, mergeE]
    split_ifs <;> ring

/-- The order of the new prime and the last item's sifting prime: `X_d − F < 0`, `F` the sifting prime's form. -/
def ordL (F : LF) (d : ℕ) : Con := ⟨(unitLF d).add (F.smul (-1)), true⟩

/-- The last item is at least the new prime: `2 X_d − G ≤ 0`, `G` the parent's last item's form. -/
def geL (G : LF) (d : ℕ) : Con := ⟨((unitLF d).smul 2).add (G.smul (-1)), false⟩

/-- **The child's coordinates**: the node's, the new prime's in `[DEN/20, max F)` with `F` its sifting prime's form,
below the sifting prime, and the last item at least the new prime. -/
theorem Sound.last_child {k m : ℕ} {s : Fin (m + 1) → Fin k} {conds : List (Cond k (m + 1))}
    {A : Rows k (m + 1)} {items : List LF} (hI : ItemsOK A items) {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound ⟨k, m + 1, s, conds⟩ A E Γ B) (hf : fits Γ B.length = true)
    (hfit : ∀ L ∈ items, L.c.length ≤ B.length) :
    Sound (lastChild s conds) (buchRows A (Fin.last m) B.length) E
      (geL (items.getD (k + m) LF.zero) B.length :: (Γ ++ [ordL (items.getD (s (Fin.last m)) LF.zero) B.length]))
      (B ++ [(NU0, (items.getD (s (Fin.last m)) LF.zero).maxB B E)]) := by
  set F := items.getD (s (Fin.last m)) LF.zero with hF
  set G := items.getD (k + m) LF.zero with hG
  have hD := DEN_pos
  -- the parent's forms at a child pair
  have key : ∀ (x : ℝ) (v : (Fin (k + 1) → ℕ) × (Fin (m + 1) → ℕ)), (∀ a, 0 < v.1 a) → (∀ i, 0 < v.2 i) →
      F.val (coords (buchRows A (Fin.last m) B.length) x v) (slack x v) =
          DEN * expo x v (Sum.inl (s (Fin.last m)).castSucc) ∧
        G.val (coords (buchRows A (Fin.last m) B.length) x v) (slack x v) =
          DEN * (expo x v (Sum.inr (Fin.last m)) + expo x v (Sum.inl (Fin.last k))) ∧
        F.val (coords (buchRows A (Fin.last m) B.length) x v) (slack x v) =
          F.val (coords A x (merge (Fin.last m) v)) (slack x (merge (Fin.last m) v)) := by
    intro x v hv1 hv2
    have eF := val_buch A (Fin.last m) (expo x v) (length_getD_le hfit (s (Fin.last m)))
    have eG := val_buch A (Fin.last m) (expo x v) (length_getD_le hfit (k + m))
    have hF' := hI.2 (Sum.inl (s (Fin.last m))) (mergeE (Fin.last m) (expo x v))
    have hG' := hI.2 (Sum.inr (Fin.last m)) (mergeE (Fin.last m) (expo x v))
    refine ⟨?_, ?_, ?_⟩
    · rw [coords_eq, show slack x v = cH (expo x v) from rfl, eF]
      exact hF'
    · rw [coords_eq, show slack x v = cH (expo x v) from rfl, eG]
      rw [show canon (Sum.inr (Fin.last m) : Fin k ⊕ Fin (m + 1)) = k + m from rfl] at hG'
      rw [hG']
      simp [mergeE]
    · rw [coords_eq, coords_eq, show slack x v = cH (expo x v) from rfl,
        show slack x (merge (Fin.last m) v) = cH (expo x (merge (Fin.last m) v)) from rfl, eF,
        expo_merge_eq (Fin.last m) x hv1 hv2]
  have h1 := h.buch hf (Fin.last m) (1 / 20) (fun _ => 0) NU0 (F.maxB B E) [ordL F B.length] ?_
  · intro x hx v hv1 hv2 hc hH
    have hge := (holds_geLast x hv1 hv2).1 (hc _ List.mem_cons_self)
    obtain ⟨hB, hΓ⟩ := h1 x hx v hv1 hv2 (fun C hC => hc C (List.mem_cons_of_mem _ hC)) hH
    refine ⟨hB, fun c hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · -- the last item is at least the new prime
      obtain ⟨-, eG, -⟩ := key x v hv1 hv2
      unfold geL Con.Holds
      simp only [Bool.false_eq_true, ↓reduceIte, LF.val_add, LF.val_smul, val_unitLF]
      rw [eG, coords_eq, cX_buch_new]
      have hlx : 0 < Real.log x := Real.log_pos hx
      have hlog : Real.log (v.1 (Fin.last k)) ≤ Real.log (v.2 (Fin.last m)) :=
        Real.log_le_log (by exact_mod_cast hv1 _) (by exact_mod_cast hge)
      have : expo x v (Sum.inl (Fin.last k)) ≤ expo x v (Sum.inr (Fin.last m)) := by
        simp only [expo, Sum.elim_inl, Sum.elim_inr]
        exact div_le_div_of_nonneg_right hlog hlx.le
      push_cast
      nlinarith
    · exact hΓ c hc'
  · intro x hx v hv1 hv2 hc hH
    obtain ⟨hcm, hlvl, hlt⟩ := lastConds_facts (by linarith) hv1 hv2 hc
    obtain ⟨hw1, hw2⟩ := pos_merge (Fin.last m) hv1 hv2
    have hHm : |slack x (merge (Fin.last m) v)| ≤ E := by rwa [← slack_buch (Fin.last m) x hv1 hv2]
    obtain ⟨hBm, -⟩ := h x hx (merge (Fin.last m) v) hw1 hw2 hcm hHm
    obtain ⟨eF, -, eFm⟩ := key x v hv1 hv2
    have hlx : 0 < Real.log x := Real.log_pos hx
    have hx0 : 0 < x := by linarith
    have eN : coords (buchRows A (Fin.last m) B.length) x v B.length =
        DEN * (Real.log (v.1 (Fin.last k)) / Real.log x) := by
      rw [coords_eq, cX_buch_new]
      rfl
    have hlog : Real.log (v.1 (Fin.last k)) < Real.log (v.1 (s (Fin.last m)).castSucc) :=
      Real.log_lt_log (by exact_mod_cast hv1 _) (by exact_mod_cast hlt)
    have hord : coords (buchRows A (Fin.last m) B.length) x v B.length <
        F.val (coords (buchRows A (Fin.last m) B.length) x v) (slack x v) := by
      rw [eN, eF]
      exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hlog hlx) hD
    refine ⟨?_, ?_, fun c hc' => ?_⟩
    · -- the level
      rw [eN, NU0_eq]
      have h2 : Real.log x / 20 ≤ Real.log (v.1 (Fin.last k)) := by
        have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlvl
        rw [Real.log_rpow hx0] at this
        linarith
      calc (DEN : ℝ) / 20 = DEN * ((Real.log x / 20) / Real.log x) := by field_simp
        _ ≤ DEN * (Real.log (v.1 (Fin.last k)) / Real.log x) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hlx.le) hD.le
    · calc _ < F.val (coords (buchRows A (Fin.last m) B.length) x v) (slack x v) := hord
        _ = F.val (coords A x (merge (Fin.last m) v)) (slack x (merge (Fin.last m) v)) := eFm
        _ ≤ F.maxB B E := F.le_maxB (length_getD_le hfit _) hBm hHm
    · simp only [List.mem_singleton] at hc'
      subst hc'
      unfold ordL Con.Holds
      simp only [↓reduceIte, LF.val_add, LF.val_smul, val_unitLF]
      push_cast
      linarith

/-! ### Swapping two items -/

/-- A condition with its two items swapped. -/
noncomputable def _root_.ShortSieveNode.Cond.swap2 {k : ℕ} (C : Cond k 2) : Cond k 2 := ⟨C.e, fun i => C.f i.rev, C.b, C.strict⟩

/-- **The node with its two items swapped**, so that Buchstab's step on the last item decomposes the first. -/
@[reducible] noncomputable def swapN {k : ℕ} (s : Fin 2 → Fin k) (conds : List (Cond k 2)) : Node :=
  ⟨k, 2, fun i => s i.rev, conds.map Cond.swap2⟩

/-- A pair with its two items swapped. -/
def swapP {k : ℕ} (v : (Fin k → ℕ) × (Fin 2 → ℕ)) : (Fin k → ℕ) × (Fin 2 → ℕ) := (v.1, fun i => v.2 i.rev)

theorem swapP_swapP {k : ℕ} (v : (Fin k → ℕ) × (Fin 2 → ℕ)) : swapP (swapP v) = v := by
  simp [swapP]

theorem holds_swap2 {k : ℕ} (C : Cond k 2) (x : ℝ) (v : (Fin k → ℕ) × (Fin 2 → ℕ)) :
    C.swap2.Holds x (swapP v).1 (swapP v).2 ↔ C.Holds x v.1 v.2 := by
  have e : C.swap2.val (swapP v).1 (swapP v).2 = C.val v.1 v.2 := by
    unfold Cond.val Cond.swap2 swapP
    congr 1
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => by simp
  unfold Cond.Holds
  rw [e]
  rfl

theorem prodP_swapP {k : ℕ} (v : (Fin k → ℕ) × (Fin 2 → ℕ)) : prodP (swapP v) = prodP v := by
  unfold prodP swapP
  congr 1
  exact Fintype.prod_equiv Fin.revPerm _ _ fun i => by simp

/-- A pair of the swapped node is the swap of a pair of the node. -/
theorem swap_iff {k : ℕ} (s : Fin 2 → Fin k) (conds : List (Cond k 2)) (x y : ℝ) (Y : ℕ)
    (v : (Fin k → ℕ) × (Fin 2 → ℕ)) :
    (v ∈ pairs k 2 Y ∧ (∀ i, SieveTree.rough (v.1 ((swapN s conds).s i)) (v.2 i)) ∧
        (swapN s conds).InI x y v.1 v.2) ↔
      (swapP v ∈ pairs k 2 Y ∧ (∀ i, SieveTree.rough ((swapP v).1 (s i)) ((swapP v).2 i)) ∧
        (⟨k, 2, s, conds⟩ : Node).InI x y (swapP v).1 (swapP v).2) := by
  have hp : v ∈ pairs k 2 Y ↔ swapP v ∈ pairs k 2 Y := by
    simp only [mem_pairs, swapP]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => h2 i.rev⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => by simpa using h2 i.rev⟩
  have hr : (∀ i, SieveTree.rough (v.1 ((swapN s conds).s i)) (v.2 i)) ↔
      ∀ i, SieveTree.rough ((swapP v).1 (s i)) ((swapP v).2 i) := by
    simp only [swapP]
    constructor
    · intro h i
      simpa using h i.rev
    · intro h i
      simpa using h i.rev
  have hc : (∀ C ∈ (swapN s conds).conds, C.Holds x v.1 v.2) ↔ ∀ C ∈ conds, C.Holds x (swapP v).1 (swapP v).2 := by
    constructor
    · intro h C hC
      have := h _ (List.mem_map_of_mem hC)
      rwa [← swapP_swapP v, holds_swap2] at this
    · intro h C hC
      obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
      have := h C' hC'
      rwa [← holds_swap2 C' x (swapP v), swapP_swapP] at this
  have hpr : prodP (v.1, v.2) = prodP ((swapP v).1, (swapP v).2) := (prodP_swapP v).symm
  unfold Node.InI
  rw [hp, hr, hc, hpr]

theorem count_swap {k : ℕ} (s : Fin 2 → Fin k) (conds : List (Cond k 2)) (x y : ℝ) :
    (swapN s conds).count x y = (⟨k, 2, s, conds⟩ : Node).count x y := by
  unfold Node.count
  refine card_nbij' swapP swapP ?_ ?_ (fun v _ => swapP_swapP v) (fun v _ => swapP_swapP v)
  · intro v hv
    rw [mem_coe, mem_filter_inst] at hv ⊢
    exact (swap_iff s conds x y _ v).1 ⟨hv.1, hv.2.1, hv.2.2⟩
  · intro v hv
    rw [mem_coe, mem_filter_inst] at hv ⊢
    have := (swap_iff s conds x y ⌊x⌋₊ (swapP v)).2
    rw [swapP_swapP] at this
    exact this ⟨hv.1, hv.2.1, hv.2.2⟩

/-- The swapped node's rows. -/
def swapRows {k : ℕ} (A : Rows k 2) : Rows k 2 := fun j t => A j (Sum.map id Fin.rev t)

/-- The swapped exponents. -/
def swapE {k : ℕ} (α : Fin k ⊕ Fin 2 → ℝ) : Fin k ⊕ Fin 2 → ℝ := fun t => α (Sum.map id Fin.rev t)

theorem cX_swap {k : ℕ} (A : Rows k 2) (α : Fin k ⊕ Fin 2 → ℝ) : cX (swapRows A) α = cX A (swapE α) := by
  funext j
  unfold cX swapRows swapE
  congr 1
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ fun i => by simp

theorem cH_swap {k : ℕ} (α : Fin k ⊕ Fin 2 → ℝ) : cH α = cH (swapE α) := by
  unfold cH swapE
  congr 2
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ fun i => by simp

theorem expo_swapP {k : ℕ} (x : ℝ) (v : (Fin k → ℕ) × (Fin 2 → ℕ)) : expo x (swapP v) = swapE (expo x v) := by
  funext t
  rcases t with a | i <;> rfl

/-- **The swapped node is sound** with the swapped rows and the same box and constraints. -/
theorem Sound.swap {k : ℕ} {s : Fin 2 → Fin k} {conds : List (Cond k 2)} {A : Rows k 2} {E : ℤ} {Γ : List Con}
    {B : Box} (h : Sound ⟨k, 2, s, conds⟩ A E Γ B) : Sound (swapN s conds) (swapRows A) E Γ B := by
  intro x hx v hv1 hv2 hc hH
  have hX : coords (swapRows A) x v = coords A x (swapP v) := by
    rw [coords_eq, coords_eq, cX_swap, expo_swapP]
  have hS : slack x v = slack x (swapP v) := by
    rw [show slack x v = cH (expo x v) from rfl, show slack x (swapP v) = cH (expo x (swapP v)) from rfl,
      cH_swap, expo_swapP]
  have hc' : ∀ C ∈ conds, C.Holds x (swapP v).1 (swapP v).2 := fun C hC => by
    have := hc _ (List.mem_map_of_mem hC)
    rwa [← swapP_swapP v, holds_swap2] at this
  rw [hX, hS]
  exact h x hx (swapP v) hv1 (fun i => hv2 i.rev) hc' (hS ▸ hH)

theorem Inv.swap {k : ℕ} {s : Fin 2 → Fin k} {conds : List (Cond k 2)} (h : Inv ⟨k, 2, s, conds⟩) :
    Inv (swapN s conds) := by
  intro x hx v hv1 hv2 hc
  have hc' : ∀ C ∈ conds, C.Holds x (swapP v).1 (swapP v).2 := fun C hC => by
    have := hc _ (List.mem_map_of_mem hC)
    rwa [← swapP_swapP v, holds_swap2] at this
  obtain ⟨h1, h2⟩ := h x hx (swapP v) hv1 (fun i => hv2 i.rev) hc'
  exact ⟨h1, fun i => by simpa [swapP] using h2 i.rev⟩

theorem CondsOK.swap {k : ℕ} {conds : List (Cond k 2)} (h : CondsOK conds) : CondsOK (conds.map Cond.swap2) := by
  intro C hC
  obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
  obtain ⟨u, w, huw⟩ := h C' hC'
  refine ⟨u.map id Fin.rev, w.map id Fin.rev, ?_⟩
  rcases u with a | i <;> rcases w with b | j <;> simpa [Cond.swap2] using huw

/-- The item at the position `p` of the swapped node, in canonical order. -/
def swapItemF (items : List LF) (k p : ℕ) : LF :=
  if p = k then items.getD (k + 1) LF.zero else if p = k + 1 then items.getD k LF.zero else items.getD p LF.zero

/-- The swapped node's items, in canonical order. -/
def swapItems (items : List LF) (k : ℕ) : List LF := List.ofFn fun p : Fin (k + 2) => swapItemF items k p

theorem itemsOK_swap {k : ℕ} {A : Rows k 2} {items : List LF} (hI : ItemsOK A items) :
    ItemsOK (swapRows A) (swapItems items k) := by
  refine ⟨by simp [swapItems], fun t α => ?_⟩
  have hget : ∀ p, p < k + 2 → (swapItems items k).getD p LF.zero = swapItemF items k p := fun p hp => by
    rw [swapItems, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hp), List.getElem_ofFn]
  rw [cX_swap, cH_swap]
  rcases t with a | i
  · rw [show canon (Sum.inl a : Fin k ⊕ Fin 2) = a from rfl, hget _ (by omega), swapItemF,
      ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hI.2 (Sum.inl a) (swapE α)
  · have h := hI.2 (Sum.inr i.rev) (swapE α)
    rw [show canon (Sum.inr i : Fin k ⊕ Fin 2) = k + i from rfl, hget _ (by omega), swapItemF]
    rw [show canon (Sum.inr i.rev : Fin k ⊕ Fin 2) = k + i.rev from rfl] at h
    have e : swapE α (Sum.inr i.rev) = α (Sum.inr i) := by simp [swapE]
    rw [e] at h
    fin_cases i
    · simpa using h
    · simpa using h

/-! ### The reversed nodes' items -/

/-- The item at the position `p` of a reversed node with `k + 2` primes, in canonical order: the new prime `X_{k+2}`,
the other primes `X_p`, `ρ = DEN − H − Σ_{j ≤ k+1} X_j` and `β = X_0 − X_{k+2}`. -/
def revItemF (k p : ℕ) : LF :=
  if p = 0 then unitLF (k + 2)
  else if p ≤ k + 1 then unitLF p
  else if p = k + 2 then ⟨DEN, List.replicate (k + 2) (-1), -1⟩
  else (unitLF 0).add ((unitLF (k + 2)).smul (-1))

/-- The items of a reversed node with `k + 2` primes, in canonical order. -/
def revItems (k : ℕ) : List LF := List.ofFn fun p : Fin (k + 4) => revItemF k p

theorem cX_rev_zero {k : ℕ} (α : Fin (k + 2) ⊕ Fin 2 → ℝ) :
    cX (revRows (k + 1)) α 0 = DEN * (α (Sum.inl 0) + α (Sum.inr 1)) := by
  unfold cX
  congr 1
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, sum_eq_single (0 : Fin (k + 2)) (fun a _ ha => ?_)
    (fun h => absurd (mem_univ _) h)]
  · simp [revRows]
  · simp [revRows, ha]

theorem cX_rev_mid {k : ℕ} (α : Fin (k + 2) ⊕ Fin 2 → ℝ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k + 1) :
    cX (revRows (k + 1)) α j = DEN * α (Sum.inl ⟨j, by omega⟩) := by
  unfold cX
  congr 1
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, sum_eq_single (⟨j, by omega⟩ : Fin (k + 2)) (fun a _ ha => ?_)
    (fun h => absurd (mem_univ _) h)]
  · simp [revRows, show j ≠ 0 by omega]
  · have haj : a.val ≠ j := fun h => ha (Fin.ext h)
    simp [revRows, haj, show j ≠ 0 by omega, show j ≠ k + 1 + 1 by omega]

theorem cX_rev_top {k : ℕ} (α : Fin (k + 2) ⊕ Fin 2 → ℝ) : cX (revRows (k + 1)) α (k + 2) = DEN * α (Sum.inl 0) := by
  unfold cX
  congr 1
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, sum_eq_single (0 : Fin (k + 2)) (fun a _ ha => ?_)
    (fun h => absurd (mem_univ _) h)]
  · simp [revRows]
  · have hak : a.val ≠ k + 2 := by have := a.isLt; omega
    simp [revRows, ha, hak]

/-- **The reversed node's items** are `DEN` times their exponents. -/
theorem itemsOK_rev (k : ℕ) : ItemsOK (revRows (k + 1)) (revItems k) := by
  refine ⟨by simp [revItems], fun t α => ?_⟩
  have hget : ∀ p, p < k + 4 → (revItems k).getD p LF.zero = revItemF k p := fun p hp => by
    rw [revItems, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hp), List.getElem_ofFn]
  rcases t with a | i
  · rw [show canon (Sum.inl a : Fin (k + 2) ⊕ Fin 2) = a from rfl, hget _ (by omega), revItemF]
    by_cases ha : a = 0
    · subst ha
      rw [ite_eq_left (by simp), val_unitLF, cX_rev_top]
    · have ha' : a.val ≠ 0 := fun h => ha (Fin.ext h)
      rw [ite_eq_right ha', ite_eq_left (by omega), val_unitLF, cX_rev_mid α (by omega) (by omega)]
  · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · -- `ρ`
      rw [show canon (Sum.inr 0 : Fin (k + 2) ⊕ Fin 2) = k + 2 from rfl, hget _ (by omega), revItemF,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      have hs : ∑ j ∈ range (k + 2), cX (revRows (k + 1)) α j =
          DEN * (α (Sum.inl 0) + α (Sum.inr 1)) + DEN * ∑ a : Fin (k + 1), α (Sum.inl a.succ) := by
        rw [sum_range_succ', cX_rev_zero, add_comm, mul_sum,
          ← Fin.sum_univ_eq_sum_range (fun j => cX (revRows (k + 1)) α (j + 1))]
        congr 1
        refine sum_congr rfl fun a _ => ?_
        rw [cX_rev_mid α (by omega) (by omega)]
        rfl
      have ht : ∑ t, α t =
          α (Sum.inl 0) + ∑ a : Fin (k + 1), α (Sum.inl a.succ) + α (Sum.inr 0) + α (Sum.inr 1) := by
        rw [Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_two]
        ring
      unfold LF.val cH
      rw [dotR_replicate_neg_one, hs, ht]
      push_cast
      ring
    · -- `β`
      rw [show canon (Sum.inr 1 : Fin (k + 2) ⊕ Fin 2) = k + 3 from rfl, hget _ (by omega), revItemF,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), LF.val_add, LF.val_smul,
        val_unitLF, val_unitLF, cX_rev_zero, cX_rev_top]
      push_cast
      ring

end ShortSieveCert

#print axioms ShortSieveCert.Sound.OK_of_decL
#print axioms ShortSieveCert.Sound.last_child
#print axioms ShortSieveCert.Inv.last
#print axioms ShortSieveCert.CondsOK.last
#print axioms ShortSieveCert.itemsOK_last
#print axioms ShortSieveCert.count_swap
#print axioms ShortSieveCert.Sound.swap
#print axioms ShortSieveCert.Inv.swap
#print axioms ShortSieveCert.CondsOK.swap
#print axioms ShortSieveCert.itemsOK_swap
#print axioms ShortSieveCert.itemsOK_rev
