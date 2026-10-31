import ShortSieveCertDrop

/-!
# The certificate's role reversals

Li's role reversal on a standard node `S(A_{p₁⋯p_{k+2}}, p_{k+2})` turns `p₁` into an item free of primes below the
level `x^{1/25}`. The result is a Type I term (`revT`) in which the rough item is a variable. The term is the node (the
item a prime) plus the reversed child (the item `pβ`, with `p ≥ x^{1/25}` its least prime factor in `p₁`'s place and
`β ≥ p` free of primes below `p`) (`ShortSieveBuch.count_rev`). A reversed node (`revN`) has primes and two rough items:
`ρ`, free of primes below the last prime, and `β`, free of primes below the first.

* `RevInv`: the reversed node's invariant, its primes at least `x^{1/25}`, `ρ` at least the last prime and `β` at least
  the first; `StdInv.rev` and `CondsOK.rev` keep the invariants for the child.
* `count_rev_std`: the Type I term is the node plus the child.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveExpand ShortSieveBuch ShortSieveTree ShortSieveTypeI

open Classical

/-- The sifting primes of a reversed node's items: `ρ` by the last prime, `β` by the first. -/
def revS (k : ℕ) : Fin 2 → Fin (k + 1) := Fin.snoc (fun _ : Fin 1 => Fin.last k) 0

/-- A reversed node: `k + 1` primes, `ρ` free of primes below the last and `β` free of primes below the first. -/
@[reducible] def revN (k : ℕ) (conds : List (Cond (k + 1) 2)) : Node := ⟨k + 1, 2, revS k, conds⟩

/-- The conditions of a standard node's reversed child at the level `x^{1/25}`: the node's, with `p₁ = pβ`, the level
`x^{1/25} ≤ p` and the order `p ≤ β`. -/
noncomputable def revConds (k : ℕ) (conds : List (Cond (k + 1) 1)) : List (Cond (k + 1) 2) :=
  conds.map Cond.revSplit ++ [lvlCond0 (1 / 25) (fun _ => 0), geCond0]

/-- The invariant of a reversed node's conditions: its primes are at least `x^{1/25}`, `ρ` is at least the last prime
and `β` at least the first. -/
def RevInv (k : ℕ) (conds : List (Cond (k + 1) 2)) : Prop :=
  ∀ x : ℝ, 1 < x → ∀ v : (Fin (k + 1) → ℕ) × (Fin 2 → ℕ), (∀ a, 0 < v.1 a) → (∀ i, 0 < v.2 i) →
    (∀ C ∈ conds, C.Holds x v.1 v.2) → (∀ a, x ^ (1 / 25 : ℝ) ≤ v.1 a) ∧ v.1 (Fin.last k) ≤ v.2 0 ∧ v.1 0 ≤ v.2 1

/-- The parent pair of a reversed child's pair: `p₁ = pβ`, the other primes and `ρ`. -/
def revMerge {k : ℕ} (v : (Fin (k + 2) → ℕ) × (Fin 2 → ℕ)) : (Fin (k + 2) → ℕ) × (Fin 1 → ℕ) :=
  (Fin.cons (v.1 0 * v.2 1) (Fin.tail v.1), fun _ => v.2 0)

theorem revMerge_pos {k : ℕ} {v : (Fin (k + 2) → ℕ) × (Fin 2 → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) :
    (∀ a, 0 < (revMerge v).1 a) ∧ ∀ i, 0 < (revMerge v).2 i := by
  refine ⟨fun a => ?_, fun i => hv2 0⟩
  induction a using Fin.cases with
  | zero => exact Nat.mul_pos (hv1 0) (hv2 1)
  | succ j => exact hv1 j.succ

/-- The child's conditions at a pair: the node's at the parent pair, the level and the order. -/
theorem revConds_facts {k : ℕ} {conds : List (Cond (k + 2) 1)} {x : ℝ} (hx : 0 < x)
    {v : (Fin (k + 2) → ℕ) × (Fin 2 → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i)
    (hc : ∀ C ∈ revConds (k + 1) conds, C.Holds x v.1 v.2) :
    (∀ C ∈ conds, C.Holds x (revMerge v).1 (revMerge v).2) ∧ x ^ (1 / 25 : ℝ) ≤ v.1 0 ∧ v.1 0 ≤ v.2 1 := by
  have e1 : v.1 = Fin.cons (v.1 0) (Fin.tail v.1) := (Fin.cons_self_tail v.1).symm
  have e2 : v.2 = Fin.snoc (fun _ : Fin 1 => v.2 0) (v.2 1) := by
    funext i
    induction i using Fin.lastCases with
    | last => rfl
    | cast j => have hj : j = 0 := Fin.fin_one_eq_zero j; subst hj; rfl
  refine ⟨fun C hC => ?_, ?_, ?_⟩
  · have h := hc _ (List.mem_append_left _ (List.mem_map_of_mem hC))
    rw [e1, e2, holds_revSplit C x _ _ (hv1 0) (hv2 1), holds_rev] at h
    exact h
  · have h := hc (lvlCond0 (1 / 25) (fun _ => 0)) (List.mem_append_right _ (by simp))
    rw [e1, holds_lvlCond0 (p := Fin.tail v.1) _ _ hx (fun j => hv1 _) (hv1 0), lvlOf_zero, Nat.ceil_le] at h
    exact h
  · have h := hc geCond0 (List.mem_append_right _ (by simp))
    rw [e1, e2, holds_geCond0 x (Fin.tail v.1) _ (hv1 0) (hv2 1)] at h
    exact h

/-- **The reversed child keeps the invariant.** -/
theorem StdInv.rev {k : ℕ} {conds : List (Cond (k + 2) 1)} (h : StdInv (k + 1) conds) :
    RevInv (k + 1) (revConds (k + 1) conds) := by
  intro x hx v hv1 hv2 hc
  obtain ⟨hcm, hlvl, hge⟩ := revConds_facts (by linarith) hv1 hv2 hc
  obtain ⟨hw1, hw2⟩ := revMerge_pos hv1 hv2
  obtain ⟨h1, h2⟩ := h x hx (revMerge v) hw1 hw2 hcm
  refine ⟨fun a => ?_, ?_, hge⟩
  · induction a using Fin.cases with
    | zero => exact hlvl
    | succ j => exact h1 j.succ
  · simpa [revMerge, Fin.tail] using h2

/-- **The reversed child's conditions are not functions of the product alone.** -/
theorem CondsOK.rev {k : ℕ} {conds : List (Cond (k + 2) 1)} (h : CondsOK conds) :
    CondsOK (revConds (k + 1) conds) := by
  intro C hC
  rcases List.mem_append.1 hC with hC | hC
  · obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    obtain ⟨u, w, huw⟩ := h C' hC'
    refine ⟨u.map id Fin.castSucc, w.map id Fin.castSucc, ?_⟩
    rcases u with a | i <;> rcases w with b | j <;> simpa [Cond.revSplit] using huw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · exact ⟨Sum.inl 0, Sum.inr 0, by simp [lvlCond0]⟩
    · exact ⟨Sum.inl 0, Sum.inr 1, by norm_num [geCond0]⟩


/-! ### The Type I term -/

theorem last_ne_zero_succ (k : ℕ) : Fin.last (k + 1) ≠ 0 := by simp [Fin.ext_iff]

/-- The Type I term of a standard node's role reversal: its primes after the first, with its rough item (free of primes
below the last) a variable, and the first prime's place free of primes below `x^{1/25}`. -/
@[reducible] noncomputable def revT (k : ℕ) (conds : List (Cond (k + 2) 1)) : TNode :=
  ⟨k + 1, 1, fun _ => Fin.last k, 1 / 25, conds.map Cond.rev⟩

theorem revT_toJ (k : ℕ) (conds : List (Cond (k + 2) 1)) :
    (revT k conds).toJ = revJ (k + 1) 1 (fun _ => Fin.last (k + 1)) (fun _ => last_ne_zero_succ k) (1 / 25)
      (fun _ => 0) conds := by
  simp only [TNode.toJ, revT, revJ]
  congr 1

/-- **The role reversal of a standard node**: the Type I term is the node plus the reversed child. -/
theorem count_rev_std {k : ℕ} {conds : List (Cond (k + 2) 1)} (hinv : StdInv (k + 1) conds) {x : ℝ} (hx : 1 < x)
    (y : ℝ) : (revT k conds).toJ.count x y =
      (std (k + 1) conds).count x y + (revN (k + 1) (revConds (k + 1) conds)).count x y := by
  rw [revT_toJ]
  refine count_rev (k + 1) 1 (fun _ => Fin.last (k + 1)) (fun _ => last_ne_zero_succ k) (1 / 25) (fun _ => 0) conds
    (by linarith) y fun w hw hc => ?_
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hw
  rw [lvlOf_zero]
  have hx25 : 1 < x ^ (1 / 25 : ℝ) := Real.one_lt_rpow hx (by norm_num)
  refine ⟨?_, ?_⟩
  · have := Nat.lt_ceil.2 (show ((1 : ℕ) : ℝ) < x ^ (1 / 25 : ℝ) by exact_mod_cast hx25)
    omega
  · -- the first prime's place is at least `x^{1/25}`, by the node's invariant at the parent pair
    have e2 : w.2 = Fin.snoc (Fin.init w.2) (w.2 (Fin.last 1)) := (Fin.snoc_init_self w.2).symm
    have hc' : ∀ C ∈ conds, C.Holds x (Fin.cons (w.2 (Fin.last 1)) w.1) (Fin.init w.2) := fun C hC => by
      have h := hc C hC
      rw [e2, holds_rev] at h
      exact h
    have hpos1 : ∀ a, 0 < (Fin.cons (w.2 (Fin.last 1)) w.1 : Fin (k + 2) → ℕ) a := fun a => by
      induction a using Fin.cases with
      | zero => exact (hρ _).1
      | succ j => exact (hp j).2.pos
    obtain ⟨h1, -⟩ := hinv x hx (Fin.cons (w.2 (Fin.last 1)) w.1, Fin.init w.2) hpos1 (fun i => (hρ _).1) hc'
    rw [Nat.ceil_le]
    simpa using h1 0

/-- The parent pair of the reversed Type I term's pair: the first prime's place in front, and the rough item. -/
def revParent {k : ℕ} (w : (Fin (k + 1) → ℕ) × (Fin 2 → ℕ)) : (Fin (k + 2) → ℕ) × (Fin 1 → ℕ) :=
  (Fin.cons (w.2 1) w.1, fun _ => w.2 0)

/-- The roles in the reversed Type I term: the parent's labels of the primes after the first and of the rough item. -/
def revRole {k : ℕ} (labels : List ℕ) (hlt3 : ∀ a : Fin (k + 1), labels.getD (a + 1) 0 < 3)
    (hρ3 : labels.getD (k + 2) 0 < 3) : Fin (k + 1) ⊕ Fin 1 → Fin 3 :=
  Sum.elim (fun a => ⟨labels.getD (a + 1) 0, hlt3 a⟩) fun _ => ⟨labels.getD (k + 2) 0, hρ3⟩

/-- The reversed Type I term's group exponents are the parent's, the first prime in group `3`. -/
theorem tExp_rev {k : ℕ} (conds : List (Cond (k + 2) 1)) {labels : List ℕ}
    (hlt4 : ∀ t : Fin (k + 2) ⊕ Fin 1, labels.getD (canon t) 0 < 4) (h3 : labels.getD 0 0 = 3)
    (hlt3 : ∀ a : Fin (k + 1), labels.getD (a + 1) 0 < 3) (hρ3 : labels.getD (k + 2) 0 < 3) (x : ℝ)
    (w : (Fin (k + 1) → ℕ) × (Fin 2 → ℕ)) (i : Fin 3) :
    tExp (revT k conds) (revRole labels hlt3 hρ3) x w i =
      grpExp (grpOf labels 4 hlt4) ⟨i, by omega⟩ (expo x (revParent w)) := by
  unfold tExp grpExp
  rw [sum_filter, sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_succ (n := k + 1)]
  have h0 : (grpOf labels 4 hlt4 (Sum.inl 0) = ⟨i, by omega⟩) ↔ False := by
    simp only [grpOf, canon, Sum.elim_inl, Fin.val_zero, h3, Fin.mk.injEq, iff_false]
    omega
  rw [ite_eq_right (h0.1 ·), zero_add]
  congr 1
  · refine sum_congr rfl fun a _ => ?_
    simp only [revRole, grpOf, canon, Sum.elim_inl, Fin.ext_iff, expo, revParent, Fin.val_succ, Fin.cons_succ]
  · refine sum_congr rfl fun j _ => ?_
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hj
    simp only [revRole, grpOf, canon, Sum.elim_inr, Fin.ext_iff, expo, revParent, Fin.val_zero, add_zero,
      Fin.castSucc_zero]


/-- A reversed node's terms have primes above `x^c`, for `c < 1/25`, and rough items above `1`. -/
theorem RevInv.big {k : ℕ} {conds : List (Cond (k + 1) 2)} (h : RevInv k conds) {c : ℝ} (hc1 : c < 1 / 25) :
    ∀ᶠ x in atTop, ∀ v ∈ (revN k conds).terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i := by
  filter_upwards [eventually_gt_atTop 1] with x hx v hv
  obtain ⟨hvp, -, hcv⟩ := mem_filter.1 hv
  obtain ⟨hp, hρ⟩ := mem_pairs.1 hvp
  obtain ⟨h1, h2, h3⟩ := h x hx v (fun a => (hp a).2.pos) (fun i => (hρ i).1) hcv
  have hxc : (1 : ℝ) < x ^ (1 / 25 : ℝ) := Real.one_lt_rpow hx (by norm_num)
  have key : ∀ a j, v.1 a ≤ v.2 j → 1 < v.2 j := fun a j hj => by
    have := (h1 a).trans (Nat.cast_le.2 hj)
    exact_mod_cast hxc.trans_le this
  refine ⟨fun a => (Real.rpow_lt_rpow_of_exponent_lt hx hc1).trans_le (h1 a), fun i => ?_⟩
  induction i using Fin.lastCases with
  | last => exact key 0 _ h3
  | cast j => have hj : j = 0 := Fin.fin_one_eq_zero j; subst hj; exact key (Fin.last k) _ h2

/-- The reversed Type I term's conditions are not functions of the product alone. -/
theorem CondsOK.revT {k : ℕ} {conds : List (Cond (k + 2) 1)} (h : CondsOK conds) :
    CondsOK (conds.map Cond.rev) := by
  intro C hC
  obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
  obtain ⟨u, w, huw⟩ := h C' hC'
  let f : Fin (k + 2) ⊕ Fin 1 → Fin (k + 1) ⊕ Fin 2 :=
    Sum.elim (Fin.cases (Sum.inr (Fin.last 1)) Sum.inl) fun i => Sum.inr i.castSucc
  have key : ∀ t, Sum.elim C'.rev.e C'.rev.f (f t) = Sum.elim C'.e C'.f t := by
    rintro (a | i)
    · induction a using Fin.cases with
      | zero =>
        simp only [f, Sum.elim_inl, Fin.cases_zero, Sum.elim_inr, Cond.rev]
        exact Fin.snoc_last _ _
      | succ j => simp [f, Cond.rev, Fin.tail]
    · simp [f, Cond.rev]
  exact ⟨f u, f w, by rw [key, key]; exact huw⟩

/-! ### The child's coordinates -/

/-- The rows of a reversed node: `X_0 = α_{p₀} + α_β` (the parent's first prime `pβ`), `X_j = α_{p_j}` for
`1 ≤ j ≤ K`, and the new coordinate `X_{K+1} = α_{p₀}`. -/
def revRows (K : ℕ) : Rows (K + 1) 2 := fun j t =>
  Sum.elim (fun a : Fin (K + 1) => if a.val = 0 then (if j = 0 ∨ j = K + 1 then 1 else 0)
      else if a.val = j then 1 else 0)
    (fun i : Fin 2 => if i.val = 1 ∧ j = 0 then 1 else 0) t

theorem expo_revMerge {k : ℕ} (x : ℝ) {v : (Fin (k + 2) → ℕ) × (Fin 2 → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) (a : Fin (k + 2)) :
    expo x (revMerge v) (Sum.inl a) = if a.val = 0 then expo x v (Sum.inl 0) + expo x v (Sum.inr 1)
      else expo x v (Sum.inl a) := by
  induction a using Fin.cases with
  | zero =>
    simp only [expo, revMerge, Sum.elim_inl, Fin.cons_zero, Fin.val_zero, ↓reduceIte, Sum.elim_inr]
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (hv1 0).ne') (by exact_mod_cast (hv2 1).ne'), add_div]
  | succ j =>
    simp [expo, revMerge, Fin.tail]

/-- **The coordinates of a reversed child's pair** up to `k + 1` are those of its parent pair. -/
theorem coords_rev {k : ℕ} (x : ℝ) {v : (Fin (k + 2) → ℕ) × (Fin 2 → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) {j : ℕ} (hj : j ≤ k + 1) :
    coords (revRows (k + 1)) x v j = coords (stdRows (k + 2)) x (revMerge v) j := by
  have hj' : j < k + 2 := by omega
  have hP : coords (stdRows (k + 2)) x (revMerge v) j = DEN * expo x (revMerge v) (Sum.inl ⟨j, hj'⟩) :=
    coords_std x (revMerge v) ⟨j, hj'⟩
  rw [hP, expo_revMerge x hv1 hv2]
  have hrow : ∀ a : Fin (k + 2), ((revRows (k + 1) j (Sum.inl a) : ℤ) : ℝ) = if a.val = j then 1 else 0 := by
    intro a
    have e : revRows (k + 1) j (Sum.inl a) = if a.val = j then 1 else 0 := by
      simp only [revRows, Sum.elim_inl]
      split_ifs <;> omega
    rw [e]
    simp
  have hrowi : ∀ i : Fin 2, ((revRows (k + 1) j (Sum.inr i) : ℤ) : ℝ) = if i.val = 1 ∧ j = 0 then 1 else 0 := by
    intro i
    simp only [revRows, Sum.elim_inr]
    split_ifs <;> simp
  unfold coords
  congr 1
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [hrow, hrowi, ite_mul, one_mul, zero_mul]
  rw [sum_eq_single (⟨j, hj'⟩ : Fin (k + 2)) (fun a _ ha => ite_eq_right (fun h => ha (Fin.ext h)))
    (fun h => absurd (mem_univ _) h)]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · simp [(Nat.pos_iff_ne_zero.1 hj0)]

/-- The new coordinate of a reversed child's pair is the new prime's exponent. -/
theorem coords_rev_new {k : ℕ} (x : ℝ) (v : (Fin (k + 2) → ℕ) × (Fin 2 → ℕ)) :
    coords (revRows (k + 1)) x v (k + 2) = DEN * expo x v (Sum.inl 0) := by
  unfold coords
  congr 1
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [revRows, Sum.elim_inl, Sum.elim_inr, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rw [sum_eq_single (0 : Fin (k + 2)) (fun a _ ha => ?_) (fun h => absurd (mem_univ _) h)]
  · simp
  · have ha0 : a.val ≠ 0 := fun h => ha (Fin.ext h)
    rw [ite_eq_right ha0, ite_eq_right (by have := a.isLt; omega), zero_mul]

/-- **The slack of a reversed child's pair** is its parent pair's. -/
theorem slack_rev {k : ℕ} (x : ℝ) {v : (Fin (k + 2) → ℕ) × (Fin 2 → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) : slack x v = slack x (revMerge v) := by
  unfold slack
  congr 2
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun a =>
    expo x (revMerge v) (Sum.inl a)), Fin.sum_univ_two, Fin.sum_univ_one]
  simp only [expo_revMerge x hv1 hv2, Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.succ_ne_zero]
  simp only [expo, revMerge, Sum.elim_inr]
  ring

/-- The order `p ≤ β` of a reversed child: `2 X_{k+2} − X_0 ≤ 0`. -/
def halfCon (k : ℕ) : Con := ⟨⟨0, [-1] ++ List.replicate (k + 1) 0 ++ [2], 0⟩, false⟩

theorem holds_halfCon (k : ℕ) (X : ℕ → ℝ) (H : ℝ) : (halfCon k).Holds X H ↔ 2 * X (k + 2) ≤ X 0 := by
  unfold halfCon Con.Holds LF.val
  simp only [Bool.false_eq_true, ↓reduceIte, dotR_append, dotR_replicate_zero, List.length_replicate, dotR,
    List.length_cons, List.length_nil, List.length_append]
  push_cast
  constructor <;> intro h <;> [skip; skip] <;> ring_nf at h ⊢ <;> linarith

/-- **The reversed child's coordinates**: the node's, the new prime's in `[DEN/25, hi_0)`, with the order `p ≤ β`. -/
theorem Sound.rev_child {k : ℕ} {conds : List (Cond (k + 2) 1)} {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound (std (k + 1) conds) (stdRows (k + 2)) E Γ B) (hlen : B.length = k + 2)
    (hf : fits Γ B.length = true) :
    Sound (revN (k + 1) (revConds (k + 1) conds)) (revRows (k + 1)) E (Γ ++ [halfCon k])
      (B ++ [(NU0, (B.getD 0 (0, 0)).2)]) := by
  intro x hx v hv1 hv2 hc hH
  obtain ⟨hcm, hlvl, hge⟩ := revConds_facts (by linarith) hv1 hv2 hc
  obtain ⟨hw1, hw2⟩ := revMerge_pos hv1 hv2
  have hsl : slack x v = slack x (revMerge v) := slack_rev x hv1 hv2
  obtain ⟨hB, hΓ⟩ := h x hx (revMerge v) hw1 hw2 hcm (hsl ▸ hH)
  have hagree : ∀ j < B.length, coords (stdRows (k + 2)) x (revMerge v) j = coords (revRows (k + 1)) x v j :=
    fun j hj => (coords_rev x hv1 hv2 (by omega)).symm
  have hD := DEN_pos
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  -- the new coordinate and the first
  have eN : coords (revRows (k + 1)) x v (k + 2) = DEN * (Real.log (v.1 0) / Real.log x) := coords_rev_new x v
  have e0 : coords (revRows (k + 1)) x v 0 = DEN * (Real.log (v.1 0) / Real.log x) +
      DEN * (Real.log (v.2 1) / Real.log x) := by
    rw [← hagree 0 (by omega)]
    have h0' : coords (stdRows (k + 2)) x (revMerge v) 0 =
        DEN * (Real.log ((revMerge v).1 0) / Real.log x) := by
      simpa using coords_std x (revMerge v) 0
    rw [h0']
    simp only [revMerge, Fin.cons_zero]
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (hv1 0).ne') (by exact_mod_cast (hv2 1).ne')]
    ring
  have hβ : 0 ≤ Real.log (v.2 1) := Real.log_nonneg (by exact_mod_cast hv2 1)
  have hlog : Real.log (v.1 0) ≤ Real.log (v.2 1) :=
    Real.log_le_log (by exact_mod_cast hv1 0) (by exact_mod_cast hge)
  have h0 := (inBox_getD B _ 0 hB (by omega)).2
  rw [hagree 0 (by omega)] at h0
  refine ⟨inBox_append B _ _ (inBox_congr B hagree hB) ?_ ?_, fun c hc' => ?_⟩
  · -- the level
    rw [hlen, eN, NU0_eq]
    have h2 : Real.log x / 25 ≤ Real.log (v.1 0) := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlvl
      rw [Real.log_rpow hx0] at this
      linarith
    calc (DEN : ℝ) / 25 = DEN * ((Real.log x / 25) / Real.log x) := by field_simp
      _ ≤ DEN * (Real.log (v.1 0) / Real.log x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hlx.le) hD.le
  · rw [hlen, eN]
    calc DEN * (Real.log (v.1 0) / Real.log x) ≤ coords (revRows (k + 1)) x v 0 := by
          rw [e0]
          have : 0 ≤ DEN * (Real.log (v.2 1) / Real.log x) := by positivity
          linarith
      _ < _ := h0
  · rcases List.mem_append.1 hc' with hcΓ | hcΓ'
    · have hlen' : c.L.c.length ≤ B.length := by
        simp only [fits, List.all_eq_true, decide_eq_true_eq] at hf
        exact hf c hcΓ
      rw [hsl]
      exact (c.holds_congr hlen' hagree _).1 (hΓ c hcΓ)
    · simp only [List.mem_singleton] at hcΓ'
      subst hcΓ'
      rw [holds_halfCon, eN, e0]
      have : DEN * (Real.log (v.1 0) / Real.log x) ≤ DEN * (Real.log (v.2 1) / Real.log x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hlx.le) hD.le
      linarith


/-! ### The decision -/

/-- **The role reversal of a standard node.** On a sound standard node with at least two primes whose box passes the
Type I check with the first prime as the cofactor, the reversed Type I term is asymptotic by Li's Lemmas 3.1 and 3.2,
so the node's loss is the reversed child's, for the opposite sign. -/
theorem Sound.OK_of_rev {k : ℕ} {conds : List (Cond (k + 2) 1)} {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound (std (k + 1) conds) (stdRows (k + 2)) E Γ B) (hE : 0 < E) (hinv : StdInv (k + 1) conds)
    (hcond : CondsOK conds) (hlen : k + 2 ≤ B.length) {acts : List LF} (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g)
    (hfa : ∀ g ∈ acts, g.c.length ≤ B.length) {labels : List ℕ} {kind : ℕ}
    (hcheck : typeICheck (stdItems (k + 2)) 0 E B acts labels kind = true) {c ρ σ L : ℝ} (hc : 0 < c)
    (hc1 : c < 1 / 25)
    (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hσ : |σ| ≤ 1) (hLi31 : ShortSieveLi.LiLemma31 (13 / 25) (2 / 25) ρ)
    (hLi32 : ShortSieveLi.LiLemma32 (13 / 25) (2 / 25) ρ)
    (hG : OK (13 / 25) ρ (-σ) (fun x y => ((revN (k + 1) (revConds (k + 1) conds)).count x y : ℝ)) L) :
    OK (13 / 25) ρ σ (fun x y => ((std (k + 1) conds).count x y : ℝ)) L := by
  have hθρ : (13 / 25 : ℝ) ≤ 1 - ρ := by linarith
  obtain ⟨hl, h3, hall⟩ := labels_of_check hcheck
  have hn : (stdItems (k + 2)).length = k + 3 := by simp [stdItems]
  rw [hn] at hl hall
  have hlt3 : ∀ a : Fin (k + 1), labels.getD (a + 1) 0 < 3 := fun a =>
    lt_of_lt_of_le (hall (a + 1) (by omega) (by omega)) (by split_ifs <;> norm_num)
  have hρ3 : labels.getD (k + 2) 0 < 3 :=
    lt_of_lt_of_le (hall (k + 2) (by omega) (by omega)) (by split_ifs <;> norm_num)
  have hlt4 : ∀ t : Fin (k + 2) ⊕ Fin 1, labels.getD (canon t) 0 < 4 := by
    rintro (a | i)
    · induction a using Fin.cases with
      | zero => simp only [canon, Sum.elim_inl, Fin.val_zero, h3]; norm_num
      | succ j => simpa [canon] using (hlt3 j).trans (by norm_num : 3 < 4)
    · have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      simpa [canon] using hρ3.trans (by norm_num : 3 < 4)
  have hrole : decide (kind ≠ 1) = false → ∀ t, revRole labels hlt3 hρ3 t ≠ 2 := by
    intro hkd t
    have hk1 : kind = 1 := by simpa using hkd
    rcases t with a | i
    · have := hall (a + 1) (by omega) (by omega)
      rw [ite_eq_left hk1] at this
      simp only [revRole, Sum.elim_inl, ne_eq, Fin.ext_iff, Fin.val_two]
      omega
    · have := hall (k + 2) (by omega) (by omega)
      rw [ite_eq_left hk1] at this
      simp only [revRole, Sum.elim_inr, ne_eq, Fin.ext_iff, Fin.val_two]
      omega
  -- the parent pair of a pair of the Type I term
  have hpar : ∀ x : ℝ, 1 < x → ∀ w ∈ (revT k conds).terms x, (∀ a, 0 < (revParent w).1 a) ∧
      (∀ i, 0 < (revParent w).2 i) ∧ (∀ C ∈ conds, C.Holds x (revParent w).1 (revParent w).2) ∧
      prodP (revParent w) = prodP w := by
    intro x hx w hw
    obtain ⟨hwp, -, hcw⟩ := mem_filter.1 hw
    obtain ⟨hp, hρ'⟩ := mem_pairs.1 hwp
    have e2 : w.2 = Fin.snoc (fun _ : Fin 1 => w.2 0) (w.2 1) := by
      funext i
      induction i using Fin.lastCases with
      | last => rfl
      | cast j => have hj : j = 0 := Fin.fin_one_eq_zero j; subst hj; rfl
    refine ⟨fun a => ?_, fun i => (hρ' 0).1, fun C hC => ?_, ?_⟩
    · induction a using Fin.cases with
      | zero => exact (hρ' 1).1
      | succ j => exact (hp j).2.pos
    · have h' := hcw _ (List.mem_map_of_mem hC)
      rw [e2, holds_rev] at h'
      exact h'
    · unfold revParent
      rw [prodP_rev]
      conv_rhs => rw [show w = (w.1, w.2) from rfl, e2]
  -- the Type I term
  have hJ : Asym (13 / 25) ρ (fun x y => ((revT k conds).toJ.count x y : ℝ)) := by
    have hreg : ∀ᶠ x in atTop, ∀ w ∈ (revT k conds).terms x, x / 2 < (prodP w : ℝ) → (prodP w : ℝ) ≤ x →
        TypeIReg (13 / 25) (1 / (100 * DEN)) (decide (kind ≠ 1))
            (tExp (revT k conds) (revRole labels hlt3 hρ3) x w) ∧
          tExp (revT k conds) (revRole labels hlt3 hρ3) x w 0 +
              tExp (revT k conds) (revRole labels hlt3 hρ3) x w 1 +
            tExp (revT k conds) (revRole labels hlt3 hρ3) x w 2 ≤ 1 - 1 / (100 * DEN) := by
      filter_upwards [abs_slack_le hE (k + 2) 1, eventually_gt_atTop 1] with x hsl hx1 w hw h1 h2
      obtain ⟨hu1, hu2, hcu, hpu⟩ := hpar x hx1 w hw
      have hH := hsl (revParent w) hu1 hu2 (by rw [hpu]; linarith) (by rw [hpu]; linarith)
      obtain ⟨hB, hΓ⟩ := h x hx1 (revParent w) hu1 hu2 hcu hH
      refine typeIReg_core (fun L hL => (stdItems_length_le _ L hL).trans hlen) hfa hcheck (inBoxC_of_inBox hB) hH
        (fun g hg => ?_) fun i => ?_
      · obtain ⟨c, hc', rfl⟩ := hacts g hg
        exact Con.val_le (hΓ c hc')
      · rw [tExp_rev conds hlt4 h3 hlt3 hρ3]
        exact val_grpLF_eq (itemsOK_std (k + 2)) hl hlt4 ⟨i, by omega⟩ (expo x (revParent w))
    have hbigT : ∀ᶠ x in atTop, ∀ w ∈ (revT k conds).terms x, (∀ a, x ^ c < w.1 a) ∧
        ∀ i : Fin (revT k conds).m, 1 < w.2 i.castSucc := by
      filter_upwards [eventually_gt_atTop 1] with x hx w hw
      obtain ⟨hu1, hu2, hcu, -⟩ := hpar x hx w hw
      obtain ⟨h1, h2⟩ := hinv x hx (revParent w) hu1 hu2 hcu
      have hxc : (1 : ℝ) < x ^ (1 / 25 : ℝ) := Real.one_lt_rpow hx (by norm_num)
      refine ⟨fun a => (Real.rpow_lt_rpow_of_exponent_lt hx hc1).trans_le ?_, fun i => ?_⟩
      · simpa [revParent] using h1 a.succ
      · have hi : i = 0 := Fin.fin_one_eq_zero i
        subst hi
        have := (h1 (Fin.last (k + 1))).trans (Nat.cast_le.2 h2)
        have h' : (1 : ℝ) < (revParent w).2 0 := hxc.trans_le this
        simpa [revParent] using h'
    have hrel := abs_count_sub_le_typeI (revT k conds) (Nat.succ_pos k) hc (by linarith) hρ hρc
      (show (0 : ℝ) < 1 / 25 by norm_num) (show 12 * ρ < (1 / 25 : ℝ) by linarith)
      (show (1 / 25 : ℝ) ≤ 2 * (13 / 25) - 1 by norm_num) (by norm_num) (by norm_num)
      (div_pos one_pos (mul_pos (by norm_num) DEN_pos)) hLi31 hLi32 hcond.revT hbigT
      (revRole labels hlt3 hρ3) (decide (kind ≠ 1)) hrole hreg
    refine asym_of_rel hrel ?_
    -- the comparison interval: the node's count plus the child's
    obtain ⟨CN, hCN0, hCN⟩ := ShortSieveLi.count_B_le (std (k + 1) conds) hc (by linarith) hρ hρc (hinv.big hc1)
    obtain ⟨CG, hCG0, hCG⟩ := ShortSieveLi.count_B_le (revN (k + 1) (revConds (k + 1) conds)) hc (by linarith)
      hρ hρc (hinv.rev.big hc1)
    refine ⟨CN + CG, by positivity, ?_⟩
    filter_upwards [hCN, hCG, eventually_gt_atTop 1] with x h1 h2 hx
    rw [count_rev_std hinv hx]
    push_cast
    have e : (CN + CG) * x ^ (1 - ρ) / Real.log x =
        CN * x ^ (1 - ρ) / Real.log x + CG * x ^ (1 - ρ) / Real.log x := by ring
    rw [e]
    exact add_le_add h1 h2
  refine OK_congr ?_ hθρ (OK_sub hσ hJ hG)
  filter_upwards [eventually_gt_atTop 1] with x hx y _ _
  rw [count_rev_std hinv hx y]
  push_cast
  ring

end ShortSieveCert

#print axioms ShortSieveCert.Sound.OK_of_rev
#print axioms ShortSieveCert.Sound.rev_child
#print axioms ShortSieveCert.StdInv.rev
#print axioms ShortSieveCert.CondsOK.rev
