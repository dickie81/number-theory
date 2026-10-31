import ShortSieveJ
import ShortSieveLi
import ShortSieveBuch

/-!
# Type I terms of the certificate and their asymptotic formula from Li's Lemmas 3.1 and 3.2

A Type I term in standard form (`TNode`) sums over `k` primes `p`, `m` rough items `ρ_i` free of primes below
`p_{s(i)}`, and a cofactor `v` free of primes below `x^ν`, with log-linear conditions on all of them; as a
`ShortSieveBuch.JNode` the cofactor is the last item (`TNode.toJ`). Its rough items are written as tuples of primes
(`ShortSieveExpand.card_expand`, for each value of the cofactor), so that its count is a sum over the patterns of the
pairs of a cut of `ShortSieveJ` (`TNode.count_eq_sum`).
-/

open Finset Real Filter

namespace ShortSieveTypeI

open ShortSieveBoxes ShortSieveTerm ShortSieveExpand ShortSieveNode ShortSieveBuch ShortSieveJ

open Classical

/-- A Type I term in standard form: `k` primes, `m` rough items `ρ_i` free of primes below `p_{s(i)}`, and a cofactor
free of primes below `x^ν`, with log-linear conditions on the primes, the items and (last) the cofactor. -/
structure TNode where
  k : ℕ
  m : ℕ
  s : Fin m → Fin k
  ν : ℝ
  conds : List (Cond k (m + 1))

/-- The Type I term as a `JNode`, the cofactor its last item. -/
@[reducible] noncomputable def TNode.toJ (T : TNode) : JNode :=
  ⟨T.k, T.m + 1, Fin.snoc (fun i => some (T.s i)) none, T.ν, fun _ => 0, T.conds⟩

/-- The level of a constant `x^ν`. -/
theorem lvlOf_zero {k : ℕ} (a x : ℝ) (p : Fin k → ℕ) : lvlOf a (fun _ => 0) x p = ⌈x ^ a⌉₊ := by
  simp [lvlOf]

/-- The siftings of a Type I term in standard form. -/
theorem sifted_toJ_iff (T : TNode) (x : ℝ) (w : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) :
    T.toJ.Sifted x w ↔ (∀ i : Fin T.m, SieveTree.rough (w.1 (T.s i)) (w.2 i.castSucc)) ∧
      SieveTree.rough ⌈x ^ T.ν⌉₊ (w.2 (Fin.last T.m)) := by
  show (∀ i, SieveTree.rough (((Fin.snoc (fun i => some (T.s i)) none : Fin (T.m + 1) → Option (Fin T.k)) i).elim
    (lvlOf T.ν (fun _ => 0) x w.1) w.1) (w.2 i)) ↔ _
  rw [lvlOf_zero]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have := h i.castSucc
      rwa [Fin.snoc_castSucc] at this
    · have := h (Fin.last T.m)
      rwa [Fin.snoc_last] at this
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact h2
    | cast i => rw [Fin.snoc_castSucc]; exact h1 i

/-- The terms of a Type I term: the pairs in `[1, x]` with its siftings and conditions. -/
noncomputable def TNode.terms (T : TNode) (x : ℝ) : Finset ((Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) :=
  (pairs T.k (T.m + 1) ⌊x⌋₊).filter fun w => T.toJ.Sifted x w ∧ ∀ C ∈ T.conds, C.Holds x w.1 w.2

/-! ### The expanded conditions -/

/-- A condition on the expanded pair `(g, v)`: `e` on the primes, `f_i` on every prime of block `i`, `f_m` on `v`. -/
def _root_.ShortSieveNode.Cond.liftJ {k m : ℕ} (C : Cond k (m + 1)) (len : Fin m → ℕ) : JAtom (Idx k m len) :=
  ⟨Sum.elim C.e fun ij => C.f ij.1.castSucc, C.f (Fin.last m), C.b, C.strict⟩

/-- The order of two primes of a block, on the expanded pair. -/
def monoJ {k m : ℕ} (len : Fin m → ℕ) (i : Fin m) (j j' : Fin (len i)) : JAtom (Idx k m len) :=
  ⟨(monoAtom len i j j').e, 0, fun _ => 0, false⟩

/-- A prime of a block at least its sifting prime, on the expanded pair. -/
def siftJ {k m : ℕ} (s : Fin m → Fin k) (len : Fin m → ℕ) (i : Fin m) (j : Fin (len i)) : JAtom (Idx k m len) :=
  ⟨(siftAtom s len i j).e, 0, fun _ => 0, false⟩

/-- The expanded conditions of a Type I term for the pattern `len`. -/
noncomputable def TNode.atoms (T : TNode) (len : Fin T.m → ℕ) : List (JAtom (Idx T.k T.m len)) :=
  T.conds.map (fun C => C.liftJ len) ++
    (((univ : Finset (Σ i : Fin T.m, Fin (len i) × Fin (len i))).filter fun t => t.2.1 < t.2.2).toList.map
      fun t => monoJ len t.1 t.2.1 t.2.2) ++
    ((univ : Finset (Σ i : Fin T.m, Fin (len i))).toList.map fun t => siftJ T.s len t.1 t.2)

theorem liftJ_val {k m : ℕ} (C : Cond k (m + 1)) {len : Fin m → ℕ} {g : Idx k m len → ℕ} (hg : ∀ t, g t ≠ 0)
    (v : ℕ) : (C.liftJ len).val g v = C.val (contract g).1 (Fin.snoc (contract g).2 v) := by
  have h := Cond.lift_val (⟨C.e, fun i => C.f i.castSucc, C.b, C.strict⟩ : Cond k m) hg
  unfold LAtom.val Cond.lift at h
  unfold JAtom.val Cond.liftJ Cond.val
  unfold Cond.val at h
  simp only at h ⊢
  rw [h, Fin.sum_univ_castSucc (n := m)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem holds_liftJ {k m : ℕ} (C : Cond k (m + 1)) {len : Fin m → ℕ} {g : Idx k m len → ℕ} (hg : ∀ t, g t ≠ 0)
    (x : ℝ) (v : ℕ) : (C.liftJ len).Holds x g v ↔ C.Holds x (contract g).1 (Fin.snoc (contract g).2 v) := by
  unfold JAtom.Holds Cond.Holds
  rw [liftJ_val C hg v]
  rfl

theorem holds_monoJ {k m : ℕ} {len : Fin m → ℕ} (i : Fin m) (j j' : Fin (len i)) {g : Idx k m len → ℕ}
    (hg : ∀ t, 0 < g t) (x : ℝ) (v : ℕ) :
    (monoJ len i j j').Holds x g v ↔ g (Sum.inr ⟨i, j⟩) ≤ g (Sum.inr ⟨i, j'⟩) := by
  rw [← holds_mono i j j' hg x]
  unfold JAtom.Holds JAtom.val LAtom.Holds LAtom.val monoJ
  simp only [zero_mul, add_zero, Bool.false_eq_true, ite_false]
  simp [monoAtom]

theorem holds_siftJ {k m : ℕ} (s : Fin m → Fin k) {len : Fin m → ℕ} (i : Fin m) (j : Fin (len i))
    {g : Idx k m len → ℕ} (hg : ∀ t, 0 < g t) (x : ℝ) (v : ℕ) :
    (siftJ s len i j).Holds x g v ↔ g (Sum.inl (s i)) ≤ g (Sum.inr ⟨i, j⟩) := by
  rw [← holds_sift s i j hg x]
  unfold JAtom.Holds JAtom.val LAtom.Holds LAtom.val siftJ
  simp only [zero_mul, add_zero, Bool.false_eq_true, ite_false]
  simp [siftAtom]

/-- **The expanded conditions.** At a pair of positive numbers they hold exactly when the term's conditions hold at
the contracted pair with the cofactor, the blocks are monotone, and every prime of a block is at least its sifting
prime. -/
theorem forall_atoms (T : TNode) {len : Fin T.m → ℕ} {g : Idx T.k T.m len → ℕ} (hg : ∀ t, 0 < g t) (x : ℝ)
    (v : ℕ) :
    (∀ A ∈ T.atoms len, A.Holds x g v) ↔
      (∀ C ∈ T.conds, C.Holds x (contract g).1 (Fin.snoc (contract g).2 v)) ∧
      (∀ i, Monotone (block g i)) ∧ ∀ i j, g (Sum.inl (T.s i)) ≤ block g i j := by
  have hg0 : ∀ t, g t ≠ 0 := fun t => (hg t).ne'
  simp only [TNode.atoms, List.forall_mem_append, List.forall_mem_map, mem_toList, mem_filter, mem_univ, true_and,
    Sigma.forall, Prod.forall, and_assoc, true_implies]
  refine and_congr (forall₂_congr fun C _ => holds_liftJ C hg0 x v) (and_congr ?_ ?_)
  · constructor
    · intro h i j j' hjj'
      rcases lt_or_eq_of_le hjj' with hlt | rfl
      · exact (holds_monoJ i j j' hg x v).1 (h i j j' hlt)
      · exact le_rfl
    · intro h i j j' hlt
      exact (holds_monoJ i j j' hg x v).2 (h i hlt.le)
  · exact forall₂_congr fun i j => holds_siftJ T.s i j hg x v


/-! ### The count as a sum over the patterns -/

/-- The product of a contracted pair with the cofactor. -/
theorem prodP_contract_snoc {k m : ℕ} {len : Fin m → ℕ} (g : Idx k m len → ℕ) (v : ℕ) :
    prodP ((contract g).1, (Fin.snoc (contract g).2 v : Fin (m + 1) → ℕ)) = (∏ t, g t) * v := by
  have h := prodP_contract g
  unfold prodP at h ⊢
  rw [Fin.prod_univ_castSucc (n := m)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [← mul_assoc, h]

/-- A sum over the pairs with one more item is a sum over the last item of sums over the pairs. -/
theorem sum_pairs_succ {k m : ℕ} (Y : ℕ) (F : (Fin k → ℕ) × (Fin (m + 1) → ℕ) → ℝ) :
    ∑ w ∈ pairs k (m + 1) Y, F w = ∑ v ∈ Icc 1 Y, ∑ u ∈ pairs k m Y, F (u.1, Fin.snoc u.2 v) := by
  rw [← sum_product_right (pairs k m Y) (Icc 1 Y) (fun z => F (z.1.1, Fin.snoc z.1.2 z.2))]
  refine sum_nbij' (fun w => ((w.1, Fin.init w.2), w.2 (Fin.last m))) (fun z => (z.1.1, Fin.snoc z.1.2 z.2))
    ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [mem_pairs] at hw
    rw [mem_product, mem_pairs]
    exact ⟨⟨hw.1, fun i => hw.2 i.castSucc⟩, mem_Icc.2 (hw.2 _)⟩
  · intro z hz
    rw [mem_product, mem_pairs] at hz
    rw [mem_pairs]
    refine ⟨hz.1.1, fun i => ?_⟩
    dsimp only
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact mem_Icc.1 hz.2
    | cast i => rw [Fin.snoc_castSucc]; exact hz.1.2 i
  · intro w _
    simp only [Fin.snoc_init_self]
  · intro z _
    simp only [Fin.init_snoc, Fin.snoc_last]
  · intro w _
    simp only [Fin.snoc_init_self]

/-- **The count as a sum over the patterns.** Let `0 < c` and suppose that, for large `x`, the conditions force every
prime above `x^c` and every rough item above `1`. Then for large `x`, the count is the sum over the patterns `len`
with `1 ≤ len_i ≤ ⌊1/c⌋₊` of the counts of the pairs of the cut of the expanded conditions. -/
theorem TNode.count_eq_sum (T : TNode) {c : ℝ} (hc : 0 < c)
    (hbig : ∀ᶠ x in atTop, ∀ w ∈ T.terms x, (∀ a, x ^ c < w.1 a) ∧ ∀ i : Fin T.m, 1 < w.2 i.castSucc) :
    ∀ᶠ x in atTop, ∀ y : ℝ, (T.toJ.count x y : ℝ) =
      ∑ len ∈ Fintype.piFinset (fun _ : Fin T.m => Icc 1 ⌊1 / c⌋₊),
        (#{w ∈ jcut c T.ν (T.atoms len) x | x - y < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} : ℝ) := by
  filter_upwards [hbig, eventually_ge_atTop (2 : ℝ)] with x hbx hx2 y
  have hx0 : 0 < x := by linarith
  set R := ⌊1 / c⌋₊ with hR
  set Y := ⌊x⌋₊ with hY
  -- the condition at a pair with the cofactor
  set P : ℕ → (Fin T.k → ℕ) → (Fin T.m → ℕ) → Prop := fun v p ρ =>
    SieveTree.rough ⌈x ^ T.ν⌉₊ v ∧ (∀ C ∈ T.conds, C.Holds x p (Fin.snoc ρ v)) ∧
      x - y < (prodP (p, (Fin.snoc ρ v : Fin (T.m + 1) → ℕ)) : ℝ) ∧
      (prodP (p, (Fin.snoc ρ v : Fin (T.m + 1) → ℕ)) : ℝ) ≤ x with hP
  -- a pair with the cofactor, sifted and satisfying `P`, is a term
  have hterm : ∀ v ∈ Icc 1 Y, ∀ u ∈ pairs T.k T.m Y, (∀ i, SieveTree.rough (u.1 (T.s i)) (u.2 i)) →
      P v u.1 u.2 → ((u.1, Fin.snoc u.2 v) : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) ∈ T.terms x := by
    intro v hv u hu hr hPv
    obtain ⟨hp, hρ⟩ := mem_pairs.1 hu
    refine mem_filter.2 ⟨mem_pairs.2 ⟨hp, fun i => ?_⟩, (sifted_toJ_iff T x _).2 ⟨fun i => ?_, ?_⟩, hPv.2.1⟩
    · dsimp only
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact mem_Icc.1 hv
      | cast i => rw [Fin.snoc_castSucc]; exact hρ i
    · simp only [Fin.snoc_castSucc]; exact hr i
    · simp only [Fin.snoc_last]; exact hPv.1
  -- the rough items have at most `R` prime factors
  have hRb : ∀ v ∈ Icc 1 Y, ∀ u ∈ pairs T.k T.m Y, (∀ i, SieveTree.rough (u.1 (T.s i)) (u.2 i)) →
      P v u.1 u.2 → ∀ i, (u.2 i).primeFactorsList.length ≤ R := by
    intro v hv u hu hr hPv i
    obtain ⟨hpbig, hρ1⟩ := hbx _ (hterm v hv u hu hr hPv)
    have hρ1' : 1 < u.2 i := by have := hρ1 i; simpa only [Fin.snoc_castSucc] using this
    have hρ0 : u.2 i ≠ 0 := by omega
    have hfac : ∀ q ∈ (u.2 i).primeFactorsList, x ^ c ≤ (q : ℝ) := fun q hq => by
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqd := Nat.dvd_of_mem_primeFactorsList hq
      have hge : u.1 (T.s i) ≤ q := by
        by_contra hlt
        exact hr i q (not_le.1 hlt) hqp hqd
      exact le_trans (hpbig _).le (by exact_mod_cast hge)
    have hρx : (u.2 i : ℝ) ≤ x := by
      have hle : u.2 i ≤ prodP (u.1, (Fin.snoc u.2 v : Fin (T.m + 1) → ℕ)) := by
        unfold prodP
        have hp0 : 0 < ∏ a, u.1 a := prod_pos fun a _ => (mem_pairs.1 hu).1 a |>.2.pos
        have hρpos : ∀ i', 0 < (Fin.snoc u.2 v : Fin (T.m + 1) → ℕ) i' := by
          intro i'
          induction i' using Fin.lastCases with
          | last => rw [Fin.snoc_last]; exact (mem_Icc.1 hv).1
          | cast i' => rw [Fin.snoc_castSucc]; exact ((mem_pairs.1 hu).2 i').1
        have h1 : u.2 i ≤ ∏ i', (Fin.snoc u.2 v : Fin (T.m + 1) → ℕ) i' := by
          have := Nat.le_of_dvd (prod_pos fun i' _ => hρpos i')
            (dvd_prod_of_mem (fun i' => (Fin.snoc u.2 v : Fin (T.m + 1) → ℕ) i') (mem_univ i.castSucc))
          simpa only [Fin.snoc_castSucc] using this
        exact le_trans h1 (Nat.le_mul_of_pos_left _ hp0)
      exact le_trans (by exact_mod_cast hle) hPv.2.2.2
    have := ShortSieveJ.length_primeFactorsList_le (by linarith : (1 : ℝ) < x) hc hρ0 hρx hfac
    exact Nat.le_floor this
  -- the count over the cofactor and the pairs
  have hA : (T.toJ.count x y : ℝ) = ∑ v ∈ Icc 1 Y,
      (#{u ∈ pairs T.k T.m Y | (∀ i, SieveTree.rough (u.1 (T.s i)) (u.2 i)) ∧ P v u.1 u.2} : ℝ) := by
    rw [JNode.count, natCast_card_filter, sum_pairs_succ]
    refine sum_congr rfl fun v hv => ?_
    rw [natCast_card_filter]
    refine sum_congr rfl fun u hu => ?_
    have hiff : (T.toJ.Sifted x ((u.1, Fin.snoc u.2 v) : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) ∧
        (∀ C ∈ T.toJ.conds, C.Holds x u.1 (Fin.snoc u.2 v)) ∧
        x - y < (prodP ((u.1, Fin.snoc u.2 v) : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) : ℝ) ∧
        (prodP ((u.1, Fin.snoc u.2 v) : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) : ℝ) ≤ x) ↔
        ((∀ i, SieveTree.rough (u.1 (T.s i)) (u.2 i)) ∧ P v u.1 u.2) := by
      rw [sifted_toJ_iff]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hP]
      tauto
    simp only [hiff]
  -- each cofactor: the expansion
  have hB : ∀ v ∈ Icc 1 Y,
      (#{u ∈ pairs T.k T.m Y | (∀ i, SieveTree.rough (u.1 (T.s i)) (u.2 i)) ∧ P v u.1 u.2} : ℝ) =
        ∑ len ∈ Fintype.piFinset (fun _ : Fin T.m => range (R + 1)),
          (#{g ∈ tuplesOf T.k T.m Y len | (∀ i, Monotone (block g i)) ∧ (∀ i, ∏ j, block g i j ≤ Y) ∧
            (∀ i j, g (Sum.inl (T.s i)) ≤ block g i j) ∧ P v (contract g).1 (contract g).2} : ℝ) := by
    intro v hv
    have h := card_expand T.s Y R (P v) (fun u hu hr hPv => hRb v hv u hu hr hPv)
    rw [← Nat.cast_sum]
    convert congrArg (Nat.cast : ℕ → ℝ) h using 2
    · congr 1; ext u; simp only [mem_filter]
    · refine sum_congr rfl fun len _ => ?_
      congr 1; ext g; simp only [mem_filter]
  -- the cofactor and the expanded tuple together
  have hC : ∀ len : Fin T.m → ℕ, ∑ v ∈ Icc 1 Y,
      (#{g ∈ tuplesOf T.k T.m Y len | (∀ i, Monotone (block g i)) ∧ (∀ i, ∏ j, block g i j ≤ Y) ∧
        (∀ i j, g (Sum.inl (T.s i)) ≤ block g i j) ∧ P v (contract g).1 (contract g).2} : ℝ) =
      (#{w ∈ tuplesOf T.k T.m Y len ×ˢ Icc 1 Y | (∀ i, Monotone (block w.1 i)) ∧
        (∀ i, ∏ j, block w.1 i j ≤ Y) ∧ (∀ i j, w.1 (Sum.inl (T.s i)) ≤ block w.1 i j) ∧
          P w.2 (contract w.1).1 (contract w.1).2} : ℝ) := by
    intro len
    rw [natCast_card_filter, sum_product_right]
    refine sum_congr rfl fun v _ => ?_
    rw [natCast_card_filter]
  -- a pair of the expanded set: its contracted pair with the cofactor is a term
  have hterm' : ∀ (len : Fin T.m → ℕ) (w : (Idx T.k T.m len → ℕ) × ℕ), w.1 ∈ tuplesOf T.k T.m Y len →
      w.2 ∈ Icc 1 Y → (∀ i, ∏ j, block w.1 i j ≤ Y) → (∀ i j, w.1 (Sum.inl (T.s i)) ≤ block w.1 i j) →
      P w.2 (contract w.1).1 (contract w.1).2 →
      (((contract w.1).1, Fin.snoc (contract w.1).2 w.2) : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) ∈ T.terms x := by
    intro len w hgT hv hY' hsift hPw
    have hgp : ∀ t, (w.1 t).Prime ∧ w.1 t ≤ Y := fun t => by
      have := SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hgT t)
      exact ⟨this.2, this.1⟩
    have hpos : ∀ i, 1 ≤ (contract w.1).2 i := fun i => by
      show 0 < ∏ j, block w.1 i j
      exact prod_pos fun j _ => (hgp _).1.pos
    refine hterm w.2 hv (contract w.1) (mem_pairs.2 ⟨fun a => ⟨(hgp _).2, (hgp _).1⟩,
      fun i => ⟨hpos i, hY' i⟩⟩) (fun i => ?_) hPw
    intro q hq hqp hqd
    simp only [contract] at hq hqd
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
    have := (Nat.prime_dvd_prime_iff_eq hqp (hgp _).1).1 hj
    have := hsift i j
    simp only [block] at this
    omega
  have hsub : (Fintype.piFinset fun _ : Fin T.m => Icc 1 R) ⊆ Fintype.piFinset fun _ : Fin T.m => range (R + 1) :=
    fun len hlen => Fintype.mem_piFinset.2 fun i => by
      have := mem_Icc.1 (Fintype.mem_piFinset.1 hlen i)
      exact mem_range.2 (by omega)
  rw [hA, sum_congr rfl hB, sum_comm, sum_congr rfl fun len _ => hC len]
  symm
  calc ∑ len ∈ Fintype.piFinset (fun _ : Fin T.m => Icc 1 R),
        (#{w ∈ jcut c T.ν (T.atoms len) x | x - y < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} : ℝ)
      = ∑ len ∈ Fintype.piFinset (fun _ : Fin T.m => Icc 1 R),
        (#{w ∈ tuplesOf T.k T.m Y len ×ˢ Icc 1 Y | (∀ i, Monotone (block w.1 i)) ∧
          (∀ i, ∏ j, block w.1 i j ≤ Y) ∧ (∀ i j, w.1 (Sum.inl (T.s i)) ≤ block w.1 i j) ∧
            P w.2 (contract w.1).1 (contract w.1).2} : ℝ) := by
        refine sum_congr rfl fun len hlen => ?_
        congr 2
        ext w
        simp only [jcut, mem_filter, mem_product]
        constructor
        · rintro ⟨⟨⟨hgQ, hv⟩, hrv, hat⟩, hp1, hp2⟩
          have hgq : ∀ t, (w.1 t).Prime ∧ ⌊x ^ c⌋₊ < w.1 t ∧ w.1 t < ⌈x ^ (2 : ℝ)⌉₊ := fun t => by
            obtain ⟨h1, h2⟩ := mem_filter.1 (Fintype.mem_piFinset.1 hgQ t)
            exact ⟨h2, (mem_Ioo.1 h1).1, (mem_Ioo.1 h1).2⟩
          have hgpos : ∀ t, 0 < w.1 t := fun t => (hgq t).1.pos
          have hv1 : 1 ≤ w.2 := (mem_Icc.1 hv).1
          obtain ⟨hC', hmono, hsift⟩ := (forall_atoms T hgpos x w.2).1 hat
          have hprodle : ((∏ t, w.1 t : ℕ) : ℝ) ≤ x := by
            refine le_trans ?_ hp2
            exact_mod_cast Nat.le_mul_of_pos_right _ (by omega)
          have hle : ∀ t, (w.1 t : ℝ) ≤ x := fun t =>
            le_trans (by exact_mod_cast Nat.le_of_dvd (prod_pos fun t _ => hgpos t) (dvd_prod_of_mem _ (mem_univ t)))
              hprodle
          refine ⟨⟨Fintype.mem_piFinset.2 fun t => SieveTypeIIU.mem_primesLe.2 ⟨Nat.le_floor (hle t), (hgq t).1⟩,
            hv⟩, hmono, fun i => Nat.le_floor ?_, hsift, hrv, hC', ?_, ?_⟩
          · have h1 : ∏ j, block w.1 i j ≤ ∏ t, w.1 t := by
              rw [← prodP_contract w.1]
              refine Nat.le_of_dvd ?_ ?_
              · rw [prodP_contract]; exact prod_pos fun t _ => hgpos t
              · exact dvd_trans (dvd_prod_of_mem (fun i' => ∏ j, block w.1 i' j) (mem_univ i)) (Dvd.intro_left _ rfl)
            exact le_trans (by exact_mod_cast h1) hprodle
          · rw [prodP_contract_snoc]; exact hp1
          · rw [prodP_contract_snoc]; exact hp2
        · rintro ⟨⟨hgT, hv⟩, hmono, hY', hsift, hPw⟩
          have hct := hterm' len w hgT hv hY' hsift hPw
          have hgp : ∀ t, (w.1 t).Prime ∧ w.1 t ≤ Y := fun t => by
            have := SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hgT t)
            exact ⟨this.2, this.1⟩
          have hgpos : ∀ t, 0 < w.1 t := fun t => (hgp t).1.pos
          obtain ⟨hpbig, -⟩ := hbx _ hct
          obtain ⟨hrv, hC', hp1, hp2⟩ := hPw
          rw [prodP_contract_snoc] at hp1 hp2
          refine ⟨⟨⟨Fintype.mem_piFinset.2 fun t => mem_filter.2 ⟨mem_Ioo.2 ⟨?_, ?_⟩, (hgp t).1⟩, hv⟩, hrv,
            (forall_atoms T hgpos x w.2).2 ⟨hC', hmono, hsift⟩⟩, hp1, hp2⟩
          · rcases t with a | ⟨i, j⟩
            · exact Nat.floor_lt' (by have := (hgp (Sum.inl a)).1.pos; omega) |>.2 (hpbig a)
            · have h1 := hpbig (T.s i)
              have h2 : (w.1 (Sum.inl (T.s i)) : ℝ) ≤ w.1 (Sum.inr ⟨i, j⟩) := by exact_mod_cast hsift i j
              exact Nat.floor_lt' (by have := (hgp (Sum.inr ⟨i, j⟩)).1.pos; omega) |>.2 (lt_of_lt_of_le h1 h2)
          · have h1 : (w.1 t : ℝ) ≤ x := le_trans (by exact_mod_cast (hgp t).2) (Nat.floor_le (by linarith))
            have h2 : x < x ^ (2 : ℝ) := by
              rw [Real.rpow_two, sq]; exact lt_mul_of_one_lt_right hx0 (by linarith)
            exact Nat.lt_ceil.2 (lt_of_le_of_lt h1 h2)
    _ = ∑ len ∈ Fintype.piFinset (fun _ : Fin T.m => range (R + 1)),
        (#{w ∈ tuplesOf T.k T.m Y len ×ˢ Icc 1 Y | (∀ i, Monotone (block w.1 i)) ∧
          (∀ i, ∏ j, block w.1 i j ≤ Y) ∧ (∀ i j, w.1 (Sum.inl (T.s i)) ≤ block w.1 i j) ∧
            P w.2 (contract w.1).1 (contract w.1).2} : ℝ) := by
        refine sum_subset hsub fun len hlen hnot => ?_
        -- some block is empty: its product `1` is not a rough item of a term
        have hex : ∃ i, len i = 0 := by
          by_contra hall
          push Not at hall
          refine hnot (Fintype.mem_piFinset.2 fun i => mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (hall i), ?_⟩)
          have := mem_range.1 (Fintype.mem_piFinset.1 hlen i)
          omega
        obtain ⟨i, hi⟩ := hex
        rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
        rintro w hw ⟨hmono, hY', hsift, hPw⟩
        obtain ⟨hgT, hv⟩ := mem_product.1 hw
        have hct := hterm' len w hgT hv hY' hsift hPw
        have h1 := (hbx _ hct).2 i
        have h2 : (contract w.1).2 i = 1 := by
          simp only [contract]
          have : IsEmpty (Fin (len i)) := by rw [hi]; exact Fin.isEmpty'
          exact Finset.prod_of_isEmpty _
        simp only [Fin.snoc_castSucc] at h1
        omega


/-! ### The asymptotic formula from Li's Lemmas 3.1 and 3.2 -/

/-- Li's level is at least `2θ − 1` on `[0, 1/2]` (`ν(α) ≥ 2θ − 1`, below his (5)). -/
theorem le_liNu {θ γ α : ℝ} (hθ : 1 / 2 < θ) (hγ : 2 * θ - 1 ≤ γ) (hα : α ≤ 1 / 2) :
    2 * θ - 1 ≤ ShortSieveLi.liNu θ γ α := by
  unfold ShortSieveLi.liNu
  refine le_min ?_ hγ
  have hθ' : 0 < 2 * θ - 1 := by linarith
  set t := (1 / 2 - α) / (2 * θ - 1) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hθ'.le
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  set h : ℝ := (⌊t⌋₊ : ℝ) + 1 with hh
  have hh1 : 1 ≤ h := by have : (0 : ℝ) ≤ ⌊t⌋₊ := Nat.cast_nonneg _; linarith
  have hkey : (h - 1) * (2 * θ - 1) ≤ 1 / 2 - α := by
    have : h - 1 ≤ t := by rw [hh]; linarith
    calc (h - 1) * (2 * θ - 1) ≤ t * (2 * θ - 1) := mul_le_mul_of_nonneg_right this hθ'.le
      _ = 1 / 2 - α := by rw [ht]; field_simp
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The group exponents of a Type I term's fixed items: `Σ_{items with role i} log/log x`. -/
noncomputable def tExp (T : TNode) (role : Fin T.k ⊕ Fin T.m → Fin 3) (x : ℝ)
    (w : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) (i : Fin 3) : ℝ :=
  grpExp role i (expo x (w.1, fun j => w.2 j.castSucc))

/-- Li's Type I regions (`α*` replaced by `1/2`) at group exponents `α`: his `D′₀` (Lemma 3.1, no group `2`) when
`kind = false`, his `D′₁ ∪ D′₂` (Lemma 3.2) when `kind = true`, with margin `η`. -/
def TypeIReg (θ η : ℝ) (kind : Bool) (α : Fin 3 → ℝ) : Prop :=
  α 0 ≤ 1 / 2 ∧
    if kind then
      (α 2 ≤ (3 * θ - 1) / 4 - η ∧ 2 * α 1 + α 2 ≤ θ - η ∧ 2 * α 1 + 3 * α 2 ≤ (1 + θ) / 2 - η) ∨
        (α 1 ≤ (1 - θ) / 2 ∧ α 2 ≤ (3 * θ - 1) / 8 - η)
    else α 1 ≤ min ((3 * θ - 1) / 2) ((1 + θ) / 5) - η


/-- **A pair of the cut is a term.** A pair of the cut of the expanded conditions with product at most `x`
contracts, with its cofactor, to a term. -/
theorem contract_mem_terms (T : TNode) {c x : ℝ} {len : Fin T.m → ℕ}
    {w : (Idx T.k T.m len → ℕ) × ℕ} (hw : w ∈ jcut c T.ν (T.atoms len) x) (hP : (jprod w : ℝ) ≤ x) :
    (((contract w.1).1, Fin.snoc (contract w.1).2 w.2) : (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) ∈ T.terms x := by
  obtain ⟨hwp, hrv, hat⟩ := mem_filter.1 hw
  obtain ⟨hgQ, hv⟩ := mem_product.1 hwp
  have hgp : ∀ t, (w.1 t).Prime := fun t => (mem_filter.1 (Fintype.mem_piFinset.1 hgQ t)).2
  have hgpos : ∀ t, 0 < w.1 t := fun t => (hgp t).pos
  obtain ⟨hC, -, hsift⟩ := (forall_atoms T hgpos x w.2).1 hat
  have hv1 : 1 ≤ w.2 := (mem_Icc.1 hv).1
  have hprodle : ((∏ t, w.1 t : ℕ) : ℝ) ≤ x :=
    le_trans (by exact_mod_cast Nat.le_mul_of_pos_right _ (by omega)) hP
  have hle : ∀ n : ℕ, n ∣ ∏ t, w.1 t → n ≤ ⌊x⌋₊ := fun n hn =>
    Nat.le_floor (le_trans (by exact_mod_cast Nat.le_of_dvd (prod_pos fun t _ => hgpos t) hn) hprodle)
  refine mem_filter.2 ⟨mem_pairs.2 ⟨fun a => ⟨hle _ (dvd_prod_of_mem _ (mem_univ _)), hgp _⟩, fun i => ?_⟩,
    (sifted_toJ_iff T x _).2 ⟨fun i => ?_, ?_⟩, hC⟩
  · dsimp only
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact mem_Icc.1 hv
    | cast i =>
      rw [Fin.snoc_castSucc]
      refine ⟨show 0 < ∏ j, block w.1 i j from prod_pos fun j _ => hgpos _, hle _ ?_⟩
      rw [← prodP_contract w.1]
      exact dvd_trans (dvd_prod_of_mem (fun i' => ∏ j, block w.1 i' j) (mem_univ i)) (Dvd.intro_left _ rfl)
  · simp only [Fin.snoc_castSucc]
    intro q hq hqp hqd
    simp only [contract] at hq hqd
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
    have := (Nat.prime_dvd_prime_iff_eq hqp (hgp _)).1 hj
    have := hsift i j
    simp only [block] at this
    omega
  · simp only [Fin.snoc_last]; exact hrv

/-- Every expanded condition has a coordinate whose coefficient differs from the cofactor's. -/
theorem atoms_ne (T : TNode) {len : Fin T.m → ℕ} (hlen : ∀ i, 0 < len i)
    (hcond : ∀ C ∈ T.conds, ∃ u w : Fin T.k ⊕ Fin (T.m + 1), Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w) :
    ∀ A ∈ T.atoms len, ∃ t, A.e t ≠ A.f := by
  intro A hA
  simp only [TNode.atoms, List.mem_append, List.mem_map, mem_toList, mem_filter, mem_univ, true_and] at hA
  rcases hA with (⟨C, hC, rfl⟩ | ⟨⟨i, j, j'⟩, hjj', rfl⟩) | ⟨⟨i, j⟩, rfl⟩
  · -- a lifted condition: otherwise every coefficient would be the cofactor's
    by_contra hall
    push Not at hall
    obtain ⟨u, w, huw⟩ := hcond C hC
    have hcoef : ∀ it : Fin T.k ⊕ Fin (T.m + 1), Sum.elim C.e C.f it = C.f (Fin.last T.m) := by
      intro it
      rcases it with a | i
      · exact hall (Sum.inl a)
      · induction i using Fin.lastCases with
        | last => rfl
        | cast i => exact hall (Sum.inr ⟨i, ⟨0, hlen i⟩⟩)
    exact huw (by rw [hcoef u, hcoef w])
  · refine ⟨Sum.inr ⟨i, j⟩, ?_⟩
    have hne : (Sum.inr ⟨i, j⟩ : Idx T.k T.m len) ≠ Sum.inr ⟨i, j'⟩ := by
      intro h
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact absurd h (ne_of_lt hjj')
    simp [monoJ, monoAtom, hne]
  · refine ⟨Sum.inr ⟨i, j⟩, ?_⟩
    simp [siftJ, siftAtom]


/-- The groups' exponents add up to the items' exponents. -/
theorem sum_grpExp {k m : ℕ} (role : Fin k ⊕ Fin m → Fin 3) (α : Fin k ⊕ Fin m → ℝ) :
    ∑ i, grpExp role i α = ∑ t, α t := by
  unfold grpExp
  exact Finset.sum_fiberwise_of_maps_to (g := role) (fun t _ => mem_univ _) α

/-- The items' exponents add up to `log ∏/log x`. -/
theorem sum_expo {k m : ℕ} (x : ℝ) {v : (Fin k → ℕ) × (Fin m → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) :
    ∑ t, expo x v t = Real.log (prodP v) / Real.log x := by
  unfold expo prodP
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← sum_div, ← sum_div, ← add_div, Nat.cast_mul, Real.log_mul, Nat.cast_prod, Nat.cast_prod,
    Real.log_prod (fun a _ => by exact_mod_cast (hv1 a).ne'), Real.log_prod (fun i _ => by exact_mod_cast (hv2 i).ne')]
  · exact_mod_cast (prod_pos fun a _ => hv1 a).ne'
  · exact_mod_cast (prod_pos fun i _ => hv2 i).ne'

/-- **The asymptotic formula for a Type I term from Li's Lemmas 3.1 and 3.2.** Let `T` have `k ≥ 1` primes, conditions
whose coefficients are not all equal, its terms' primes above `x^c` and rough items above `1` for large `x`, and the
level `x^ν`, `12ρ < ν ≤ 2θ − 1`. If for large `x` every term with product in `(x/2, x]` has its fixed items grouped by
`role` into Li's region (`D′₀` of Lemma 3.1, or `D′₁ ∪ D′₂` of Lemma 3.2) with margin `η`, and the fixed items'
exponents add up to at most `1 − η`, then there is `C` such that for `ε ∈ (0, 1]`, large `x` and
`x^θ ≤ y ≤ x^{1−ρ}`, its terms in `(x − y, x]` number `(y/x^{1−ρ})` times those in `(x − x^{1−ρ}, x]`, up to `ε`
relatively and `C y/log² x`.

Each pattern of the expansion is a cut of `ShortSieveJ.abs_card_jcut_sub_le`; on a box that holds a pair of the cut
the groups' exponents are at most the term's, and Li's regions are bounded above, so the lemma applies to the box,
at the level `x^ν` with `ν ≤ 2θ − 1 ≤ ν(α₁)` (`le_liNu`). -/
theorem abs_count_sub_le_typeI (T : TNode) (hk : 0 < T.k) {c θ γ ρ η : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hν : 0 < T.ν) (hρν : 12 * ρ < T.ν) (hνθ : T.ν ≤ 2 * θ - 1)
    (hθ : 1 / 2 < θ) (hγ : 2 * θ - 1 ≤ γ) (hη : 0 < η)
    (hLi31 : ShortSieveLi.LiLemma31 θ γ ρ) (hLi32 : ShortSieveLi.LiLemma32 θ γ ρ)
    (hcond : ∀ C ∈ T.conds, ∃ u w : Fin T.k ⊕ Fin (T.m + 1), Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w)
    (hbig : ∀ᶠ x in atTop, ∀ w ∈ T.terms x, (∀ a, x ^ c < w.1 a) ∧ ∀ i : Fin T.m, 1 < w.2 i.castSucc)
    (role : Fin T.k ⊕ Fin T.m → Fin 3) (kind : Bool) (hrole : kind = false → ∀ t, role t ≠ 2)
    (hreg : ∀ᶠ x in atTop, ∀ w ∈ T.terms x, x / 2 < (prodP w : ℝ) → (prodP w : ℝ) ≤ x →
      TypeIReg θ η kind (tExp T role x w) ∧ tExp T role x w 0 + tExp T role x w 1 + tExp T role x w 2 ≤ 1 - η) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(T.toJ.count x y : ℝ) - y / x ^ (1 - ρ) * T.toJ.count x (x ^ (1 - ρ))| ≤
        ε * (y / x ^ (1 - ρ)) * T.toJ.count x (x ^ (1 - ρ)) + C * y / Real.log x ^ 2 := by
  set P := Fintype.piFinset fun _ : Fin T.m => Icc 1 ⌊1 / c⌋₊ with hP
  have hpat : ∀ len ∈ P, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y →
      y ≤ x ^ (1 - ρ) →
      |(#{w ∈ jcut c T.ν (T.atoms len) x | x - y < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) *
          #{w ∈ jcut c T.ν (T.atoms len) x | x - x ^ (1 - ρ) < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x}| ≤
        ε * (y / x ^ (1 - ρ)) *
          #{w ∈ jcut c T.ν (T.atoms len) x | x - x ^ (1 - ρ) < (jprod w : ℝ) ∧ (jprod w : ℝ) ≤ x} +
          C * y / Real.log x ^ 2 := by
    intro len hlen
    have hlen1 : ∀ i, 0 < len i := fun i => (mem_Icc.1 (Fintype.mem_piFinset.1 hlen i)).1
    have hd : 0 < Fintype.card (Idx T.k T.m len) := Fintype.card_pos_iff.2 ⟨Sum.inl ⟨0, hk⟩⟩
    -- the entries of a pair of the cut are positive
    have hposJ : ∀ x : ℝ, ∀ w ∈ jcut c T.ν (T.atoms len) x, (∀ a, 0 < (contract w.1).1 a) ∧
        ∀ i, 0 < (contract w.1).2 i := by
      intro x w hw
      have hgp : ∀ t, (w.1 t).Prime :=
        fun t => (mem_filter.1 (Fintype.mem_piFinset.1 (mem_product.1 (mem_filter.1 hw).1).1 t)).2
      exact ⟨fun a => (hgp _).pos, fun i => show 0 < ∏ j, block w.1 i j from prod_pos fun j _ => (hgp _).pos⟩
    -- the region at the term of a pair of the cut with product in `(x/2, x]`
    have hregJ : ∀ᶠ x in atTop, ∀ w ∈ jcut c T.ν (T.atoms len) x, x / 2 < (jprod w : ℝ) → (jprod w : ℝ) ≤ x →
        TypeIReg θ η kind (fun i => grpExp role i (expo x (contract w.1))) ∧
          ∑ i, grpExp role i (expo x (contract w.1)) ≤ 1 - η := by
      filter_upwards [hreg] with x hx
      intro w hw h1 h2
      have ht := contract_mem_terms T hw h2
      have hP' : (prodP (((contract w.1).1, Fin.snoc (contract w.1).2 w.2) :
          (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) : ℝ) = jprod w := by
        rw [prodP_contract_snoc]; rfl
      obtain ⟨hR, hS⟩ := hx _ ht (by rw [hP']; exact h1) (by rw [hP']; exact h2)
      have he : ∀ i, tExp T role x (((contract w.1).1, Fin.snoc (contract w.1).2 w.2) :
          (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) i = grpExp role i (expo x (contract w.1)) := fun i => by
        simp only [tExp, Fin.snoc_castSucc]
      rw [show tExp T role x (((contract w.1).1, Fin.snoc (contract w.1).2 w.2) :
          (Fin T.k → ℕ) × (Fin (T.m + 1) → ℕ)) = fun i => grpExp role i (expo x (contract w.1)) from funext he]
        at hR hS
      refine ⟨hR, ?_⟩
      rw [Fin.sum_univ_three]
      exact hS
    refine abs_card_jcut_sub_le (Sum.inl ⟨0, hk⟩) hc hc1 hν hρ hρc hρν hη (T.atoms len)
      (atoms_ne T hlen1 hcond) ?_ ?_
    · -- the cut's `g` is at most `x^{1−η}`
      filter_upwards [hregJ, eventually_gt_atTop (1 : ℝ)] with x hx hx1
      intro w hw h1 h2
      obtain ⟨-, hsum⟩ := hx w hw h1 h2
      obtain ⟨hp1, hp2⟩ := hposJ x w hw
      have hx0 : 0 < x := by linarith
      have hlx : 0 < Real.log x := Real.log_pos hx1
      rw [sum_grpExp, sum_expo x hp1 hp2, prodP_contract, div_le_iff₀ hlx] at hsum
      have hpos : (0 : ℝ) < ((∏ j, w.1 j : ℕ) : ℝ) := by
        have : 0 < ∏ j, w.1 j := prod_pos fun t _ =>
          (mem_filter.1 (Fintype.mem_piFinset.1 (mem_product.1 (mem_filter.1 hw).1).1 t)).2.pos
        exact_mod_cast this
      rw [← Real.exp_log hpos, ← Real.exp_log (Real.rpow_pos_of_pos hx0 (1 - η)), Real.log_rpow hx0]
      exact Real.exp_le_exp.2 (by linarith)
    · -- Li's lemma on the boxes
      intro ε hε
      have h31 := hLi31 (Idx T.k T.m len) (ShortSieveLi.liftGrp len role) (c / 2) η ε (by positivity) hη hε
      have h32 := hLi32 (Idx T.k T.m len) (ShortSieveLi.liftGrp len role) (c / 2) η ε (by positivity) hη hε
      filter_upwards [h31, h32, hregJ, eventually_gt_atTop (1 : ℝ)] with x h31x h32x hx hx1
      intro y hy1 hy2 N M hN hNM hMN ⟨w₀, hw₀, h1, h2, hw₀box⟩
      obtain ⟨hR, -⟩ := hx w₀ hw₀ h1 h2
      obtain ⟨hp1, hp2⟩ := hposJ x w₀ hw₀
      have hlx : 0 < Real.log x := Real.log_pos hx1
      have hN1 : ∀ j, 1 ≤ N j := fun j => by
        have : (1 : ℝ) ≤ N j := le_trans (Real.one_le_rpow hx1.le (by positivity)) (hN j)
        exact_mod_cast this
      -- each group's exponent over the box's lower corners is between `0` and the term's
      have hgrp : ∀ i : Fin 3, 0 ≤ Real.log (ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) i N) / Real.log x ∧
          Real.log (ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) i N) / Real.log x ≤
            grpExp role i (expo x (contract w₀.1)) := by
        intro i
        obtain ⟨hb1, -, -⟩ := ShortSieveLi.grpProd_le_prod_le (ShortSieveLi.liftGrp len role) i
          (fun j => (ShortSieveLi.mem_tuples.1 hw₀box j).1.le) (fun j => (ShortSieveLi.mem_tuples.1 hw₀box j).2.1)
          hMN hd
        have hpg := prod_group role w₀.1 i
        have hlog := ShortSieveLi.log_grp_prod role hx1 hp1 hp2 i
        have hge1 : (1 : ℝ) ≤ ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) i N := by
          exact_mod_cast ShortSieveLi.one_le_grpProd _ i hN1
        refine ⟨div_nonneg (Real.log_nonneg hge1) hlx.le, ?_⟩
        rw [div_le_iff₀ hlx]
        have h3 : Real.log (ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) i N) ≤
            Real.log (∏ t ∈ univ.filter (ShortSieveLi.liftGrp len role · = i), (w₀.1 t : ℝ)) :=
          Real.log_le_log (by linarith) hb1
        have h4 : Real.log (∏ t ∈ univ.filter (ShortSieveLi.liftGrp len role · = i), (w₀.1 t : ℝ)) =
            Real.log x * grpExp role i (expo x (contract w₀.1)) := by
          rw [← hlog, ← hpg]
          rfl
        linarith
      have hratio : ∀ i, ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) i M ≤
          2 * ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) i N := fun i => by
        obtain ⟨-, -, hb3⟩ := ShortSieveLi.grpProd_le_prod_le (ShortSieveLi.liftGrp len role) i
          (fun j => (ShortSieveLi.mem_tuples.1 hw₀box j).1.le) (fun j => (ShortSieveLi.mem_tuples.1 hw₀box j).2.1)
          hMN hd
        exact_mod_cast hb3
      obtain ⟨h0a, h0b⟩ := hgrp 0
      obtain ⟨h1a, h1b⟩ := hgrp 1
      obtain ⟨h2a, h2b⟩ := hgrp 2
      obtain ⟨hR0, hR'⟩ := hR
      have hα0 : Real.log (ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) 0 N) / Real.log x ≤ 1 / 2 :=
        h0b.trans hR0
      have hνle : T.ν ≤ ShortSieveLi.liNu θ γ
          (Real.log (ShortSieveLi.grpProd (ShortSieveLi.liftGrp len role) 0 N) / Real.log x) :=
        hνθ.trans (le_liNu hθ hγ hα0)
      cases kind with
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hR'
        have hrl : ∀ j, ShortSieveLi.liftGrp len role j ≠ 2 := by
          intro j
          rcases j with a | ⟨i, j⟩
          · exact hrole rfl (Sum.inl a)
          · exact hrole rfl (Sum.inr i)
        exact h31x y hy1 hy2 T.ν N M hrl hN hNM hratio hα0 (h1b.trans hR') hν hνle
      | true =>
        simp only [ite_true] at hR'
        refine h32x y hy1 hy2 T.ν N M hN hNM hratio hα0 ?_ hν hνle
        rcases hR' with ⟨ha, hb, hc'⟩ | ⟨ha, hb⟩
        · left
          exact ⟨h2b.trans ha, by linarith, by linarith⟩
        · right
          exact ⟨h1b.trans ha, h2b.trans hb⟩
  choose! Cf hCf using hpat
  refine ⟨∑ len ∈ P, Cf len, fun ε hε hε1 => ?_⟩
  filter_upwards [T.count_eq_sum hc hbig, (eventually_all_finset P).2 fun len hlen => hCf len hlen ε hε hε1]
    with x hsum hall y hy1 hy2
  rw [hsum y, hsum (x ^ (1 - ρ)), mul_sum, mul_sum, ← sum_sub_distrib, sum_mul, sum_div, ← sum_add_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun len hlen => hall len hlen y hy1 hy2)

end ShortSieveTypeI

#print axioms ShortSieveTypeI.forall_atoms
#print axioms ShortSieveTypeI.TNode.count_eq_sum
#print axioms ShortSieveTypeI.le_liNu
#print axioms ShortSieveTypeI.abs_count_sub_le_typeI
