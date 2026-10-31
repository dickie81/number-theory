import ShortSieveCertBox
import ShortSieveTree

/-!
# The certificate's coordinates on a node's terms

A certificate node is a `ShortSieveNode.Node` with `k` primes and `m` rough items together with coordinate rows `A`:
the coordinate `j` of a pair is `X_j = DEN Σ_t A_{jt} α_t`, `α_t = log(item_t)/log x` (`coords`), as the
generator's `x_j = α_j` for primes and sums of exponents after a role reversal. The slack `H = DEN(1 − Σ_t α_t)`
(`slack`) is `DEN(1 − log n/log x)` for the pair's product `n`.

* `LF.val_coords`: a form at a pair's coordinates and slack is `c₀ + c_η DEN + DEN Σ_t w_t α_t`, with item weights
  `w_t = Σ_j c_j A_{jt} − c_η` (`wt`).
* `holds_toCond`: so a constraint in coordinates is a node condition, exactly (`toCond`).
* `Sound`: the checker's invariant. At every pair satisfying the node's conditions with `|H| ≤ E` the coordinates lie
  in the box and satisfy the constraints. Splits (`Sound.split`, `Sound.split_neg`), tightening (`Sound.tighten`) and
  boxes cut along a coordinate (`Sound.cut_lt`, `Sound.cut_ge`) keep it.
* `abs_slack_le`: for large `x`, a pair with product in `(x/4, 2x]` has `|H| ≤ E`.
* `OK_of_out`: a node whose tightened box is empty, or on whose box a constraint fails, has no terms for large `x`,
  hence no loss.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveTree

open Classical

/-- The denominator of the certificate's coordinates. -/
def DEN : ℕ := 100 * 2 ^ 30

theorem DEN_pos : (0 : ℝ) < DEN := by norm_num [DEN]

/-- A node's coordinate rows: the coordinate `j` is `DEN Σ_t A_{jt} α_t`, `α_t` the exponents of the items. -/
abbrev Rows (k m : ℕ) := ℕ → Fin k ⊕ Fin m → ℤ

/-- The coordinates of a pair. -/
noncomputable def coords {k m : ℕ} (A : Rows k m) (x : ℝ) (v : (Fin k → ℕ) × (Fin m → ℕ)) : ℕ → ℝ :=
  fun j => DEN * ∑ t, (A j t : ℝ) * expo x v t

/-- The slack `DEN(1 − Σ_t α_t)`. -/
noncomputable def slack {k m : ℕ} (x : ℝ) (v : (Fin k → ℕ) × (Fin m → ℕ)) : ℝ := DEN * (1 - ∑ t, expo x v t)

/-- The weight of a form on the item `t`: `w_t = Σ_j c_j A_{jt} − c_η`. -/
noncomputable def wt {k m : ℕ} (A : Rows k m) (L : LF) (t : Fin k ⊕ Fin m) : ℝ :=
  ∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t - L.ce

theorem dotR_eq_sum : ∀ (c : List ℤ) (X : ℕ → ℝ), dotR c X = ∑ j ∈ range c.length, (c.getD j 0 : ℝ) * X j
  | [], _ => by simp [dotR]
  | a :: l, X => by
    rw [dotR, dotR_eq_sum l, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- A form at a pair's coordinates and slack. -/
theorem LF.val_coords {k m : ℕ} (A : Rows k m) (L : LF) (x : ℝ) (v : (Fin k → ℕ) × (Fin m → ℕ)) :
    L.val (coords A x v) (slack x v) = (L.c0 + L.ce * DEN) + DEN * ∑ t, wt A L t * expo x v t := by
  unfold LF.val coords slack wt
  rw [dotR_eq_sum]
  have h1 : ∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * (DEN * ∑ t, (A j t : ℝ) * expo x v t) =
      DEN * ∑ t, (∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) * expo x v t := by
    calc ∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * (DEN * ∑ t, (A j t : ℝ) * expo x v t)
        = ∑ j ∈ range L.c.length, ∑ t, (DEN : ℝ) * ((L.c.getD j 0 : ℝ) * A j t * expo x v t) := by
          refine sum_congr rfl fun j _ => ?_
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun t _ => by ring
      _ = ∑ t, ∑ j ∈ range L.c.length, (DEN : ℝ) * ((L.c.getD j 0 : ℝ) * A j t * expo x v t) := sum_comm
      _ = DEN * ∑ t, (∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) * expo x v t := by
          rw [mul_sum]
          refine sum_congr rfl fun t _ => ?_
          rw [sum_mul, mul_sum]
  have h2 : ∑ t, ((∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) - L.ce) * expo x v t =
      ∑ t, (∑ j ∈ range L.c.length, (L.c.getD j 0 : ℝ) * A j t) * expo x v t - L.ce * ∑ t, expo x v t := by
    simp_rw [sub_mul]
    rw [sum_sub_distrib, mul_sum]
  rw [h1, h2]
  ring

/-- A constraint in coordinates as a node condition: `Σ_t w_t log item_t < −((c₀ + c_η DEN)/DEN) log x`. -/
noncomputable def toCond {k m : ℕ} (A : Rows k m) (C : Con) : Cond k m :=
  ⟨fun a => wt A C.L (Sum.inl a), fun i => wt A C.L (Sum.inr i),
    fun x => -((C.L.c0 + C.L.ce * DEN : ℝ) / DEN) * Real.log x, C.strict⟩

theorem val_toCond {k m : ℕ} (A : Rows k m) (C : Con) {x : ℝ} (hx : 1 < x) (v : (Fin k → ℕ) × (Fin m → ℕ)) :
    (toCond A C).val v.1 v.2 = Real.log x * ∑ t, wt A C.L t * expo x v t := by
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold Cond.val toCond
  rw [Fintype.sum_sum_type, mul_add, mul_sum, mul_sum]
  simp only [expo, Sum.elim_inl, Sum.elim_inr]
  congr 1 <;> refine sum_congr rfl fun t _ => ?_ <;> field_simp

/-- **Constraints are node conditions.** For `x > 1`, the condition `toCond A C` holds at a pair exactly when the
constraint holds at its coordinates and slack. -/
theorem holds_toCond {k m : ℕ} (A : Rows k m) (C : Con) {x : ℝ} (hx : 1 < x) (v : (Fin k → ℕ) × (Fin m → ℕ)) :
    (toCond A C).Holds x v.1 v.2 ↔ C.Holds (coords A x v) (slack x v) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hD := DEN_pos
  have hval := C.L.val_coords A x v
  set S := ∑ t, wt A C.L t * expo x v t with hS
  unfold Cond.Holds Con.Holds
  rw [val_toCond A C hx v, hval]
  have hb : (toCond A C).b x = -((C.L.c0 + C.L.ce * DEN : ℝ) / DEN) * Real.log x := rfl
  have hst : (toCond A C).strict = C.strict := rfl
  rw [hb, hst]
  have key : ∀ K : ℝ, (Real.log x * S < -(K / DEN) * Real.log x ↔ K + DEN * S < 0) ∧
      (Real.log x * S ≤ -(K / DEN) * Real.log x ↔ K + DEN * S ≤ 0) := fun K => by
    have e : -(K / DEN) * Real.log x = Real.log x * (-K / DEN) := by ring
    rw [e, mul_lt_mul_iff_of_pos_left hlx, mul_le_mul_iff_of_pos_left hlx, lt_div_iff₀ hD, le_div_iff₀ hD]
    constructor <;> constructor <;> intro h <;> linarith
  split_ifs
  · exact (key _).1
  · exact (key _).2

/-- The complement of a constraint: `−L ≤ 0` for `L < 0`, `−L < 0` for `L ≤ 0`. -/
def Con.neg (C : Con) : Con := ⟨⟨-C.L.c0, C.L.c.map (- ·), -C.L.ce⟩, !C.strict⟩

theorem dotR_neg : ∀ (c : List ℤ) (X : ℕ → ℝ), dotR (c.map (- ·)) X = -dotR c X
  | [], _ => by simp [dotR]
  | a :: l, X => by
    simp only [List.map_cons, dotR, dotR_neg l]
    push_cast
    ring

theorem Con.holds_neg (C : Con) (X : ℕ → ℝ) (H : ℝ) : C.neg.Holds X H ↔ ¬C.Holds X H := by
  have hv : C.neg.L.val X H = -C.L.val X H := by
    unfold Con.neg LF.val
    simp only [dotR_neg]
    push_cast
    ring
  have hs : C.neg.strict = !C.strict := rfl
  unfold Con.Holds
  rw [hv, hs]
  cases C.strict
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, not_le, neg_lt_zero]
  · simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true, not_lt, neg_nonpos]

/-! ### The invariant -/

/-- **The checker's invariant.** At every pair with positive items satisfying the node's conditions and with slack at
most `E`, the coordinates lie in the box and satisfy the constraints. -/
def Sound (N : Node) (A : Rows N.k N.m) (E : ℤ) (Γ : List Con) (B : Box) : Prop :=
  ∀ x : ℝ, 1 < x → ∀ v : (Fin N.k → ℕ) × (Fin N.m → ℕ), (∀ a, 0 < v.1 a) → (∀ i, 0 < v.2 i) →
    (∀ C ∈ N.conds, C.Holds x v.1 v.2) → |slack x v| ≤ E →
      InBox B (coords A x v) ∧ ∀ c ∈ Γ, c.Holds (coords A x v) (slack x v)

/-- A split's first child: the node with the condition, and the constraint added. -/
theorem Sound.split {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (C : Con) : Sound ⟨N.k, N.m, N.s, toCond A C :: N.conds⟩ A E (C :: Γ) B := by
  intro x hx v hv1 hv2 hc hH
  have hc' : ∀ C' ∈ N.conds, C'.Holds x v.1 v.2 := fun C' h' => hc C' (List.mem_cons_of_mem _ h')
  obtain ⟨hB, hΓ⟩ := h x hx v hv1 hv2 hc' hH
  refine ⟨hB, fun c hc0 => ?_⟩
  rcases List.mem_cons.1 hc0 with rfl | hcΓ
  · exact (holds_toCond A c hx v).1 (hc _ List.mem_cons_self)
  · exact hΓ c hcΓ

/-- A split's second child: the node with the complementary condition, and the complementary constraint. -/
theorem Sound.split_neg {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (C : Con) : Sound ⟨N.k, N.m, N.s, (toCond A C).neg :: N.conds⟩ A E (C.neg :: Γ) B := by
  intro x hx v hv1 hv2 hc hH
  have hc' : ∀ C' ∈ N.conds, C'.Holds x v.1 v.2 := fun C' h' => hc C' (List.mem_cons_of_mem _ h')
  obtain ⟨hB, hΓ⟩ := h x hx v hv1 hv2 hc' hH
  refine ⟨hB, fun c hc0 => ?_⟩
  rcases List.mem_cons.1 hc0 with rfl | hcΓ
  · have h1 := hc _ List.mem_cons_self
    rw [holds_neg, holds_toCond A C hx v] at h1
    exact (Con.holds_neg C _ _).2 h1
  · exact hΓ c hcΓ

/-- Tightening the box by the constraints keeps the invariant. -/
theorem Sound.tighten {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (hf : fits Γ B.length = true) (cs : List Con) (hcs : ∀ c ∈ cs, c ∈ Γ) :
    Sound N A E Γ (tightenList E cs B) := by
  intro x hx v hv1 hv2 hc hH
  obtain ⟨hB, hΓ⟩ := h x hx v hv1 hv2 hc hH
  have hf' : fits cs B.length = true := by
    simp only [fits, List.all_eq_true] at hf ⊢
    exact fun c hc => hf c (hcs c hc)
  exact ⟨(tightenList_sound hH cs B hf' hB fun c hc => hΓ c (hcs c hc)).1, hΓ⟩

/-- The coordinate `j` is below `p`. -/
def ltCon (j : ℕ) (p : ℤ) : Con := ⟨⟨-p, (List.replicate j 0) ++ [1], 0⟩, true⟩

theorem dotR_unit (j : ℕ) (X : ℕ → ℝ) : dotR ((List.replicate j 0) ++ [1]) X = X j := by
  rw [dotR_append, dotR_replicate_zero, List.length_replicate]
  simp [dotR]

theorem holds_ltCon (j : ℕ) (p : ℤ) (X : ℕ → ℝ) (H : ℝ) : (ltCon j p).Holds X H ↔ X j < p := by
  unfold ltCon Con.Holds LF.val
  simp only [↓reduceIte, dotR_unit]
  push_cast
  constructor <;> intro h <;> linarith

theorem inBox_cut_lt : ∀ (B : Box) (X : ℕ → ℝ) (j : ℕ) (p : ℤ), InBox B X → X j < p →
    InBox (B.modify j fun b => (b.1, min b.2 p)) X
  | [], _, _, _, h, _ => by simpa using h
  | b :: B, X, 0, p, ⟨h1, h2, hB⟩, h => by
    refine ⟨h1, ?_, hB⟩
    simp only [Int.cast_min]
    exact lt_min h2 h
  | b :: B, X, j + 1, p, ⟨h1, h2, hB⟩, h => by
    exact ⟨h1, h2, inBox_cut_lt B _ j p hB h⟩

theorem inBox_cut_ge : ∀ (B : Box) (X : ℕ → ℝ) (j : ℕ) (p : ℤ), InBox B X → (p : ℝ) ≤ X j →
    InBox (B.modify j fun b => (max b.1 p, b.2)) X
  | [], _, _, _, h, _ => by simpa using h
  | b :: B, X, 0, p, ⟨h1, h2, hB⟩, h => by
    refine ⟨?_, h2, hB⟩
    simp only [Int.cast_max]
    exact max_le h1 h
  | b :: B, X, j + 1, p, ⟨h1, h2, hB⟩, h => by
    exact ⟨h1, h2, inBox_cut_ge B _ j p hB h⟩

/-- A cut of the box along the coordinate `j` at `p`: the part below `p`. -/
theorem Sound.cut_lt {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (j : ℕ) (p : ℤ) : Sound ⟨N.k, N.m, N.s, toCond A (ltCon j p) :: N.conds⟩ A E Γ
      (B.modify j fun b => (b.1, min b.2 p)) := by
  intro x hx v hv1 hv2 hc hH
  obtain ⟨hB, hΓ⟩ := (h.split (ltCon j p)) x hx v hv1 hv2 hc hH
  refine ⟨inBox_cut_lt B _ j p hB ((holds_ltCon j p _ _).1 (hΓ _ List.mem_cons_self)), fun c hc' => ?_⟩
  exact hΓ c (List.mem_cons_of_mem _ hc')

/-- A cut of the box along the coordinate `j` at `p`: the part from `p` on. -/
theorem Sound.cut_ge {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (j : ℕ) (p : ℤ) : Sound ⟨N.k, N.m, N.s, (toCond A (ltCon j p)).neg :: N.conds⟩ A E Γ
      (B.modify j fun b => (max b.1 p, b.2)) := by
  intro x hx v hv1 hv2 hc hH
  obtain ⟨hB, hΓ⟩ := (h.split_neg (ltCon j p)) x hx v hv1 hv2 hc hH
  have h1 := hΓ _ List.mem_cons_self
  rw [Con.holds_neg, holds_ltCon, not_lt] at h1
  exact ⟨inBox_cut_ge B _ j p hB h1, fun c hc' => hΓ c (List.mem_cons_of_mem _ hc')⟩

/-! ### The slack, and nodes without terms -/

/-- The exponents of a pair with positive items add up to `log n/log x`. -/
theorem sum_expo {k m : ℕ} (x : ℝ) {v : (Fin k → ℕ) × (Fin m → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) :
    ∑ t, expo x v t = Real.log (prodP v : ℕ) / Real.log x := by
  rw [Fintype.sum_sum_type]
  simp only [expo, Sum.elim_inl, Sum.elim_inr]
  rw [← sum_div, ← sum_div, ← add_div]
  congr 1
  unfold prodP
  push_cast
  rw [Real.log_mul (prod_pos fun a _ => by exact_mod_cast hv1 a).ne' (prod_pos fun i _ => by exact_mod_cast hv2 i).ne',
    Real.log_prod (fun a _ => by exact_mod_cast (hv1 a).ne'), Real.log_prod (fun i _ => by exact_mod_cast (hv2 i).ne')]

/-- **The slack is small** for the pairs with product in `(x/4, 2x]`: `|H| ≤ DEN log 4/log x ≤ E` for large `x`. -/
theorem abs_slack_le {E : ℤ} (hE : 0 < E) (k m : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ v : (Fin k → ℕ) × (Fin m → ℕ), (∀ a, 0 < v.1 a) → (∀ i, 0 < v.2 i) →
      x / 4 < (prodP v : ℝ) → (prodP v : ℝ) ≤ 2 * x → |slack x v| ≤ E := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have hD := DEN_pos
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  filter_upwards [eventually_gt_atTop 1, (tendsto_log_atTop.eventually_ge_atTop (DEN * Real.log 4 / E))]
    with x hx1 hlx v hv1 hv2 h1 h2
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos hx1
  have hn0 : (0 : ℝ) < prodP v := by linarith
  unfold slack
  rw [sum_expo x hv1 hv2]
  -- `|log x − log n| ≤ log 4`
  have e1 : Real.log (prodP v : ℕ) ≤ Real.log x + Real.log 2 := by
    rw [← Real.log_mul hx0.ne' (by norm_num)]
    exact Real.log_le_log hn0 (by linarith)
  have e2 : Real.log x - Real.log 4 ≤ Real.log (prodP v : ℕ) := by
    rw [← Real.log_div hx0.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hd : |1 - Real.log (prodP v : ℕ) / Real.log x| ≤ Real.log 4 / Real.log x := by
    have e3 : 1 - Real.log (prodP v : ℕ) / Real.log x = (Real.log x - Real.log (prodP v : ℕ)) / Real.log x := by
      field_simp
    rw [e3, abs_div, abs_of_pos hlx0, div_le_div_iff_of_pos_right hlx0, abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hD]
  have h3 : Real.log 4 / Real.log x ≤ E / DEN := by
    rw [div_le_div_iff₀ hlx0 hD]
    rw [div_le_iff₀ hE'] at hlx
    linarith
  calc (DEN : ℝ) * |1 - Real.log (prodP v : ℕ) / Real.log x| ≤ DEN * (E / DEN) :=
        mul_le_mul_of_nonneg_left (hd.trans h3) hD.le
    _ = E := by field_simp

/-- No point of the box satisfies the constraints: after tightening twice the box is empty, or a constraint fails on
it (the generator's `OUT`). -/
def Out (E : ℤ) (Γ : List Con) (B : Box) : Bool :=
  fits Γ B.length && ((tightenList E Γ (tightenList E Γ B)).isEmpty ||
    Γ.any fun c => c.fails (tightenList E Γ (tightenList E Γ B)) E)

theorem Sound.false_of_out {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (hout : Out E Γ B = true) {x : ℝ} (hx : 1 < x) {v : (Fin N.k → ℕ) × (Fin N.m → ℕ)} (hv1 : ∀ a, 0 < v.1 a)
    (hv2 : ∀ i, 0 < v.2 i) (hc : ∀ C ∈ N.conds, C.Holds x v.1 v.2) (hH : |slack x v| ≤ E) : False := by
  unfold Out at hout
  rw [Bool.and_eq_true, Bool.or_eq_true] at hout
  obtain ⟨hf, hout⟩ := hout
  have h2 := (h.tighten hf Γ fun c hc => hc).tighten
  have hlen1 := (tightenList_sound hH Γ B hf (h x hx v hv1 hv2 hc hH).1 (h x hx v hv1 hv2 hc hH).2).2
  have hf1 : fits Γ (tightenList E Γ B).length = true := by rw [hlen1]; exact hf
  obtain ⟨hB, hΓ⟩ := (h2 hf1 Γ fun c hc => hc) x hx v hv1 hv2 hc hH
  rcases hout with he | ha
  · rw [not_isEmpty hB] at he
    exact Bool.false_ne_true he
  · obtain ⟨c, hcΓ, hcf⟩ := List.any_eq_true.1 ha
    exact Con.not_holds_of_fails hcf hB hH (hΓ c hcΓ)

/-- **No terms.** If no point satisfies the constraints, the node counts nothing in `(x − y, x]` for `y ≤ x/2` and
large `x`. -/
theorem Sound.count_eq_zero {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (hE : 0 < E) (hout : Out E Γ B = true) : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, y ≤ x / 2 → N.count x y = 0 := by
  filter_upwards [abs_slack_le hE N.k N.m, eventually_gt_atTop 1] with x hsl hx1 y hy
  unfold Node.count
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v hv hI
  obtain ⟨hp, hρ⟩ := ShortSieveBuch.mem_pairs.1 hv
  have hv1 : ∀ a, 0 < v.1 a := fun a => (hp a).2.pos
  have hv2 : ∀ i, 0 < v.2 i := fun i => (hρ i).1
  obtain ⟨-, hcond, hlo, hhi⟩ := hI
  exact h.false_of_out hout hx1 hv1 hv2 hcond (hsl v hv1 hv2 (by linarith) (by linarith))

/-- **An empty region has no loss.** -/
theorem Sound.OK_of_out {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B)
    (hE : 0 < E) (hout : Out E Γ B = true) {θ ρ σ : ℝ} (hρ : 0 < ρ) (hθρ : θ ≤ 1 - ρ) :
    OK θ ρ σ (fun x y => (N.count x y : ℝ)) 0 := by
  refine OK_zero hθρ ?_
  filter_upwards [h.count_eq_zero hE hout, eventually_gt_atTop 1,
    (tendsto_rpow_atTop hρ).eventually_ge_atTop 2] with x hx hx1 hxr y _ hy2
  have hx0 : 0 < x := by linarith
  have hyx : y ≤ x / 2 := by
    have e : x ^ (1 - ρ) * x ^ ρ = x := by rw [← Real.rpow_add hx0]; simp
    have : x ^ (1 - ρ) * 2 ≤ x := by
      calc x ^ (1 - ρ) * 2 ≤ x ^ (1 - ρ) * x ^ ρ :=
            mul_le_mul_of_nonneg_left hxr (Real.rpow_nonneg hx0.le _)
        _ = x := e
    linarith
  rw [hx y hyx]
  simp

end ShortSieveCert

#print axioms ShortSieveCert.holds_toCond
#print axioms ShortSieveCert.Sound.tighten
#print axioms ShortSieveCert.Sound.cut_ge
#print axioms ShortSieveCert.abs_slack_le
#print axioms ShortSieveCert.Sound.OK_of_out
