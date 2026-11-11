/-
# The tree of a reversed term bounds it

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdRevDefs.lean` defines the nodes of the tree of a reversed term (`SieveAd.opsK`): its boxes
are the atoms' cells with, before them, the cells of a chain. Here, for a route (`x = q^L`):

* `aset na k`, `aprodR na rt`: the first `na` entries of a tuple, the atoms, and their product; `slabP q e₁ e₂ na`:
  the product lies in `(x^{e₁/DEN}, x^{e₂/DEN}]`, which is two atoms of the library (`slabE`, `slabP_iff`,
  `thrOK_slabE`). `famK`: the tuples of a box under that condition.
* `Wsum`: the sum of `1/∏rt` over them; `RKl`: that sum for the atoms' box of a list, the weight of the costs.
  `Wsum_chain_le`: `Wsum` of a box is at most the weight times the sums of `1/p` over the chain's cells.
* `PK ctx na bl par c`: for a box `bl` with a chain, the term of its tuples under the condition of `ctx`, with its
  sign, is at least `−((c/K + ε)·RKl + o(1))x/(φ(q) log x)`, for every `ε > 0`.
* `pk_vanish`, `pk_eval`, `pk_drop`, `pk_split`, `pk_buch`: the nodes. A chain's box that passes `vanishK` has no
  term, since `n/r'` lies between `x^{(l₁−1)/DEN}` and `x^{(h₁+1)/DEN}`; one that passes `dropK` has its term in the
  comparison set at most the cost, by `SieveRough.psi_point_w` with `r'` among the primes before the last; the
  evaluations are the tests', which are sound under the condition's two atoms (`Tests.SoundX`).
* `rulesK`, `solveK_sound`: so a cost that the search of the tree returns below its limit has `PK`.

The file imports `SieveAdSearchG.lean` and `SieveAdRevCount.lean`.
-/
import SieveAdSearchG
import SieveAdRevCount

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K omKw cdiv trB exB DEN_pos' K_pos')

/-! ### Exponents and logarithms -/

theorem le_logDEN {x v e : ℝ} (hx : 1 < x) (h : x ^ (e / DEN) ≤ v) :
    e ≤ Real.log v / Real.log x * DEN := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) h
  rw [Real.log_rpow hx0] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hlx]
  have hD := DEN_pos'
  have := mul_le_mul_of_nonneg_right h1 hD.le
  calc e * Real.log x = e / DEN * Real.log x * DEN := by field_simp
    _ ≤ Real.log v * DEN := this

theorem logDEN_le {x v e : ℝ} (hx : 1 < x) (hv : 0 < v) (h : v ≤ x ^ (e / DEN)) :
    Real.log v / Real.log x * DEN ≤ e := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have h1 := Real.log_le_log hv h
  rw [Real.log_rpow hx0] at h1
  rw [div_mul_eq_mul_div, div_le_iff₀ hlx]
  have hD := DEN_pos'
  have := mul_le_mul_of_nonneg_right h1 hD.le
  calc Real.log v * DEN ≤ e / DEN * Real.log x * DEN := this
    _ = e * Real.log x := by field_simp

/-! ### The chain and the atoms of a list -/

/-- The cells of the atoms: the last `na` cells of the box. -/
def atomsOf (na : ℕ) (bl : List Cell) : List Cell := bl.drop (bl.length - na)

theorem chainOf_cons {na : ℕ} {bl : List Cell} (h : na ≤ bl.length) (x : Cell) :
    chainOf na (x :: bl) = x :: chainOf na bl := by
  unfold chainOf
  simp only [List.length_cons]
  rw [show bl.length + 1 - na = (bl.length - na) + 1 by omega]
  rfl

theorem atomsOf_cons {na : ℕ} {bl : List Cell} (h : na ≤ bl.length) (x : Cell) :
    atomsOf na (x :: bl) = atomsOf na bl := by
  unfold atomsOf
  simp only [List.length_cons]
  rw [show bl.length + 1 - na = (bl.length - na) + 1 by omega]
  rfl

theorem chainOf_of_le {na : ℕ} {bl : List Cell} (h : bl.length ≤ na) : chainOf na bl = [] := by
  unfold chainOf
  rw [show bl.length - na = 0 by omega]
  rfl

theorem atomsOf_of_le {na : ℕ} {bl : List Cell} (h : bl.length ≤ na) : atomsOf na bl = bl := by
  unfold atomsOf
  rw [show bl.length - na = 0 by omega]
  rfl

/-- A box with a chain is the chain's newest cell before a box. -/
theorem exists_cons_of_lt {na : ℕ} {bl : List Cell} (h : na < bl.length) :
    ∃ c bl₀, bl = c :: bl₀ ∧ na ≤ bl₀.length := by
  cases bl with
  | nil => simp at h
  | cons c bl₀ => exact ⟨c, bl₀, rfl, by simpa [Nat.lt_succ_iff] using h⟩

/-- A sum over the chain's indices is the sum over the chain's cells. -/
theorem sum_chain (F : Cell → ℕ) (na : ℕ) : ∀ (bl : List Cell) (k : ℕ) (h : bl.length = k),
    ∑ i : Fin k, (if (i : ℕ) < na then 0 else F (boxFn bl k h i)) = ((chainOf na bl).map F).sum := by
  intro bl
  induction bl with
  | nil =>
    intro k h
    subst h
    simp [chainOf]
  | cons x bl ih =>
    intro k h
    subst h
    show ∑ i : Fin (bl.length + 1), (if (i : ℕ) < na then 0 else F (boxFn (x :: bl) (bl.length + 1) rfl i)) = _
    rw [boxFn_cons x bl bl.length rfl, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [ih bl.length rfl]
    by_cases hna : bl.length < na
    · rw [chainOf_of_le (bl := x :: bl) (by simp only [List.length_cons]; omega), chainOf_of_le (bl := bl) hna.le]
      simp [hna]
    · rw [chainOf_cons (not_lt.1 hna) x]
      simp only [hna, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [add_comm]

variable [Route]

/-! ### The product of the atoms -/

/-- The indices of the atoms: the first `na`. -/
def aset (na k : ℕ) : Finset (Fin k) := Finset.univ.filter fun i => (i : ℕ) < na

/-- The indices of the chain: the others. -/
def cset (na k : ℕ) : Finset (Fin k) := Finset.univ.filter fun i => ¬ (i : ℕ) < na

/-- The product of the atoms of a tuple. -/
noncomputable def aprodR (na : ℕ) {k : ℕ} (rt : Fin k → ℕ) : ℝ := ∏ i ∈ aset na k, (rt i : ℝ)

omit [Route] in
theorem aprodR_eq (na : ℕ) {k : ℕ} (rt : Fin k → ℕ) :
    aprodR na rt = ∏ i : Fin k, if (i : ℕ) < na then (rt i : ℝ) else 1 := by
  unfold aprodR aset
  rw [Finset.prod_filter]

omit [Route] in
theorem aprodR_snoc {na k : ℕ} (hna : na ≤ k) (rt : Fin k → ℕ) (p : ℕ) :
    aprodR na (Fin.snoc rt p : Fin (k + 1) → ℕ) = aprodR na rt := by
  rw [aprodR_eq, aprodR_eq, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  simp only [show ¬ k < na by omega, ↓reduceIte, mul_one]

omit [Route] in
theorem aprodR_init {na k : ℕ} (hna : na ≤ k) (y : Fin (k + 1) → ℕ) : aprodR na (Fin.init y) = aprodR na y := by
  conv_rhs => rw [← Fin.snoc_init_self y]
  exact (aprodR_snoc hna _ _).symm

omit [Route] in
/-- The product of a tuple is the atoms' product times the chain's. -/
theorem prod_eq_aprodR_mul (na : ℕ) {k : ℕ} (rt : Fin k → ℕ) :
    ∏ i, (rt i : ℝ) = aprodR na rt * ∏ i ∈ cset na k, (rt i : ℝ) := by
  unfold aprodR aset cset
  rw [Finset.prod_filter_mul_prod_filter_not]

omit [Route] in
/-- With no chain, the atoms' product is the tuple's. -/
theorem aprodR_full {na k : ℕ} (hk : k ≤ na) (rt : Fin k → ℕ) : aprodR na rt = ∏ i, (rt i : ℝ) := by
  rw [aprodR_eq]
  exact Finset.prod_congr rfl fun i _ => by simp [show (i : ℕ) < na from lt_of_lt_of_le i.2 hk]

/-- The product of the primes of a set of indices, for a tuple of a box. -/
theorem prod_set_bounds_x {q : ℕ} (hx0 : 0 < xq q) {k : ℕ} {bx : Fin k → Cell} {rt : Fin k → ℕ}
    (hc : ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN))
    (S : Finset (Fin k)) :
    xq q ^ (((∑ i ∈ S, (bx i).1 : ℕ) : ℝ) / DEN) ≤ ∏ i ∈ S, (rt i : ℝ) ∧
      ∏ i ∈ S, (rt i : ℝ) ≤ xq q ^ (((∑ i ∈ S, (bx i).2 : ℕ) : ℝ) / DEN) := by
  constructor
  · rw [Nat.cast_sum, Finset.sum_div, Real.rpow_sum_of_pos hx0]
    exact Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hx0.le _) fun i _ => (hc i).1
  · rw [Nat.cast_sum, Finset.sum_div, Real.rpow_sum_of_pos hx0]
    exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (hc i).2.le

omit [Route] in
/-- A sum over the chain's indices of a box, by its list. -/
theorem sum_cset (F : Cell → ℕ) (na : ℕ) (bl : List Cell) (k : ℕ) (h : bl.length = k) :
    ∑ i ∈ cset na k, F (boxFn bl k h i) = ((chainOf na bl).map F).sum := by
  unfold cset
  rw [Finset.sum_filter, ← sum_chain F na bl k h]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> rfl

/-! ### The condition on the atoms' product -/

/-- The atoms' product lies in `(x^{e₁/DEN}, x^{e₂/DEN}]`. -/
def slabP (q e₁ e₂ na : ℕ) {k : ℕ} (rt : Fin k → ℕ) : Prop :=
  xq q ^ ((e₁ : ℝ) / DEN) < aprodR na rt ∧ aprodR na rt ≤ xq q ^ ((e₂ : ℝ) / DEN)

/-- The condition, as two atoms. -/
noncomputable def slabE (q e₁ e₂ na k : ℕ) : List (Atom k) :=
  [Atom.prodGt (aset na k) (xq q ^ ((e₁ : ℝ) / DEN)), Atom.prodLe (aset na k) (xq q ^ ((e₂ : ℝ) / DEN))]

theorem slabP_iff (q e₁ e₂ na : ℕ) {k : ℕ} (rt : Fin k → ℕ) :
    slabP q e₁ e₂ na rt ↔ ∀ A ∈ slabE q e₁ e₂ na k, A.sem rt := by
  simp [slabP, slabE, aprodR]

theorem slabP_init (q e₁ e₂ : ℕ) {na k : ℕ} (hna : na ≤ k) (y : Fin (k + 1) → ℕ) :
    slabP q e₁ e₂ na (Fin.init y) ↔ slabP q e₁ e₂ na y := by
  unfold slabP
  rw [aprodR_init hna]

/-- For `x ≥ 1` and exponents at most `DEN`, the thresholds of the condition's atoms lie in `[1, q^{L+1}]`. -/
theorem thrOK_slabE {q : ℕ} (hq : 1 ≤ q) (hL : 0 ≤ L) {e₁ e₂ : ℕ} (h1 : e₁ ≤ DEN) (h2 : e₂ ≤ DEN) (na k : ℕ) :
    ThrOK q (slabE q e₁ e₂ na k) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1 hL
  have hD := DEN_pos'
  have hpow : ∀ a : ℕ, a ≤ DEN → 1 ≤ xq q ^ ((a : ℝ) / DEN) ∧ xq q ^ ((a : ℝ) / DEN) ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
    intro a ha
    refine ⟨Real.one_le_rpow hx1 (by positivity), ?_⟩
    have h1 : xq q ^ ((a : ℝ) / DEN) ≤ xq q ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [div_le_one hD]; exact_mod_cast ha)
    rw [Real.rpow_one] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
  intro A hA
  simp only [slabE, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl
  · exact hpow _ h1
  · exact hpow _ h2

/-- The tuples of a box whose atoms' product lies in `(x^{e₁/DEN}, x^{e₂/DEN}]`. -/
noncomputable def famK (q e₁ e₂ na : ℕ) {k : ℕ} (bx : Fin k → Cell) : Finset (Fin k → ℕ) :=
  (famB q bx).filter (slabP q e₁ e₂ na)

/-- The first primes of a tuple of a box with one more cell are a tuple of the box. -/
theorem init_mem_famB {q k : ℕ} {bx : Fin k → Cell} {c : Cell} {y : Fin (k + 1) → ℕ}
    (hy : y ∈ famB q (Fin.snoc (α := fun _ => Cell) bx c)) : Fin.init y ∈ famB q bx := by
  obtain ⟨hpr, hsa, hc⟩ := mem_famB.1 hy
  refine mem_famB.2 ⟨fun i => hpr i.castSucc, fun a b hab => hsa (Fin.castSucc_lt_castSucc_iff.2 hab), fun i => ?_⟩
  have := hc i.castSucc
  simp only [Fin.snoc_castSucc] at this
  exact this

/-- The last prime of a tuple of a box with one more cell lies in that cell. -/
theorem last_mem_boxP {q k : ℕ} {bx : Fin k → Cell} {c : Cell} (hc : c.1 ≤ c.2) {y : Fin (k + 1) → ℕ}
    (hy : y ∈ famB q (Fin.snoc (α := fun _ => Cell) bx c)) : y (Fin.last k) ∈ boxP (xq q) c.1 (c.2 - c.1) := by
  obtain ⟨hpr, -, hcc⟩ := mem_famB.1 hy
  have h := hcc (Fin.last k)
  simp only [Fin.snoc_last] at h
  rw [boxP, mem_primesIn]
  refine ⟨(hpr _).2, h.1, ?_⟩
  have e : ((c.1 : ℝ) + ((c.2 - c.1 : ℕ) : ℝ)) = (c.2 : ℝ) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hc]
  rw [e]
  exact h.2

/-- **A sum over the tuples with one more prime.** For a function `f ≥ 0` of the last prime: the sum of
`f(p_last)/∏(the others)` over the tuples of the box with one more cell `c`, under the condition, is at most the sum
of `1/∏` over the tuples of the box under the condition, times the sum of `f` over the primes of the cell. -/
theorem famK_snoc_sum_le {q e₁ e₂ na k : ℕ} (hna : na ≤ k) (bx : Fin k → Cell) (c : Cell) (hc : c.1 ≤ c.2)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ rt ∈ famK q e₁ e₂ na (Fin.snoc (α := fun _ => Cell) bx c),
        (∏ i : Fin k, (1 / (rt i.castSucc : ℝ))) * f (rt (Fin.last k)) ≤
      (∑ r ∈ famK q e₁ e₂ na bx, ∏ i, (1 / (r i : ℝ))) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), f p := by
  refine sum_snoc_le _ _ _ (fun rt hrt => ?_) (fun r => ∏ i, (1 / (r i : ℝ))) f
    (fun r => Finset.prod_nonneg fun i _ => by positivity) hf
  rw [famK, Finset.mem_filter] at hrt
  exact ⟨Finset.mem_filter.2 ⟨init_mem_famB hrt.1, (slabP_init q e₁ e₂ hna rt).2 hrt.2⟩, last_mem_boxP hc hrt.1⟩

/-! ### The sums of `1/∏rt` -/

/-- The sum of `1/∏rt` over the tuples of the box of a list under the condition. -/
noncomputable def Wsum (q e₁ e₂ na : ℕ) (bl : List Cell) : ℝ :=
  ∑ rt ∈ famK q e₁ e₂ na (boxFn bl bl.length rfl), ∏ i, (1 / (rt i : ℝ))

theorem Wsum_eq (q e₁ e₂ na : ℕ) (bl : List Cell) (k : ℕ) (h : bl.length = k) :
    Wsum q e₁ e₂ na bl = ∑ rt ∈ famK q e₁ e₂ na (boxFn bl k h), ∏ i, (1 / (rt i : ℝ)) := by
  subst h
  rfl

theorem Wsum_nonneg (q e₁ e₂ na : ℕ) (bl : List Cell) : 0 ≤ Wsum q e₁ e₂ na bl :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity

/-- **The weight of the costs**: the sum of `1/r'` over the atoms' box of a list, under the condition. -/
noncomputable def RKl (q e₁ e₂ na : ℕ) (bl : List Cell) : ℝ := Wsum q e₁ e₂ na (atomsOf na bl)

theorem RKl_nonneg (q e₁ e₂ na : ℕ) (bl : List Cell) : 0 ≤ RKl q e₁ e₂ na bl := Wsum_nonneg _ _ _ _ _

theorem RKl_cons (q e₁ e₂ : ℕ) {na : ℕ} {bl : List Cell} (h : na ≤ bl.length) (x : Cell) :
    RKl q e₁ e₂ na (x :: bl) = RKl q e₁ e₂ na bl := by
  unfold RKl
  rw [atomsOf_cons h]

/-- The sums of `1/p` over the cells of a list, multiplied. -/
noncomputable def TRl (x : ℝ) : List Cell → ℝ
  | [] => 1
  | c :: b => (∑ p ∈ boxP x c.1 (c.2 - c.1), 1 / (p : ℝ)) * TRl x b

omit [Route] in
theorem TRl_nonneg (x : ℝ) (b : List Cell) : 0 ≤ TRl x b := by
  induction b with
  | nil => simp [TRl]
  | cons c b ih => exact mul_nonneg (sum_inv_nonneg _) ih

/-- One more cell of the chain: `Wsum` grows by at most the sum of `1/p` over the cell. -/
theorem Wsum_cons_le (q e₁ e₂ : ℕ) {na : ℕ} {bl : List Cell} (hna : na ≤ bl.length) (c : Cell) (hc : c.1 ≤ c.2) :
    Wsum q e₁ e₂ na (c :: bl) ≤ Wsum q e₁ e₂ na bl * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / (p : ℝ) := by
  rw [Wsum_eq q e₁ e₂ na (c :: bl) (bl.length + 1) rfl, boxFn_cons c bl bl.length rfl]
  have h := famK_snoc_sum_le (q := q) (e₁ := e₁) (e₂ := e₂) hna (boxFn bl bl.length rfl) c hc
    (fun p => 1 / (p : ℝ)) (fun p => by positivity)
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [Fin.prod_univ_castSucc]

/-- **`Wsum` of a box is at most the weight times the sums of `1/p` over the chain's cells.** -/
theorem Wsum_chain_le (q e₁ e₂ na : ℕ) : ∀ bl : List Cell, na ≤ bl.length → (∀ c ∈ chainOf na bl, c.1 ≤ c.2) →
    Wsum q e₁ e₂ na bl ≤ RKl q e₁ e₂ na bl * TRl (xq q) (chainOf na bl) := by
  intro bl
  induction bl with
  | nil =>
    intro _ _
    rw [chainOf_of_le (by simp)]
    unfold RKl
    rw [atomsOf_of_le (by simp)]
    simp [TRl]
  | cons c bl ih =>
    intro hna hcells
    by_cases h : na ≤ bl.length
    · rw [chainOf_cons h c] at hcells ⊢
      have hc := hcells c (List.mem_cons_self ..)
      have h1 := Wsum_cons_le q e₁ e₂ h c hc
      have h2 := ih h fun d hd => hcells d (List.mem_cons_of_mem _ hd)
      rw [RKl_cons q e₁ e₂ h c]
      have h0 := sum_inv_nonneg (boxP (xq q) c.1 (c.2 - c.1))
      calc Wsum q e₁ e₂ na (c :: bl)
          ≤ Wsum q e₁ e₂ na bl * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / (p : ℝ) := h1
        _ ≤ RKl q e₁ e₂ na bl * TRl (xq q) (chainOf na bl) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / (p : ℝ) :=
            mul_le_mul_of_nonneg_right h2 h0
        _ = RKl q e₁ e₂ na bl * TRl (xq q) (c :: chainOf na bl) := by simp only [TRl]; ring
    · have hle : (c :: bl).length ≤ na := by simp only [List.length_cons] at hna ⊢; omega
      rw [chainOf_of_le hle]
      unfold RKl
      rw [atomsOf_of_le hle]
      simp [TRl]

omit [Route] in
/-- `limsup` of the sums of `1/p` over the cells of a list is at most the product of their `trB`. -/
theorem evLe_TRl : ∀ b : List Cell, (∀ d ∈ b, 0 < d.1) →
    EvLe (fun x => TRl x b) ((b.map fun d => trB d.1 (d.2 - d.1)).prod) := by
  intro b
  induction b with
  | nil =>
    intro _ δ hδ
    exact Filter.Eventually.of_forall fun x => by simp [TRl]; linarith
  | cons c b ih =>
    intro hb
    have h1 := ih fun d hd => hb d (List.mem_cons_of_mem _ hd)
    have hc := hb c (List.mem_cons_self ..)
    have hP0 : 0 ≤ (b.map fun d => trB d.1 (d.2 - d.1)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
        exact SieveCert.trB_nonneg _ _
    have hm := EvLe.mul (SieveCert.trB_nonneg c.1 (c.2 - c.1)) hP0
      (Filter.Eventually.of_forall fun x => sum_inv_nonneg (boxP x c.1 (c.2 - c.1)))
      (Filter.Eventually.of_forall fun x => TRl_nonneg x b) (evLe_box_tr (w := c.2 - c.1) hc) h1
    simpa only [TRl, List.map_cons, List.prod_cons] using hm

/-! ### What the tree of a reversed term proves -/

/-- The lower exponent of the range of `r'`, for the cell `ctx` of the prime that is reversed. -/
def e1 (ctx : Cell) : ℕ := DEN - ctx.2

/-- The upper exponent of the range of `r'`. -/
def e2 (ctx : Cell) : ℕ := DEN - ctx.1 + 1

/-- **What the tree of a reversed term proves** of a box with a chain: the term of its tuples under the condition,
with its sign, is at least `−((c/K + ε)·RKl + o(1))x/(φ(q) log x)`, for every `ε > 0`. -/
def PK (ctx : Cell) (na : ℕ) (bl : List Cell) (par : Bool) (c : ℕ) : Prop :=
  na < bl.length → ∀ (k' : ℕ) (h : bl.length = k' + 1) (ε : ℝ), 0 < ε →
    BdP (fun q => slabP q (e1 ctx) (e2 ctx) na) (fun q => RKl q (e1 ctx) (e2 ctx) na bl) par ((c : ℝ) / K + ε)
      (boxFn bl (k' + 1) h)

/-- The condition's atoms have thresholds as in `ThrOK`, for `q ≥ 1`. -/
theorem thrOK_ctx [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1) (na k : ℕ) :
    ∀ᶠ q : ℕ in atTop, ThrOK q (slabE q (e1 ctx) (e2 ctx) na k) := by
  have hD1 : 1 ≤ DEN := by unfold SieveCert.DEN; exact Nat.one_le_two_pow
  filter_upwards [eventually_ge_atTop 1] with q hq
  exact thrOK_slabE hq L_pos.le (by unfold e1; omega) (by unfold e2; omega) na k

/-- A box of at most twelve cells that a test evaluates is evaluated under the condition. -/
theorem evIP_slab [RouteOK] {τ : Tests} (hτ : τ.SoundX) {ctx : Cell} (hctx : 0 < ctx.1) (na : ℕ) {bl : List Cell}
    {cfg : Cfg} {k' : ℕ} (h : bl.length = k' + 1) (hk : k' + 1 ≤ 12) (hI : τ.okI bl cfg = true) :
    EvIP (fun q => slabP q (e1 ctx) (e2 ctx) na) (boxFn bl (k' + 1) h) := by
  have h0 := (hτ.soundI bl cfg k' h hk hI).evIP (fun q => slabE q (e1 ctx) (e2 ctx) na (k' + 1))
    (fun q => by simp [slabE]) (thrOK_ctx hctx na (k' + 1))
  intro η hη
  filter_upwards [h0 η hη] with q hq a ha
  rw [dIP_congr (P' := fun rt => ∀ A ∈ slabE q (e1 ctx) (e2 ctx) na (k' + 1), A.sem rt)
    fun rt _ => slabP_iff q _ _ na rt]
  exact hq a ha

/-- A box of at most twelve cells whose terms at a floor a test evaluates has them evaluated under the condition. -/
theorem evJP_slab [RouteOK] {τ : Tests} (hτ : τ.SoundX) {ctx : Cell} (hctx : 0 < ctx.1) (na : ℕ) {bl : List Cell}
    {f : ℕ} {cfg : Cfg} {k : ℕ} (h : bl.length = k) (hk : k ≤ 12) (hJ : τ.okJ bl f cfg = true) :
    EvJP (fun q => slabP q (e1 ctx) (e2 ctx) na) f (boxFn bl k h) := by
  have h0 := (hτ.soundJ bl f cfg k h hk hJ).evJP (fun q => slabE q (e1 ctx) (e2 ctx) na k)
    (fun q => by simp [slabE]) (thrOK_ctx hctx na k)
  intro η hη
  filter_upwards [h0 η hη] with q hq a ha
  rw [dJP_congr (P' := fun rt => ∀ A ∈ slabE q (e1 ctx) (e2 ctx) na k, A.sem rt)
    fun rt _ => slabP_iff q _ _ na rt]
  exact hq a ha

/-- A box that a test evaluates. -/
theorem pk_eval [RouteOK] {τ : Tests} (hτ : τ.SoundX) {ctx : Cell} (hctx : 0 < ctx.1) {na : ℕ} {bl : List Cell}
    {par : Bool} {cfg : Cfg} (hg : (opsK ctx na).grd bl = true) (hI : τ.okI bl cfg = true) :
    PK ctx na bl par 0 := by
  intro hna k' h ε hε
  simp only [opsK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hg
  have h0 : BdP (fun q => slabP q (e1 ctx) (e2 ctx) na) (fun q => RKl q (e1 ctx) (e2 ctx) na bl) par 0
      (boxFn bl (k' + 1) h) := bdP_eval (evIP_slab hτ hctx na h (by omega) hI)
  refine bdP_mono (Filter.Eventually.of_forall fun q => RKl_nonneg q _ _ _ _) h0 ?_
  simp only [Nat.cast_zero, zero_div, zero_add]
  exact hε.le

/-- A cut of the newest cell. -/
theorem pk_split [RouteOK] {ctx : Cell} {na : ℕ} {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}
    (h1 : a < m) (h2 : m < top) (hl : PK ctx na ((a, m) :: bl) par c1) (hr : PK ctx na ((m, top) :: bl) par c2) :
    PK ctx na ((a, top) :: bl) par (c1 + c2) := by
  intro hna k' h ε hε
  have hna' : na ≤ bl.length := by simp only [List.length_cons] at hna; omega
  have hk : bl.length = k' := by simpa using h
  subst hk
  have hL := hl (by simpa using hna) bl.length rfl (ε / 2) (by positivity)
  have hR := hr (by simpa using hna) bl.length rfl (ε / 2) (by positivity)
  simp only [RKl_cons _ _ _ hna'] at hL hR ⊢
  have ebx : boxFn ((a, top) :: bl) (bl.length + 1) h =
      Fin.snoc (α := fun _ => Cell) (boxFn bl bl.length rfl) (a, top) := boxFn_cons _ _ _ rfl
  have el : Function.update (boxFn ((a, top) :: bl) (bl.length + 1) h) (Fin.last _)
      ((boxFn ((a, top) :: bl) (bl.length + 1) h (Fin.last _)).1, m) =
        boxFn ((a, m) :: bl) (bl.length + 1) rfl := by
    rw [ebx, boxFn_cons (a, m) bl bl.length rfl, Fin.snoc_last, Fin.update_snoc_last]
  have er : Function.update (boxFn ((a, top) :: bl) (bl.length + 1) h) (Fin.last _)
      (m, (boxFn ((a, top) :: bl) (bl.length + 1) h (Fin.last _)).2) =
        boxFn ((m, top) :: bl) (bl.length + 1) rfl := by
    rw [ebx, boxFn_cons (m, top) bl bl.length rfl, Fin.snoc_last, Fin.update_snoc_last]
  have key := bdP_split (P := fun q => slabP q (e1 ctx) (e2 ctx) na)
    (R := fun q => RKl q (e1 ctx) (e2 ctx) na bl) (par := par) (boxFn ((a, top) :: bl) (bl.length + 1) h)
    (Fin.last _) (c := m) (by rw [ebx, Fin.snoc_last]; exact h1.le) (by rw [ebx, Fin.snoc_last]; exact h2.le)
    (by rw [el]; exact hL) (by rw [er]; exact hR)
  have e : ((c1 + c2 : ℕ) : ℝ) / K + ε = ((c1 : ℝ) / K + ε / 2) + ((c2 : ℝ) / K + ε / 2) := by
    push_cast; ring
  rw [e]
  exact key

/-- Buchstab's identity at a floor that passes a test. -/
theorem pk_buch [RouteOK] {τ : Tests} (hτ : τ.SoundX) {ctx : Cell} (hctx : 0 < ctx.1) {na : ℕ} {x : Cell}
    {b : List Cell} {par : Bool} {f : ℕ} {cfg : Cfg} {c : ℕ} (hg : (opsK ctx na).grd (x :: b) = true)
    (hfx : f ≤ x.1) (hJ : τ.okJ (x :: b) f cfg = true) (hc : PK ctx na ((f, x.2) :: x :: b) (!par) c) :
    PK ctx na (x :: b) par c := by
  intro hna k' h ε hε
  simp only [opsK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hg
  have hlast : boxFn (x :: b) (k' + 1) h (Fin.last k') = x := by simp [boxFn]
  have hEvJ := evJP_slab hτ hctx na h (by omega) hJ
  have h2len : ((f, x.2) :: x :: b).length = k' + 1 + 1 := by simp [← h]
  have hch := hc (by simp only [List.length_cons] at hna ⊢; omega) (k' + 1) h2len ε hε
  simp only [RKl_cons _ _ _ hna.le] at hch
  have ech : boxFn ((f, x.2) :: x :: b) (k' + 1 + 1) h2len =
      Fin.snoc (α := fun _ => Cell) (boxFn (x :: b) (k' + 1) h) (f, x.2) := boxFn_cons (f, x.2) (x :: b) (k' + 1) h
  rw [ech] at hch
  have hpred : (fun (q : ℕ) (y : Fin (k' + 1 + 1) → ℕ) => slabP q (e1 ctx) (e2 ctx) na y) =
      fun q y => slabP q (e1 ctx) (e2 ctx) na (Fin.init y) := by
    funext q y
    exact propext (slabP_init q _ _ (by omega) y).symm
  refine bdP_buch (boxFn (x :: b) (k' + 1) h) (f := f) (by rw [hlast]; exact hfx) hEvJ ?_
  rw [hlast, ← hpred]
  exact hch

/-- A chain's box with no term. -/
theorem pk_vanish [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) {na : ℕ} {bl : List Cell}
    {par : Bool} (hv : vanishK ctx (chainOf na bl) = true) : PK ctx na bl par 0 := by
  intro hna k' h ε hε η hη
  obtain ⟨c, bl₀, rfl, hna0⟩ := exists_cons_of_lt hna
  rw [chainOf_cons hna0 c] at hv
  simp only [vanishK, Bool.and_eq_true, Nat.ble_eq] at hv
  obtain ⟨hv1, hv2⟩ := hv
  have hk : bl₀.length = k' := by simpa using h
  subst hk
  have hD := DEN_pos'
  filter_upwards [big_ev] with q hq a _
  obtain ⟨-, hx3, -, hN2, -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hvan : ∀ g : ℕ → ℝ, famI g (N1 q) (N2 q)
      ((famB q (boxFn (c :: bl₀) (bl₀.length + 1) h)).filter (slabP q (e1 ctx) (e2 ctx) na)) = 0 := by
    intro g
    refine famI_vanish g _ _ _ fun rt hrt => ?_
    rw [Finset.mem_filter] at hrt
    obtain ⟨hrt, hsl⟩ := hrt
    obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hrt
    have hpb := prod_set_bounds_x hx0 hc (cset na (bl₀.length + 1))
    rw [sum_cset (fun d => d.1) na (c :: bl₀) _ h, sum_cset (fun d => d.2) na (c :: bl₀) _ h,
      chainOf_cons hna0 c] at hpb
    simp only [List.map_cons, List.sum_cons] at hpb
    rw [← loSum_eq, ← hiSum_eq] at hpb
    have hprod := prod_eq_aprodR_mul na rt
    have ha0 : 0 ≤ aprodR na rt := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have hc0 : 0 ≤ ∏ i ∈ cset na (bl₀.length + 1), (rt i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have hlast : boxFn (c :: bl₀) (bl₀.length + 1) h (Fin.last _) = c := by simp [boxFn]
    constructor
    · have h1 : (∏ i, (rt i : ℝ)) ≤ xq q := by
        rw [hprod]
        calc aprodR na rt * ∏ i ∈ cset na (bl₀.length + 1), (rt i : ℝ)
            ≤ xq q ^ ((e2 ctx : ℝ) / DEN) * xq q ^ (((c.2 + hiSum (chainOf na bl₀) : ℕ) : ℝ) / DEN) :=
              mul_le_mul hsl.2 hpb.2 hc0 (Real.rpow_nonneg hx0.le _)
          _ = xq q ^ (((e2 ctx + (c.2 + hiSum (chainOf na bl₀)) : ℕ) : ℝ) / DEN) := by
              rw [← Real.rpow_add hx0]; congr 1; push_cast; ring
          _ ≤ xq q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by
              rw [div_le_one hD]
              exact_mod_cast (show e2 ctx + (c.2 + hiSum (chainOf na bl₀)) ≤ DEN by unfold e2; omega))
          _ = xq q := Real.rpow_one _
      refine Nat.le_floor ?_
      push_cast
      exact h1
    · have h3 : xq q ^ (((DEN : ℝ) + 1) / DEN) ≤ (∏ i, (rt i : ℝ)) * rt (Fin.last _) := by
        rw [hprod]
        calc xq q ^ (((DEN : ℝ) + 1) / DEN)
            ≤ xq q ^ (((e1 ctx + (c.1 + loSum (chainOf na bl₀)) + c.1 : ℕ) : ℝ) / DEN) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (div_le_div_of_nonneg_right (by
                exact_mod_cast (show DEN + 1 ≤ e1 ctx + (c.1 + loSum (chainOf na bl₀)) + c.1 by unfold e1; omega))
                hD.le)
          _ = xq q ^ ((e1 ctx : ℝ) / DEN) * xq q ^ (((c.1 + loSum (chainOf na bl₀) : ℕ) : ℝ) / DEN) *
                xq q ^ ((c.1 : ℝ) / DEN) := by
              rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; push_cast; ring
          _ ≤ aprodR na rt * (∏ i ∈ cset na (bl₀.length + 1), (rt i : ℝ)) * rt (Fin.last _) :=
              mul_le_mul (mul_le_mul hsl.1.le hpb.1 (Real.rpow_nonneg hx0.le _) ha0)
                (by have := (hc (Fin.last _)).1; rwa [hlast] at this) (Real.rpow_nonneg hx0.le _)
                (mul_nonneg ha0 hc0)
      have h4 : (N2 q : ℝ) < (((∏ i, rt i) * rt (Fin.last _) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h4
  have hd : dIP q a (boxFn (c :: bl₀) (bl₀.length + 1) h) (slabP q (e1 ctx) (e2 ctx) na) = 0 := by
    unfold dIP
    rw [hvan, hvan, sub_zero]
  have hX := Xq_pos hq
  have hRn := RKl_nonneg q (e1 ctx) (e2 ctx) na (c :: bl₀)
  have hK := K_pos'
  rw [hd, mul_zero, neg_nonpos]
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (mul_nonneg (add_nonneg (mul_nonneg (by positivity) hRn) hη.le) hX.le)

omit [Route] in
/-- The certificate's cost of a dropped chain's box is at least the bound: for any `Ω`,
`Ω/K·(∏ trB over the cells before the last)·exB(last) ≤ ⌈Ω·exF·trProd/SC^n⌉/K`. -/
theorem dropK_ge (Ω : ℕ) (c : Cell) (b : List Cell) (hc : 0 < c.1) (hb : ∀ d ∈ b, 0 < d.1) :
    (Ω : ℝ) / K * ((b.map fun d => trB d.1 (d.2 - d.1)).prod * exB c.1 (c.2 - c.1)) ≤
      (cdiv (Ω * (exF c.1 (c.2 - c.1) * trProd b)) (SC ^ (b.length + 1)) : ℝ) / K := by
  obtain ⟨hP, hP0⟩ := prod_trB_le b hb
  have hE := exB_le_exF (w := c.2 - c.1) hc
  have hE0 := SieveCert.exB_nonneg c.1 (c.2 - c.1)
  have hS := SC_pos
  have hK := K_pos'
  have h1 : (b.map fun d => trB d.1 (d.2 - d.1)).prod * exB c.1 (c.2 - c.1) ≤
      (trProd b : ℝ) / (SC : ℝ) ^ b.length * ((exF c.1 (c.2 - c.1) : ℝ) / SC) :=
    mul_le_mul hP hE hE0 (hP0.trans hP)
  have h2 : (Ω : ℝ) * ((trProd b : ℝ) / (SC : ℝ) ^ b.length * ((exF c.1 (c.2 - c.1) : ℝ) / SC)) ≤
      (cdiv (Ω * (exF c.1 (c.2 - c.1) * trProd b)) (SC ^ (b.length + 1)) : ℝ) := by
    have hpos : 0 < SC ^ (b.length + 1) := pow_pos (by unfold SC; norm_num) _
    have h3 := SieveCert.div_le_cdiv (Ω * (exF c.1 (c.2 - c.1) * trProd b)) (SC ^ (b.length + 1)) hpos
    refine le_trans (le_of_eq ?_) h3
    push_cast
    rw [pow_succ]
    field_simp
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
  exact (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)).trans h2

/-- A chain's box that is dropped. -/
theorem pk_drop [RouteOK] {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) {na : ℕ} {bl : List Cell}
    {par : Bool} {dc : ℕ} (hd : dropK ctx (chainOf na bl) par = some dc) : PK ctx na bl par dc := by
  intro hna k' h ε hε η hη
  obtain ⟨c, bl₀, rfl, hna0⟩ := exists_cons_of_lt hna
  rw [chainOf_cons hna0 c] at hd
  have hk : bl₀.length = k' := by simpa using h
  subst hk
  obtain ⟨b, hbdef⟩ : ∃ b, b = chainOf na bl₀ := ⟨_, rfl⟩
  rw [← hbdef] at hd
  simp only [dropK] at hd
  by_cases hcond : (par && cellsOK (c :: b) && Nat.ble (c.2 + hiSum b + 1) ctx.1) = true
  swap
  · rw [Bool.not_eq_true] at hcond
    rw [hcond, Bool.cond_false] at hd
    exact absurd hd (by simp)
  rw [hcond, Bool.cond_true, Option.some.injEq] at hd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
  obtain ⟨⟨hpar, hcells⟩, hfit⟩ := hcond
  subst hpar
  have hcl := (cellsOK_iff _).1 hcells
  have hc := hcl c (List.mem_cons_self ..)
  have hb : ∀ d ∈ b, 0 < d.1 ∧ d.1 < d.2 := fun d hd' => hcl d (List.mem_cons_of_mem _ hd')
  have hlohi : loSum b ≤ hiSum b := by
    have := widths_add b fun d hd' => (hb d hd').2.le
    omega
  have hD := DEN_pos'
  have hK := K_pos'
  -- the numbers of the bound
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = loSum b + (DEN - ctx.2) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = c.2 + hiSum b - (c.1 + loSum b) + (ctx.2 - ctx.1 + 1) := ⟨_, rfl⟩
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ℕ, Ω = omKw s c.1 W (c.2 - c.1) := ⟨_, rfl⟩
  rw [← hs, ← hW, ← hΩ] at hd
  have hsW : s + c.1 + W ≤ DEN := by rw [hs, hW]; omega
  have hsW2 : e2 ctx + hiSum b + c.2 ≤ s + c.1 + W := by rw [hs, hW]; unfold e2; omega
  have hs1 : s ≤ e1 ctx + loSum b := by rw [hs]; unfold e1; omega
  obtain ⟨Pb, hPb⟩ : ∃ Pb : ℝ, Pb = (b.map fun d => trB d.1 (d.2 - d.1)).prod := ⟨_, rfl⟩
  have hPb0 : 0 ≤ Pb := by
    rw [hPb]
    exact List.prod_nonneg fun x hx => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
      exact SieveCert.trB_nonneg _ _
  have hPc0 : 0 ≤ exB c.1 (c.2 - c.1) := SieveCert.exB_nonneg _ _
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = Pb * exB c.1 (c.2 - c.1) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; exact mul_nonneg hPb0 hPc0
  obtain ⟨Wc, hWc⟩ : ∃ Wc : ℝ, Wc = (Ω : ℝ) / K := ⟨_, rfl⟩
  have hWc0 : 0 ≤ Wc := by rw [hWc]; positivity
  have hfix : Wc * P ≤ (dc : ℝ) / K := by
    rw [hWc, hP, hPb, ← hd]
    exact dropK_ge Ω c b hc.1 fun d hd' => (hb d hd').1
  have hT : EvLe (fun x => TRl x b * (Real.log x * ∑ p ∈ boxP x c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p))) P := by
    rw [hP, hPb]
    exact EvLe.mul (by rw [← hPb]; exact hPb0) hPc0 (Filter.Eventually.of_forall fun x => TRl_nonneg x b)
      (ev_log_mul_nonneg fun x => boxP x c.1 (c.2 - c.1)) (evLe_TRl b fun d hd' => (hb d hd').1)
      (evLe_box_ex (w := c.2 - c.1) hc.1)
  -- the margins
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = min 1 (ε / (3 * (P + 1))) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; exact lt_min one_pos (by positivity)
  have hε₁1 : ε₁ ≤ 1 := by rw [hε₁]; exact min_le_left _ _
  have hε₁P : ε₁ * P ≤ ε / 3 := by
    have h1 : ε₁ ≤ ε / (3 * (P + 1)) := by rw [hε₁]; exact min_le_right _ _
    calc ε₁ * P ≤ ε / (3 * (P + 1)) * P := mul_le_mul_of_nonneg_right h1 hP0
      _ ≤ ε / (3 * (P + 1)) * (P + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 3 := by field_simp
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℝ, δ₁ = ε / (3 * (Wc + 1)) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  have hWδ : (Wc + 1) * δ₁ = ε / 3 := by rw [hδ₁]; field_simp
  have hkey : (Wc + ε₁) * (P + δ₁) ≤ (dc : ℝ) / K + ε := by nlinarith
  obtain ⟨z₀, hz₀⟩ := psi_le (2 * DEN / c.1) hε₁0
  have hc1' : (0 : ℝ) < c.1 := by exact_mod_cast hc.1
  filter_upwards [big_ev, SieveDrop.tendsto_xq.eventually (hT δ₁ hδ₁0),
    SieveDrop.tendsto_xq.eventually (Real.tendsto_log_atTop.eventually_gt_atTop (DEN * Real.log 2)),
    SieveDrop.tendsto_xq.eventually ((tendsto_rpow_atTop (div_pos hc1' hD)).eventually_ge_atTop (z₀ : ℝ)),
    eventually_ge_atTop 1] with q hq hTq hlx2 hxz hq1 a _
  obtain ⟨-, hx3, -, -, -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 < xq q := by linarith
  have hlx : 0 < Real.log (xq q) := Real.log_pos hx1
  have hτ : Real.log 2 / Real.log (xq q) * DEN < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hlx]; linarith
  have hX := Xq_pos hq
  have hRn := RKl_nonneg q (e1 ctx) (e2 ctx) na bl₀
  have ebx : boxFn (c :: bl₀) (bl₀.length + 1) h =
      Fin.snoc (α := fun _ => Cell) (boxFn bl₀ bl₀.length rfl) c := boxFn_cons c bl₀ bl₀.length rfl
  obtain ⟨F, hF⟩ : ∃ F, F = famK q (e1 ctx) (e2 ctx) na
      (Fin.snoc (α := fun _ => Cell) (boxFn bl₀ bl₀.length rfl) c) := ⟨_, rfl⟩
  have hdI : dIP q a (boxFn (c :: bl₀) (bl₀.length + 1) h) (slabP q (e1 ctx) (e2 ctx) na) =
      famI (gA q a) (N1 q) (N2 q) F - famI (gB q) (N1 q) (N2 q) F := by
    rw [hF, ebx]
    rfl
  have hA : 0 ≤ famI (gA q a) (N1 q) (N2 q) F := famI_nonneg (gA_nonneg q a) _ _ _
  have hprimes : ∀ rt ∈ F, ∀ i, (rt i).Prime := by
    intro rt hrt i
    rw [hF, famK, Finset.mem_filter] at hrt
    exact ((mem_famB.1 hrt.1).1 i).2
  have hB := SieveDrop.famI_gB_le q F hprimes hq1
  -- each tuple
  have hterm : ∀ rt ∈ F, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last bl₀.length)) : ℝ) ≤
      (Wc + ε₁) * (xq q / Real.log (xq q)) * ((∏ i : Fin bl₀.length, (1 / (rt i.castSucc : ℝ))) *
        (Real.log (xq q) / ((rt (Fin.last bl₀.length) : ℝ) * Real.log (rt (Fin.last bl₀.length))))) := by
    intro rt hrt
    rw [hF, famK, Finset.mem_filter] at hrt
    obtain ⟨hrt, hsl⟩ := hrt
    have hr₀ := init_mem_famB hrt
    have hsl₀ := (slabP_init q (e1 ctx) (e2 ctx) hna0 rt).2 hsl
    obtain ⟨hp₀, -, hc₀⟩ := mem_famB.1 hr₀
    have hpl := mem_primesIn.1 (last_mem_boxP hc.2.le hrt)
    obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = rt (Fin.last bl₀.length) := ⟨_, rfl⟩
    rw [← hpdef] at hpl ⊢
    have hp2 : 2 ≤ p := hpl.1.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpl.1.pos
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpl.1.one_lt)
    obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = ∏ i : Fin bl₀.length, ((Fin.init rt i : ℕ) : ℝ) := ⟨_, rfl⟩
    have hd1 : 1 ≤ d := by
      rw [hddef]
      exact Finset.one_le_prod₀ fun i _ => by exact_mod_cast (hp₀ i).2.one_lt.le
    have hd0 : 0 < d := by linarith
    have hpb := prod_set_bounds_x hx0 hc₀ (cset na bl₀.length)
    rw [sum_cset (fun d => d.1) na bl₀ _ rfl, sum_cset (fun d => d.2) na bl₀ _ rfl, ← hbdef, ← loSum_eq,
      ← hiSum_eq] at hpb
    have hdsplit : d = aprodR na (Fin.init rt) * ∏ i ∈ cset na bl₀.length, ((Fin.init rt i : ℕ) : ℝ) := by
      rw [hddef]
      exact prod_eq_aprodR_mul na (Fin.init rt)
    have ha0 : 0 ≤ aprodR na (Fin.init rt) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have hc0 : 0 ≤ ∏ i ∈ cset na bl₀.length, ((Fin.init rt i : ℕ) : ℝ) :=
      Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have hdlo : xq q ^ (((s : ℕ) : ℝ) / DEN) ≤ d := by
      rw [hdsplit]
      calc xq q ^ (((s : ℕ) : ℝ) / DEN) ≤ xq q ^ (((e1 ctx + loSum b : ℕ) : ℝ) / DEN) :=
            Real.rpow_le_rpow_of_exponent_le hx1.le
              (div_le_div_of_nonneg_right (by exact_mod_cast hs1) hD.le)
        _ = xq q ^ ((e1 ctx : ℝ) / DEN) * xq q ^ ((loSum b : ℝ) / DEN) := by
            rw [← Real.rpow_add hx0]; congr 1; push_cast; ring
        _ ≤ aprodR na (Fin.init rt) * ∏ i ∈ cset na bl₀.length, ((Fin.init rt i : ℕ) : ℝ) :=
            mul_le_mul hsl₀.1.le hpb.1 (Real.rpow_nonneg hx0.le _) ha0
    have hdhi : d ≤ xq q ^ (((e2 ctx + hiSum b : ℕ) : ℝ) / DEN) := by
      rw [hdsplit]
      calc aprodR na (Fin.init rt) * ∏ i ∈ cset na bl₀.length, ((Fin.init rt i : ℕ) : ℝ)
          ≤ xq q ^ ((e2 ctx : ℝ) / DEN) * xq q ^ ((hiSum b : ℝ) / DEN) :=
            mul_le_mul hsl₀.2 hpb.2 hc0 (Real.rpow_nonneg hx0.le _)
        _ = xq q ^ (((e2 ctx + hiSum b : ℕ) : ℝ) / DEN) := by
            rw [← Real.rpow_add hx0]; congr 1; push_cast; ring
    have hpz : z₀ ≤ p := by
      have h1 : (z₀ : ℝ) ≤ p := le_trans hxz hpl.2.1
      exact_mod_cast h1
    have hphi : (p : ℝ) ≤ xq q ^ (((c.1 : ℝ) + ((c.2 - c.1 : ℕ) : ℝ)) / DEN) := hpl.2.2.le
    have hdp : d * p ≤ xq q ^ (((s + c.1 + W : ℕ) : ℝ) / DEN) := by
      calc d * p ≤ xq q ^ (((e2 ctx + hiSum b : ℕ) : ℝ) / DEN) *
            xq q ^ (((c.1 : ℝ) + ((c.2 - c.1 : ℕ) : ℝ)) / DEN) :=
            mul_le_mul hdhi hphi hp0.le (Real.rpow_nonneg hx0.le _)
        _ = xq q ^ (((e2 ctx + hiSum b + c.2 : ℕ) : ℝ) / DEN) := by
            rw [← Real.rpow_add hx0]
            congr 1
            have e : ((c.1 : ℝ) + ((c.2 - c.1 : ℕ) : ℝ)) = (c.2 : ℝ) := by
              rw [← Nat.cast_add, Nat.add_sub_cancel' hc.2.le]
            rw [e]
            push_cast
            ring
        _ ≤ xq q ^ (((s + c.1 + W : ℕ) : ℝ) / DEN) :=
            Real.rpow_le_rpow_of_exponent_le hx1.le (div_le_div_of_nonneg_right (by exact_mod_cast hsW2) hD.le)
    have hψ := psi_point_w (s := s) (t := c.1) (W := W) (w := c.2 - c.1) (ε := ε₁) (x := xq q) (d := d) (p := p)
      hc.1 hz₀ hx1 hτ hd1 hp2 hpz (le_logDEN hx1 hdlo) (le_logDEN hx1 hpl.2.1) (logDEN_le hx1 hp0 hphi)
      (by
        rw [← add_div, ← Real.log_mul hd0.ne' hp0.ne']
        have := logDEN_le hx1 (mul_pos hd0 hp0) hdp
        push_cast at this
        exact this)
      (by exact_mod_cast hsW)
    rw [← hΩ, ← hWc] at hψ
    have hcast : ((∏ i, rt i : ℕ) : ℝ) = d * p := by
      rw [hddef, hpdef, Fin.prod_univ_castSucc]
      push_cast
      rfl
    rw [hcast]
    refine hψ.trans (le_of_eq ?_)
    have hprod : ∏ i : Fin bl₀.length, (1 / (rt i.castSucc : ℝ)) = 1 / d := by
      rw [hddef, Finset.prod_div_distrib, Finset.prod_const_one]
      rfl
    rw [hprod]
    have := hlx.ne'
    have := hlp.ne'
    field_simp
  -- the sum
  have hsum : ∑ rt ∈ F, (∏ i : Fin bl₀.length, (1 / (rt i.castSucc : ℝ))) *
      (Real.log (xq q) / ((rt (Fin.last bl₀.length) : ℝ) * Real.log (rt (Fin.last bl₀.length)))) ≤
        RKl q (e1 ctx) (e2 ctx) na bl₀ * (P + δ₁) := by
    rw [hF]
    have h1 := famK_snoc_sum_le (q := q) (e₁ := e1 ctx) (e₂ := e2 ctx) hna0 (boxFn bl₀ bl₀.length rfl) c hc.2.le
      (fun p => Real.log (xq q) / ((p : ℝ) * Real.log p))
      (fun p => div_nonneg hlx.le (mul_nonneg (Nat.cast_nonneg p) (Real.log_natCast_nonneg p)))
    refine h1.trans ?_
    have h2 := Wsum_chain_le q (e1 ctx) (e2 ctx) na bl₀ hna0 (by rw [← hbdef]; exact fun d hd' => (hb d hd').2.le)
    rw [← hbdef] at h2
    have h3 : ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), Real.log (xq q) / ((p : ℝ) * Real.log p) =
        Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have h4 : 0 ≤ Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p) :=
      mul_nonneg hlx.le (Finset.sum_nonneg fun p _ =>
        div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg p) (Real.log_natCast_nonneg p)))
    rw [h3]
    calc (∑ r ∈ famK q (e1 ctx) (e2 ctx) na (boxFn bl₀ bl₀.length rfl), ∏ i, (1 / (r i : ℝ))) *
          (Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p))
        ≤ RKl q (e1 ctx) (e2 ctx) na bl₀ * TRl (xq q) b *
          (Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p)) :=
          mul_le_mul_of_nonneg_right h2 h4
      _ = RKl q (e1 ctx) (e2 ctx) na bl₀ * (TRl (xq q) b *
          (Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p))) := by ring
      _ ≤ RKl q (e1 ctx) (e2 ctx) na bl₀ * (P + δ₁) := mul_le_mul_of_nonneg_left hTq hRn
  have hΨ : ∑ rt ∈ F, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last bl₀.length)) : ℝ) ≤
      ((dc : ℝ) / K + ε) * RKl q (e1 ctx) (e2 ctx) na bl₀ * Xq q := by
    have hxl : 0 ≤ xq q / Real.log (xq q) := (div_pos hx0 hlx).le
    calc ∑ rt ∈ F, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last bl₀.length)) : ℝ)
        ≤ ∑ rt ∈ F, (Wc + ε₁) * (xq q / Real.log (xq q)) * ((∏ i : Fin bl₀.length, (1 / (rt i.castSucc : ℝ))) *
            (Real.log (xq q) / ((rt (Fin.last bl₀.length) : ℝ) * Real.log (rt (Fin.last bl₀.length))))) :=
          Finset.sum_le_sum hterm
      _ = (Wc + ε₁) * (xq q / Real.log (xq q)) * ∑ rt ∈ F, (∏ i : Fin bl₀.length, (1 / (rt i.castSucc : ℝ))) *
            (Real.log (xq q) / ((rt (Fin.last bl₀.length) : ℝ) * Real.log (rt (Fin.last bl₀.length)))) := by
          rw [Finset.mul_sum]
      _ ≤ (Wc + ε₁) * (xq q / Real.log (xq q)) * (RKl q (e1 ctx) (e2 ctx) na bl₀ * (P + δ₁)) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hxl)
      _ = (Wc + ε₁) * (P + δ₁) * RKl q (e1 ctx) (e2 ctx) na bl₀ * Xq q := by unfold Xq; ring
      _ ≤ ((dc : ℝ) / K + ε) * RKl q (e1 ctx) (e2 ctx) na bl₀ * Xq q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hRn) hX.le
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  rw [RKl_cons q _ _ hna0 c, hdI]
  simp only [sg, ite_true, one_mul]
  have h5 : (q.totient : ℝ)⁻¹ * ∑ rt ∈ F, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last bl₀.length)) : ℝ) ≤
      (q.totient : ℝ)⁻¹ * ((((dc : ℝ) / K + ε) * RKl q (e1 ctx) (e2 ctx) na bl₀ + η) * Xq q) := by
    refine mul_le_mul_of_nonneg_left (hΨ.trans ?_) hφ
    nlinarith [mul_nonneg hη.le hX.le]
  linarith

/-! ### The search of the tree is sound -/

/-- **The nodes of the tree of a reversed term prove `PK`**, for tests that are sound under two more atoms and a
cell `ctx` with `0 < l₁ ≤ h₁ ≤ DEN`. -/
theorem rulesK [RouteOK] {τ : Tests} (hτ : τ.SoundX) {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN)
    (na : ℕ) : Rules (opsK ctx na) τ (PK ctx na) where
  van := fun _ hv => pk_vanish hctx hv
  evl := fun hg hI => pk_eval hτ hctx.1 hg hI
  drp := fun _ hd => pk_drop hctx hd
  alt := fun _ h => absurd h (lt_irrefl _)
  split := fun h1 h2 hl hr => pk_split h1 h2 hl hr
  buch := fun hg _ hfx hJ hc => pk_buch hτ hctx.1 hg hfx hJ hc

/-- **The search of the tree of a reversed term is sound**: a cost that it returns below its limit has `PK`. -/
theorem solveK_sound [RouteOK] {τ : Tests} (hτ : τ.SoundX) {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (na : ℕ) (S : Strat) (n : ℕ) :
    RecP (PK ctx na) (solveG (opsK ctx na) τ S n) :=
  solveG_sound (rulesK hτ hctx na) S n

/-- Buchstab's identity between two floors: the terms of a box at the level of its last prime's lower end are the
terms at a floor `f` below it, minus the term of the box with one more prime in `[x^{f/DEN}, x^{lo/DEN})`. -/
theorem dJP_level {q : ℕ} (hx : 1 ≤ xq q) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) {f : ℕ}
    (hf : f ≤ (bx (Fin.last k')).1) (hlh : (bx (Fin.last k')).1 ≤ (bx (Fin.last k')).2)
    (P : (Fin (k' + 1) → ℕ) → Prop) :
    dJP q a (bx (Fin.last k')).1 bx P = dJP q a f bx P -
      dIP q a (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).1)) (fun y => P (Fin.init y)) := by
  have h1 := dIP_buch hx a bx hf P
  have h2 := dIP_buch hx a bx (le_refl (bx (Fin.last k')).1) P
  have h3 := dIP_cut hx a (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2)) (Fin.last (k' + 1))
    (c := (bx (Fin.last k')).1) (by rw [Fin.snoc_last]; exact hf) (by rw [Fin.snoc_last]; exact hlh)
    (fun y => P (Fin.init y))
  rw [Fin.snoc_last, Fin.update_snoc_last, Fin.update_snoc_last] at h3
  linarith

/-- **The cost of the terms of an atoms' box at its level.** For tests that are sound under two more atoms: if
`rootJ` returns a cost `C` below its limit on the atoms' box `c :: b` of at most twelve cells, with `c.1 ≤ c.2`,
then the terms of the box under the condition, at the floor `x^{c.1/DEN}`, are at most
`((C/K + ε)·Σ 1/r' + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set, for every `ε > 0`. -/
theorem rootJ_sound [RouteOK] {τ : Tests} (hτ : τ.SoundX) {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (S : Strat) (fuel : ℕ) (c : Cell) (b : List Cell)
    (hc : c.1 ≤ c.2) (hlen : b.length + 1 ≤ 12) {lim : ℕ} (h : rootJ τ S ctx fuel (c :: b) lim < lim) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
      dJP q a c.1 (boxFn (c :: b) (b.length + 1) rfl) (slabP q (e1 ctx) (e2 ctx) (b.length + 1)) ≤
        (q.totient : ℝ)⁻¹ * ((((rootJ τ S ctx fuel (c :: b) lim : ℝ) / K + ε) *
          Wsum q (e1 ctx) (e2 ctx) (b.length + 1) (c :: b) + η) * Xq q) := by
  intro ε hε η hη
  have hK := K_pos'
  have hlast : boxFn (c :: b) (b.length + 1) rfl (Fin.last b.length) = c := by simp [boxFn]
  unfold rootJ at h ⊢
  cases hJ : firstJ τ (c :: b) c.1 (S.propJ (c :: b)) with
  | none =>
    simp only [hJ] at h
    omega
  | some f =>
    simp only [hJ] at h ⊢
    obtain ⟨-, hfc, cfg, hok⟩ := firstJ_some hJ
    by_cases hcf : Nat.ble c.1 f = true
    · rw [hcf, Bool.cond_true]
      rw [Nat.ble_eq] at hcf
      have hfeq : f = c.1 := le_antisymm hfc hcf
      subst hfeq
      have hEv := evJP_slab hτ hctx.1 (b.length + 1) (bl := c :: b) (k := b.length + 1) rfl hlen hok
      filter_upwards [hEv η hη, big_ev] with q hq hbig a ha
      have hX := Xq_pos hbig
      have hW := Wsum_nonneg q (e1 ctx) (e2 ctx) (b.length + 1) (c :: b)
      have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
      have h1 := (le_abs_self _).trans (hq a ha)
      refine h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hX.le) hφ)
      simp only [Nat.cast_zero, zero_div, zero_add]
      nlinarith
    · rw [Bool.not_eq_true] at hcf
      rw [hcf, Bool.cond_false] at h ⊢
      have hfc' : f < c.1 := by
        by_contra hge
        have : Nat.ble c.1 f = true := by rw [Nat.ble_eq]; omega
        rw [this] at hcf
        exact absurd hcf (by simp)
      obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = kids (solveG (opsK ctx (Nat.succ b.length)) τ S fuel) c.1 (c :: b) true
          (S.cuts (c :: b) f) f lim := ⟨_, rfl⟩
      rw [← hCdef] at h ⊢
      have hPK : PK ctx (b.length + 1) ((f, c.1) :: c :: b) true C := by
        rw [hCdef]
        exact kidsP_sound (rulesK hτ hctx (b.length + 1)).split (solveK_sound hτ hctx (b.length + 1) S fuel)
          c.1 (c :: b) true _ f lim (by rw [← hCdef]; exact h)
      have h2len : ((f, c.1) :: c :: b).length = b.length + 1 + 1 := by simp
      have hch := hPK (by simp) (b.length + 1) h2len ε hε
      simp only [RKl_cons _ _ _ (show b.length + 1 ≤ (c :: b).length by simp)] at hch
      have ech : boxFn ((f, c.1) :: c :: b) (b.length + 1 + 1) h2len =
          Fin.snoc (α := fun _ => Cell) (boxFn (c :: b) (b.length + 1) rfl) (f, c.1) :=
        boxFn_cons (f, c.1) (c :: b) (b.length + 1) rfl
      rw [ech] at hch
      have hEv := evJP_slab hτ hctx.1 (b.length + 1) (bl := c :: b) (k := b.length + 1) rfl hlen hok
      have hR : ∀ q, RKl q (e1 ctx) (e2 ctx) (b.length + 1) (c :: b) =
          Wsum q (e1 ctx) (e2 ctx) (b.length + 1) (c :: b) := by
        intro q
        unfold RKl
        rw [atomsOf_of_le (by simp)]
      filter_upwards [hEv (η / 2) (by positivity), hch (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig a ha
      obtain ⟨-, hx3, -⟩ := big_facts hbig
      have h1 := (le_abs_self _).trans (hq1 a ha)
      have h2 := hq2 a ha
      simp only [sg, ite_true, one_mul] at h2
      rw [hR q] at h2
      have hlev := dJP_level (q := q) (by linarith) a (boxFn (c :: b) (b.length + 1) rfl) (f := f)
        (by rw [hlast]; exact hfc) (by rw [hlast]; exact hc) (slabP q (e1 ctx) (e2 ctx) (b.length + 1))
      rw [hlast] at hlev
      have hpred : (fun (y : Fin (b.length + 1 + 1) → ℕ) => slabP q (e1 ctx) (e2 ctx) (b.length + 1) (Fin.init y)) =
          fun y => slabP q (e1 ctx) (e2 ctx) (b.length + 1) y := by
        funext y
        exact propext (slabP_init q _ _ (le_refl _) y)
      have hlev' : dJP q a c.1 (boxFn (c :: b) (b.length + 1) rfl) (slabP q (e1 ctx) (e2 ctx) (b.length + 1)) =
          dJP q a f (boxFn (c :: b) (b.length + 1) rfl) (slabP q (e1 ctx) (e2 ctx) (b.length + 1)) -
            dIP q a (Fin.snoc (α := fun _ => Cell) (boxFn (c :: b) (b.length + 1) rfl) (f, c.1))
              (slabP q (e1 ctx) (e2 ctx) (b.length + 1)) := by
        rw [hlev, hpred]
      rw [hlev']
      have e : (q.totient : ℝ)⁻¹ * ((((C : ℝ) / K + ε) * Wsum q (e1 ctx) (e2 ctx) (b.length + 1) (c :: b) + η) *
          Xq q) = (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ *
            ((((C : ℝ) / K + ε) * Wsum q (e1 ctx) (e2 ctx) (b.length + 1) (c :: b) + η / 2) * Xq q) := by ring
      rw [e]
      linarith

end SieveAd

#print axioms SieveAd.solveK_sound
#print axioms SieveAd.rootJ_sound
