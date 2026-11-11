/-
# A tree of Buchstab steps on boxes of cells: what a tree that passes the check gives

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The trees, their check `ok` and their cost are `SieveAdDefs.lean`'s. For a route (`SieveRoute.Route`,
with `x = q^L`, `N₁ = ⌊x⌋`, `N₂ = ⌊2x⌋`), `famB q bx` is the family of the box `bx`: the strictly decreasing tuples of
primes up to `N₂` whose `i`-th prime has its exponent in the cell `bx i`, that is `x^{lo_i/DEN} ≤ p_i < x^{hi_i/DEN}`.

* `famI_cut`, `famI_buch`, `famI_vanish_box`: the exact steps of a tree. The term of a box is the sum of the terms
  of its two parts under a cut of a cell; it is `Σ S(A_r, z) − Σ S(A_{rp}, p)` for a floor `z = ⌈x^{f/DEN}⌉` at
  most the last prime's least value, the second sum being the term of the box with one more cell `(f, hi_last)`;
  and it is `0` at a large modulus when the upper ends sum to at most `DEN − 1` and the lower ends, with the last
  one twice, to at least `DEN + 1`.
* `drop_bound`, `dropCost_ge`: for a box whose cells have `0 < lo ≤ hi` and whose upper ends sum to at most `DEN`,
  the term in the comparison set is at most `(B + δ)x/(φ(q) log x)` for large `q`, with `B` the bound of
  `SieveRough.shareBox`; the certificate's `dropCost/K` is such a `B`.
* `shareBd`, `dropB_bound`, `dropBCost_ge`: for a box of two primes at least whose lower ends, with the last one
  twice, sum to at least `DEN + 1`, the only terms are the products `n = p₁⋯p_k` themselves, since a cofactor's
  primes are at least the last prime. The last prime is then a prime of `(x/r', 2x/r']`, `r'` the product of the
  others; so for upper ends of the others that sum to `s < DEN`, the term in the comparison set is at most
  `(B + δ)x/(φ(q) log x)` for large `q`, with `B = DEN/(DEN − s)·Π trB`; the certificate's `dropBCost/K` is such
  a `B`.
* `Tests.Sound`: the tests are sound when a box that passes `okI` has its term evaluated (`EvI`: its versions in
  `𝒜` and in the comparison set differ by `o(x/(φ(q) log x))`), and one that passes `okJ` at a floor has its terms
  at that floor evaluated (`EvJ`).
* `sound`: for sound tests, a tree that passes `ok` on a box, for a term of the sign `par`, has the term, with that
  sign, at least `−(cost/K + o(1))x/(φ(q) log x)` (`Bd`). By induction on the tree.
* `Ttop_eq`, `Ttop_gB_ge`: the root. With `z_top = ⌈x^{(DEN/2+1)/DEN}⌉`, above `√(2x)`,
  `S(·, z_top) = S(·, z) − Σ_{z ≤ p < z_top} S(·_p, p)`, the second sum being the term of the box of one prime with
  the cell `(f₀, DEN/2 + 1)`; and `S(ℬ, z_top) ≥ φ(q)⁻¹((1 − ε)x/log x − q)` for large `q`.
* `linnik_large_tree`, `linnik_tree`: **the theorem from a tree.** For a route with `RouteOK` and sound tests: if
  the terms at the floor of the box with no prime pass `okJ`, the tree passes `ok` on the box of one prime, for a
  term of the sign `−`, and its cost is below `K`, then for large `q` every class prime to `q` has a prime in
  `(q^L, 2q^L]`, and for every `q` one at most `K'q^L`.

No test is proved sound here: the file is the part of a certificate that does not depend on the estimates.

The file imports `SieveAdDefs.lean`, `SieveBox.lean`, `SieveDrop.lean` and `SieveMain2.lean`.
-/
import SieveAdDefs
import SieveBox
import SieveDrop
import SieveMain2

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K omKw cdiv trB exB DEN_pos' K_pos')

/-! ### The cells of a list, by the prime's index -/

/-- The cells of a list as a function of the prime's index: the list has the newest prime first. -/
def boxFn (bl : List Cell) (k : ℕ) (h : bl.length = k) : Fin k → Cell :=
  fun i => bl[k - 1 - (i : ℕ)]'(by have := i.2; omega)

theorem getElem_cons_of_eq {x : Cell} {bl : List Cell} {m n : ℕ} (hm : m < (x :: bl).length) (hn : n < bl.length)
    (h : m = n + 1) : (x :: bl)[m] = bl[n] := by
  subst h
  rfl

/-- One more cell, for a new prime, is the last value of the box. -/
theorem boxFn_cons (x : Cell) (bl : List Cell) (k : ℕ) (h : bl.length = k) :
    boxFn (x :: bl) (k + 1) (by simp [h]) = Fin.snoc (α := fun _ => Cell) (boxFn bl k h) x := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [boxFn]
  | cast j =>
    simp only [boxFn, Fin.snoc_castSucc, Fin.val_castSucc]
    have hj := j.2
    exact getElem_cons_of_eq _ _ (by omega)

/-- A cell replaced at the position `t` of the list is the value at the index `k − 1 − t` replaced. -/
theorem boxFn_set (bl : List Cell) (k : ℕ) (h : bl.length = k) (t : ℕ) (ht : t < k) (c : Cell) :
    boxFn (bl.set t c) k (by simp [h]) = Function.update (boxFn bl k h) ⟨k - 1 - t, by omega⟩ c := by
  funext i
  have hi := i.2
  simp only [boxFn, List.getElem_set, Function.update_apply]
  by_cases hti : t = k - 1 - (i : ℕ)
  · have : i = ⟨k - 1 - t, by omega⟩ := Fin.ext (by simp only; omega)
    simp only [eq_true hti, eq_true this, ite_true]
  · have : i ≠ ⟨k - 1 - t, by omega⟩ := fun e => hti (by rw [e]; simp only; omega)
    simp only [eq_false hti, eq_false this, ite_false]

/-- The cell at the position `t` of the list. -/
theorem getC_eq (bl : List Cell) (k : ℕ) (h : bl.length = k) (t : ℕ) (ht : t < k) :
    getC bl t = boxFn bl k h ⟨k - 1 - t, by omega⟩ := by
  unfold getC boxFn
  rw [List.getD_eq_getElem _ _ (by omega)]
  congr 1
  simp only
  omega

/-! ### The products of a box in a dyadic range -/

/-- Over the tuples of primes in the intervals `[x^{a_t/DEN}, x^{(a_t+w_t)/DEN})`, the number of primes in
`(x/r', 2x/r']`, `r'` the tuple's product. -/
noncomputable def SBd (x : ℝ) {m : ℕ} (a w : Fin m → ℕ) : ℝ :=
  ∑ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)),
    (((Finset.Ioc ⌊x / (∏ t, rt t : ℕ)⌋₊ ⌊2 * (x / (∏ t, rt t : ℕ))⌋₊).filter Nat.Prime).card : ℝ)

/-- **The products of a box in `(x, 2x]`.** For `m` intervals with positive lower ends whose upper ends sum to
`s < DEN`, and `B ≥ DEN/(DEN − s)·∏_t trB(a_t, w_t)`: for every `δ > 0`, eventually
`SBd x a w ≤ (B + δ)·x/log x`. The primes of `(y, 2y]` number at most `(1 + ε)y/log y`, and `y = x/r'` is at
least `x^{(DEN−s)/DEN}`. -/
theorem shareBd {m : ℕ} (a w : Fin m → ℕ) (ha : ∀ t, 0 < a t) (hfit : ∑ t, (a t + w t) < DEN) {B : ℝ}
    (hB : (DEN : ℝ) / ((DEN - ∑ t, (a t + w t) : ℕ) : ℝ) * ∏ t, trB (a t) (w t) ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, SBd x a w ≤ (B + δ) * (x / Real.log x) := by
  have hD := DEN_pos'
  set s : ℕ := ∑ t, (a t + w t) with hs
  have hsD : (s : ℝ) < DEN := by exact_mod_cast hfit
  have hcast : ((DEN - s : ℕ) : ℝ) = (DEN : ℝ) - s := Nat.cast_sub hfit.le
  have hd0 : (0 : ℝ) < (DEN : ℝ) - s := by linarith
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (DEN : ℝ) / ((DEN : ℝ) - s) := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hW]; positivity
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = ((DEN : ℝ) - s) / DEN := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hWβ : W * β = 1 := by rw [hW, hβ]; field_simp
  have hPt : ∀ t, (0 : ℝ) ≤ trB (a t) (w t) := fun t => SieveCert.trB_nonneg _ _
  have hR := SieveRough.EvLe.prod (fun t x => ∑ p ∈ boxP x (a t) (w t), 1 / (p : ℝ)) (fun t => trB (a t) (w t)) hPt
    (fun t => Filter.Eventually.of_forall fun x => SieveRough.sum_inv_nonneg _) (fun t => evLe_box_tr (ha t))
  rw [hcast, ← hW] at hB
  refine SieveRough.evLe_finish hW0.le (Finset.prod_nonneg fun t _ => hPt t) hB hR (fun ε hε => ?_) hδ
  obtain ⟨y₀, hy₀⟩ := SieveRough.card_primes_dyadic (ε := ε / W) (by positivity)
  filter_upwards [eventually_gt_atTop 1, (tendsto_rpow_atTop hβ0).eventually_ge_atTop (max y₀ 1)] with x hx1 hxβ
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hterm : ∀ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)),
      (((Finset.Ioc ⌊x / (∏ t, rt t : ℕ)⌋₊ ⌊2 * (x / (∏ t, rt t : ℕ))⌋₊).filter Nat.Prime).card : ℝ) ≤
        (W + ε) * (x / Real.log x) * ∏ t, (1 / (rt t : ℝ)) := by
    intro rt hrt
    rw [Fintype.mem_piFinset] at hrt
    have hmem := fun t => mem_primesIn.1 (hrt t)
    have hpos : ∀ t, (0 : ℝ) < rt t := fun t => by exact_mod_cast (hmem t).1.pos
    have hr0 : (0 : ℝ) < ∏ t, (rt t : ℝ) := Finset.prod_pos fun t _ => hpos t
    have hrle : ∏ t, (rt t : ℝ) ≤ x ^ ((s : ℝ) / DEN) := by
      rw [hs, Nat.cast_sum, Finset.sum_div, Real.rpow_sum_of_pos hx0]
      refine Finset.prod_le_prod₀ (fun t _ => (hpos t).le) fun t _ => ?_
      have := (hmem t).2.2.le
      rwa [← Nat.cast_add] at this
    have hrcast : ((∏ t, rt t : ℕ) : ℝ) = ∏ t, (rt t : ℝ) := by push_cast; rfl
    rw [hrcast]
    set r : ℝ := ∏ t, (rt t : ℝ) with hr
    -- `y = x/r ≥ x^β`
    have hy : x ^ β ≤ x / r := by
      rw [le_div_iff₀ hr0]
      calc x ^ β * r ≤ x ^ β * x ^ ((s : ℝ) / DEN) := mul_le_mul_of_nonneg_left hrle (Real.rpow_nonneg hx0.le _)
        _ = x := by
          rw [← Real.rpow_add hx0, hβ]
          have : ((DEN : ℝ) - s) / DEN + (s : ℝ) / DEN = 1 := by
            rw [← add_div, sub_add_cancel, div_self hD.ne']
          rw [this, Real.rpow_one]
    have hy0 : y₀ ≤ x / r := le_trans (le_trans (le_max_left _ _) hxβ) hy
    have hy1 : 1 ≤ x / r := le_trans (le_trans (le_max_right _ _) hxβ) hy
    have hcard := hy₀ (x / r) hy0
    have hlog : β * Real.log x ≤ Real.log (2 * (x / r)) := by
      rw [← Real.log_rpow hx0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) (by linarith)
    have hlog0 : 0 < Real.log (2 * (x / r)) := lt_of_lt_of_le (mul_pos hβ0 hlx) hlog
    refine hcard.trans ?_
    rw [div_le_iff₀ hlog0]
    have e1 : (W + ε) * (x / Real.log x) * ∏ t, (1 / (rt t : ℝ)) = (1 + ε / W) * (x / r) * (W / Real.log x) := by
      rw [Finset.prod_div_distrib, Finset.prod_const_one, ← hr]
      have h1 : (1 + ε / W) * W = W + ε := by field_simp
      rw [← h1]
      ring
    rw [e1]
    have hnn : 0 ≤ (1 + ε / W) * (x / r) := by positivity
    have h2 : 1 ≤ W / Real.log x * Real.log (2 * (x / r)) := by
      have : W / Real.log x * (β * Real.log x) = 1 := by
        rw [div_mul_eq_mul_div, ← mul_assoc, hWβ, one_mul, div_self hlx.ne']
      calc (1 : ℝ) = W / Real.log x * (β * Real.log x) := this.symm
        _ ≤ W / Real.log x * Real.log (2 * (x / r)) := mul_le_mul_of_nonneg_left hlog (by positivity)
    calc (1 + ε / W) * (x / r) = (1 + ε / W) * (x / r) * 1 := by ring
      _ ≤ (1 + ε / W) * (x / r) * (W / Real.log x * Real.log (2 * (x / r))) := mul_le_mul_of_nonneg_left h2 hnn
      _ = (1 + ε / W) * (x / r) * (W / Real.log x) * Real.log (2 * (x / r)) := by ring
  calc SBd x a w ≤ ∑ rt ∈ Fintype.piFinset (fun t => boxP x (a t) (w t)),
        (W + ε) * (x / Real.log x) * ∏ t, (1 / (rt t : ℝ)) := Finset.sum_le_sum hterm
    _ = (W + ε) * (x / Real.log x) * ∏ t, ∑ p ∈ boxP x (a t) (w t), 1 / (p : ℝ) := by
        rw [← Finset.mul_sum, Finset.prod_univ_sum]

/-! ### Sums and products over a box, by its list -/

theorem sum_boxFn {M : Type*} [AddCommMonoid M] (F : Cell → M) :
    ∀ (bl : List Cell) (k : ℕ) (h : bl.length = k), ∑ i : Fin k, F (boxFn bl k h i) = (bl.map F).sum := by
  intro bl
  induction bl with
  | nil =>
    intro k h
    subst h
    simp
  | cons x bl ih =>
    intro k h
    subst h
    show ∑ i : Fin (bl.length + 1), F (boxFn (x :: bl) (bl.length + 1) rfl i) = _
    rw [boxFn_cons x bl bl.length rfl, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, ih bl.length rfl, List.map_cons, List.sum_cons]
    rw [add_comm]

theorem prod_boxFn {M : Type*} [CommMonoid M] (F : Cell → M) :
    ∀ (bl : List Cell) (k : ℕ) (h : bl.length = k), ∏ i : Fin k, F (boxFn bl k h i) = (bl.map F).prod := by
  intro bl
  induction bl with
  | nil =>
    intro k h
    subst h
    simp
  | cons x bl ih =>
    intro k h
    subst h
    show ∏ i : Fin (bl.length + 1), F (boxFn (x :: bl) (bl.length + 1) rfl i) = _
    rw [boxFn_cons x bl bl.length rfl, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, ih bl.length rfl, List.map_cons, List.prod_cons]
    rw [mul_comm]

theorem loSum_eq (bl : List Cell) : loSum bl = (bl.map Prod.fst).sum := by
  induction bl with
  | nil => rfl
  | cons x bl ih => simp [loSum, ih]

theorem hiSum_eq (bl : List Cell) : hiSum bl = (bl.map Prod.snd).sum := by
  induction bl with
  | nil => rfl
  | cons x bl ih => simp [hiSum, ih]

theorem cellsOK_iff (bl : List Cell) : cellsOK bl = true ↔ ∀ c ∈ bl, 0 < c.1 ∧ c.1 < c.2 := by
  induction bl with
  | nil => simp [cellsOK]
  | cons x bl ih => simp [cellsOK, ih, Nat.blt_eq, and_assoc]

theorem boxFn_mem (bl : List Cell) (k : ℕ) (h : bl.length = k) (i : Fin k) : boxFn bl k h i ∈ bl :=
  List.getElem_mem _

/-- The widths' sum is the upper ends' sum minus the lower ends'. -/
theorem widths_add (bl : List Cell) (h : ∀ c ∈ bl, c.1 ≤ c.2) :
    (bl.map fun c => c.2 - c.1).sum + loSum bl = hiSum bl := by
  induction bl with
  | nil => rfl
  | cons x bl ih =>
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [List.map_cons, List.sum_cons, loSum, hiSum]
    omega

/-! ### The cost of a dropped box, in fixed point -/

theorem SC_pos : (0 : ℝ) < SC := by unfold SC; positivity

/-- `trB ≤ trF/SC`. -/
theorem trB_le_trF {a w : ℕ} (ha : 0 < a) : trB a w ≤ (trF a w : ℝ) / SC := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h := SieveCert.div_le_cdiv (SC * (w * (2 * a + w))) (2 * a * (a + w)) (by positivity)
  rw [le_div_iff₀ SC_pos]
  unfold trF trB
  push_cast at h ⊢
  calc (w : ℝ) * (2 * a + w) / (2 * a * (a + w)) * SC = SC * (w * (2 * a + w)) / (2 * a * (a + w)) := by ring
    _ ≤ _ := h

/-- `exB ≤ exF/SC`. -/
theorem exB_le_exF {a w : ℕ} (ha : 0 < a) : exB a w ≤ (exF a w : ℝ) / SC := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h := SieveCert.div_le_cdiv (SC * (DEN * w)) (a * (a + w)) (by positivity)
  rw [le_div_iff₀ SC_pos]
  unfold exF exB
  push_cast at h ⊢
  calc (DEN : ℝ) * w / (a * (a + w)) * SC = SC * (DEN * w) / (a * (a + w)) := by ring
    _ ≤ _ := h

/-- The product of the cells' `trB` is at most `trProd/SC^n`. -/
theorem prod_trB_le (bl : List Cell) (h : ∀ c ∈ bl, 0 < c.1) :
    (bl.map fun c => trB c.1 (c.2 - c.1)).prod ≤ (trProd bl : ℝ) / (SC : ℝ) ^ bl.length ∧
      0 ≤ (bl.map fun c => trB c.1 (c.2 - c.1)).prod := by
  induction bl with
  | nil => simp [trProd]
  | cons x bl ih =>
    obtain ⟨h1, h0⟩ := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hx := trB_le_trF (w := x.2 - x.1) (h x (List.mem_cons_self ..))
    have hx0 := SieveCert.trB_nonneg x.1 (x.2 - x.1)
    have hS := SC_pos
    constructor
    · simp only [List.map_cons, List.prod_cons, trProd, List.length_cons, Nat.cast_mul]
      calc trB x.1 (x.2 - x.1) * (bl.map fun c => trB c.1 (c.2 - c.1)).prod
          ≤ (trF x.1 (x.2 - x.1) : ℝ) / SC * ((trProd bl : ℝ) / (SC : ℝ) ^ bl.length) :=
            mul_le_mul hx h1 h0 (hx0.trans hx)
        _ = (trF x.1 (x.2 - x.1) : ℝ) * (trProd bl : ℝ) / (SC : ℝ) ^ (bl.length + 1) := by
            rw [pow_succ]
            field_simp
    · simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg hx0 h0

/-- **The certificate's cost of a dropped box** is at least the bound of `SieveRough.shareBox`. -/
theorem dropCost_ge (bl : List Cell) (m : ℕ) (h : bl.length = m + 1) (hok : cellsOK bl = true) :
    (omKw (∑ t : Fin m, (boxFn bl (m + 1) h t.castSucc).1) (boxFn bl (m + 1) h (Fin.last m)).1
        (∑ i, ((boxFn bl (m + 1) h i).2 - (boxFn bl (m + 1) h i).1))
        ((boxFn bl (m + 1) h (Fin.last m)).2 - (boxFn bl (m + 1) h (Fin.last m)).1) : ℝ) / K *
      ((∏ t : Fin m, trB (boxFn bl (m + 1) h t.castSucc).1
          ((boxFn bl (m + 1) h t.castSucc).2 - (boxFn bl (m + 1) h t.castSucc).1)) *
        exB (boxFn bl (m + 1) h (Fin.last m)).1
          ((boxFn bl (m + 1) h (Fin.last m)).2 - (boxFn bl (m + 1) h (Fin.last m)).1)) ≤
      (dropCost bl : ℝ) / K := by
  obtain ⟨c, b, rfl⟩ : ∃ c b, bl = c :: b := by
    cases bl with
    | nil => simp at h
    | cons c b => exact ⟨c, b, rfl⟩
  have hm : b.length = m := by simpa using h
  subst hm
  have hcells := (cellsOK_iff _).1 hok
  have hc := hcells c (List.mem_cons_self ..)
  have hb : ∀ d ∈ b, 0 < d.1 ∧ d.1 < d.2 := fun d hd => hcells d (List.mem_cons_of_mem _ hd)
  have hbox : boxFn (c :: b) (b.length + 1) h = Fin.snoc (α := fun _ => Cell) (boxFn b b.length rfl) c :=
    boxFn_cons c b b.length rfl
  have e1 : ∑ t : Fin b.length, (boxFn (c :: b) (b.length + 1) h t.castSucc).1 = loSum b := by
    rw [hbox]
    simp only [Fin.snoc_castSucc]
    rw [sum_boxFn (fun d => d.1), loSum_eq]
  have e2 : (boxFn (c :: b) (b.length + 1) h (Fin.last b.length)) = c := by
    rw [hbox, Fin.snoc_last]
  have e3 : ∑ i, ((boxFn (c :: b) (b.length + 1) h i).2 - (boxFn (c :: b) (b.length + 1) h i).1) =
      c.2 + hiSum b - (c.1 + loSum b) := by
    rw [hbox, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [sum_boxFn (fun d => d.2 - d.1)]
    have := widths_add b fun d hd => (hb d hd).2.le
    omega
  have e4 : ∏ t : Fin b.length, trB (boxFn (c :: b) (b.length + 1) h t.castSucc).1
      ((boxFn (c :: b) (b.length + 1) h t.castSucc).2 - (boxFn (c :: b) (b.length + 1) h t.castSucc).1) =
      (b.map fun d => trB d.1 (d.2 - d.1)).prod := by
    rw [hbox]
    simp only [Fin.snoc_castSucc]
    rw [prod_boxFn (fun d => trB d.1 (d.2 - d.1))]
  rw [e1, e2, e3, e4]
  obtain ⟨hP, hP0⟩ := prod_trB_le b fun d hd => (hb d hd).1
  have hE := exB_le_exF (w := c.2 - c.1) hc.1
  have hE0 := SieveCert.exB_nonneg c.1 (c.2 - c.1)
  have hS := SC_pos
  have hK := K_pos'
  set om : ℕ := omKw (loSum b) c.1 (c.2 + hiSum b - (c.1 + loSum b)) (c.2 - c.1) with hom
  have h1 : (b.map fun d => trB d.1 (d.2 - d.1)).prod * exB c.1 (c.2 - c.1) ≤
      (trProd b : ℝ) / (SC : ℝ) ^ b.length * ((exF c.1 (c.2 - c.1) : ℝ) / SC) :=
    mul_le_mul hP hE hE0 (hP0.trans hP)
  have h2 : (om : ℝ) * ((trProd b : ℝ) / (SC : ℝ) ^ b.length * ((exF c.1 (c.2 - c.1) : ℝ) / SC)) ≤
      (dropCost (c :: b) : ℝ) := by
    have hpos : 0 < SC ^ (b.length + 1) := pow_pos (by unfold SC; norm_num) _
    have h3 := SieveCert.div_le_cdiv (om * (exF c.1 (c.2 - c.1) * trProd b)) (SC ^ (b.length + 1)) hpos
    refine le_trans (le_of_eq ?_) h3
    push_cast
    rw [pow_succ]
    field_simp
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
  exact (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)).trans h2

/-- **The certificate's cost of a box dropped for its products** is at least the bound of `shareBd`. -/
theorem dropBCost_ge (bl : List Cell) (m : ℕ) (h : bl.length = m + 2) (hok : cellsOK bl = true)
    (hfit : ∑ t : Fin (m + 1), (boxFn bl (m + 2) h t.castSucc).2 < DEN) :
    (DEN : ℝ) / ((DEN - ∑ t : Fin (m + 1), (boxFn bl (m + 2) h t.castSucc).2 : ℕ) : ℝ) *
      ∏ t : Fin (m + 1), trB (boxFn bl (m + 2) h t.castSucc).1
        ((boxFn bl (m + 2) h t.castSucc).2 - (boxFn bl (m + 2) h t.castSucc).1) ≤
      (dropBCost bl : ℝ) / K := by
  obtain ⟨c, b, rfl⟩ : ∃ c b, bl = c :: b := by
    cases bl with
    | nil => simp at h
    | cons c b => exact ⟨c, b, rfl⟩
  have hm : b.length = m + 1 := by simpa using h
  have hcells := (cellsOK_iff _).1 hok
  have hb : ∀ d ∈ b, 0 < d.1 ∧ d.1 < d.2 := fun d hd => hcells d (List.mem_cons_of_mem _ hd)
  have hbox : boxFn (c :: b) (m + 2) h = Fin.snoc (α := fun _ => Cell) (boxFn b (m + 1) hm) c :=
    boxFn_cons c b (m + 1) hm
  have e1 : ∑ t : Fin (m + 1), (boxFn (c :: b) (m + 2) h t.castSucc).2 = hiSum b := by
    rw [hbox]
    simp only [Fin.snoc_castSucc]
    rw [sum_boxFn (fun d => d.2), hiSum_eq]
  have e4 : ∏ t : Fin (m + 1), trB (boxFn (c :: b) (m + 2) h t.castSucc).1
      ((boxFn (c :: b) (m + 2) h t.castSucc).2 - (boxFn (c :: b) (m + 2) h t.castSucc).1) =
      (b.map fun d => trB d.1 (d.2 - d.1)).prod := by
    rw [hbox]
    simp only [Fin.snoc_castSucc]
    rw [prod_boxFn (fun d => trB d.1 (d.2 - d.1))]
  rw [e1] at hfit
  rw [e1, e4]
  obtain ⟨hP, hP0⟩ := prod_trB_le b fun d hd => (hb d hd).1
  have hS := SC_pos
  have hK := K_pos'
  have hD := DEN_pos'
  have hcast : ((DEN - hiSum b : ℕ) : ℝ) = (DEN : ℝ) - hiSum b := Nat.cast_sub hfit.le
  have hd0 : (0 : ℝ) < (DEN : ℝ) - hiSum b := by
    have : (hiSum b : ℝ) < DEN := by exact_mod_cast hfit
    linarith
  rw [hcast]
  have h1 : (DEN : ℝ) / ((DEN : ℝ) - hiSum b) * (b.map fun d => trB d.1 (d.2 - d.1)).prod ≤
      (DEN : ℝ) / ((DEN : ℝ) - hiSum b) * ((trProd b : ℝ) / (SC : ℝ) ^ b.length) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have h2 : (K : ℝ) * ((DEN : ℝ) / ((DEN : ℝ) - hiSum b) * ((trProd b : ℝ) / (SC : ℝ) ^ b.length)) ≤
      (dropBCost (c :: b) : ℝ) := by
    have hpos : 0 < (DEN - hiSum b) * SC ^ b.length :=
      Nat.mul_pos (by omega) (pow_pos (by unfold SC; norm_num) _)
    have h3 := SieveCert.div_le_cdiv (K * DEN * trProd b) ((DEN - hiSum b) * SC ^ b.length) hpos
    refine le_trans (le_of_eq ?_) h3
    push_cast
    rw [hcast]
    field_simp
  rw [le_div_iff₀ hK]
  calc (DEN : ℝ) / ((DEN : ℝ) - hiSum b) * (b.map fun d => trB d.1 (d.2 - d.1)).prod * K
      ≤ (DEN : ℝ) / ((DEN : ℝ) - hiSum b) * ((trProd b : ℝ) / (SC : ℝ) ^ b.length) * K :=
        mul_le_mul_of_nonneg_right h1 hK.le
    _ = (K : ℝ) * ((DEN : ℝ) / ((DEN : ℝ) - hiSum b) * ((trProd b : ℝ) / (SC : ℝ) ^ b.length)) := by ring
    _ ≤ _ := h2

variable [Route]

/-! ### The family of a box -/

/-- The family of a box: the strictly decreasing tuples of primes up to `N₂` with `x^{lo_i/DEN} ≤ p_i < x^{hi_i/DEN}`. -/
noncomputable def famB (q : ℕ) {k : ℕ} (bx : Fin k → Cell) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => SieveTypeIIU.primesLe (N2 q)).filter fun rt =>
    StrictAnti rt ∧ ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN)

theorem mem_famB {q k : ℕ} {bx : Fin k → Cell} {rt : Fin k → ℕ} :
    rt ∈ famB q bx ↔ (∀ i, rt i ≤ N2 q ∧ (rt i).Prime) ∧ StrictAnti rt ∧
      ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN) := by
  rw [famB, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [SieveTypeIIU.mem_primesLe]

/-- The powers `x^{a/DEN}` increase with `a`, for `x ≥ 1`. -/
theorem pow_mono {q : ℕ} (hx : 1 ≤ xq q) {a b : ℕ} (hab : a ≤ b) :
    xq q ^ ((a : ℝ) / DEN) ≤ xq q ^ ((b : ℝ) / DEN) :=
  Real.rpow_le_rpow_of_exponent_le hx (div_le_div_of_nonneg_right (by exact_mod_cast hab) DEN_pos'.le)

/-! ### A cut of a cell -/

/-- The box with the cell `i` cut from above at `c ≤ hi_i`: the tuples of the box with `p_i < x^{c/DEN}`. -/
theorem famB_cut_lo {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ}
    (h2 : c ≤ (bx i).2) :
    famB q (Function.update bx i ((bx i).1, c)) =
      (famB q bx).filter fun rt => (rt i : ℝ) < xq q ^ ((c : ℝ) / DEN) := by
  ext rt
  simp only [mem_famB, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hsa, hc⟩
    have hi := hc i
    simp only [Function.update_self] at hi
    refine ⟨⟨hp, hsa, fun j => ?_⟩, hi.2⟩
    by_cases hj : j = i
    · subst hj
      exact ⟨hi.1, hi.2.trans_le (pow_mono hx h2)⟩
    · have := hc j
      rwa [Function.update_of_ne hj] at this
  · rintro ⟨⟨hp, hsa, hc⟩, hlt⟩
    refine ⟨hp, hsa, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact ⟨(hc j).1, hlt⟩
    · rw [Function.update_of_ne hj]
      exact hc j

/-- The box with the cell `i` cut from below at `c ≥ lo_i`: the tuples of the box with `p_i ≥ x^{c/DEN}`. -/
theorem famB_cut_hi {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ}
    (h1 : (bx i).1 ≤ c) :
    famB q (Function.update bx i (c, (bx i).2)) =
      (famB q bx).filter fun rt => ¬ (rt i : ℝ) < xq q ^ ((c : ℝ) / DEN) := by
  ext rt
  simp only [mem_famB, Finset.mem_filter, not_lt]
  constructor
  · rintro ⟨hp, hsa, hc⟩
    have hi := hc i
    simp only [Function.update_self] at hi
    refine ⟨⟨hp, hsa, fun j => ?_⟩, hi.1⟩
    by_cases hj : j = i
    · subst hj
      exact ⟨(pow_mono hx h1).trans hi.1, hi.2⟩
    · have := hc j
      rwa [Function.update_of_ne hj] at this
  · rintro ⟨⟨hp, hsa, hc⟩, hge⟩
    refine ⟨hp, hsa, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact ⟨hge, (hc j).2⟩
    · rw [Function.update_of_ne hj]
      exact hc j

/-- **A cut.** For `lo_i ≤ c ≤ hi_i`, the term of a box is the sum of the terms of the boxes with the cell `i` cut
at `c`. -/
theorem famI_cut (g : ℕ → ℝ) {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ}
    (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2) :
    famI g (N1 q) (N2 q) (famB q bx) =
      famI g (N1 q) (N2 q) (famB q (Function.update bx i ((bx i).1, c))) +
        famI g (N1 q) (N2 q) (famB q (Function.update bx i (c, (bx i).2))) := by
  unfold famI
  rw [famB_cut_lo hx bx i h2, famB_cut_hi hx bx i h1, Finset.sum_filter_add_sum_filter_not]

/-! ### Buchstab's identity on a box -/

/-- Buchstab's identity for a tuple of a box and a number `n ≠ 0`, with a floor `z` at most the last prime. -/
theorem buch_pt_box {q : ℕ} {k' : ℕ} {bx : Fin (k' + 1) → Cell} {rt : Fin (k' + 1) → ℕ} (hrt : rt ∈ famB q bx)
    {z : ℕ} (hzl : z ≤ rt (Fin.last k')) (g : ℕ → ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) =
      g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0) -
        ∑ p ∈ SieveTree.primesIco z (rt (Fin.last k')),
          g n * (if (∏ i, (Fin.snoc rt p : Fin (k' + 2) → ℕ) i) ∣ n ∧
            SieveTree.rough ((Fin.snoc rt p : Fin (k' + 2) → ℕ) (Fin.last _)) n then 1 else 0) := by
  obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hrt
  have hW : ∀ p : ℕ, p.Prime → p ∣ ∏ i, rt i → rt (Fin.last k') ≤ p := by
    intro p hpp hd
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hd
    rw [(Nat.prime_dvd_prime_iff_eq hpp (hp i).2).1 hi]
    exact hsa.antitone (Fin.le_last i)
  rw [buchstab_pt hn0 hzl hW, mul_sub, Finset.mul_sum]
  simp only [prod_snoc, Fin.snoc_last]

/-- The tuples of a box with one more prime `p ∈ [⌈x^{f/DEN}⌉, p_last)` are the tuples of the box with one more cell
`(f, hi_last)`. -/
theorem famB_snoc_sum (q : ℕ) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (f : ℕ) (G : (Fin (k' + 2) → ℕ) → ℝ) :
    ∑ rt ∈ famB q bx, ∑ p ∈ SieveTree.primesIco ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (rt (Fin.last k')), G (Fin.snoc rt p) =
      ∑ y ∈ famB q (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2)), G y := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => Fin.snoc x.1 x.2) (fun y => ⟨Fin.init y, y (Fin.last _)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨rt, p⟩ h
    rw [Finset.mem_sigma] at h
    obtain ⟨hrt, hp⟩ := h
    dsimp only at hrt hp
    rw [SieveTree.mem_primesIco] at hp
    obtain ⟨hpr, hsa, hc⟩ := mem_famB.1 hrt
    show (Fin.snoc rt p : Fin (k' + 2) → ℕ) ∈ _
    rw [mem_famB]
    refine ⟨fun i => ?_, SieveP6Chain.strictAnti_snoc hsa
      (fun u => lt_of_lt_of_le hp.2.1 (hsa.antitone (Fin.le_last u))), fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact ⟨hp.2.1.le.trans (hpr _).1, hp.2.2⟩
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact hpr i
    · induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        refine ⟨Nat.ceil_le.1 hp.1, lt_trans ?_ (hc (Fin.last k')).2⟩
        exact_mod_cast hp.2.1
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact hc i
  · intro y hy
    obtain ⟨hpr, hsa, hc⟩ := mem_famB.1 hy
    rw [Finset.mem_sigma, SieveTree.mem_primesIco]
    refine ⟨mem_famB.2 ⟨fun i => hpr i.castSucc, fun a b hab => hsa (Fin.castSucc_lt_castSucc_iff.2 hab),
      fun i => ?_⟩, ?_, ?_, (hpr _).2⟩
    · have := hc i.castSucc
      simp only [Fin.snoc_castSucc] at this
      exact this
    · have := (hc (Fin.last _)).1
      simp only [Fin.snoc_last] at this
      exact Nat.ceil_le.2 this
    · exact hsa (Fin.castSucc_lt_last _)
  · rintro ⟨rt, p⟩ _
    simp only [Fin.init_snoc, Fin.snoc_last]
  · intro y _
    simp only [Fin.snoc_init_self]
  · intro _ _
    rfl

/-- A prime of a box is at least the ceiling of `x^{f/DEN}` for `f` at most its cell's lower end. -/
theorem ceil_le_last {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} {bx : Fin (k' + 1) → Cell} {rt : Fin (k' + 1) → ℕ}
    (hrt : rt ∈ famB q bx) {f : ℕ} (hf : f ≤ (bx (Fin.last k')).1) :
    ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ ≤ rt (Fin.last k') :=
  Nat.ceil_le.2 ((pow_mono hx hf).trans ((mem_famB.1 hrt).2.2 _).1)

/-- **Buchstab's identity on a box**, with the floor `z = ⌈x^{f/DEN}⌉` for `f ≤ lo_last`: the term of the box is
`Σ S(A_r, z)` minus the term of the box with the cell `(f, hi_last)` for one more prime. -/
theorem famI_buch (g : ℕ → ℝ) {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) {f : ℕ}
    (hf : f ≤ (bx (Fin.last k')).1) :
    famI g (N1 q) (N2 q) (famB q bx) =
      famJ g (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (famB q bx) -
        famI g (N1 q) (N2 q) (famB q (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2))) := by
  have hpt : ∀ rt ∈ famB q bx, ∀ n ∈ Ioc (N1 q) (N2 q),
      g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) =
        g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ n then 1 else 0) -
          ∑ p ∈ SieveTree.primesIco ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (rt (Fin.last k')),
            g n * (if (∏ i, (Fin.snoc rt p : Fin (k' + 2) → ℕ) i) ∣ n ∧
              SieveTree.rough ((Fin.snoc rt p : Fin (k' + 2) → ℕ) (Fin.last _)) n then 1 else 0) := by
    intro rt hrt n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hn).1; omega
    exact buch_pt_box hrt (ceil_le_last hx hrt hf) g hn0
  unfold famI famJ
  rw [Finset.sum_congr rfl fun rt hrt => Finset.sum_congr rfl (hpt rt hrt)]
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [← famB_snoc_sum q bx f]
  refine Finset.sum_congr rfl fun rt _ => ?_
  exact Finset.sum_comm

/-! ### A box with no term -/

/-- `q` is large for the cells: `x^{1/DEN} ≥ 3`. -/
def Big (q : ℕ) : Prop := 3 ≤ (q : ℝ) ^ (L / (DEN : ℝ))

theorem big_ev [RouteOK] : ∀ᶠ q : ℕ in atTop, Big q :=
  ((tendsto_rpow_atTop (div_pos L_pos DEN_pos')).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3

/-- At a large modulus: `q ≥ 2`, `x ≥ 3`, `x^{(DEN−1)/DEN} ≤ N₁`, `N₂ < x^{(DEN+1)/DEN}` and `x^{1/DEN} ≥ 3`. -/
theorem big_facts [RouteOK] {q : ℕ} (hq : Big q) :
    2 ≤ q ∧ 3 ≤ xq q ∧ xq q ^ (((DEN : ℝ) - 1) / DEN) ≤ N1 q ∧ (N2 q : ℝ) < xq q ^ (((DEN : ℝ) + 1) / DEN) ∧
      3 ≤ xq q ^ (1 / (DEN : ℝ)) := by
  have hD := DEN_pos'
  have hL := (L_pos : (0 : ℝ) < L)
  have hq2 : 2 ≤ q := by
    by_contra hlt
    have h1 : (q : ℝ) ≤ 1 := by exact_mod_cast (show q ≤ 1 by omega)
    have h2 : (q : ℝ) ^ (L / (DEN : ℝ)) ≤ 1 := Real.rpow_le_one (Nat.cast_nonneg _) h1 (by positivity)
    unfold Big at hq
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hx0 : 0 < xq q := Real.rpow_pos_of_pos hq0 _
  have hy : xq q ^ (1 / (DEN : ℝ)) = (q : ℝ) ^ (L / (DEN : ℝ)) := by
    rw [← Real.rpow_mul hq0.le, mul_one_div]
  have hy3 : 3 ≤ xq q ^ (1 / (DEN : ℝ)) := by rw [hy]; exact hq
  have hD1 : (1 : ℝ) ≤ DEN := by
    have : (1 : ℕ) ≤ DEN := by unfold SieveCert.DEN; exact Nat.one_le_two_pow
    exact_mod_cast this
  have hx1 : 1 ≤ xq q := Real.one_le_rpow hq1 hL.le
  have hx3 : 3 ≤ xq q := by
    have h : xq q ^ (1 / (DEN : ℝ)) ≤ xq q ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [div_le_one hD]; exact hD1)
    rw [Real.rpow_one] at h
    linarith
  refine ⟨hq2, hx3, ?_, ?_, hy3⟩
  · have e : xq q ^ (((DEN : ℝ) - 1) / DEN) * xq q ^ (1 / (DEN : ℝ)) = xq q := by
      rw [← Real.rpow_add hx0]
      have : ((DEN : ℝ) - 1) / DEN + 1 / DEN = 1 := by rw [← add_div, sub_add_cancel, div_self hD.ne']
      rw [this, Real.rpow_one]
    have h0 : 0 ≤ xq q ^ (((DEN : ℝ) - 1) / DEN) := Real.rpow_nonneg hx0.le _
    have h1 : xq q ^ (((DEN : ℝ) - 1) / DEN) * 3 ≤ xq q := by
      calc xq q ^ (((DEN : ℝ) - 1) / DEN) * 3 ≤ xq q ^ (((DEN : ℝ) - 1) / DEN) * xq q ^ (1 / (DEN : ℝ)) :=
            mul_le_mul_of_nonneg_left hy3 h0
        _ = xq q := e
    have h2 : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    linarith
  · have e : xq q ^ (((DEN : ℝ) + 1) / DEN) = xq q * xq q ^ (1 / (DEN : ℝ)) := by
      rw [← Real.rpow_one_add' hx0.le (by positivity)]
      congr 1
      field_simp
    have h1 : (N2 q : ℝ) ≤ 2 * xq q := Nat.floor_le (by positivity)
    rw [e]
    nlinarith

/-- The product of a tuple of the box is at most `x^{Σhi/DEN}` and at least `x^{Σlo/DEN}`. -/
theorem prod_bounds {q : ℕ} (hx0 : 0 < xq q) {k : ℕ} {bx : Fin k → Cell} {rt : Fin k → ℕ}
    (hc : ∀ i, xq q ^ (((bx i).1 : ℝ) / DEN) ≤ rt i ∧ (rt i : ℝ) < xq q ^ (((bx i).2 : ℝ) / DEN)) :
    xq q ^ (((∑ i, (bx i).1 : ℕ) : ℝ) / DEN) ≤ ∏ i, (rt i : ℝ) ∧
      ∏ i, (rt i : ℝ) ≤ xq q ^ (((∑ i, (bx i).2 : ℕ) : ℝ) / DEN) := by
  constructor
  · rw [Nat.cast_sum, Finset.sum_div, Real.rpow_sum_of_pos hx0]
    exact Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hx0.le _) fun i _ => (hc i).1
  · rw [Nat.cast_sum, Finset.sum_div, Real.rpow_sum_of_pos hx0]
    exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => (hc i).2.le

/-- **A box with no term.** If the upper ends sum to at most `DEN − 1` and the lower ends, with the last one
twice, to at least `DEN + 1`, the term of the box is `0` at a large modulus. -/
theorem famI_vanish_box [RouteOK] (g : ℕ → ℝ) {q : ℕ} (hq : Big q) {k' : ℕ} (bx : Fin (k' + 1) → Cell)
    (h1 : ∑ i, (bx i).2 + 1 ≤ DEN) (h2 : DEN + 1 ≤ ∑ i, (bx i).1 + (bx (Fin.last k')).1) :
    famI g (N1 q) (N2 q) (famB q bx) = 0 := by
  obtain ⟨-, hx3, hN1, hN2, -⟩ := big_facts hq
  have hD := DEN_pos'
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  refine famI_vanish g _ _ _ fun rt hrt => ?_
  obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hrt
  obtain ⟨hlo, hhi⟩ := prod_bounds hx0 hc
  constructor
  · have h1' : ((∑ i, (bx i).2 : ℕ) : ℝ) + 1 ≤ DEN := by exact_mod_cast h1
    have : (∏ i, (rt i : ℝ)) ≤ N1 q :=
      hhi.trans (le_trans (Real.rpow_le_rpow_of_exponent_le hx1
        (div_le_div_of_nonneg_right (by linarith) hD.le)) hN1)
    exact_mod_cast this
  · have h2' : (DEN : ℝ) + 1 ≤ ((∑ i, (bx i).1 : ℕ) : ℝ) + ((bx (Fin.last k')).1 : ℝ) := by exact_mod_cast h2
    have h3 : (N2 q : ℝ) < (∏ i, (rt i : ℝ)) * rt (Fin.last k') := by
      calc (N2 q : ℝ) < xq q ^ (((DEN : ℝ) + 1) / DEN) := hN2
        _ ≤ xq q ^ ((((∑ i, (bx i).1 : ℕ) : ℝ) + ((bx (Fin.last k')).1 : ℝ)) / DEN) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (div_le_div_of_nonneg_right h2' hD.le)
        _ = xq q ^ (((∑ i, (bx i).1 : ℕ) : ℝ) / DEN) * xq q ^ (((bx (Fin.last k')).1 : ℝ) / DEN) := by
            rw [add_div, Real.rpow_add hx0]
        _ ≤ (∏ i, (rt i : ℝ)) * rt (Fin.last k') :=
            mul_le_mul hlo (hc _).1 (Real.rpow_nonneg hx0.le _) (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
    exact_mod_cast h3

/-! ### A dropped box -/

/-- **A dropped box.** For a box whose cells have `0 < lo ≤ hi` and whose upper ends sum to at most `DEN`, and
`B` at least the bound of `SieveRough.shareBox`: for every `δ > 0` and large `q`, the term of the box in the
comparison set is at most `(B + δ)x/(φ(q) log x)`. -/
theorem drop_bound [RouteOK] {m : ℕ} (bx : Fin (m + 1) → Cell) (hlo : ∀ i, 0 < (bx i).1)
    (hle : ∀ i, (bx i).1 ≤ (bx i).2) (hfit : ∑ i, (bx i).2 ≤ DEN) {B : ℝ}
    (hB : (omKw (∑ t : Fin m, (bx t.castSucc).1) (bx (Fin.last m)).1 (∑ i, ((bx i).2 - (bx i).1))
        ((bx (Fin.last m)).2 - (bx (Fin.last m)).1) : ℝ) / K *
      ((∏ t : Fin m, trB (bx t.castSucc).1 ((bx t.castSucc).2 - (bx t.castSucc).1)) *
        exB (bx (Fin.last m)).1 ((bx (Fin.last m)).2 - (bx (Fin.last m)).1)) ≤ B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, famI (gB q) (N1 q) (N2 q) (famB q bx) ≤
      (q.totient : ℝ)⁻¹ * ((B + δ) * (xq q / Real.log (xq q))) := by
  have hfit' : (∑ t : Fin m, (bx t.castSucc).1) + (bx (Fin.last m)).1 + ∑ i, ((bx i).2 - (bx i).1) ≤ DEN := by
    have e : (∑ t : Fin m, (bx t.castSucc).1) + (bx (Fin.last m)).1 = ∑ i, (bx i).1 :=
      (Fin.sum_univ_castSucc fun i => (bx i).1).symm
    have e2 : ∑ i, (bx i).1 + ∑ i, ((bx i).2 - (bx i).1) = ∑ i, (bx i).2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.add_sub_cancel' (hle i)
    omega
  have hsh := SieveRough.shareBox (fun i => (bx i).1) (fun i => (bx i).2 - (bx i).1) hlo hfit' hB hδ
  filter_upwards [SieveDrop.tendsto_xq.eventually hsh, eventually_ge_atTop 1] with q hq hq1
  have h1 := SieveDrop.famI_gB_le q (famB q bx) (fun rt hrt i => ((mem_famB.1 hrt).1 i).2) hq1
  refine h1.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hq) (by positivity))
  unfold SB
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
  intro rt hrt
  obtain ⟨hp, -, hc⟩ := mem_famB.1 hrt
  rw [Fintype.mem_piFinset]
  intro t
  rw [boxP, mem_primesIn]
  refine ⟨(hp t).2, (hc t).1, ?_⟩
  have : (((bx t).1 : ℝ) + ((bx t).2 - (bx t).1 : ℕ)) = ((bx t).2 : ℝ) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' (hle t)]
  rw [this]
  exact (hc t).2

/-- **A box dropped for its products.** For a box of two primes at least whose cells have `0 < lo ≤ hi`, whose
lower ends, with the last one twice, sum to at least `DEN + 1`, and whose upper ends but the last sum to `s < DEN`,
and `B ≥ DEN/(DEN − s)·∏ trB` over the primes but the last: for every `δ > 0` and large `q`, the term of the box in
the comparison set is at most `(B + δ)x/(φ(q) log x)`. A tuple of the box has no `n` with a cofactor, so it counts
`n = ∏rt` alone, when that is in `(x, 2x]`: the last prime is then a prime of `(x/r', 2x/r']`. -/
theorem dropB_bound [RouteOK] {m : ℕ} (bx : Fin (m + 2) → Cell) (hlo : ∀ i, 0 < (bx i).1)
    (hle : ∀ i, (bx i).1 ≤ (bx i).2) (hreg : DEN + 1 ≤ ∑ i, (bx i).1 + (bx (Fin.last (m + 1))).1)
    (hfit : ∑ t : Fin (m + 1), (bx t.castSucc).2 < DEN) {B : ℝ}
    (hB : (DEN : ℝ) / ((DEN - ∑ t : Fin (m + 1), (bx t.castSucc).2 : ℕ) : ℝ) *
      ∏ t : Fin (m + 1), trB (bx t.castSucc).1 ((bx t.castSucc).2 - (bx t.castSucc).1) ≤ B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, famI (gB q) (N1 q) (N2 q) (famB q bx) ≤
      (q.totient : ℝ)⁻¹ * ((B + δ) * (xq q / Real.log (xq q))) := by
  have hD := DEN_pos'
  have haw : ∀ t : Fin (m + 1), (bx t.castSucc).1 + ((bx t.castSucc).2 - (bx t.castSucc).1) = (bx t.castSucc).2 :=
    fun t => Nat.add_sub_cancel' (hle _)
  have hsum : ∑ t : Fin (m + 1), ((bx t.castSucc).1 + ((bx t.castSucc).2 - (bx t.castSucc).1)) =
      ∑ t : Fin (m + 1), (bx t.castSucc).2 := Finset.sum_congr rfl fun t _ => haw t
  have hfit' : ∑ t : Fin (m + 1), ((bx t.castSucc).1 + ((bx t.castSucc).2 - (bx t.castSucc).1)) < DEN := by
    rw [hsum]
    exact hfit
  have hB' : (DEN : ℝ) /
      ((DEN - ∑ t : Fin (m + 1), ((bx t.castSucc).1 + ((bx t.castSucc).2 - (bx t.castSucc).1)) : ℕ) : ℝ) *
        ∏ t : Fin (m + 1), trB (bx t.castSucc).1 ((bx t.castSucc).2 - (bx t.castSucc).1) ≤ B := by
    rw [hsum]
    exact hB
  have hsh := shareBd (B := B) (fun t : Fin (m + 1) => (bx t.castSucc).1)
    (fun t : Fin (m + 1) => (bx t.castSucc).2 - (bx t.castSucc).1) (fun t => hlo _) hfit' hB' hδ
  filter_upwards [SieveDrop.tendsto_xq.eventually hsh, big_ev] with q hq hbig
  obtain ⟨hq2, hx3, -, -, hy3⟩ := big_facts hbig
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have h1 := SieveDrop.famI_gB_le q (famB q bx) (fun rt hrt i => ((mem_famB.1 hrt).1 i).2) (by omega)
  refine h1.trans (mul_le_mul_of_nonneg_left (le_trans ?_ hq) (by positivity))
  -- a tuple counts at most its own product
  have hA : ∀ rt ∈ famB q bx, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last (m + 1))) : ℝ) ≤
      if xq q < ((∏ i, rt i : ℕ) : ℝ) ∧ ((∏ i, rt i : ℕ) : ℝ) ≤ 2 * xq q then 1 else 0 := by
    intro rt hrt
    obtain ⟨hp, -, hc⟩ := mem_famB.1 hrt
    obtain ⟨hlo', -⟩ := prod_bounds hx0 hc
    have hrc : ((∏ i, rt i : ℕ) : ℝ) = ∏ i, (rt i : ℝ) := by push_cast; rfl
    have hr0 : (0 : ℝ) < ((∏ i, rt i : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun i _ => (hp i).2.pos
    have hbig2 : 2 * xq q < ((∏ i, rt i : ℕ) : ℝ) * rt (Fin.last (m + 1)) := by
      have h2' : (DEN : ℝ) + 1 ≤ ((∑ i, (bx i).1 : ℕ) : ℝ) + ((bx (Fin.last (m + 1))).1 : ℝ) := by
        exact_mod_cast hreg
      have e : xq q ^ (((DEN : ℝ) + 1) / DEN) = xq q * xq q ^ (1 / (DEN : ℝ)) := by
        rw [← Real.rpow_one_add' hx0.le (by positivity)]
        congr 1
        field_simp
      calc 2 * xq q < xq q * xq q ^ (1 / (DEN : ℝ)) := by nlinarith
        _ = xq q ^ (((DEN : ℝ) + 1) / DEN) := e.symm
        _ ≤ xq q ^ ((((∑ i, (bx i).1 : ℕ) : ℝ) + ((bx (Fin.last (m + 1))).1 : ℝ)) / DEN) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (div_le_div_of_nonneg_right h2' hD.le)
        _ = xq q ^ (((∑ i, (bx i).1 : ℕ) : ℝ) / DEN) * xq q ^ (((bx (Fin.last (m + 1))).1 : ℝ) / DEN) := by
            rw [add_div, Real.rpow_add hx0]
        _ ≤ ((∏ i, rt i : ℕ) : ℝ) * rt (Fin.last (m + 1)) := by
            rw [hrc]
            exact mul_le_mul hlo' (hc _).1 (Real.rpow_nonneg hx0.le _)
              (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
    have hy0 : 0 < xq q / ((∏ i, rt i : ℕ) : ℝ) := div_pos hx0 hr0
    have h2y : 2 * (xq q / ((∏ i, rt i : ℕ) : ℝ)) < rt (Fin.last (m + 1)) := by
      rw [← mul_div_assoc, div_lt_iff₀ hr0]
      linarith
    by_cases hy1 : 1 ≤ xq q / ((∏ i, rt i : ℕ) : ℝ)
    · rw [Psi_eq_zero hy1 h2y]
      split_ifs <;> norm_num
    · rw [not_le, div_lt_one hr0] at hy1
      by_cases h2 : ((∏ i, rt i : ℕ) : ℝ) ≤ 2 * xq q
      · have hcond : xq q < ((∏ i, rt i : ℕ) : ℝ) ∧ ((∏ i, rt i : ℕ) : ℝ) ≤ 2 * xq q := ⟨hy1, h2⟩
        simp only [hcond, and_self, ↓reduceIte]
        have hle1 : Psi (xq q / ((∏ i, rt i : ℕ) : ℝ)) (rt (Fin.last (m + 1))) ≤ 1 := by
          unfold Psi roughSet
          refine (Finset.card_filter_le _ _).trans ?_
          rw [Nat.card_Ioc]
          have hf : ⌊2 * (xq q / ((∏ i, rt i : ℕ) : ℝ))⌋₊ < 2 := by
            rw [Nat.floor_lt (by positivity), ← mul_div_assoc, div_lt_iff₀ hr0]
            push_cast
            linarith
          omega
        exact_mod_cast hle1
      · have hcond : ¬ (xq q < ((∏ i, rt i : ℕ) : ℝ) ∧ ((∏ i, rt i : ℕ) : ℝ) ≤ 2 * xq q) := fun hh => h2 hh.2
        simp only [hcond, ↓reduceIte]
        have h0 : Psi (xq q / ((∏ i, rt i : ℕ) : ℝ)) (rt (Fin.last (m + 1))) = 0 := by
          unfold Psi roughSet
          have hf : ⌊2 * (xq q / ((∏ i, rt i : ℕ) : ℝ))⌋₊ = 0 := by
            rw [Nat.floor_eq_zero, ← mul_div_assoc, div_lt_one hr0]
            linarith
          rw [hf]
          simp
        rw [h0]
        norm_num
  -- the tuples whose product is in `(x, 2x]`, by their primes but the last
  obtain ⟨P', hP'⟩ : ∃ P' : Finset (Fin (m + 1) → ℕ), P' = Fintype.piFinset fun t : Fin (m + 1) =>
      boxP (xq q) (bx t.castSucc).1 ((bx t.castSucc).2 - (bx t.castSucc).1) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : (Fin (m + 1) → ℕ) → Finset ℕ, Q' = fun rt' =>
      (Finset.Ioc ⌊xq q / ((∏ t, rt' t : ℕ) : ℝ)⌋₊ ⌊2 * (xq q / ((∏ t, rt' t : ℕ) : ℝ))⌋₊).filter Nat.Prime :=
    ⟨_, rfl⟩
  have hcard : ((famB q bx).filter fun rt =>
      xq q < ((∏ i, rt i : ℕ) : ℝ) ∧ ((∏ i, rt i : ℕ) : ℝ) ≤ 2 * xq q).card ≤ (P'.sigma Q').card := by
    refine Finset.card_le_card_of_injOn
      (fun rt => (⟨Fin.init rt, rt (Fin.last (m + 1))⟩ : Sigma fun _ : Fin (m + 1) → ℕ => ℕ)) ?_ ?_
    · intro rt hrt
      rw [Finset.mem_coe, Finset.mem_filter] at hrt
      obtain ⟨hmem, hlt, hle2⟩ := hrt
      obtain ⟨hp, -, hc⟩ := mem_famB.1 hmem
      have hprod : ((∏ i, rt i : ℕ) : ℝ) =
          ((∏ t : Fin (m + 1), rt t.castSucc : ℕ) : ℝ) * rt (Fin.last (m + 1)) := by
        rw [Fin.prod_univ_castSucc]
        push_cast
        rfl
      have hinit : ((∏ t, Fin.init rt t : ℕ) : ℝ) = ((∏ t : Fin (m + 1), rt t.castSucc : ℕ) : ℝ) := rfl
      have hr0 : (0 : ℝ) < ((∏ t : Fin (m + 1), rt t.castSucc : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos fun (t : Fin (m + 1)) _ => (hp t.castSucc).2.pos
      rw [hprod] at hlt hle2
      rw [Finset.mem_coe, Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · show Fin.init rt ∈ P'
        rw [hP', Fintype.mem_piFinset]
        intro t
        rw [boxP, mem_primesIn]
        refine ⟨(hp t.castSucc).2, (hc t.castSucc).1, ?_⟩
        have : (((bx t.castSucc).1 : ℝ) + ((bx t.castSucc).2 - (bx t.castSucc).1 : ℕ)) =
            ((bx t.castSucc).2 : ℝ) := by
          rw [← Nat.cast_add, haw t]
        rw [this]
        exact (hc t.castSucc).2
      · show rt (Fin.last (m + 1)) ∈ Q' (Fin.init rt)
        rw [hQ']
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        rw [hinit]
        refine ⟨⟨?_, ?_⟩, (hp _).2⟩
        · rw [Nat.floor_lt (by positivity), div_lt_iff₀ hr0]
          linarith [mul_comm (rt (Fin.last (m + 1)) : ℝ) ((∏ t : Fin (m + 1), rt t.castSucc : ℕ) : ℝ)]
        · refine Nat.le_floor ?_
          rw [← mul_div_assoc, le_div_iff₀ hr0]
          linarith [mul_comm (rt (Fin.last (m + 1)) : ℝ) ((∏ t : Fin (m + 1), rt t.castSucc : ℕ) : ℝ)]
    · intro rt₁ _ rt₂ _ heq
      simp only [Sigma.mk.injEq, heq_eq_eq] at heq
      rw [← Fin.snoc_init_self rt₁, ← Fin.snoc_init_self rt₂, heq.1, heq.2]
  calc ∑ rt ∈ famB q bx, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last (m + 1))) : ℝ)
      ≤ ∑ rt ∈ famB q bx,
          (if xq q < ((∏ i, rt i : ℕ) : ℝ) ∧ ((∏ i, rt i : ℕ) : ℝ) ≤ 2 * xq q then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hA
    _ = (((famB q bx).filter fun rt =>
          xq q < ((∏ i, rt i : ℕ) : ℝ) ∧ ((∏ i, rt i : ℕ) : ℝ) ≤ 2 * xq q).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ ((P'.sigma Q').card : ℝ) := by exact_mod_cast hcard
    _ = SBd (xq q) (fun t : Fin (m + 1) => (bx t.castSucc).1)
          (fun t : Fin (m + 1) => (bx t.castSucc).2 - (bx t.castSucc).1) := by
        rw [Finset.card_sigma, hP', hQ']
        unfold SBd
        push_cast
        rfl

/-! ### What the tests and a tree give -/

/-- `x/log x`. -/
noncomputable def Xq (q : ℕ) : ℝ := xq q / Real.log (xq q)

theorem Xq_pos [RouteOK] {q : ℕ} (hq : Big q) : 0 < Xq q := by
  obtain ⟨-, hx3, -⟩ := big_facts hq
  exact div_pos (by linarith) (Real.log_pos (by linarith))

/-- The term of a box in `𝒜` minus its term in the comparison set. -/
noncomputable def dI (q : ℕ) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) : ℝ :=
  famI (gA q a) (N1 q) (N2 q) (famB q bx) - famI (gB q) (N1 q) (N2 q) (famB q bx)

/-- The terms `Σ S(·_r, ⌈x^{f/DEN}⌉)` of a box in `𝒜` minus those in the comparison set. -/
noncomputable def dJ (q : ℕ) (a : ZMod q) (f : ℕ) {k : ℕ} (bx : Fin k → Cell) : ℝ :=
  famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (famB q bx) -
    famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (famB q bx)

/-- The term of the box is evaluated: its two versions differ by `o(x/(φ(q) log x))`. -/
def EvI {k' : ℕ} (bx : Fin (k' + 1) → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → |dI q a bx| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- The terms of the box at the floor `x^{f/DEN}` are evaluated. -/
def EvJ {k : ℕ} (f : ℕ) (bx : Fin k → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → |dJ q a f bx| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- **The tests are sound**: a box that passes one has its term, or its terms at the floor, evaluated. -/
structure Tests.Sound (τ : Tests) : Prop where
  soundI : ∀ (bl : List Cell) (cfg : Cfg) (k' : ℕ) (h : bl.length = k' + 1), τ.okI bl cfg = true →
    EvI (boxFn bl (k' + 1) h)
  soundJ : ∀ (bl : List Cell) (f : ℕ) (cfg : Cfg) (k : ℕ) (h : bl.length = k), τ.okJ bl f cfg = true →
    EvJ f (boxFn bl k h)

/-- The sign with which a term enters the sieve. -/
def sg (par : Bool) : ℝ := if par then 1 else -1

omit [Route] in
theorem sg_not (par : Bool) : sg (!par) = -sg par := by
  cases par <;> simp [sg]

omit [Route] in
theorem neg_abs_le_sg (par : Bool) (d : ℝ) : -|d| ≤ sg par * d := by
  cases par
  · simp only [sg, Bool.false_eq_true, ite_false, neg_mul, one_mul, neg_le_neg_iff]
    exact le_abs_self d
  · simp only [sg, ite_true, one_mul]
    exact neg_abs_le d

/-- The term of the box, with its sign, is at least `−(C + o(1))x/(φ(q) log x)`. -/
def Bd (par : Bool) (C : ℝ) {k' : ℕ} (bx : Fin (k' + 1) → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    -((q.totient : ℝ)⁻¹ * ((C + η) * Xq q)) ≤ sg par * dI q a bx

theorem dI_cut {q : ℕ} (hx : 1 ≤ xq q) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ}
    (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2) :
    dI q a bx = dI q a (Function.update bx i ((bx i).1, c)) + dI q a (Function.update bx i (c, (bx i).2)) := by
  unfold dI
  rw [famI_cut (gA q a) hx bx i h1 h2, famI_cut (gB q) hx bx i h1 h2]
  ring

theorem dI_buch {q : ℕ} (hx : 1 ≤ xq q) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) {f : ℕ}
    (hf : f ≤ (bx (Fin.last k')).1) :
    dI q a bx = dJ q a f bx - dI q a (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2)) := by
  unfold dI dJ
  rw [famI_buch (gA q a) hx bx hf, famI_buch (gB q) hx bx hf]
  ring

/-- **A tree that passes the check bounds its term**: for sound tests, a tree valid on a box, for a term of the
sign `par`, has the term at least `−(cost/K + o(1))x/(φ(q) log x)` with that sign. -/
theorem sound [RouteOK] {τ : Tests} (hτ : τ.Sound) (T : Tree) :
    ∀ (bl : List Cell) (par : Bool) (k' : ℕ) (h : bl.length = k' + 1), ok τ T bl par = true →
      Bd par ((cost T bl : ℝ) / K) (boxFn bl (k' + 1) h) := by
  induction T with
  | vanish =>
    intro bl par k' h hok η hη
    obtain ⟨c, b, rfl⟩ : ∃ c b, bl = c :: b := by
      cases bl with
      | nil => simp at h
      | cons c b => exact ⟨c, b, rfl⟩
    simp only [ok, vanishOK, Bool.and_eq_true, Nat.ble_eq] at hok
    have e1 : ∑ i, (boxFn (c :: b) (k' + 1) h i).2 = c.2 + hiSum b := by
      rw [sum_boxFn (fun d => d.2), hiSum_eq]
      simp
    have e2 : ∑ i, (boxFn (c :: b) (k' + 1) h i).1 = c.1 + loSum b := by
      rw [sum_boxFn (fun d => d.1), loSum_eq]
      simp
    have e3 : (boxFn (c :: b) (k' + 1) h (Fin.last k')).1 = c.1 := by simp [boxFn]
    filter_upwards [big_ev] with q hq a _
    have hA := famI_vanish_box (gA q a) hq (boxFn (c :: b) (k' + 1) h) (by omega) (by omega)
    have hB := famI_vanish_box (gB q) hq (boxFn (c :: b) (k' + 1) h) (by omega) (by omega)
    have hd : dI q a (boxFn (c :: b) (k' + 1) h) = 0 := by unfold dI; rw [hA, hB, sub_zero]
    have hX := Xq_pos hq
    rw [hd, mul_zero, neg_nonpos]
    simp only [cost, Nat.cast_zero, zero_div, zero_add]
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (mul_nonneg hη.le hX.le)
  | drop =>
    intro bl par k' h hok η hη
    simp only [ok, Bool.and_eq_true] at hok
    obtain ⟨hpar, hdrop⟩ := hok
    obtain ⟨c, b, rfl⟩ : ∃ c b, bl = c :: b := by
      cases bl with
      | nil => simp at h
      | cons c b => exact ⟨c, b, rfl⟩
    simp only [dropOK, Bool.and_eq_true, Nat.ble_eq] at hdrop
    obtain ⟨hcells, hfit⟩ := hdrop
    have hc := (cellsOK_iff _).1 hcells
    have hfit' : ∑ i, (boxFn (c :: b) (k' + 1) h i).2 ≤ DEN := by
      rw [sum_boxFn (fun d => d.2), ← hiSum_eq]
      exact hfit
    have hdb := drop_bound (boxFn (c :: b) (k' + 1) h) (fun i => (hc _ (boxFn_mem _ _ h i)).1)
      (fun i => (hc _ (boxFn_mem _ _ h i)).2.le) hfit' (dropCost_ge (c :: b) k' h hcells) hη
    filter_upwards [hdb] with q hq a _
    have hA : 0 ≤ famI (gA q a) (N1 q) (N2 q) (famB q (boxFn (c :: b) (k' + 1) h)) :=
      famI_nonneg (gA_nonneg q a) _ _ _
    subst hpar
    simp only [sg, ite_true, one_mul, cost]
    unfold dI Xq
    linarith
  | dropB =>
    intro bl par k' h hok η hη
    simp only [ok, Bool.and_eq_true] at hok
    obtain ⟨hpar, hdrop⟩ := hok
    obtain ⟨c, b, rfl⟩ : ∃ c b, bl = c :: b := by
      cases bl with
      | nil => simp at h
      | cons c b => exact ⟨c, b, rfl⟩
    simp only [dropBOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hdrop
    obtain ⟨⟨⟨hb0, hcells⟩, hreg⟩, hfit⟩ := hdrop
    obtain ⟨m, rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by simp at h; omega⟩
    have hc := (cellsOK_iff _).1 hcells
    have hm : b.length = m + 1 := by simpa using h
    have hbox : boxFn (c :: b) (m + 1 + 1) h = Fin.snoc (α := fun _ => Cell) (boxFn b (m + 1) hm) c :=
      boxFn_cons c b (m + 1) hm
    have e1 : ∑ i, (boxFn (c :: b) (m + 1 + 1) h i).1 = c.1 + loSum b := by
      rw [sum_boxFn (fun d => d.1), loSum_eq]
      simp
    have e3 : (boxFn (c :: b) (m + 1 + 1) h (Fin.last (m + 1))).1 = c.1 := by rw [hbox, Fin.snoc_last]
    have e2 : ∑ t : Fin (m + 1), (boxFn (c :: b) (m + 1 + 1) h t.castSucc).2 = hiSum b := by
      rw [hbox]
      simp only [Fin.snoc_castSucc]
      rw [sum_boxFn (fun d => d.2), hiSum_eq]
    have hdb := dropB_bound (boxFn (c :: b) (m + 1 + 1) h) (fun i => (hc _ (boxFn_mem _ _ h i)).1)
      (fun i => (hc _ (boxFn_mem _ _ h i)).2.le) (by rw [e1, e3]; omega) (by rw [e2]; exact hfit)
      (dropBCost_ge (c :: b) m h hcells (by rw [e2]; exact hfit)) hη
    filter_upwards [hdb] with q hq a _
    have hA : 0 ≤ famI (gA q a) (N1 q) (N2 q) (famB q (boxFn (c :: b) (m + 1 + 1) h)) :=
      famI_nonneg (gA_nonneg q a) _ _ _
    subst hpar
    simp only [sg, ite_true, one_mul, cost]
    unfold dI Xq
    linarith
  | evalI cfg =>
    intro bl par k' h hok η hη
    simp only [ok, Bool.and_eq_true] at hok
    filter_upwards [hτ.soundI bl cfg k' h hok.2 η hη] with q hq a ha
    have h1 := neg_abs_le_sg par (dI q a (boxFn bl (k' + 1) h))
    have h2 := hq a ha
    simp only [cost, Nat.cast_zero, zero_div, zero_add]
    linarith
  | split t c l r ihl ihr =>
    intro bl par k' h hok η hη
    simp only [ok, Bool.and_eq_true, splitOK, Nat.blt_eq] at hok
    obtain ⟨⟨⟨ht, hlo⟩, hhi⟩, hokl⟩ := hok.1
    have hokr := hok.2
    have ht' : t < k' + 1 := by omega
    set bx := boxFn bl (k' + 1) h with hbx
    set i : Fin (k' + 1) := ⟨k' + 1 - 1 - t, by omega⟩ with hi
    have hget : getC bl t = bx i := getC_eq bl (k' + 1) h t ht'
    have hl1 : (setHi bl t c).length = k' + 1 := by simp [setHi, h]
    have hr1 : (setLo bl t c).length = k' + 1 := by simp [setLo, h]
    have el : boxFn (setHi bl t c) (k' + 1) hl1 = Function.update bx i ((bx i).1, c) :=
      (boxFn_set bl (k' + 1) h t ht' ((getC bl t).1, c)).trans (by rw [hget])
    have er : boxFn (setLo bl t c) (k' + 1) hr1 = Function.update bx i (c, (bx i).2) :=
      (boxFn_set bl (k' + 1) h t ht' (c, (getC bl t).2)).trans (by rw [hget])
    have hL := ihl (setHi bl t c) par k' hl1 hokl (η / 2) (by positivity)
    have hR := ihr (setLo bl t c) par k' hr1 hokr (η / 2) (by positivity)
    rw [el] at hL
    rw [er] at hR
    filter_upwards [hL, hR, big_ev] with q h1 h2 hq a ha
    obtain ⟨-, hx3, -⟩ := big_facts hq
    rw [hget] at hlo hhi
    rw [dI_cut (by linarith) a bx i hlo.le hhi.le, mul_add]
    have h1' := h1 a ha
    have h2' := h2 a ha
    simp only [cost, Nat.cast_add, add_div]
    have e : (q.totient : ℝ)⁻¹ * (((cost l (setHi bl t c) : ℝ) / K + (cost r (setLo bl t c) : ℝ) / K + η) * Xq q) =
        (q.totient : ℝ)⁻¹ * (((cost l (setHi bl t c) : ℝ) / K + η / 2) * Xq q) +
          (q.totient : ℝ)⁻¹ * (((cost r (setLo bl t c) : ℝ) / K + η / 2) * Xq q) := by ring
    rw [e]
    linarith
  | buch f cfg ch ih =>
    intro bl par k' h hok η hη
    obtain ⟨x, b', rfl⟩ : ∃ x b', bl = x :: b' := by
      cases bl with
      | nil => simp at h
      | cons x b' => exact ⟨x, b', rfl⟩
    simp only [ok, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hok
    obtain ⟨⟨⟨hf0, hfx⟩, hokJ⟩, hokch⟩ := hok
    set bx := boxFn (x :: b') (k' + 1) h with hbx
    have hlast : bx (Fin.last k') = x := by simp [hbx, boxFn]
    have h2len : ((f, x.2) :: x :: b').length = k' + 1 + 1 := by simp [← h]
    have ech : boxFn ((f, x.2) :: x :: b') (k' + 1 + 1) h2len = Fin.snoc (α := fun _ => Cell) bx (f, x.2) :=
      boxFn_cons (f, x.2) (x :: b') (k' + 1) h
    have hJ := hτ.soundJ (x :: b') f cfg (k' + 1) h hokJ (η / 2) (by positivity)
    have hC := ih ((f, x.2) :: x :: b') (!par) (k' + 1) h2len hokch (η / 2) (by positivity)
    rw [ech] at hC
    filter_upwards [hJ, hC, big_ev] with q h1 h2 hq a ha
    obtain ⟨-, hx3, -⟩ := big_facts hq
    have hf' : f ≤ (bx (Fin.last k')).1 := by rw [hlast]; exact hfx
    rw [dI_buch (by linarith) a bx hf', hlast, mul_sub]
    have h1' := h1 a ha
    have h2' := h2 a ha
    rw [sg_not] at h2'
    have h3 := neg_abs_le_sg par (dJ q a f bx)
    simp only [cost]
    have e : (q.totient : ℝ)⁻¹ * (((cost ch ((f, x.2) :: x :: b') : ℝ) / K + η) * Xq q) =
        (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) +
          (q.totient : ℝ)⁻¹ * (((cost ch ((f, x.2) :: x :: b') : ℝ) / K + η / 2) * Xq q) := by ring
    rw [e]
    linarith

/-! ### The top of the sieve -/

/-- The top of the sieve, `⌈x^{(DEN/2+1)/DEN}⌉`: above `√(2x)` at a large modulus. -/
noncomputable def ztop (q : ℕ) : ℕ := ⌈xq q ^ (((DEN / 2 + 1 : ℕ) : ℝ) / DEN)⌉₊

/-- `S(·, z_top)`, with weights `g`. -/
noncomputable def Ttop (q : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ioc (N1 q) (N2 q), g m * (if SieveTree.rough (ztop q) m then 1 else 0)

theorem famB_zero (q : ℕ) (bx : Fin 0 → Cell) : famB q bx = Finset.univ := by
  ext rt
  simp only [Finset.mem_univ, iff_true]
  exact mem_famB.2 ⟨fun i => i.elim0, fun a => a.elim0, fun i => i.elim0⟩

/-- With no prime, the terms at a floor are `S(·, z)`. -/
theorem famJ_zero (g : ℕ → ℝ) (q z : ℕ) (bx : Fin 0 → Cell) :
    famJ g (N1 q) (N2 q) z (famB q bx) =
      ∑ m ∈ Ioc (N1 q) (N2 q), g m * (if SieveTree.rough z m then 1 else 0) := by
  unfold famJ
  rw [famB_zero, Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_dvd, true_and]

omit [Route] in
theorem half_DEN : DEN / 2 + 1 + 1 ≤ DEN ∧ DEN + 1 ≤ 2 * (DEN / 2 + 1) := by
  unfold SieveCert.DEN
  norm_num

/-- **The root.** At a large modulus, `S(·, z_top) = S(·, z) − Σ_{z ≤ p < z_top} S(·_p, p)` for the floor
`z = ⌈x^{f₀/DEN}⌉`: the terms at the floor of the box with no prime, minus the term of the box of one prime with
the cell `(f₀, DEN/2 + 1)`. -/
theorem Ttop_eq [RouteOK] {q : ℕ} (hq : Big q) (g : ℕ → ℝ) {f₀ : ℕ} (hf₀ : f₀ ≤ DEN / 2 + 1) :
    Ttop q g = famJ g (N1 q) (N2 q) ⌈xq q ^ ((f₀ : ℝ) / DEN)⌉₊ (famB q (boxFn [] 0 rfl)) -
      famI g (N1 q) (N2 q) (famB q (boxFn [(f₀, DEN / 2 + 1)] 1 rfl)) := by
  obtain ⟨-, hx3, -, -, -⟩ := big_facts hq
  have hD := DEN_pos'
  have hx1 : 1 ≤ xq q := by linarith
  set z := ⌈xq q ^ ((f₀ : ℝ) / DEN)⌉₊ with hz
  have hzt : z ≤ ztop q := Nat.ceil_le_ceil (pow_mono hx1 hf₀)
  have hbox : ∀ i : Fin 1, boxFn [(f₀, DEN / 2 + 1)] 1 rfl i = (f₀, DEN / 2 + 1) := fun i => by
    simp [boxFn]
  have hpt : ∀ m ∈ Ioc (N1 q) (N2 q), g m * (if SieveTree.rough (ztop q) m then 1 else 0) =
      g m * (if SieveTree.rough z m then 1 else 0) -
        ∑ p ∈ SieveTree.primesIco z (ztop q), g m * (if p ∣ m ∧ SieveTree.rough p m then 1 else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Ioc.1 hm).1; omega
    have h := buchstab_pt (W := 1) hm0 hzt (fun p hp hd => absurd (Nat.dvd_one.1 hd) hp.one_lt.ne')
    simp only [one_dvd, true_and, one_mul] at h
    rw [h, mul_sub, Finset.mul_sum]
  rw [famJ_zero]
  unfold Ttop famI
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_nbij' (fun p => fun _ => p) (fun rt => rt 0) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [SieveTree.mem_primesIco] at hp
    rw [mem_famB]
    have hpz : (p : ℝ) < xq q ^ (((DEN / 2 + 1 : ℕ) : ℝ) / DEN) := Nat.lt_ceil.1 hp.2.1
    refine ⟨fun _ => ⟨?_, hp.2.2⟩,
      fun a b hab => absurd (Fin.lt_def.1 hab) (by have := a.2; have := b.2; omega), fun i => ?_⟩
    · have h1 : xq q ^ (((DEN / 2 + 1 : ℕ) : ℝ) / DEN) ≤ xq q ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by
          rw [div_le_one hD]
          exact_mod_cast (show DEN / 2 + 1 ≤ DEN by have := half_DEN.1; omega))
      rw [Real.rpow_one] at h1
      have h2 : 2 * xq q - 1 < (N2 q : ℝ) := Nat.sub_one_lt_floor _
      have h3 : (p : ℝ) < (N2 q : ℝ) := by linarith
      exact_mod_cast h3.le
    · rw [hbox i]
      exact ⟨Nat.ceil_le.1 hp.1, hpz⟩
  · intro rt hrt
    obtain ⟨hpr, -, hc⟩ := mem_famB.1 hrt
    have h0 := hc 0
    rw [hbox 0] at h0
    rw [SieveTree.mem_primesIco]
    exact ⟨Nat.ceil_le.2 h0.1, Nat.lt_ceil.2 h0.2, (hpr 0).2⟩
  · intro p _
    rfl
  · intro rt _
    funext i
    rw [Fin.fin_one_eq_zero i]
  · intro p _
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_add, pow_one]

/-- For `ε > 0` and large `q`: `S(ℬ, z_top) ≥ φ(q)⁻¹((1 − ε)x/log x − q)`. -/
theorem Ttop_gB_ge [RouteOK] {ε : ℝ} (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop,
    (q.totient : ℝ)⁻¹ * ((1 - ε) * Xq q - q) ≤ Ttop q (gB q) := by
  filter_upwards [SieveDrop.tendsto_xq.eventually (SieveMain.primes_dyadic_ge hε), big_ev] with q hq hbig
  obtain ⟨hq2, hx3, hN1, -, -⟩ := big_facts hbig
  have hD := DEN_pos'
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  set P := (Ioc (N1 q) (N2 q)).filter Nat.Prime with hP
  set Pc := P.filter (fun p => Nat.Coprime p q) with hPc
  have hztopN : ztop q ≤ N1 q := by
    refine Nat.ceil_le.2 (le_trans (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) hN1)
    rw [div_le_div_iff_of_pos_right hD]
    have : ((DEN / 2 + 1 : ℕ) : ℝ) + 1 ≤ (DEN : ℝ) := by exact_mod_cast half_DEN.1
    linarith
  have hT : (q.totient : ℝ)⁻¹ * (Pc.card : ℝ) ≤ Ttop q (gB q) := by
    unfold Ttop
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    have hsub : Pc ⊆ Ioc (N1 q) (N2 q) := fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
      mul_nonneg (SieveDrop.gB_nonneg q m) (by split_ifs <;> norm_num))
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hPc, hP, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨h1, -⟩, hpp⟩, hcop⟩ := hp
    have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).2 hcop
    have hr : SieveTree.rough (ztop q) p := by
      intro ℓ hℓ hℓp hd
      have := (Nat.prime_dvd_prime_iff_eq hℓp hpp).1 hd
      omega
    simp only [gB, hu, ite_true, hr, Nat.cast_one, mul_one]
  have hcount : (P.card : ℝ) - q ≤ Pc.card := by
    have h1 : P.filter (fun p => ¬ Nat.Coprime p q) ⊆ q.primeFactors := by
      intro p hp
      rw [Finset.mem_filter, hP, Finset.mem_filter] at hp
      rw [Nat.mem_primeFactors]
      exact ⟨hp.1.2, (Nat.Prime.dvd_iff_not_coprime hp.1.2).2 hp.2, by omega⟩
    have h2 : q.primeFactors.card ≤ q := by
      calc q.primeFactors.card ≤ (Finset.Icc 1 q).card := Finset.card_le_card fun p hp => by
            rw [Finset.mem_Icc]
            exact ⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le,
              Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)⟩
        _ = q := by simp
    have h3 := Finset.card_filter_add_card_filter_not (s := P) (fun p => Nat.Coprime p q)
    have h4 := (Finset.card_le_card h1).trans h2
    have : (P.card : ℝ) ≤ Pc.card + q := by
      rw [hPc]
      exact_mod_cast (show P.card ≤ (P.filter fun p => Nat.Coprime p q).card + q by omega)
    linarith
  have hP' : (1 - ε) * (xq q / Real.log (xq q)) ≤ (P.card : ℝ) := hq
  calc (q.totient : ℝ)⁻¹ * ((1 - ε) * Xq q - q)
      ≤ (q.totient : ℝ)⁻¹ * (Pc.card : ℝ) := mul_le_mul_of_nonneg_left (by unfold Xq; linarith) hφ.le
    _ ≤ Ttop q (gB q) := hT

/-! ### The theorem -/

/-- **Linnik's theorem at `x = q^L`, for large `q`, from a bound of the first term.** For a route with `RouteOK`:
if the terms at the floor `x^{f₀/DEN}` of the box with no prime are evaluated, and the term of the box of one prime
with the cell `(f₀, DEN/2 + 1)` is at most `(C + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set, with `C < 1`,
then there is `q₀` such that for `q ≥ 1` with `q ≥ q₀` and `a` a unit mod `q` there is a prime `p ≡ a (mod q)` with
`q^L < p ≤ 2q^L`. -/
theorem linnik_large_bd [RouteOK] (f₀ : ℕ) (hf₀ : f₀ ≤ DEN / 2 + 1) (hJ0 : EvJ f₀ (boxFn [] 0 rfl)) {C : ℝ}
    (hC1 : C < 1) (hBd : Bd false C (boxFn [(f₀, DEN / 2 + 1)] 1 rfl)) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L := by
  have hK := K_pos'
  have hL0 : 0 < L := L_pos
  have hD := DEN_pos'
  set ε : ℝ := (1 - C) / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hJ := hJ0 ε hε0
  have hI := hBd ε hε0
  have hlog := SieveMain.ev_log_le (c := ε / L) (r := L - 1) (by positivity) (by linarith [two_lt_L])
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (hJ.and (hI.and ((Ttop_gB_ge hε0).and (big_ev.and hlog))))
  refine ⟨q₀, fun q _ hq a ha => ?_⟩
  obtain ⟨h1, h2, hTB, hbig, hlg⟩ := hq₀ q hq
  obtain ⟨hq2, hx3, hN1, hN2, hy3⟩ := big_facts hbig
  have hX := Xq_pos hbig
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hx0 : 0 < xq q := by linarith
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  have h1' := h1 a ha
  have h2' : -((q.totient : ℝ)⁻¹ * ((C + ε) * Xq q)) ≤ sg false * dI q a (boxFn [(f₀, DEN / 2 + 1)] 1 rfl) :=
    h2 a ha
  have hdiff : Ttop q (gA q a) - Ttop q (gB q) =
      dJ q a f₀ (boxFn [] 0 rfl) - dI q a (boxFn [(f₀, DEN / 2 + 1)] 1 rfl) := by
    rw [Ttop_eq hbig (gA q a) hf₀, Ttop_eq hbig (gB q) hf₀]
    unfold dJ dI
    ring
  -- `q ≤ εX`
  have hqX : (q : ℝ) ≤ ε * Xq q := by
    have hlogx : Real.log (xq q) = L * Real.log q := Real.log_rpow hq0 _
    have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    unfold Xq
    rw [hlogx, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have h2'' : L * Real.log q ≤ ε * (q : ℝ) ^ (L - 1) := by
      have := hlg
      rw [div_mul_eq_mul_div, le_div_iff₀ hL0] at this
      linarith
    have hsplit : (q : ℝ) * (q : ℝ) ^ (L - 1) = xq q := by
      rw [← Real.rpow_one_add' hq0.le (by rw [add_sub_cancel]; exact hL0.ne'), add_sub_cancel]
    calc (q : ℝ) * (L * Real.log q) ≤ (q : ℝ) * (ε * (q : ℝ) ^ (L - 1)) := mul_le_mul_of_nonneg_left h2'' hq0.le
      _ = ε * xq q := by rw [← hsplit]; ring
  -- `S(𝒜, z_top) > 0`
  have hpos : 0 < Ttop q (gA q a) := by
    have h3 := neg_abs_le_sg true (dJ q a f₀ (boxFn [] 0 rfl))
    simp only [sg, ite_true, one_mul, Bool.false_eq_true, ite_false, neg_mul] at h3 h2'
    have e1 : (q.totient : ℝ)⁻¹ * ((1 - ε) * Xq q - q) - (q.totient : ℝ)⁻¹ * (ε * Xq q) -
        (q.totient : ℝ)⁻¹ * ((C + ε) * Xq q) ≤ Ttop q (gA q a) := by linarith
    have e2 : (q.totient : ℝ)⁻¹ * ((1 - C) / 2 * Xq q) ≤ (q.totient : ℝ)⁻¹ * ((1 - ε) * Xq q - q) -
        (q.totient : ℝ)⁻¹ * (ε * Xq q) - (q.totient : ℝ)⁻¹ * ((C + ε) * Xq q) := by
      have : (1 - C) / 2 * Xq q ≤ ((1 - ε) * Xq q - q) - (ε * Xq q) - ((C + ε) * Xq q) := by
        rw [hε] at hqX ⊢
        linarith
      nlinarith
    have : 0 < (q.totient : ℝ)⁻¹ * ((1 - C) / 2 * Xq q) :=
      mul_pos hφ (mul_pos (by linarith) hX)
    linarith
  -- a term of `S(𝒜, z_top)` is positive: a prime `≡ a`
  unfold Ttop at hpos
  obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  have hmA : (m : ZMod q) = a := by
    by_contra h
    simp [gA, h] at hm0
  have hmr : SieveTree.rough (ztop q) m := by
    by_contra h
    simp [h] at hm0
  rw [Finset.mem_Ioc] at hm
  have hN1' : 1 ≤ N1 q := Nat.le_floor (by simpa using (show (1 : ℝ) ≤ xq q by linarith))
  have hm2 : 2 ≤ m := by omega
  refine ⟨m, ?_, hmA, Nat.lt_of_floor_lt hm.1, ?_⟩
  · by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hmin := (SieveStops2.rough_iff_le_minFac hm2).1 hmr
    have hz : N2 q < (ztop q) ^ 2 := by
      set y := xq q ^ (((DEN / 2 + 1 : ℕ) : ℝ) / DEN) with hy
      have hy0 : 0 ≤ y := Real.rpow_nonneg hx0.le _
      have h4 : y ≤ (ztop q : ℝ) := Nat.le_ceil _
      have h5 : xq q ^ (((DEN : ℝ) + 1) / DEN) ≤ y * y := by
        rw [hy, ← Real.rpow_add hx0]
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
        rw [← add_div, div_le_div_iff_of_pos_right hD]
        have : (DEN : ℝ) + 1 ≤ 2 * ((DEN / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast half_DEN.2
        linarith
      have h6 : (N2 q : ℝ) < ((ztop q) ^ 2 : ℕ) := by
        push_cast
        nlinarith
      exact_mod_cast h6
    have : (ztop q) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hmin 2
    omega
  · have : (m : ℝ) ≤ N2 q := by exact_mod_cast hm.2
    exact this.trans (Nat.floor_le (by positivity))

/-- **Linnik's theorem at `x = q^L`, for large `q`, from a tree.** For a route with `RouteOK` and sound tests: if
the terms at the floor `x^{f₀/DEN}` of the box with no prime pass the test, the tree is valid on the box of one prime
with the cell `(f₀, DEN/2 + 1)`, for a term of the sign `−`, and its cost is below `K`, then there is `q₀` such that
for `q ≥ 1` with `q ≥ q₀` and `a` a unit mod `q` there is a prime `p ≡ a (mod q)` with `q^L < p ≤ 2q^L`. -/
theorem linnik_large_tree [RouteOK] {τ : Tests} (hτ : τ.Sound) (T : Tree) (f₀ : ℕ) (cfg₀ : Cfg)
    (hf₀ : f₀ ≤ DEN / 2 + 1) (hroot : τ.okJ [] f₀ cfg₀ = true) (hok : ok τ T [(f₀, DEN / 2 + 1)] false = true)
    (hcost : cost T [(f₀, DEN / 2 + 1)] < K) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L := by
  refine linnik_large_bd f₀ hf₀ (hτ.soundJ [] f₀ cfg₀ 0 rfl hroot) (C := (cost T [(f₀, DEN / 2 + 1)] : ℝ) / K) ?_
    (sound hτ T [(f₀, DEN / 2 + 1)] false 0 rfl hok)
  rw [div_lt_one K_pos']
  exact_mod_cast hcost

/-- **Linnik's theorem with exponent `L`, from a bound of the first term**: `linnik_large_bd` for every modulus. -/
theorem linnik_bd [RouteOK] (f₀ : ℕ) (hf₀ : f₀ ≤ DEN / 2 + 1) (hJ0 : EvJ f₀ (boxFn [] 0 rfl)) {C : ℝ}
    (hC1 : C < 1) (hBd : Bd false C (boxFn [(f₀, DEN / 2 + 1)] 1 rfl)) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K' * (q : ℝ) ^ L :=
  SieveMain2.route_of_large L_pos.le (linnik_large_bd f₀ hf₀ hJ0 hC1 hBd)

/-- **Linnik's theorem with exponent `L`, from a tree.** For a route with `RouteOK` and sound tests: if the terms
at the floor `x^{f₀/DEN}` of the box with no prime pass the test, the tree is valid on the box of one prime with the
cell `(f₀, DEN/2 + 1)`, for a term of the sign `−`, and its cost is below `K`, then there is `K'` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K'·q^L`. -/
theorem linnik_tree [RouteOK] {τ : Tests} (hτ : τ.Sound) (T : Tree) (f₀ : ℕ) (cfg₀ : Cfg)
    (hf₀ : f₀ ≤ DEN / 2 + 1) (hroot : τ.okJ [] f₀ cfg₀ = true) (hok : ok τ T [(f₀, DEN / 2 + 1)] false = true)
    (hcost : cost T [(f₀, DEN / 2 + 1)] < K) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K' * (q : ℝ) ^ L :=
  SieveMain2.route_of_large L_pos.le (linnik_large_tree hτ T f₀ cfg₀ hf₀ hroot hok hcost)

omit [Route] in
/-- **Linnik's theorem from a tree, for any route**: `linnik_tree` with the route as a variable. -/
theorem linnik_tree_at (R : Route) (hR : @RouteOK R) {τ : Tests} (hτ : @Tests.Sound R τ) (T : Tree) (f₀ : ℕ)
    (cfg₀ : Cfg) (hf₀ : f₀ ≤ DEN / 2 + 1) (hroot : τ.okJ [] f₀ cfg₀ = true)
    (hok : ok τ T [(f₀, DEN / 2 + 1)] false = true) (hcost : cost T [(f₀, DEN / 2 + 1)] < K) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K' * (q : ℝ) ^ (@Route.L R) :=
  @linnik_tree R hR τ hτ T f₀ cfg₀ hf₀ hroot hok hcost

end SieveAd

#print axioms SieveAd.linnik_tree
#print axioms SieveAd.linnik_bd
#print axioms SieveAd.linnik_tree_at
