/-
# The cost of an atoms' box of a reversed term

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. For an atoms' box `β` of a reversal through a prime with the cell `ctx = (l₁, h₁)`, and the level
`z = ⌈x^{y/DEN}⌉`, `y` the lower end of the least atom's cell (`SieveAdRevDefs.lean`):

* `famB_empty_of_emptyBox`: a box that passes `emptyBox` has no tuple.
* `trButR`, `trButR_le`, `prod_but`: the product of `trB` over the cells but one, its fixed-point bound, and the
  product by the primes' indices.
* `Wslab_le`: `limsup` of the sum of `1/r'` over the tuples of the box whose product lies in
  `(x^{e₁/DEN}, x^{e₂/DEN}]` is at most `trB(lo_iq, e₂ − e₁)·∏_{others} trB`, for any prime of the box as the one
  that the condition confines: `SieveAd.slab_sum_le` and `sum_inv_slab`.
* `famK_sum_split`: a sum over the tuples with product in `(x^{e₁/DEN}, x^{e₂/DEN}]` is the sum over
  `(x^{e₁/DEN}, x^{m/DEN}]` plus the sum over `(x^{m/DEN}, x^{e₂/DEN}]`.
* `famPr`: the numbers `n = K·r'` with `K` prime, over a family, with weights. `tuple_gB_le`, `tuple_diff_le`: for
  one `r'`, the numbers `n` of the comparison set with `r' | n` rough at `z` are at most `Ψ(x/r', z)/φ(q)`, and they
  exceed those with `n/r'` prime by at most `(Ψ(x/r', z) − #{primes of (x/r', 2x/r']})/φ(q)`, when such an `n` is
  rough at `z`.

The file imports `SieveAdRev.lean`.
-/
import SieveAdRev

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K omKw cdiv trB DEN_pos' K_pos')

/-! ### Boxes with no tuple -/

/-- A box that passes `emptyBox` has no tuple: a cell is empty, or wholly at or above the next older prime's. -/
theorem famB_empty_of_emptyBox [Route] {q : ℕ} (hx : 1 ≤ xq q) : ∀ (β : List Cell) (k : ℕ) (h : β.length = k),
    emptyBox β = true → famB q (boxFn β k h) = ∅ := by
  intro β
  induction β with
  | nil =>
    intro k h he
    simp [emptyBox] at he
  | cons c b ih =>
    intro k h he
    have hk : k = b.length + 1 := by simp at h; omega
    subst hk
    rw [Finset.eq_empty_iff_forall_notMem]
    intro rt hrt
    have ebx : boxFn (c :: b) (b.length + 1) h = Fin.snoc (α := fun _ => Cell) (boxFn b b.length rfl) c :=
      boxFn_cons c b b.length rfl
    rw [ebx] at hrt
    obtain ⟨hp, hsa, hcc⟩ := mem_famB.1 hrt
    have hl := hcc (Fin.last b.length)
    simp only [Fin.snoc_last] at hl
    simp only [emptyBox, Bool.or_eq_true, Nat.ble_eq] at he
    rcases he with he | he
    · have := pow_mono hx he
      linarith [hl.1, hl.2]
    · cases b with
      | nil => simp at he
      | cons d b' =>
        simp only [Bool.or_eq_true, Nat.ble_eq] at he
        rcases he with he | he
        · have hprev := hcc (Fin.castSucc (Fin.last b'.length))
          simp only [Fin.snoc_castSucc] at hprev
          have hd : boxFn (d :: b') (d :: b').length rfl (Fin.last b'.length) = d := by simp [boxFn]
          rw [hd] at hprev
          have hlt : rt (Fin.last (d :: b').length) < rt (Fin.castSucc (Fin.last b'.length)) :=
            hsa (Fin.castSucc_lt_last _)
          have h1 : (rt (Fin.last (d :: b').length) : ℝ) < rt (Fin.castSucc (Fin.last b'.length)) := by
            exact_mod_cast hlt
          have := pow_mono hx he
          linarith [hl.1, hprev.2]
        · have h0 := ih (d :: b').length rfl he
          have hinit := init_mem_famB hrt
          rw [h0] at hinit
          exact absurd hinit (Finset.notMem_empty _)

/-! ### The product of `trB` over the cells but one -/

/-- The product of `trB` over the cells but the one at the position `i`. -/
noncomputable def trButR : ℕ → List Cell → ℝ
  | _, [] => 1
  | 0, _ :: b => (b.map fun d => trB d.1 (d.2 - d.1)).prod
  | i + 1, c :: b => trB c.1 (c.2 - c.1) * trButR i b

/-- `trButR ≤ trBut/SC^{n−1}`, and `trButR ≥ 0`. -/
theorem trButR_le : ∀ (β : List Cell) (i : ℕ), (∀ c ∈ β, 0 < c.1) → i < β.length →
    trButR i β ≤ (trBut i β : ℝ) / (SC : ℝ) ^ (β.length - 1) ∧ 0 ≤ trButR i β := by
  intro β
  induction β with
  | nil =>
    intro i _ hi
    simp at hi
  | cons c b ih =>
    intro i hβ hi
    have hb : ∀ d ∈ b, 0 < d.1 := fun d hd => hβ d (List.mem_cons_of_mem _ hd)
    cases i with
    | zero =>
      simp only [trButR, trBut, List.length_cons, Nat.add_sub_cancel]
      exact prod_trB_le b hb
    | succ i =>
      have hi' : i < b.length := by simpa using hi
      obtain ⟨h1, h0⟩ := ih i hb hi'
      have hx := trB_le_trF (w := c.2 - c.1) (hβ c (List.mem_cons_self ..))
      have hx0 := SieveCert.trB_nonneg c.1 (c.2 - c.1)
      have hS := SC_pos
      constructor
      · simp only [trButR, trBut, List.length_cons, Nat.add_sub_cancel, Nat.cast_mul]
        calc trB c.1 (c.2 - c.1) * trButR i b
            ≤ (trF c.1 (c.2 - c.1) : ℝ) / SC * ((trBut i b : ℝ) / (SC : ℝ) ^ (b.length - 1)) :=
              mul_le_mul hx h1 h0 (hx0.trans hx)
          _ = (trF c.1 (c.2 - c.1) : ℝ) * (trBut i b : ℝ) / (SC : ℝ) ^ b.length := by
              have e : (SC : ℝ) ^ b.length = (SC : ℝ) ^ (b.length - 1) * SC := by
                rw [← pow_succ]
                congr 1
                omega
              rw [e]
              field_simp
      · simp only [trButR]
        exact mul_nonneg hx0 h0

/-- The product of `trB` over the primes but the one of the cell at the position `iq`, by the primes' indices. -/
theorem prod_but : ∀ (β : List Cell) (k : ℕ) (h : β.length = k) (iq : ℕ), iq < k →
    ∏ j : Fin k, (if (j : ℕ) = k - 1 - iq then 1
      else trB (boxFn β k h j).1 ((boxFn β k h j).2 - (boxFn β k h j).1)) = trButR iq β := by
  intro β
  induction β with
  | nil =>
    intro k h iq hiq
    subst h
    simp at hiq
  | cons c b ih =>
    intro k h iq hiq
    subst h
    show ∏ j : Fin (b.length + 1), (if (j : ℕ) = b.length + 1 - 1 - iq then 1
      else trB (boxFn (c :: b) (b.length + 1) rfl j).1
        ((boxFn (c :: b) (b.length + 1) rfl j).2 - (boxFn (c :: b) (b.length + 1) rfl j).1)) = _
    rw [boxFn_cons c b b.length rfl, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    cases iq with
    | zero =>
      have e1 : ∏ j : Fin b.length, (if (j : ℕ) = b.length + 1 - 1 - 0 then 1
          else trB (boxFn b b.length rfl j).1 ((boxFn b b.length rfl j).2 - (boxFn b b.length rfl j).1)) =
          ∏ j : Fin b.length, trB (boxFn b b.length rfl j).1
            ((boxFn b b.length rfl j).2 - (boxFn b b.length rfl j).1) :=
        Finset.prod_congr rfl fun j _ => by
          have hj := j.2
          split_ifs with h1
          · exact absurd h1 (by omega)
          · rfl
      rw [e1, prod_boxFn (fun d => trB d.1 (d.2 - d.1))]
      simp [trButR]
    | succ i =>
      have hi' : i < b.length := by simpa using hiq
      have e1 : ∏ j : Fin b.length, (if (j : ℕ) = b.length + 1 - 1 - (i + 1) then 1
          else trB (boxFn b b.length rfl j).1 ((boxFn b b.length rfl j).2 - (boxFn b b.length rfl j).1)) =
          trButR i b := by
        rw [← ih b.length rfl i hi']
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show b.length + 1 - 1 - (i + 1) = b.length - 1 - i by omega]
      rw [e1]
      simp only [show ¬ (b.length = b.length + 1 - 1 - (i + 1)) by omega, ↓reduceIte, trButR]
      rw [mul_comm]

/-- A product over the indices but `i`. -/
theorem prod_succAbove_eq {k : ℕ} (i : Fin (k + 1)) (G : Fin (k + 1) → ℝ) :
    ∏ j : Fin k, G (i.succAbove j) = ∏ j : Fin (k + 1), if j = i then 1 else G j := by
  rw [Fin.prod_univ_succAbove _ i]
  simp only [↓reduceIte, one_mul]
  exact Finset.prod_congr rfl fun j _ => by simp only [Fin.succAbove_ne i j, ↓reduceIte]

variable [Route]

/-! ### The sums of `1/r'` over the tuples whose product lies in a range -/

/-- **The sum of `1/r'` over an atoms' box under the condition.** For a box of `k + 1` cells with `0 < lo ≤ hi`,
a position `iq`, exponents `e₁ ≤ e₂` and `B ≥ trB(lo_iq, e₂ − e₁)·∏_{others} trB`: for every `δ > 0` and large `q`,
the sum of `1/r'` over the tuples of the box with product in `(x^{e₁/DEN}, x^{e₂/DEN}]` is at most `B + δ`. -/
theorem Wslab_le [RouteOK] {k : ℕ} (β : List Cell) (hk : β.length = k + 1) (hβ : ∀ c ∈ β, 0 < c.1 ∧ c.1 ≤ c.2)
    (iq : ℕ) (hiq : iq < k + 1) {e₁ e₂ : ℕ} (he : e₁ ≤ e₂) {B : ℝ}
    (hB : trB (getC β iq).1 (e₂ - e₁) * trButR iq β ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, Wsum q e₁ e₂ (k + 1) β ≤ B + δ := by
  have hD := DEN_pos'
  obtain ⟨bx, hbx⟩ : ∃ bx, bx = boxFn β (k + 1) hk := ⟨_, rfl⟩
  have hcell : ∀ j, 0 < (bx j).1 ∧ (bx j).1 ≤ (bx j).2 := fun j => by
    rw [hbx]; exact hβ _ (boxFn_mem β _ hk j)
  obtain ⟨i, hi⟩ : ∃ i : Fin (k + 1), i = ⟨k + 1 - 1 - iq, by omega⟩ := ⟨_, rfl⟩
  have hget : getC β iq = bx i := by rw [hbx, hi]; exact getC_eq β (k + 1) hk iq hiq
  obtain ⟨a, ha⟩ : ∃ a, a = (bx i).1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact (hcell i).1
  obtain ⟨w, hw⟩ : ∃ w, w = e₂ - e₁ := ⟨_, rfl⟩
  obtain ⟨Tq, hTq⟩ : ∃ Tq, Tq = trB a w := ⟨_, rfl⟩
  have hTq0 : 0 ≤ Tq := by rw [hTq]; exact SieveCert.trB_nonneg _ _
  obtain ⟨Po, hPo⟩ : ∃ Po, Po = trButR iq β := ⟨_, rfl⟩
  have hPo_eq : ∏ j : Fin k, trB (bx (i.succAbove j)).1 ((bx (i.succAbove j)).2 - (bx (i.succAbove j)).1) = Po := by
    rw [prod_succAbove_eq i (fun j => trB (bx j).1 ((bx j).2 - (bx j).1)), hPo, ← prod_but β (k + 1) hk iq hiq, hbx]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact if_congr (by rw [hi, Fin.ext_iff]) rfl rfl
  have hPo0 : 0 ≤ Po := by
    rw [← hPo_eq]; exact Finset.prod_nonneg fun j _ => SieveCert.trB_nonneg _ _
  rw [hget, ← ha, ← hw, ← hTq, ← hPo] at hB
  obtain ⟨d, hd⟩ : ∃ d, d = min 1 (δ / (Tq + Po + 1)) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact lt_min one_pos (by positivity)
  have hd1 : d ≤ 1 := by rw [hd]; exact min_le_left _ _
  have hd2 : d * (Tq + Po + 1) ≤ δ := by
    have h := min_le_right 1 (δ / (Tq + Po + 1))
    rw [← hd] at h
    calc d * (Tq + Po + 1) ≤ δ / (Tq + Po + 1) * (Tq + Po + 1) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = δ := div_mul_cancel₀ _ (by positivity)
  have hprod := EvLe.prod
    (fun j x => ∑ p ∈ boxP x (bx (i.succAbove j)).1 ((bx (i.succAbove j)).2 - (bx (i.succAbove j)).1), 1 / (p : ℝ))
    (fun j => trB (bx (i.succAbove j)).1 ((bx (i.succAbove j)).2 - (bx (i.succAbove j)).1))
    (fun j => SieveCert.trB_nonneg _ _) (fun j => Filter.Eventually.of_forall fun x => sum_inv_nonneg _)
    (fun j => evLe_box_tr (hcell _).1)
  rw [hPo_eq] at hprod
  filter_upwards [SieveDrop.tendsto_xq.eventually (sum_inv_slab (a := a) (w := w) ha0 hd0),
    SieveDrop.tendsto_xq.eventually (hprod d hd0), big_ev] with q hfibq hprodq hbig
  obtain ⟨-, hx3, -⟩ := big_facts hbig
  have hx0 : 0 < xq q := by linarith
  rw [Wsum_eq q e₁ e₂ (k + 1) β (k + 1) hk, ← hbx]
  obtain ⟨S, hS⟩ : ∃ S : Fin (k + 1) → Finset ℕ, S = fun j => boxP (xq q) (bx j).1 ((bx j).2 - (bx j).1) :=
    ⟨_, rfl⟩
  have hSmem : ∀ j p, p ∈ S j → p.Prime ∧ xq q ^ (((bx j).1 : ℝ) / DEN) ≤ p := by
    intro j p hp
    rw [hS] at hp
    exact ⟨(mem_primesIn.1 hp).1, (mem_primesIn.1 hp).2.1⟩
  have hsub : famK q e₁ e₂ (k + 1) bx ⊆ (Fintype.piFinset S).filter (fun r =>
      xq q ^ ((e₁ : ℝ) / DEN) < ((∏ j, r j : ℕ) : ℝ) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ xq q ^ ((e₂ : ℝ) / DEN)) := by
    intro rt hrt
    rw [famK, Finset.mem_filter] at hrt
    obtain ⟨hrt, hsl⟩ := hrt
    obtain ⟨hp, -, hc⟩ := mem_famB.1 hrt
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun j => ?_, ?_⟩
    · rw [hS]
      show rt j ∈ boxP (xq q) (bx j).1 ((bx j).2 - (bx j).1)
      rw [boxP, mem_primesIn]
      refine ⟨(hp j).2, (hc j).1, ?_⟩
      have e : (((bx j).1 : ℝ) + (((bx j).2 - (bx j).1 : ℕ) : ℝ)) = ((bx j).2 : ℝ) := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' (hcell j).2]
      rw [e]
      exact (hc j).2
    · unfold slabP at hsl
      rw [aprodR_full (le_refl _)] at hsl
      push_cast
      exact hsl
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ =>
    Finset.prod_nonneg fun j _ => by positivity).trans ?_
  have hslab := slab_sum_le S i (c := Tq + d) (θ₁ := xq q ^ ((e₁ : ℝ) / DEN)) (θ₂ := xq q ^ ((e₂ : ℝ) / DEN))
    (A₀ := xq q ^ ((a : ℝ) / DEN)) (fun j p hp => (hSmem j p hp).1)
    (fun p hp => by rw [ha]; exact (hSmem i p hp).2) (Real.rpow_pos_of_pos hx0 _) (Real.rpow_nonneg hx0.le _)
    (fun A B hA hB => by
      rw [hTq]
      refine hfibq A B hA (hB.trans (le_of_eq ?_))
      congr 1
      rw [← Real.rpow_sub hx0, hw]
      congr 1
      rw [Nat.cast_sub he]
      ring)
  refine hslab.trans ?_
  have hprodq' : ∏ j : Fin k, ∑ p ∈ S (i.succAbove j), 1 / (p : ℝ) ≤ Po + d := by
    rw [hS]
    exact hprodq
  calc (Tq + d) * ∏ j : Fin k, ∑ p ∈ S (i.succAbove j), 1 / (p : ℝ)
      ≤ (Tq + d) * (Po + d) := mul_le_mul_of_nonneg_left hprodq' (by linarith)
    _ = Tq * Po + d * (Tq + Po + d) := by ring
    _ ≤ B + δ := by nlinarith [mul_nonneg hd0.le (sub_nonneg.2 hd1)]

/-- A sum over the tuples with product in `(x^{e₁/DEN}, x^{e₂/DEN}]` is the sum over `(x^{e₁/DEN}, x^{m/DEN}]` plus
the sum over `(x^{m/DEN}, x^{e₂/DEN}]`, for `e₁ ≤ m ≤ e₂`. -/
theorem famK_sum_split {q : ℕ} (hx : 1 ≤ xq q) {e₁ m e₂ : ℕ} (h1 : e₁ ≤ m) (h2 : m ≤ e₂) (na : ℕ) {k : ℕ}
    (bx : Fin k → Cell) (G : (Fin k → ℕ) → ℝ) :
    ∑ rt ∈ famK q e₁ e₂ na bx, G rt = ∑ rt ∈ famK q e₁ m na bx, G rt + ∑ rt ∈ famK q m e₂ na bx, G rt := by
  have hA : famK q e₁ m na bx = (famK q e₁ e₂ na bx).filter fun rt => aprodR na rt ≤ xq q ^ ((m : ℝ) / DEN) := by
    ext rt
    simp only [famK, slabP, Finset.mem_filter]
    constructor
    · rintro ⟨hrt, hlo, hhi⟩
      exact ⟨⟨hrt, hlo, hhi.trans (pow_mono hx h2)⟩, hhi⟩
    · rintro ⟨⟨hrt, hlo, -⟩, hhi⟩
      exact ⟨hrt, hlo, hhi⟩
  have hB : famK q m e₂ na bx = (famK q e₁ e₂ na bx).filter fun rt => ¬ aprodR na rt ≤ xq q ^ ((m : ℝ) / DEN) := by
    ext rt
    simp only [famK, slabP, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨hrt, hlo, hhi⟩
      exact ⟨⟨hrt, lt_of_le_of_lt (pow_mono hx h1) hlo, hhi⟩, hlo⟩
    · rintro ⟨⟨hrt, -, hhi⟩, hlo⟩
      exact ⟨hrt, hlo, hhi⟩
  rw [hA, hB, Finset.sum_filter_add_sum_filter_not]

/-! ### The numbers of the comparison set over one `r'` -/

/-- The numbers `n = K·∏rt` with `K` prime, with weights `g`, over a family. -/
noncomputable def famPr (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) : ℝ :=
  ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, g n * (if (∏ i, rt i) ∣ n ∧ (n / ∏ i, rt i).Prime then 1 else 0)

/-- For `q ≥ 1` and `r > 0`, the numbers `n` of the comparison set with `r | n` and no prime factor below `z` are at
most `Ψ(x/r, z)/φ(q)`. -/
theorem tuple_gB_le {q : ℕ} (hq : 1 ≤ q) {r z : ℕ} (hr : 0 < r) :
    ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if r ∣ n ∧ SieveTree.rough z n then 1 else 0) ≤
      (q.totient : ℝ)⁻¹ * (Psi (xq q / r) z : ℝ) := by
  have hx : 0 < xq q := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  calc ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if r ∣ n ∧ SieveTree.rough z n then 1 else 0)
      ≤ ∑ n ∈ Ioc (N1 q) (N2 q), (q.totient : ℝ)⁻¹ * (if r ∣ n ∧ SieveTree.rough z n then 1 else 0) :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (SieveDrop.gB_le q n) (by split_ifs <;> norm_num)
    _ = (q.totient : ℝ)⁻¹ * (((Ioc (N1 q) (N2 q)).filter
          (fun n => r ∣ n ∧ SieveTree.rough z n)).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.card_filter]
        push_cast
        rfl
    _ ≤ (q.totient : ℝ)⁻¹ * (Psi (xq q / r) z : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast SieveDrop.card_le_Psi hx hr

/-- For `q ≥ 1` and `r > 0` such that the `n ∈ (N₁, N₂]` with `r | n` and `n/r` prime have no prime factor below
`z`: the numbers `n` of the comparison set with `r | n` and no prime factor below `z` exceed those with `n/r` prime
by at most `(Ψ(x/r, z) − #{primes of (x/r, 2x/r]})/φ(q)`. -/
theorem tuple_diff_le {q : ℕ} (hq : 1 ≤ q) {r z : ℕ} (hr : 0 < r)
    (H : ∀ n ∈ Ioc (N1 q) (N2 q), r ∣ n → (n / r).Prime → SieveTree.rough z n) :
    ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if r ∣ n ∧ SieveTree.rough z n then 1 else 0) -
        ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if r ∣ n ∧ (n / r).Prime then 1 else 0) ≤
      (q.totient : ℝ)⁻¹ * ((Psi (xq q / r) z : ℝ) -
        (((Ioc ⌊xq q / r⌋₊ ⌊2 * (xq q / r)⌋₊).filter Nat.Prime).card : ℝ)) := by
  have hx : 0 < xq q := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨T, hT⟩ : ∃ T, T = (Ioc (N1 q) (N2 q)).filter (fun n => r ∣ n ∧ SieveTree.rough z n) := ⟨_, rfl⟩
  have hpt : ∀ n ∈ Ioc (N1 q) (N2 q),
      gB q n * (if r ∣ n ∧ SieveTree.rough z n then 1 else 0) -
        gB q n * (if r ∣ n ∧ (n / r).Prime then 1 else 0) ≤
      (q.totient : ℝ)⁻¹ * (if (r ∣ n ∧ SieveTree.rough z n) ∧ ¬ (n / r).Prime then 1 else 0) := by
    intro n hn
    have hg := SieveDrop.gB_le q n
    have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
    by_cases hA : r ∣ n ∧ SieveTree.rough z n
    · by_cases hP : (n / r).Prime
      · simp [hA, hP]
      · simp only [hA, hP, and_self, and_false, not_false_eq_true, ↓reduceIte, mul_one, mul_zero, sub_zero]
        exact hg
    · have hB : ¬ (r ∣ n ∧ (n / r).Prime) := fun hB => hA ⟨hB.1, H n hn hB.1 hB.2⟩
      simp [hA, hB]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_boole]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcT : T.card ≤ Psi (xq q / r) z := by rw [hT]; exact SieveDrop.card_le_Psi hx hr
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun n => (n / r).Prime)
  have hinj : ((Ioc ⌊xq q / r⌋₊ ⌊2 * (xq q / r)⌋₊).filter Nat.Prime).card ≤
      (T.filter fun n => (n / r).Prime).card := by
    refine Finset.card_le_card_of_injOn (fun K => K * r) ?_ ?_
    · intro K hK
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hK
      obtain ⟨⟨hK1, hK2⟩, hKp⟩ := hK
      have hn1 : N1 q < K * r := by
        have h1 : xq q / r < (K : ℝ) := Nat.lt_of_floor_lt hK1
        rw [div_lt_iff₀ hr'] at h1
        rw [Nat.floor_lt hx.le]
        push_cast
        exact h1
      have hn2 : K * r ≤ N2 q := by
        have h1 : (K : ℝ) ≤ 2 * (xq q / r) := (Nat.le_floor_iff (by positivity)).1 hK2
        refine Nat.le_floor ?_
        push_cast
        rw [mul_div_assoc', le_div_iff₀ hr'] at h1
        exact h1
      have hdiv : K * r / r = K := Nat.mul_div_cancel K hr
      rw [Finset.mem_coe, Finset.mem_filter, hT, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨⟨hn1, hn2⟩, dvd_mul_left r K, H (K * r) (Finset.mem_Ioc.2 ⟨hn1, hn2⟩) (dvd_mul_left r K)
        (by rw [hdiv]; exact hKp)⟩, by rw [hdiv]; exact hKp⟩
    · intro K₁ _ K₂ _ h
      exact Nat.eq_of_mul_eq_mul_right hr h
  have heq : (Ioc (N1 q) (N2 q)).filter (fun n => (r ∣ n ∧ SieveTree.rough z n) ∧ ¬ (n / r).Prime) =
      T.filter (fun n => ¬ (n / r).Prime) := by
    rw [hT, Finset.filter_filter]
  rw [heq]
  have h1 : (T.filter fun n => ¬ (n / r).Prime).card +
      ((Ioc ⌊xq q / r⌋₊ ⌊2 * (xq q / r)⌋₊).filter Nat.Prime).card ≤ Psi (xq q / r) z := by omega
  have h2 := (Nat.cast_le (α := ℝ)).2 h1
  push_cast at h2
  linarith

/-! ### The cost of an atoms' box -/

omit [Route] in
/-- A box that does not pass `emptyBox` has cells with `lo < hi`. -/
theorem cells_of_not_emptyBox : ∀ β : List Cell, emptyBox β = false → ∀ c ∈ β, c.1 < c.2 := by
  intro β
  induction β with
  | nil => intro _ c hc; simp at hc
  | cons c b ih =>
    intro he d hd
    simp only [emptyBox, Bool.or_eq_false_iff] at he
    obtain ⟨he1, he2⟩ := he
    rcases List.mem_cons.1 hd with rfl | hd
    · by_contra hlt
      have : Nat.ble d.2 d.1 = true := by rw [Nat.ble_eq]; omega
      rw [this] at he1
      exact absurd he1 (by simp)
    · cases b with
      | nil => simp at hd
      | cons d' b' =>
        simp only [Bool.or_eq_false_iff] at he2
        exact ih he2.2 d hd

/-- **What the cost of an atoms' box bounds**: the terms of the box under the condition, at the level of its least
prime's lower end, in `𝒜`, minus the numbers `K·r'` of the comparison set with `K` prime, over the `r'` of the box
between `x^{(DEN−h₁+1)/DEN}` and `x^{(DEN−l₁)/DEN}`, are at most `(C/K + o(1))x/(φ(q) log x)`. -/
def FamBd (ctx : Cell) (β : List Cell) (C : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ (((getC β 0).1 : ℝ) / DEN)⌉₊
        (famK q (e1 ctx) (e2 ctx) β.length (boxFn β β.length rfl)) -
      famPr (gB q) (N1 q) (N2 q) (famK q (e1 ctx + 1) (e2 ctx - 1) β.length (boxFn β β.length rfl)) ≤
        (q.totient : ℝ)⁻¹ * (((C : ℝ) / K + η) * Xq q)

omit [Route] in
/-- The fixed-point cost of a sum of `1/r'`: `(A/K)·trB(a, w)·trButR ≤ ⌈m·trF(a, w)·trBut·A/SC^n⌉/K` for `m ≥ 1`
copies. -/
theorem cost_ge (β : List Cell) (hβ : ∀ c ∈ β, 0 < c.1) (iq : ℕ) (hiq : iq < β.length) (a w : ℕ) (ha : 0 < a)
    (A : ℕ) :
    (A : ℝ) / K * (trB a w * trButR iq β) ≤ (cdiv (trF a w * trBut iq β * A) (SC ^ β.length) : ℝ) / K := by
  have hK := K_pos'
  have hS := SC_pos
  obtain ⟨h1, h0⟩ := trButR_le β iq hβ hiq
  have hx := trB_le_trF (w := w) ha
  have hx0 := SieveCert.trB_nonneg a w
  have h2 : trB a w * trButR iq β ≤ (trF a w : ℝ) / SC * ((trBut iq β : ℝ) / (SC : ℝ) ^ (β.length - 1)) :=
    mul_le_mul hx h1 h0 (hx0.trans hx)
  have hpos : 0 < SC ^ β.length := pow_pos (by unfold SC; norm_num) _
  have h3 := SieveCert.div_le_cdiv (trF a w * trBut iq β * A) (SC ^ β.length) hpos
  have e : (SC : ℝ) ^ β.length = (SC : ℝ) ^ (β.length - 1) * SC := by
    rw [← pow_succ]
    congr 1
    omega
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
  refine (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg A)).trans (le_trans (le_of_eq ?_) h3)
  push_cast
  rw [e]
  field_simp

set_option maxHeartbeats 1600000 in
/-- **The cost of an atoms' box bounds it.** For tests that are sound under two more atoms, a cell
`ctx = (l₁, h₁)` with `0 < l₁ < h₁ ≤ DEN`, and an atoms' box `β` of at most twelve cells with positive lower ends,
its least prime's lower end `y` at most `l₁` with `h₁ + y + 1 ≤ DEN`: a cost that `famCost` returns below its limit
bounds the box (`FamBd`). -/
theorem famCost_sound [RouteOK] {τ : Tests} (hτ : τ.SoundX) (SK : Cell → ℕ → Strat) (fuel : ℕ) {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 < ctx.2 ∧ ctx.2 ≤ DEN) (β : List Cell) (hβ : ∀ c ∈ β, 0 < c.1)
    (hlen : β.length ≤ 12) (iq : ℕ) (hiq : iq < β.length) (hy : (getC β 0).1 ≤ ctx.1)
    (hyh : ctx.2 + (getC β 0).1 + 1 ≤ DEN) {lim : ℕ} (h : famCost τ SK fuel ctx β iq lim < lim) :
    FamBd ctx β (famCost τ SK fuel ctx β iq lim) := by
  intro η hη
  have hD := DEN_pos'
  have hK := K_pos'
  unfold famCost at h ⊢
  by_cases hem : emptyBox β = true
  · rw [hem, Bool.cond_true]
    filter_upwards [big_ev] with q hbig a _
    obtain ⟨-, hx3, -⟩ := big_facts hbig
    have hempty := famB_empty_of_emptyBox (q := q) (by linarith) β β.length rfl hem
    have hX := Xq_pos hbig
    simp only [famK, hempty, Finset.filter_empty, famJ, famPr, Finset.sum_empty, sub_zero, Nat.cast_zero,
      zero_div, zero_add]
    positivity
  rw [Bool.not_eq_true] at hem
  rw [hem, Bool.cond_false] at h ⊢
  obtain ⟨c, b, rfl⟩ : ∃ c b, β = c :: b := by
    cases β with
    | nil => simp at hiq
    | cons c b => exact ⟨c, b, rfl⟩
  have hcells := cells_of_not_emptyBox _ hem
  have hβ' : ∀ d ∈ c :: b, 0 < d.1 ∧ d.1 ≤ d.2 := fun d hd => ⟨hβ d hd, (hcells d hd).le⟩
  have hyc : (getC (c :: b) 0).1 = c.1 := rfl
  rw [hyc] at hy hyh
  obtain ⟨C, hCdef⟩ : ∃ C, C = rootJ τ (SK ctx (c :: b).length) ctx fuel (c :: b) CAPK := ⟨_, rfl⟩
  simp only [← hCdef] at h ⊢
  by_cases hcap : Nat.ble CAPK C = true
  · rw [hcap, Bool.cond_true] at h
    omega
  rw [Bool.not_eq_true] at hcap
  rw [hcap, Bool.cond_false] at h ⊢
  have hClt : C < CAPK := by
    by_contra hge
    have : Nat.ble CAPK C = true := by rw [Nat.ble_eq]; omega
    rw [this] at hcap
    exact absurd hcap (by simp)
  have hctx' : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN := ⟨hctx.1, hctx.2.1.le, hctx.2.2⟩
  have hroot := rootJ_sound hτ hctx' (SK ctx (c :: b).length) fuel c b (hcells c (List.mem_cons_self ..)).le
    (by simpa using hlen) (lim := CAPK) (by rw [← hCdef]; exact hClt)
  rw [← hCdef] at hroot
  -- the numbers of the cost
  obtain ⟨y, hydef⟩ : ∃ y : ℕ, y = c.1 := ⟨_, rfl⟩
  rw [← hydef] at hy hyh hroot
  have hy0 : 0 < y := by rw [hydef]; exact hβ c (List.mem_cons_self ..)
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy0
  obtain ⟨qa, hqa⟩ : ∃ qa : ℕ, qa = (getC (c :: b) iq).1 := ⟨_, rfl⟩
  have hqa0 : 0 < qa := by
    rw [hqa, getC_eq (c :: b) (b.length + 1) rfl iq (by simpa using hiq)]
    exact hβ _ (boxFn_mem _ _ rfl _)
  obtain ⟨Ri, hRi⟩ : ∃ Ri : ℝ, Ri = trB qa (ctx.2 - ctx.1 - 1) * trButR iq (c :: b) := ⟨_, rfl⟩
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℝ, Rb = trB qa 1 * trButR iq (c :: b) := ⟨_, rfl⟩
  have hTR0 := (trButR_le (c :: b) iq hβ hiq).2
  have hRi0 : 0 ≤ Ri := by rw [hRi]; exact mul_nonneg (SieveCert.trB_nonneg _ _) hTR0
  have hRb0 : 0 ≤ Rb := by rw [hRb]; exact mul_nonneg (SieveCert.trB_nonneg _ _) hTR0
  obtain ⟨omi, homi⟩ : ∃ omi : ℕ, omi = omKw (DEN - ctx.2 - y) y (ctx.2 - ctx.1) 1 := ⟨_, rfl⟩
  obtain ⟨omb, homb⟩ : ∃ omb : ℕ, omb = omKw (DEN - ctx.2 - y - 1) y (ctx.2 - ctx.1 + 2) 1 := ⟨_, rfl⟩
  obtain ⟨pen, hpen⟩ : ∃ pen : ℝ, pen = (penK ctx y : ℝ) / K := ⟨_, rfl⟩
  obtain ⟨bd, hbd⟩ : ∃ bd : ℝ, bd = (bdK ctx y : ℝ) / K := ⟨_, rfl⟩
  have hpen0 : 0 ≤ pen := by rw [hpen]; positivity
  have hbd0 : 0 ≤ bd := by rw [hbd]; positivity
  have hh' : (0 : ℝ) < ctx.2 := by exact_mod_cast (show 0 < ctx.2 by omega)
  have hpenge : (omi : ℝ) / K * ((DEN : ℝ) / y) - (DEN : ℝ) / ctx.2 ≤ pen := by
    rw [hpen, le_div_iff₀ hK]
    have h1 := SieveCert.div_le_cdiv (omi * DEN) y hy0
    have h2 : ((K * DEN / ctx.2 : ℕ) : ℝ) ≤ ((K * DEN : ℕ) : ℝ) / ctx.2 := Nat.cast_div_le
    have h3 : (cdiv (omi * DEN) y : ℝ) - ((K * DEN / ctx.2 : ℕ) : ℝ) ≤ (penK ctx y : ℝ) := by
      have : cdiv (omi * DEN) y ≤ cdiv (omi * DEN) y - K * DEN / ctx.2 + K * DEN / ctx.2 := by omega
      have h4 : (cdiv (omi * DEN) y : ℝ) ≤ ((cdiv (omi * DEN) y - K * DEN / ctx.2 : ℕ) : ℝ) +
          ((K * DEN / ctx.2 : ℕ) : ℝ) := by exact_mod_cast this
      unfold penK
      rw [← homi]
      linarith
    push_cast at h1 h2
    have e : ((omi : ℝ) / K * ((DEN : ℝ) / y) - (DEN : ℝ) / ctx.2) * K =
        (omi : ℝ) * DEN / y - (K : ℝ) * DEN / ctx.2 := by field_simp
    rw [e]
    linarith
  have hbdge : (omb : ℝ) / K * ((DEN : ℝ) / y) ≤ bd := by
    rw [hbd, le_div_iff₀ hK]
    have h1 := SieveCert.div_le_cdiv (omb * DEN) y hy0
    push_cast at h1
    have e : (omb : ℝ) / K * ((DEN : ℝ) / y) * K = (omb : ℝ) * DEN / y := by field_simp
    rw [e]
    unfold bdK
    rw [← homb]
    exact h1
  -- the cost
  have hcost : ((C : ℝ) / K + pen) * Ri + ((C : ℝ) / K + bd) * (2 * Rb) ≤
      ((cdiv (trF qa (ctx.2 - ctx.1 - 1) * trBut iq (c :: b) * (C + penK ctx y)) (SC ^ (c :: b).length) +
        cdiv (2 * trF qa 1 * trBut iq (c :: b) * (C + bdK ctx y)) (SC ^ (c :: b).length) : ℕ) : ℝ) / K := by
    have h1 := cost_ge (c :: b) hβ iq hiq qa (ctx.2 - ctx.1 - 1) hqa0 (C + penK ctx y)
    have h2 := cost_ge (c :: b) hβ iq hiq qa 1 hqa0 (2 * (C + bdK ctx y))
    have e2 : trF qa 1 * trBut iq (c :: b) * (2 * (C + bdK ctx y)) =
        2 * trF qa 1 * trBut iq (c :: b) * (C + bdK ctx y) := by ring
    rw [e2] at h2
    rw [← hRi] at h1
    rw [← hRb] at h2
    push_cast at h1 h2 ⊢
    rw [add_div]
    have e3 : ((C : ℝ) / K + pen) * Ri = ((C : ℝ) + penK ctx y) / K * Ri := by rw [hpen]; ring
    have e4 : ((C : ℝ) / K + bd) * (2 * Rb) = 2 * ((C : ℝ) + bdK ctx y) / K * Rb := by rw [hbd]; ring
    rw [e3, e4]
    linarith
  -- the margins
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 + (DEN : ℝ) / ctx.2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 3 * ((C : ℝ) / K) + Ri + 4 * Rb + 3 + pen + u * Ri + u + 2 * bd + 2 := ⟨_, rfl⟩
  have hCK0 : (0 : ℝ) ≤ (C : ℝ) / K := by positivity
  have hM0 : 0 < M := by
    rw [hM]
    have := mul_nonneg hu0 hRi0
    linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min 1 (η / (2 * M)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := by rw [ht]; exact min_le_left _ _
  have htM : t * M ≤ η / 2 := by
    have h1 : t ≤ η / (2 * M) := by rw [ht]; exact min_le_right _ _
    calc t * M ≤ η / (2 * M) * M := mul_le_mul_of_nonneg_right h1 hM0.le
      _ = η / 2 := by field_simp
  -- the exponents of the three ranges
  have hD1 : 1 ≤ DEN := by unfold SieveCert.DEN; exact Nat.one_le_two_pow
  have he12 : e1 ctx + 1 ≤ e2 ctx - 1 := by unfold e1 e2; omega
  have hwi : e2 ctx - 1 - (e1 ctx + 1) = ctx.2 - ctx.1 - 1 := by unfold e1 e2; omega
  have hwl : e1 ctx + 1 - e1 ctx = 1 := by omega
  have hwh : e2 ctx - (e2 ctx - 1) = 1 := by unfold e2; omega
  have hWi := Wslab_le (c :: b) (k := b.length) rfl hβ' iq (by simpa using hiq) he12 (B := Ri)
    (by rw [hwi, ← hqa, hRi]) ht0
  have hWl := Wslab_le (c :: b) (k := b.length) rfl hβ' iq (by simpa using hiq) (Nat.le_succ (e1 ctx)) (B := Rb)
    (by rw [hwl, ← hqa, hRb]) ht0
  have hWh := Wslab_le (c :: b) (k := b.length) rfl hβ' iq (by simpa using hiq) (Nat.sub_le (e2 ctx) 1) (B := Rb)
    (by rw [hwh, ← hqa, hRb]) ht0
  -- the rough numbers and the primes of `(x/r', 2x/r']`
  have hsi : DEN - ctx.2 - y + y + 1 = e1 ctx + 1 := by unfold e1; omega
  have hsi2 : DEN - ctx.2 - y + y + (ctx.2 - ctx.1) = e2 ctx - 1 := by unfold e1 e2 at *; omega
  have hsb : DEN - ctx.2 - y - 1 + y + 1 = e1 ctx := by unfold e1; omega
  have hsb2 : DEN - ctx.2 - y - 1 + y + (ctx.2 - ctx.1 + 2) = e2 ctx := by unfold e2; omega
  have hψi := psi_level (y := y) (s := DEN - ctx.2 - y) (W := ctx.2 - ctx.1) hy0 (by omega) ht0
  have hψb := psi_level (y := y) (s := DEN - ctx.2 - y - 1) (W := ctx.2 - ctx.1 + 2) hy0 (by omega) ht0
  rw [hsi, hsi2, ← homi] at hψi
  rw [hsb, hsb2, ← homb] at hψb
  have hc1' : (0 : ℝ) < (ctx.1 : ℝ) / DEN := div_pos (by exact_mod_cast hctx.1) hD
  have hπ := primes_level (h := ctx.2) (by omega) hc1' ht0
  filter_upwards [hroot t ht0 (η / 2) (by positivity), hWi, hWl, hWh, SieveDrop.tendsto_xq.eventually hψi,
    SieveDrop.tendsto_xq.eventually hψb, SieveDrop.tendsto_xq.eventually hπ, big_ev, eventually_ge_atTop 1]
    with q hrootq hWiq hWlq hWhq hψiq hψbq hπq hbig hq1 a ha
  obtain ⟨-, hx3, -, -, -⟩ := big_facts hbig
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hlx : 0 < Real.log (xq q) := Real.log_pos (by linarith)
  have hX := Xq_pos hbig
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  obtain ⟨z, hz⟩ : ∃ z : ℕ, z = ⌈xq q ^ ((y : ℝ) / DEN)⌉₊ := ⟨_, rfl⟩
  rw [hyc, ← hydef, ← hz]
  rw [← hz] at hψiq hψbq
  obtain ⟨bx, hbx⟩ : ∃ bx, bx = boxFn (c :: b) (c :: b).length rfl := ⟨_, rfl⟩
  rw [← hbx]
  have hlastc : bx (Fin.last b.length) = c := by rw [hbx]; simp [boxFn]
  -- a tuple of the box under a condition between the two ends
  have htuple : ∀ {ea eb : ℕ}, e1 ctx ≤ ea → eb ≤ e2 ctx → ∀ rt ∈ famK q ea eb (c :: b).length bx,
      (0 < ∏ i, rt i) ∧ xq q ^ ((ea : ℝ) / DEN) < ((∏ i, rt i : ℕ) : ℝ) ∧
        ((∏ i, rt i : ℕ) : ℝ) ≤ xq q ^ ((eb : ℝ) / DEN) ∧ (∀ i, (rt i).Prime ∧ z ≤ rt i) := by
    intro ea eb _ _ rt hrt
    rw [famK, Finset.mem_filter] at hrt
    obtain ⟨hrt, hsl⟩ := hrt
    obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hrt
    unfold slabP at hsl
    rw [aprodR_full (le_refl _)] at hsl
    have hcast : ((∏ i, rt i : ℕ) : ℝ) = ∏ i, (rt i : ℝ) := by push_cast; rfl
    rw [hcast]
    refine ⟨Finset.prod_pos fun i _ => (hp i).2.pos, hsl.1, hsl.2, fun i => ⟨(hp i).2, ?_⟩⟩
    have h1 : z ≤ rt (Fin.last b.length) := by
      rw [hz]
      refine Nat.ceil_le.2 ?_
      have := (hc (Fin.last b.length)).1
      rw [hlastc, ← hydef] at this
      exact this
    exact h1.trans (hsa.antitone (Fin.le_last i))
  have hxr : ∀ rt : Fin (c :: b).length → ℕ, (0 < ∏ i, rt i) →
      xq q / ((∏ i, rt i : ℕ) : ℝ) / Real.log (xq q) = Xq q * ∏ i, (1 / (rt i : ℝ)) := by
    intro rt hpos
    have hr' : (0 : ℝ) < ((∏ i, rt i : ℕ) : ℝ) := by exact_mod_cast hpos
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    unfold Xq
    push_cast at hr' ⊢
    field_simp
  -- the terms of a tuple in the comparison set
  have hJb : ∀ {ea eb : ℕ}, e1 ctx ≤ ea → eb ≤ e2 ctx → ∀ rt ∈ famK q ea eb (c :: b).length bx,
      ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0) ≤
        (q.totient : ℝ)⁻¹ * ((bd + t) * (Xq q * ∏ i, (1 / (rt i : ℝ)))) := by
    intro ea eb hea heb rt hrt
    obtain ⟨hpos, hlo, hhi, -⟩ := htuple hea heb rt hrt
    have h1 := tuple_gB_le hq1 (z := z) hpos
    have h2 := hψbq ((∏ i, rt i : ℕ) : ℝ) ((pow_mono hx1 hea).trans hlo.le) (hhi.trans (pow_mono hx1 heb))
    rw [hxr rt hpos] at h2
    have h3 : 0 ≤ Xq q * ∏ i, (1 / (rt i : ℝ)) :=
      mul_nonneg hX.le (Finset.prod_nonneg fun i _ => by positivity)
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right (by linarith) h3)) hφ)
  have hJi : ∀ rt ∈ famK q (e1 ctx + 1) (e2 ctx - 1) (c :: b).length bx,
      ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0) -
          ∑ n ∈ Ioc (N1 q) (N2 q), gB q n * (if (∏ i, rt i) ∣ n ∧ (n / ∏ i, rt i).Prime then 1 else 0) ≤
        (q.totient : ℝ)⁻¹ * ((pen + t * u) * (Xq q * ∏ i, (1 / (rt i : ℝ)))) := by
    intro rt hrt
    obtain ⟨hpos, hlo, hhi, hpr⟩ := htuple (Nat.le_succ _) (Nat.sub_le _ _) rt hrt
    obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = ∏ i, rt i := ⟨_, rfl⟩
    rw [← hrdef] at hpos hlo hhi ⊢
    have hr' : (0 : ℝ) < r := by exact_mod_cast hpos
    -- `x/r` lies between `x^{l₁/DEN}` and `x^{h₁/DEN}`
    have hYlo : xq q ^ ((ctx.1 : ℝ) / DEN) ≤ xq q / r := by
      rw [le_div_iff₀ hr']
      calc xq q ^ ((ctx.1 : ℝ) / DEN) * r ≤ xq q ^ ((ctx.1 : ℝ) / DEN) * xq q ^ (((e2 ctx - 1 : ℕ) : ℝ) / DEN) :=
            mul_le_mul_of_nonneg_left hhi (Real.rpow_nonneg hx0.le _)
        _ = xq q ^ (1 : ℝ) := by
            rw [← Real.rpow_add hx0]
            congr 1
            have : ((e2 ctx - 1 : ℕ) : ℝ) = (DEN : ℝ) - ctx.1 := by
              rw [show e2 ctx - 1 = DEN - ctx.1 by unfold e2; omega, Nat.cast_sub (by omega)]
            rw [this]
            field_simp
            ring
        _ = xq q := Real.rpow_one _
    have hYhi : xq q / r ≤ xq q ^ ((ctx.2 : ℝ) / DEN) := by
      rw [div_le_iff₀ hr']
      calc xq q = xq q ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ xq q ^ ((ctx.2 : ℝ) / DEN) * xq q ^ (((e1 ctx + 1 : ℕ) : ℝ) / DEN) := by
            rw [← Real.rpow_add hx0]
            refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
            have : ((e1 ctx + 1 : ℕ) : ℝ) = (DEN : ℝ) - ctx.2 + 1 := by
              unfold e1
              rw [Nat.cast_add, Nat.cast_sub hctx.2.2, Nat.cast_one]
            rw [this, ← add_div, le_div_iff₀ hD]
            linarith
        _ ≤ xq q ^ ((ctx.2 : ℝ) / DEN) * r := mul_le_mul_of_nonneg_left hlo.le (Real.rpow_nonneg hx0.le _)
    -- a number `n = K·r` with `K` prime has no prime factor below `z`
    have H : ∀ n ∈ Ioc (N1 q) (N2 q), r ∣ n → (n / r).Prime → SieveTree.rough z n := by
      intro n hn hdvd hKp
      obtain ⟨m, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left m hpos] at hKp
      have hmz : z ≤ m := by
        rw [hz]
        refine Nat.ceil_le.2 ?_
        have h1 : xq q < ((r * m : ℕ) : ℝ) := by
          have := (Finset.mem_Ioc.1 hn).1
          exact Nat.lt_of_floor_lt this
        push_cast at h1
        have h2 : xq q / r < m := by rw [div_lt_iff₀ hr']; linarith
        have h3 : xq q ^ ((y : ℝ) / DEN) ≤ xq q ^ ((ctx.1 : ℝ) / DEN) := pow_mono hx1 hy
        linarith
      intro p hpz hpp hpd
      rcases (Nat.Prime.dvd_mul hpp).1 hpd with hd | hd
      · rw [hrdef] at hd
        obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hd
        have := (Nat.prime_dvd_prime_iff_eq hpp (hpr i).1).1 hi
        have := (hpr i).2
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hpp hKp).1 hd
        omega
    have h1 := tuple_diff_le hq1 (z := z) hpos H
    have h2 := hψiq (r : ℝ) hlo.le hhi
    have h3 := hπq (xq q / r) hYlo hYhi
    have hxr' : xq q / (r : ℝ) / Real.log (xq q) = Xq q * ∏ i, (1 / (rt i : ℝ)) := by
      rw [hrdef]; exact hxr rt (by rw [← hrdef]; exact hpos)
    rw [hxr'] at h2 h3
    have h4 : 0 ≤ Xq q * ∏ i, (1 / (rt i : ℝ)) :=
      mul_nonneg hX.le (Finset.prod_nonneg fun i _ => by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hφ)
    have h5 : ((omi : ℝ) / K * ((DEN : ℝ) / y) + t - (1 - t) * ((DEN : ℝ) / ctx.2)) ≤ pen + t * u := by
      have e1 : ((omi : ℝ) / K * ((DEN : ℝ) / y) + t - (1 - t) * ((DEN : ℝ) / ctx.2)) =
          ((omi : ℝ) / K * ((DEN : ℝ) / y) - (DEN : ℝ) / ctx.2) + t * (1 + (DEN : ℝ) / ctx.2) := by ring
      rw [e1, hu]
      linarith
    calc (Psi (xq q / r) z : ℝ) - (((Ioc ⌊xq q / r⌋₊ ⌊2 * (xq q / r)⌋₊).filter Nat.Prime).card : ℝ)
        ≤ ((omi : ℝ) / K * ((DEN : ℝ) / y) + t) * (Xq q * ∏ i, (1 / (rt i : ℝ))) -
            (1 - t) * ((DEN : ℝ) / ctx.2) * (Xq q * ∏ i, (1 / (rt i : ℝ))) := by linarith
      _ = ((omi : ℝ) / K * ((DEN : ℝ) / y) + t - (1 - t) * ((DEN : ℝ) / ctx.2)) *
            (Xq q * ∏ i, (1 / (rt i : ℝ))) := by ring
      _ ≤ (pen + t * u) * (Xq q * ∏ i, (1 / (rt i : ℝ))) := mul_le_mul_of_nonneg_right h5 h4
  -- the three ranges
  obtain ⟨Wl, hWldef⟩ : ∃ Wl : ℝ, Wl = Wsum q (e1 ctx) (e1 ctx + 1) (b.length + 1) (c :: b) := ⟨_, rfl⟩
  obtain ⟨Wi, hWidef⟩ : ∃ Wi : ℝ, Wi = Wsum q (e1 ctx + 1) (e2 ctx - 1) (b.length + 1) (c :: b) := ⟨_, rfl⟩
  obtain ⟨Wh, hWhdef⟩ : ∃ Wh : ℝ, Wh = Wsum q (e2 ctx - 1) (e2 ctx) (b.length + 1) (c :: b) := ⟨_, rfl⟩
  rw [← hWidef] at hWiq
  rw [← hWldef] at hWlq
  rw [← hWhdef] at hWhq
  have hWl0 : 0 ≤ Wl := by rw [hWldef]; exact Wsum_nonneg _ _ _ _ _
  have hWi0 : 0 ≤ Wi := by rw [hWidef]; exact Wsum_nonneg _ _ _ _ _
  have hWh0 : 0 ≤ Wh := by rw [hWhdef]; exact Wsum_nonneg _ _ _ _ _
  have hsplit : ∀ G : (Fin (c :: b).length → ℕ) → ℝ, ∑ rt ∈ famK q (e1 ctx) (e2 ctx) (c :: b).length bx, G rt =
      ∑ rt ∈ famK q (e1 ctx) (e1 ctx + 1) (c :: b).length bx, G rt +
        ∑ rt ∈ famK q (e1 ctx + 1) (e2 ctx - 1) (c :: b).length bx, G rt +
          ∑ rt ∈ famK q (e2 ctx - 1) (e2 ctx) (c :: b).length bx, G rt := by
    intro G
    rw [famK_sum_split hx1 (Nat.le_succ (e1 ctx)) (by omega : e1 ctx + 1 ≤ e2 ctx) (c :: b).length bx G,
      famK_sum_split hx1 he12 (Nat.sub_le (e2 ctx) 1) (c :: b).length bx G, add_assoc]
  have hWfull : Wsum q (e1 ctx) (e2 ctx) (b.length + 1) (c :: b) = Wl + Wi + Wh := by
    rw [hWldef, hWidef, hWhdef]
    unfold Wsum
    rw [← hbx]
    exact hsplit _
  have hWsum : ∀ ea eb : ℕ, ∑ rt ∈ famK q ea eb (c :: b).length bx, ∏ i, (1 / (rt i : ℝ)) =
      Wsum q ea eb (b.length + 1) (c :: b) := by
    intro ea eb
    unfold Wsum
    rw [← hbx]
    rfl
  -- the terms in the comparison set, less the primes
  obtain ⟨JA, hJA⟩ : ∃ JA : ℝ, JA = famJ (gA q a) (N1 q) (N2 q) z
      (famK q (e1 ctx) (e2 ctx) (c :: b).length bx) := ⟨_, rfl⟩
  obtain ⟨JB, hJB⟩ : ∃ JB : ℝ, JB = famJ (gB q) (N1 q) (N2 q) z
      (famK q (e1 ctx) (e2 ctx) (c :: b).length bx) := ⟨_, rfl⟩
  obtain ⟨Jl, hJl⟩ : ∃ Jl : ℝ, Jl = famJ (gB q) (N1 q) (N2 q) z
      (famK q (e1 ctx) (e1 ctx + 1) (c :: b).length bx) := ⟨_, rfl⟩
  obtain ⟨Jm, hJm⟩ : ∃ Jm : ℝ, Jm = famJ (gB q) (N1 q) (N2 q) z
      (famK q (e1 ctx + 1) (e2 ctx - 1) (c :: b).length bx) := ⟨_, rfl⟩
  obtain ⟨Jh, hJh⟩ : ∃ Jh : ℝ, Jh = famJ (gB q) (N1 q) (N2 q) z
      (famK q (e2 ctx - 1) (e2 ctx) (c :: b).length bx) := ⟨_, rfl⟩
  obtain ⟨PB, hPB⟩ : ∃ PB : ℝ, PB = famPr (gB q) (N1 q) (N2 q)
      (famK q (e1 ctx + 1) (e2 ctx - 1) (c :: b).length bx) := ⟨_, rfl⟩
  obtain ⟨dJ, hdJdef⟩ : ∃ dJ : ℝ, dJ = dJP q a y (boxFn (c :: b) (b.length + 1) rfl)
      (slabP q (e1 ctx) (e2 ctx) (b.length + 1)) := ⟨_, rfl⟩
  have hJsplit : JB = Jl + Jm + Jh := by
    rw [hJB, hJl, hJm, hJh]
    unfold famJ
    exact hsplit _
  have hl : Jl ≤ (q.totient : ℝ)⁻¹ * ((bd + t) * (Xq q * Wl)) := by
    rw [hJl, hWldef, ← hWsum]
    unfold famJ
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun rt hrt => hJb (le_refl _) (by omega) rt hrt
  have hh : Jh ≤ (q.totient : ℝ)⁻¹ * ((bd + t) * (Xq q * Wh)) := by
    rw [hJh, hWhdef, ← hWsum]
    unfold famJ
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun rt hrt => hJb (by omega) (le_refl _) rt hrt
  have hi : Jm - PB ≤ (q.totient : ℝ)⁻¹ * ((pen + t * u) * (Xq q * Wi)) := by
    rw [hJm, hPB, hWidef, ← hWsum]
    unfold famJ famPr
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun rt hrt => hJi rt hrt
  have hA : dJ ≤ (q.totient : ℝ)⁻¹ * ((((C : ℝ) / K + t) * (Wl + Wi + Wh) + η / 2) * Xq q) := by
    have h0 := hrootq a ha
    rw [hWfull] at h0
    rw [hdJdef]
    exact h0
  have hdJ : JA - JB = dJ := by
    rw [hJA, hJB, hdJdef, hbx, hz]
    rfl
  -- together
  have h1 : ((C : ℝ) / K + t) * (Wl + Wi + Wh) ≤ ((C : ℝ) / K + t) * (Ri + 2 * Rb + 3 * t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (pen + t * u) * Wi ≤ (pen + t * u) * (Ri + t) :=
    mul_le_mul_of_nonneg_left hWiq (add_nonneg hpen0 (mul_nonneg ht0.le hu0))
  have h3 : (bd + t) * (Wl + Wh) ≤ (bd + t) * (2 * Rb + 2 * t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hid : ((C : ℝ) / K + t) * (Ri + 2 * Rb + 3 * t) + (pen + t * u) * (Ri + t) + (bd + t) * (2 * Rb + 2 * t) =
      (((C : ℝ) / K + pen) * Ri + ((C : ℝ) / K + bd) * (2 * Rb)) +
        t * (3 * ((C : ℝ) / K) + Ri + 2 * Rb + 3 * t + pen + u * Ri + t * u + 2 * bd + 2 * Rb + 2 * t) := by ring
  have hbr : 3 * ((C : ℝ) / K) + Ri + 2 * Rb + 3 * t + pen + u * Ri + t * u + 2 * bd + 2 * Rb + 2 * t ≤ M := by
    rw [hM]
    have := mul_le_of_le_one_left hu0 ht1
    linarith
  have htbr := mul_le_mul_of_nonneg_left hbr ht0.le
  obtain ⟨cost, hcostdef⟩ : ∃ cost : ℝ, cost =
      ((cdiv (trF qa (ctx.2 - ctx.1 - 1) * trBut iq (c :: b) * (C + penK ctx y)) (SC ^ (c :: b).length) +
        cdiv (2 * trF qa 1 * trBut iq (c :: b) * (C + bdK ctx y)) (SC ^ (c :: b).length) : ℕ) : ℝ) / K :=
    ⟨_, rfl⟩
  rw [← hcostdef] at hcost
  have hfin : ((C : ℝ) / K + t) * (Wl + Wi + Wh) + η / 2 + ((bd + t) * (Wl + Wh) + (pen + t * u) * Wi) ≤
      cost + η := by linarith
  have hfin' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfin hX.le) hφ
  rw [← hqa, ← hcostdef, ← hJA, ← hPB]
  have e2 : (q.totient : ℝ)⁻¹ * ((((C : ℝ) / K + t) * (Wl + Wi + Wh) + η / 2 +
      ((bd + t) * (Wl + Wh) + (pen + t * u) * Wi)) * Xq q) =
      (q.totient : ℝ)⁻¹ * ((((C : ℝ) / K + t) * (Wl + Wi + Wh) + η / 2) * Xq q) +
        ((q.totient : ℝ)⁻¹ * ((bd + t) * (Xq q * Wl)) + (q.totient : ℝ)⁻¹ * ((pen + t * u) * (Xq q * Wi)) +
          (q.totient : ℝ)⁻¹ * ((bd + t) * (Xq q * Wh))) := by ring
  rw [e2] at hfin'
  linarith

end SieveAd

#print axioms SieveAd.famCost_sound
