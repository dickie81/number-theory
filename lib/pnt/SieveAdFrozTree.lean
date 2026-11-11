/-
# The nodes of the tree of a reversed term over a frozen part

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFroz.lean` has the terms of a chain's box over a frozen part, a finite family of numbers
`R`, and the nodes of a tree that only use the chain. Here the frozen part lies in the range of `r'` for a cell
`ctx = (l₁, h₁)` of the prime that is reversed (`InSlab`: `x^{(DEN−h₁)/DEN} < R ≤ x^{(DEN−l₁+1)/DEN}`), so `n/R`
lies between `x^{(l₁−1)/DEN}` and `x^{(h₁+1)/DEN}`, and the search of `SieveAdRevDefs.lean` (`SieveAd.opsK`) is
sound on it: its boxes are the chain's cells followed by a fixed list `β` of cells that describes the frozen part
to the tests.

* `famB_snoc_sum_le`, `Bsum`, `Bsum_le`: the sum of `1/∏c` over the chains of a box is at most the product of the
  sums of `1/p` over its cells.
* `card_le_PsiR`, `famIR_gB_le`: for one `R`, the term of a family of chains in the comparison set is at most
  `φ(q)⁻¹ Σ_c Ψ(x/(R·∏c), c_last)`.
* `bdF_vanish`: a chain's box that passes `vanishK` has no term over the frozen part.
* `bdF_drop`: a chain's box that passes `dropK`, for a term of the sign `+`, has its term at least
  `−((dc/K + ε)·Σ 1/R + o(1))x/(φ(q) log x)`: `SieveRough.psi_point_w` with `R` among the primes before the last.
* `PF S R β bl par c`: what the tree proves of a box `bl = ch ++ β`: `BdF` at the cost `c/K + ε` for the chain
  `ch`, for every `ε > 0`. `SoundF τ S R β`: the tests are sound for the frozen part, on the boxes `ch ++ β` of
  at most twelve cells.
* `frozRules`, `frozSolve_sound`: **the search is sound over a frozen part**: a cost that
  `solveG (opsK ctx β.length) τ S n` returns below its limit has `PF`.
* `famJ_levelN`, `dJF_level`: Buchstab's identity between two floors for the chain with no prime: the terms at
  the level `x^{t/DEN}` are the terms at a floor `f ≤ t`, minus the term of the chain of one prime in
  `[x^{f/DEN}, x^{t/DEN})`.
* `frozSolve_sound_at`, `dJF_level_at`: the two with the route as a variable.

The file imports `SieveAdFroz.lean` and `SieveAdRev.lean`.
-/
import SieveAdFroz
import SieveAdRev

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K omKw cdiv trB exB DEN_pos' K_pos')

variable [Route]

/-! ### The sums of `1/∏c` over the chains of a box -/

/-- **A sum over the chains with one more prime.** For a function `f ≥ 0` of the last prime: the sum of
`f(c_last)/∏(the others)` over the chains of the box with one more cell `c` is at most the sum of `1/∏` over the
chains of the box, times the sum of `f` over the primes of the cell. -/
theorem famB_snoc_sum_le {q k : ℕ} (bx : Fin k → Cell) (c : Cell) (hc : c.1 ≤ c.2) (f : ℕ → ℝ)
    (hf : ∀ p, 0 ≤ f p) :
    ∑ rt ∈ famB q (Fin.snoc (α := fun _ => Cell) bx c),
        (∏ i : Fin k, (1 / (rt i.castSucc : ℝ))) * f (rt (Fin.last k)) ≤
      (∑ r ∈ famB q bx, ∏ i, (1 / (r i : ℝ))) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), f p :=
  sum_snoc_le _ _ _ (fun _ hrt => ⟨init_mem_famB hrt, last_mem_boxP hc hrt⟩) (fun r => ∏ i, (1 / (r i : ℝ))) f
    (fun _ => Finset.prod_nonneg fun i _ => by positivity) hf

/-- The sum of `1/∏c` over the chains of the box of a list. -/
noncomputable def Bsum (q : ℕ) (bl : List Cell) : ℝ :=
  ∑ rt ∈ famB q (boxFn bl bl.length rfl), ∏ i, (1 / (rt i : ℝ))

theorem Bsum_eq (q : ℕ) (bl : List Cell) (k : ℕ) (h : bl.length = k) :
    Bsum q bl = ∑ rt ∈ famB q (boxFn bl k h), ∏ i, (1 / (rt i : ℝ)) := by
  subst h
  rfl

/-- **The sum of `1/∏c` over the chains of a box is at most the product of the sums of `1/p` over its cells.** -/
theorem Bsum_le (q : ℕ) : ∀ bl : List Cell, (∀ c ∈ bl, c.1 ≤ c.2) → Bsum q bl ≤ TRl (xq q) bl := by
  intro bl
  induction bl with
  | nil =>
    intro _
    rw [Bsum_eq q [] 0 rfl, famB_zero, Fintype.sum_unique]
    simp [TRl]
  | cons c bl ih =>
    intro hcells
    have hc := hcells c (List.mem_cons_self ..)
    have h2 := ih fun d hd => hcells d (List.mem_cons_of_mem _ hd)
    have h0 := sum_inv_nonneg (boxP (xq q) c.1 (c.2 - c.1))
    have h1 : Bsum q (c :: bl) ≤ Bsum q bl * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / (p : ℝ) := by
      rw [Bsum_eq q (c :: bl) (bl.length + 1) rfl, boxFn_cons c bl bl.length rfl]
      have h := famB_snoc_sum_le (q := q) (boxFn bl bl.length rfl) c hc (fun p => 1 / (p : ℝ))
        (fun p => by positivity)
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun rt _ => ?_
      rw [Fin.prod_univ_castSucc]
    calc Bsum q (c :: bl) ≤ Bsum q bl * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / (p : ℝ) := h1
      _ ≤ TRl (xq q) bl * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / (p : ℝ) := mul_le_mul_of_nonneg_right h2 h0
      _ = TRl (xq q) (c :: bl) := by simp only [TRl]; ring

/-! ### The comparison set's count of a chain family over a multiple -/

omit [Route] in
/-- For `x > 0`, `R > 0` and `W > 0`: the `n ∈ (x, 2x]` with `R·W ∣ n` and `n/R` free of primes below `z` inject
into `Ψ(x/(RW), z)` by `n ↦ n/(RW)`. -/
theorem card_le_PsiR {x : ℝ} (hx : 0 < x) {R W z : ℕ} (hR : 0 < R) (hW : 0 < W) :
    ((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (fun n => R * W ∣ n ∧ SieveTree.rough z (n / R))).card ≤
      Psi (x / ((R * W : ℕ) : ℝ)) z := by
  unfold Psi roughSet
  have hRW : 0 < R * W := Nat.mul_pos hR hW
  have hW' : (0 : ℝ) < ((R * W : ℕ) : ℝ) := by exact_mod_cast hRW
  refine Finset.card_le_card_of_injOn (fun n => n / (R * W)) ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    dsimp only
    rw [Nat.mul_div_cancel_left c hRW]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.floor_lt (by positivity), div_lt_iff₀ hW']
      have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h4 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((R * W * c : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h4 ⊢
      linarith
    · rw [Nat.le_floor_iff (by positivity)]
      have h3 : ((R * W * c : ℕ) : ℝ) ≤ 2 * x := (Nat.cast_le.2 h2).trans (Nat.floor_le (by positivity))
      rw [mul_div_assoc', le_div_iff₀ hW']
      push_cast at h3 ⊢
      linarith
    · intro p hp
      by_contra hlt
      have e : R * W * c / R = W * c := by rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hR]
      rw [e] at hr
      exact hr p (not_le.1 hlt) (Nat.prime_of_mem_primeFactors hp)
        (dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) W)
  · intro n₁ hn₁ n₂ hn₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hn₁ hn₂
    exact (Nat.div_left_inj hn₁.2.1 hn₂.2.1).1 h

/-- **A chain family's count in the comparison set, over the multiples of `R`.** For `q ≥ 1`, `R > 0` and a
family of tuples of primes, it is at most `φ(q)⁻¹ Σ_c Ψ(x/(R·∏c), c_last)`. -/
theorem famIR_gB_le (q : ℕ) {R : ℕ} (hR : 0 < R) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ))
    (hF : ∀ rt ∈ F, ∀ i, (rt i).Prime) (hq : 1 ≤ q) :
    famIR (gB q) (N1 q) (N2 q) R F ≤
      (q.totient : ℝ)⁻¹ * ∑ rt ∈ F, (Psi (xq q / ((R * ∏ i, rt i : ℕ) : ℝ)) (rt (Fin.last k')) : ℝ) := by
  have hx : 0 < xq q := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  rw [famIR_eq _ _ _ hR, Finset.mul_sum]
  refine Finset.sum_le_sum fun rt hrt => ?_
  have hW : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hF rt hrt i).pos
  calc ∑ n ∈ Ioc (N1 q) (N2 q), gB q n *
        (if R * ∏ i, rt i ∣ n ∧ SieveTree.rough (rt (Fin.last k')) (n / R) then 1 else 0)
      ≤ ∑ n ∈ Ioc (N1 q) (N2 q), (q.totient : ℝ)⁻¹ *
        (if R * ∏ i, rt i ∣ n ∧ SieveTree.rough (rt (Fin.last k')) (n / R) then 1 else 0) :=
        Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_right (SieveDrop.gB_le q n) (by split_ifs <;> norm_num)
    _ = (q.totient : ℝ)⁻¹ * (((Ioc (N1 q) (N2 q)).filter
          (fun n => R * ∏ i, rt i ∣ n ∧ SieveTree.rough (rt (Fin.last k')) (n / R))).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.card_filter]
        push_cast
        rfl
    _ ≤ (q.totient : ℝ)⁻¹ * (Psi (xq q / ((R * ∏ i, rt i : ℕ) : ℝ)) (rt (Fin.last k')) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast card_le_PsiR hx hR hW

/-! ### A frozen part in the range of `r'` -/

/-- The frozen part lies in the range of `r'` for the cell `ctx` of the prime that is reversed: at a large
modulus every `R` is above `x^{(DEN−h₁)/DEN}` and at most `x^{(DEN−l₁+1)/DEN}`. -/
def InSlab {ι : Type} (S : ℕ → Finset ι) (R : ι → ℕ) (ctx : Cell) : Prop :=
  ∀ᶠ q : ℕ in atTop, ∀ i ∈ S q,
    xq q ^ ((e1 ctx : ℝ) / DEN) < R i ∧ (R i : ℝ) ≤ xq q ^ ((e2 ctx : ℝ) / DEN)

/-- **A chain's box with no term**, over a frozen part in the range of `r'`. -/
theorem bdF_vanish [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (hS : InSlab S R ctx) (c : Cell) (b : List Cell)
    {par : Bool} (hv : vanishK ctx (c :: b) = true) {C : ℝ} (hC : 0 ≤ C) :
    BdF S R par C (boxFn (c :: b) (b.length + 1) rfl) := by
  intro η hη
  simp only [vanishK, Bool.and_eq_true, Nat.ble_eq] at hv
  obtain ⟨hv1, hv2⟩ := hv
  have hD := DEN_pos'
  filter_upwards [big_ev, hS] with q hq hSq a _
  obtain ⟨-, hx3, -, hN2, -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hlast : boxFn (c :: b) (b.length + 1) rfl (Fin.last _) = c := by simp [boxFn]
  have hvan : ∀ g : ℕ → ℝ, ∀ i ∈ S q,
      famIR g (N1 q) (N2 q) (R i) (famB q (boxFn (c :: b) (b.length + 1) rfl)) = 0 := by
    intro g i hi
    obtain ⟨hRlo, hRhi⟩ := hSq i hi
    have hR0 : (0 : ℝ) < R i := lt_of_le_of_lt (Real.rpow_nonneg hx0.le _) hRlo
    have hRpos : 0 < R i := by exact_mod_cast hR0
    refine famI_vanish _ _ _ _ fun rt hrt => ?_
    obtain ⟨hp, hsa, hc⟩ := mem_famB.1 hrt
    have hpb := prod_bounds hx0 hc
    rw [sum_boxFn (fun d => d.1) (c :: b) (b.length + 1) rfl, sum_boxFn (fun d => d.2) (c :: b) (b.length + 1) rfl]
      at hpb
    simp only [List.map_cons, List.sum_cons] at hpb
    rw [← loSum_eq, ← hiSum_eq] at hpb
    have hc0 : 0 ≤ ∏ i, (rt i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    constructor
    · have h1 : (R i : ℝ) * ∏ j, (rt j : ℝ) ≤ xq q := by
        calc (R i : ℝ) * ∏ j, (rt j : ℝ)
            ≤ xq q ^ ((e2 ctx : ℝ) / DEN) * xq q ^ (((c.2 + hiSum b : ℕ) : ℝ) / DEN) :=
              mul_le_mul hRhi hpb.2 hc0 (Real.rpow_nonneg hx0.le _)
          _ = xq q ^ (((e2 ctx + (c.2 + hiSum b) : ℕ) : ℝ) / DEN) := by
              rw [← Real.rpow_add hx0]; congr 1; push_cast; ring
          _ ≤ xq q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by
              rw [div_le_one hD]
              exact_mod_cast (show e2 ctx + (c.2 + hiSum b) ≤ DEN by unfold e2; omega))
          _ = xq q := Real.rpow_one _
      have h2 : (∏ j, rt j) * R i ≤ N1 q := by
        refine Nat.le_floor ?_
        push_cast
        linarith
      exact (Nat.le_div_iff_mul_le hRpos).2 h2
    · have h3 : xq q ^ (((DEN : ℝ) + 1) / DEN) ≤ (R i : ℝ) * (∏ j, (rt j : ℝ)) * rt (Fin.last _) := by
        calc xq q ^ (((DEN : ℝ) + 1) / DEN)
            ≤ xq q ^ (((e1 ctx + (c.1 + loSum b) + c.1 : ℕ) : ℝ) / DEN) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (div_le_div_of_nonneg_right (by
                exact_mod_cast (show DEN + 1 ≤ e1 ctx + (c.1 + loSum b) + c.1 by unfold e1; omega))
                hD.le)
          _ = xq q ^ ((e1 ctx : ℝ) / DEN) * xq q ^ (((c.1 + loSum b : ℕ) : ℝ) / DEN) *
                xq q ^ ((c.1 : ℝ) / DEN) := by
              rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; push_cast; ring
          _ ≤ (R i : ℝ) * (∏ j, (rt j : ℝ)) * rt (Fin.last _) :=
              mul_le_mul (mul_le_mul hRlo.le hpb.1 (Real.rpow_nonneg hx0.le _) hR0.le)
                (by have := (hc (Fin.last _)).1; rwa [hlast] at this) (Real.rpow_nonneg hx0.le _)
                (mul_nonneg hR0.le hc0)
      have h4 : (N2 q : ℝ) < ((((∏ j, rt j) * rt (Fin.last _)) * R i : ℕ) : ℝ) := by
        push_cast
        linarith
      exact (Nat.div_lt_iff_lt_mul hRpos).2 (by exact_mod_cast h4)
  have hd : dIF q a (S q) R (boxFn (c :: b) (b.length + 1) rfl) = 0 := by
    unfold dIF
    exact Finset.sum_eq_zero fun i hi => by rw [hvan _ i hi, hvan _ i hi, sub_zero]
  have hX := Xq_pos hq
  have hW := WF_nonneg (S q) R
  rw [hd, mul_zero, neg_nonpos]
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (mul_nonneg (add_nonneg (mul_nonneg hC hW) hη.le) hX.le)

/-- **A chain's box that is dropped**, over a frozen part in the range of `r'`: for a term of the sign `+`, the
cost that `dropK` gives, in units of the sum of `1/R`. -/
theorem bdF_drop [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (hS : InSlab S R ctx) (c : Cell) (b : List Cell)
    {par : Bool} {dc : ℕ} (hd : dropK ctx (c :: b) par = some dc) {ε : ℝ} (hε : 0 < ε) :
    BdF S R par ((dc : ℝ) / K + ε) (boxFn (c :: b) (b.length + 1) rfl) := by
  intro η hη
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
  filter_upwards [big_ev, hS, SieveDrop.tendsto_xq.eventually (hT δ₁ hδ₁0),
    SieveDrop.tendsto_xq.eventually (Real.tendsto_log_atTop.eventually_gt_atTop (DEN * Real.log 2)),
    SieveDrop.tendsto_xq.eventually ((tendsto_rpow_atTop (div_pos hc1' hD)).eventually_ge_atTop (z₀ : ℝ)),
    eventually_ge_atTop 1] with q hq hSq hTq hlx2 hxz hq1 a _
  obtain ⟨-, hx3, -, -, -⟩ := big_facts hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 < xq q := by linarith
  have hlx : 0 < Real.log (xq q) := Real.log_pos hx1
  have hτ : Real.log 2 / Real.log (xq q) * DEN < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hlx]; linarith
  have hX := Xq_pos hq
  have hWn := WF_nonneg (S q) R
  have ebx : boxFn (c :: b) (b.length + 1) rfl =
      Fin.snoc (α := fun _ => Cell) (boxFn b b.length rfl) c := boxFn_cons c b b.length rfl
  obtain ⟨F, hF⟩ : ∃ F, F = famB q (Fin.snoc (α := fun _ => Cell) (boxFn b b.length rfl) c) := ⟨_, rfl⟩
  have hprimes : ∀ rt ∈ F, ∀ i, (rt i).Prime := by
    intro rt hrt i
    rw [hF] at hrt
    exact ((mem_famB.1 hrt).1 i).2
  -- each `R` and each chain
  have hterm : ∀ i ∈ S q, ∀ rt ∈ F,
      (Psi (xq q / ((R i * ∏ j, rt j : ℕ) : ℝ)) (rt (Fin.last b.length)) : ℝ) ≤
        (Wc + ε₁) * (xq q / Real.log (xq q)) * (1 / (R i : ℝ) * ((∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ))) *
          (Real.log (xq q) / ((rt (Fin.last b.length) : ℝ) * Real.log (rt (Fin.last b.length)))))) := by
    intro i hi rt hrt
    obtain ⟨hRlo, hRhi⟩ := hSq i hi
    have hR0 : (0 : ℝ) < R i := lt_of_le_of_lt (Real.rpow_nonneg hx0.le _) hRlo
    have hR1 : (1 : ℝ) ≤ R i := by
      have : 0 < R i := by exact_mod_cast hR0
      exact_mod_cast this
    rw [hF] at hrt
    have hr₀ := init_mem_famB hrt
    obtain ⟨hp₀, -, hc₀⟩ := mem_famB.1 hr₀
    have hpl := mem_primesIn.1 (last_mem_boxP hc.2.le hrt)
    obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = rt (Fin.last b.length) := ⟨_, rfl⟩
    rw [← hpdef] at hpl ⊢
    have hp2 : 2 ≤ p := hpl.1.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpl.1.pos
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpl.1.one_lt)
    obtain ⟨d₀, hd₀def⟩ : ∃ d₀ : ℝ, d₀ = ∏ j : Fin b.length, ((Fin.init rt j : ℕ) : ℝ) := ⟨_, rfl⟩
    have hd₀1 : 1 ≤ d₀ := by
      rw [hd₀def]
      exact Finset.one_le_prod₀ fun j _ => by exact_mod_cast (hp₀ j).2.one_lt.le
    have hd₀0 : 0 < d₀ := by linarith
    have hpb := prod_bounds hx0 hc₀
    rw [sum_boxFn (fun d => d.1) b _ rfl, sum_boxFn (fun d => d.2) b _ rfl, ← loSum_eq, ← hiSum_eq, ← hd₀def]
      at hpb
    obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = (R i : ℝ) * d₀ := ⟨_, rfl⟩
    have hd1 : 1 ≤ d := by rw [hddef]; exact one_le_mul_of_one_le_of_one_le hR1 hd₀1
    have hd0 : 0 < d := by linarith
    have hdlo : xq q ^ (((s : ℕ) : ℝ) / DEN) ≤ d := by
      rw [hddef]
      calc xq q ^ (((s : ℕ) : ℝ) / DEN) ≤ xq q ^ (((e1 ctx + loSum b : ℕ) : ℝ) / DEN) :=
            Real.rpow_le_rpow_of_exponent_le hx1.le
              (div_le_div_of_nonneg_right (by exact_mod_cast hs1) hD.le)
        _ = xq q ^ ((e1 ctx : ℝ) / DEN) * xq q ^ ((loSum b : ℝ) / DEN) := by
            rw [← Real.rpow_add hx0]; congr 1; push_cast; ring
        _ ≤ (R i : ℝ) * d₀ := mul_le_mul hRlo.le hpb.1 (Real.rpow_nonneg hx0.le _) hR0.le
    have hdhi : d ≤ xq q ^ (((e2 ctx + hiSum b : ℕ) : ℝ) / DEN) := by
      rw [hddef]
      calc (R i : ℝ) * d₀ ≤ xq q ^ ((e2 ctx : ℝ) / DEN) * xq q ^ ((hiSum b : ℝ) / DEN) :=
            mul_le_mul hRhi hpb.2 hd₀0.le (Real.rpow_nonneg hx0.le _)
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
    have hcast : ((R i * ∏ j, rt j : ℕ) : ℝ) = d * p := by
      rw [hddef, hd₀def, hpdef, Fin.prod_univ_castSucc]
      push_cast
      rw [mul_assoc]
      rfl
    rw [hcast]
    refine hψ.trans (le_of_eq ?_)
    have hprod : ∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ)) = 1 / d₀ := by
      rw [hd₀def, Finset.prod_div_distrib, Finset.prod_const_one]
      rfl
    rw [hprod, hddef]
    have := hlx.ne'
    have := hlp.ne'
    have := hR0.ne'
    have := hd₀0.ne'
    field_simp
  -- the sum over the chains
  have hin : ∑ rt ∈ F, (∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ))) *
      (Real.log (xq q) / ((rt (Fin.last b.length) : ℝ) * Real.log (rt (Fin.last b.length)))) ≤ P + δ₁ := by
    rw [hF]
    have h1 := famB_snoc_sum_le (q := q) (boxFn b b.length rfl) c hc.2.le
      (fun p => Real.log (xq q) / ((p : ℝ) * Real.log p))
      (fun p => div_nonneg hlx.le (mul_nonneg (Nat.cast_nonneg p) (Real.log_natCast_nonneg p)))
    refine h1.trans ?_
    have h2 := Bsum_le q b fun d hd' => (hb d hd').2.le
    have h3 : ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), Real.log (xq q) / ((p : ℝ) * Real.log p) =
        Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have h4 : 0 ≤ Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p) :=
      mul_nonneg hlx.le (Finset.sum_nonneg fun p _ =>
        div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg p) (Real.log_natCast_nonneg p)))
    rw [h3]
    calc (∑ r ∈ famB q (boxFn b b.length rfl), ∏ i, (1 / (r i : ℝ))) *
          (Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p))
        ≤ TRl (xq q) b *
          (Real.log (xq q) * ∑ p ∈ boxP (xq q) c.1 (c.2 - c.1), 1 / ((p : ℝ) * Real.log p)) :=
          mul_le_mul_of_nonneg_right h2 h4
      _ ≤ P + δ₁ := hTq
  have hsum : ∑ i ∈ S q, ∑ rt ∈ F, 1 / (R i : ℝ) * ((∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ))) *
      (Real.log (xq q) / ((rt (Fin.last b.length) : ℝ) * Real.log (rt (Fin.last b.length))))) ≤
        WF (S q) R * (P + δ₁) := by
    calc ∑ i ∈ S q, ∑ rt ∈ F, 1 / (R i : ℝ) * ((∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ))) *
          (Real.log (xq q) / ((rt (Fin.last b.length) : ℝ) * Real.log (rt (Fin.last b.length)))))
        = ∑ i ∈ S q, 1 / (R i : ℝ) * ∑ rt ∈ F, (∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ))) *
          (Real.log (xq q) / ((rt (Fin.last b.length) : ℝ) * Real.log (rt (Fin.last b.length)))) :=
          Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S q, 1 / (R i : ℝ) * (P + δ₁) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left hin (by positivity)
      _ = WF (S q) R * (P + δ₁) := by unfold WF; rw [Finset.sum_mul]
  have hΨ : ∑ i ∈ S q, ∑ rt ∈ F, (Psi (xq q / ((R i * ∏ j, rt j : ℕ) : ℝ)) (rt (Fin.last b.length)) : ℝ) ≤
      ((dc : ℝ) / K + ε) * WF (S q) R * Xq q := by
    have hxl : 0 ≤ xq q / Real.log (xq q) := (div_pos hx0 hlx).le
    calc ∑ i ∈ S q, ∑ rt ∈ F, (Psi (xq q / ((R i * ∏ j, rt j : ℕ) : ℝ)) (rt (Fin.last b.length)) : ℝ)
        ≤ ∑ i ∈ S q, ∑ rt ∈ F, (Wc + ε₁) * (xq q / Real.log (xq q)) *
            (1 / (R i : ℝ) * ((∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ))) *
              (Real.log (xq q) / ((rt (Fin.last b.length) : ℝ) * Real.log (rt (Fin.last b.length)))))) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun rt hrt => hterm i hi rt hrt
      _ = (Wc + ε₁) * (xq q / Real.log (xq q)) * ∑ i ∈ S q, ∑ rt ∈ F,
            1 / (R i : ℝ) * ((∏ j : Fin b.length, (1 / (rt j.castSucc : ℝ))) *
              (Real.log (xq q) / ((rt (Fin.last b.length) : ℝ) * Real.log (rt (Fin.last b.length))))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ ≤ (Wc + ε₁) * (xq q / Real.log (xq q)) * (WF (S q) R * (P + δ₁)) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hxl)
      _ = (Wc + ε₁) * (P + δ₁) * WF (S q) R * Xq q := by unfold Xq; ring
      _ ≤ ((dc : ℝ) / K + ε) * WF (S q) R * Xq q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hWn) hX.le
  -- the term
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hA : ∀ i ∈ S q, 0 ≤ famIR (gA q a) (N1 q) (N2 q) (R i) F := fun i _ =>
    famI_nonneg (fun N => gA_nonneg q a (R i * N)) _ _ _
  have hB : ∀ i ∈ S q, famIR (gB q) (N1 q) (N2 q) (R i) F ≤
      (q.totient : ℝ)⁻¹ * ∑ rt ∈ F, (Psi (xq q / ((R i * ∏ j, rt j : ℕ) : ℝ)) (rt (Fin.last b.length)) : ℝ) := by
    intro i hi
    have hR0 : (0 : ℝ) < R i := lt_of_le_of_lt (Real.rpow_nonneg hx0.le _) (hSq i hi).1
    exact famIR_gB_le q (by exact_mod_cast hR0) F hprimes hq1
  have hdI : dIF q a (S q) R (boxFn (c :: b) (b.length + 1) rfl) =
      ∑ i ∈ S q, (famIR (gA q a) (N1 q) (N2 q) (R i) F - famIR (gB q) (N1 q) (N2 q) (R i) F) := by
    rw [hF, ← ebx]
    rfl
  rw [hdI]
  simp only [sg, ite_true, one_mul]
  have h5 : -((q.totient : ℝ)⁻¹ * ∑ i ∈ S q, ∑ rt ∈ F,
      (Psi (xq q / ((R i * ∏ j, rt j : ℕ) : ℝ)) (rt (Fin.last b.length)) : ℝ)) ≤
        ∑ i ∈ S q, (famIR (gA q a) (N1 q) (N2 q) (R i) F - famIR (gB q) (N1 q) (N2 q) (R i) F) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i hi => by linarith [hA i hi, hB i hi]
  have h6 : (q.totient : ℝ)⁻¹ * ∑ i ∈ S q, ∑ rt ∈ F,
      (Psi (xq q / ((R i * ∏ j, rt j : ℕ) : ℝ)) (rt (Fin.last b.length)) : ℝ) ≤
        (q.totient : ℝ)⁻¹ * ((((dc : ℝ) / K + ε) * WF (S q) R + η) * Xq q) := by
    refine mul_le_mul_of_nonneg_left (hΨ.trans ?_) hφ
    nlinarith [mul_nonneg hη.le hX.le]
  linarith

/-! ### What the tree proves, and the search -/

/-- **What the tree of a reversed term proves over a frozen part**, of a box `bl = ch ++ β`, the chain's cells
followed by the list `β` that describes the frozen part to the tests: the term of the chain `ch` over the frozen
part, with its sign, is at least `−((c/K + ε)·Σ 1/R + o(1))x/(φ(q) log x)`, for every `ε > 0`. -/
def PF {ι : Type} (S : ℕ → Finset ι) (R : ι → ℕ) (β : List Cell) (bl : List Cell) (par : Bool) (c : ℕ) : Prop :=
  ∀ ch : List Cell, bl = ch ++ β → ∀ (k' : ℕ) (h : ch.length = k' + 1) (ε : ℝ), 0 < ε →
    BdF S R par ((c : ℝ) / K + ε) (boxFn ch (k' + 1) h)

/-- **The tests are sound for a frozen part** described by the list `β`: on a box `ch ++ β` of at most twelve
cells, a test that passes evaluates the term of the chain `ch` over the frozen part, or its terms at the floor. -/
structure SoundF (τ : Tests) {ι : Type} (S : ℕ → Finset ι) (R : ι → ℕ) (β : List Cell) : Prop where
  soundI : ∀ (ch : List Cell) (cfg : Cfg) (k' : ℕ) (h : ch.length = k' + 1), ch.length + β.length ≤ 12 →
    τ.okI (ch ++ β) cfg = true → EvIF S R (boxFn ch (k' + 1) h)
  soundJ : ∀ (ch : List Cell) (f : ℕ) (cfg : Cfg) (k : ℕ) (h : ch.length = k), ch.length + β.length ≤ 12 →
    τ.okJ (ch ++ β) f cfg = true → EvJF S R f (boxFn ch k h)

omit [Route] in
/-- The chain of a box `ch ++ β` is `ch`. -/
theorem chainOf_append (ch β : List Cell) : chainOf β.length (ch ++ β) = ch := by
  unfold chainOf
  rw [List.length_append, Nat.add_sub_cancel]
  exact List.take_left' rfl

omit [Route] in
/-- A box `x :: bl` that is a nonempty chain followed by `β` has its chain's first cell `x`. -/
theorem cons_eq_append {x : Cell} {bl ch β : List Cell} (h : x :: bl = ch ++ β) (hch : ch ≠ []) :
    ∃ ch' : List Cell, ch = x :: ch' ∧ bl = ch' ++ β := by
  cases ch with
  | nil => exact absurd rfl hch
  | cons y ch' =>
    rw [List.cons_append, List.cons.injEq] at h
    exact ⟨ch', by rw [h.1], h.2⟩

/-- A chain's box with no term. -/
theorem pf_vanish [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (hS : InSlab S R ctx) {β bl : List Cell} {par : Bool}
    (hv : vanishK ctx (chainOf β.length bl) = true) : PF S R β bl par 0 := by
  intro ch hbl k' h ε hε
  subst hbl
  rw [chainOf_append] at hv
  cases ch with
  | nil => simp at h
  | cons c b =>
    have hk : b.length = k' := by simpa using h
    subst hk
    exact bdF_vanish hctx hS c b hv (by positivity)

/-- A box that a test evaluates. -/
theorem pf_eval [RouteOK] {τ : Tests} {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell} {β : List Cell}
    (hτ : SoundF τ S R β) {bl : List Cell} {par : Bool} {cfg : Cfg}
    (hg : (opsK ctx β.length).grd bl = true) (hI : τ.okI bl cfg = true) : PF S R β bl par 0 := by
  intro ch hbl k' h ε hε
  subst hbl
  simp only [opsK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.length_append] at hg
  refine bdF_mono (bdF_eval (hτ.soundI ch cfg k' h hg.2 hI)) ?_
  simp only [Nat.cast_zero, zero_div, zero_add]
  exact hε.le

/-- A chain's box that is dropped. -/
theorem pf_drop [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (hS : InSlab S R ctx) {β bl : List Cell} {par : Bool}
    {dc : ℕ} (hd : dropK ctx (chainOf β.length bl) par = some dc) : PF S R β bl par dc := by
  intro ch hbl k' h ε hε
  subst hbl
  rw [chainOf_append] at hd
  cases ch with
  | nil => simp at h
  | cons c b =>
    have hk : b.length = k' := by simpa using h
    subst hk
    exact bdF_drop hctx hS c b hd hε

/-- A cut of the newest cell. -/
theorem pf_split [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {β : List Cell} {a m top : ℕ}
    {bl : List Cell} {par : Bool} {c1 c2 : ℕ} (h1 : a < m) (h2 : m < top)
    (hl : PF S R β ((a, m) :: bl) par c1) (hr : PF S R β ((m, top) :: bl) par c2) :
    PF S R β ((a, top) :: bl) par (c1 + c2) := by
  intro ch hbl k' h ε hε
  obtain ⟨ch', rfl, hbl'⟩ := cons_eq_append hbl (by intro h0; rw [h0] at h; simp at h)
  have hk : ch'.length = k' := by simpa using h
  subst hk
  have hL := hl ((a, m) :: ch') (by rw [hbl']; rfl) ch'.length rfl (ε / 2) (by positivity)
  have hR := hr ((m, top) :: ch') (by rw [hbl']; rfl) ch'.length rfl (ε / 2) (by positivity)
  have ebx : boxFn ((a, top) :: ch') (ch'.length + 1) h =
      Fin.snoc (α := fun _ => Cell) (boxFn ch' ch'.length rfl) (a, top) := boxFn_cons _ _ _ rfl
  have el : Function.update (boxFn ((a, top) :: ch') (ch'.length + 1) h) (Fin.last _)
      ((boxFn ((a, top) :: ch') (ch'.length + 1) h (Fin.last _)).1, m) =
        boxFn ((a, m) :: ch') (ch'.length + 1) rfl := by
    rw [ebx, boxFn_cons (a, m) ch' ch'.length rfl, Fin.snoc_last, Fin.update_snoc_last]
  have er : Function.update (boxFn ((a, top) :: ch') (ch'.length + 1) h) (Fin.last _)
      (m, (boxFn ((a, top) :: ch') (ch'.length + 1) h (Fin.last _)).2) =
        boxFn ((m, top) :: ch') (ch'.length + 1) rfl := by
    rw [ebx, boxFn_cons (m, top) ch' ch'.length rfl, Fin.snoc_last, Fin.update_snoc_last]
  have key := bdF_split (S := S) (R := R) (par := par) (boxFn ((a, top) :: ch') (ch'.length + 1) h)
    (Fin.last _) (c := m) (by rw [ebx, Fin.snoc_last]; exact h1.le) (by rw [ebx, Fin.snoc_last]; exact h2.le)
    (by rw [el]; exact hL) (by rw [er]; exact hR)
  have e : ((c1 + c2 : ℕ) : ℝ) / K + ε = ((c1 : ℝ) / K + ε / 2) + ((c2 : ℝ) / K + ε / 2) := by
    push_cast; ring
  rw [e]
  exact key

/-- Buchstab's identity at a floor that passes a test. -/
theorem pf_buch [RouteOK] {τ : Tests} {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell} {β : List Cell}
    (hτ : SoundF τ S R β) {x : Cell} {b : List Cell} {par : Bool} {f : ℕ} {cfg : Cfg} {c : ℕ}
    (hg : (opsK ctx β.length).grd (x :: b) = true) (hfx : f ≤ x.1) (hJ : τ.okJ (x :: b) f cfg = true)
    (hc : PF S R β ((f, x.2) :: x :: b) (!par) c) : PF S R β (x :: b) par c := by
  intro ch hbl k' h ε hε
  obtain ⟨ch', rfl, hbl'⟩ := cons_eq_append hbl (by intro h0; rw [h0] at h; simp at h)
  subst hbl'
  simp only [opsK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.length_cons, List.length_append] at hg
  have hlast : boxFn (x :: ch') (k' + 1) h (Fin.last k') = x := by simp [boxFn]
  have hEvJ := hτ.soundJ (x :: ch') f cfg (k' + 1) h (by simp only [List.length_cons]; omega) hJ
  have h2len : ((f, x.2) :: x :: ch').length = k' + 1 + 1 := by simp [← h]
  have hch := hc ((f, x.2) :: x :: ch') rfl (k' + 1) h2len ε hε
  have ech : boxFn ((f, x.2) :: x :: ch') (k' + 1 + 1) h2len =
      Fin.snoc (α := fun _ => Cell) (boxFn (x :: ch') (k' + 1) h) (f, x.2) :=
    boxFn_cons (f, x.2) (x :: ch') (k' + 1) h
  rw [ech] at hch
  refine bdF_buch (boxFn (x :: ch') (k' + 1) h) (f := f) (by rw [hlast]; exact hfx) hEvJ ?_
  rw [hlast]
  exact hch

/-- **The nodes of the tree of a reversed term prove `PF`**, for a frozen part in the range of `r'` for a cell
`ctx` with `0 < l₁ ≤ h₁ ≤ DEN` and tests that are sound for it. -/
theorem frozRules [RouteOK] {τ : Tests} {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (hS : InSlab S R ctx) {β : List Cell}
    (hτ : SoundF τ S R β) : Rules (opsK ctx β.length) τ (PF S R β) where
  van := fun _ hv => pf_vanish hctx hS hv
  evl := fun hg hI => pf_eval hτ hg hI
  drp := fun _ hd => pf_drop hctx hS hd
  alt := fun _ h => absurd h (lt_irrefl _)
  split := fun h1 h2 hl hr => pf_split h1 h2 hl hr
  buch := fun hg _ hfx hJ hc => pf_buch hτ hg hfx hJ hc

/-- **The search of the tree of a reversed term is sound over a frozen part**: a cost that it returns below its
limit has `PF`. -/
theorem frozSolve_sound [RouteOK] {τ : Tests} {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {ctx : Cell}
    (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (hS : InSlab S R ctx) {β : List Cell}
    (hτ : SoundF τ S R β) (St : Strat) (n : ℕ) :
    RecP (PF S R β) (solveG (opsK ctx β.length) τ St n) :=
  solveG_sound (frozRules hctx hS hτ) St n

/-! ### The top of a reversed tree -/

/-- **Buchstab's identity between two floors, for the chain with no prime**, on any range: for `f ≤ t ≤ DEN` at a
large modulus, the terms at the level `⌈x^{t/DEN}⌉` are the terms at the floor `⌈x^{f/DEN}⌉` minus the term of
the box of one prime with the cell `(f, t)`. -/
theorem famJ_levelN [RouteOK] {q : ℕ} (hq : Big q) (g : ℕ → ℝ) (N₁ N₂ : ℕ) {f t : ℕ} (hft : f ≤ t)
    (ht : t ≤ DEN) :
    famJ g N₁ N₂ ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ (famB q (boxFn [] 0 rfl)) =
      famJ g N₁ N₂ ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (famB q (boxFn [] 0 rfl)) -
        famI g N₁ N₂ (famB q (boxFn [(f, t)] 1 rfl)) := by
  obtain ⟨-, hx3, -, -, -⟩ := big_facts hq
  have hD := DEN_pos'
  have hx1 : 1 ≤ xq q := by linarith
  set z := ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ with hz
  set Z := ⌈xq q ^ ((t : ℝ) / DEN)⌉₊ with hZ
  have hzZ : z ≤ Z := Nat.ceil_le_ceil (pow_mono hx1 hft)
  have hbox : ∀ i : Fin 1, boxFn [(f, t)] 1 rfl i = (f, t) := fun i => by simp [boxFn]
  have hJ : ∀ w : ℕ, famJ g N₁ N₂ w (famB q (boxFn [] 0 rfl)) =
      ∑ m ∈ Ioc N₁ N₂, g m * (if SieveTree.rough w m then 1 else 0) := by
    intro w
    unfold famJ
    rw [famB_zero, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_dvd, true_and]
  have hpt : ∀ m ∈ Ioc N₁ N₂, g m * (if SieveTree.rough Z m then 1 else 0) =
      g m * (if SieveTree.rough z m then 1 else 0) -
        ∑ p ∈ SieveTree.primesIco z Z, g m * (if p ∣ m ∧ SieveTree.rough p m then 1 else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Ioc.1 hm).1; omega
    have h := buchstab_pt (W := 1) hm0 hzZ (fun p hp hd => absurd (Nat.dvd_one.1 hd) hp.one_lt.ne')
    simp only [one_dvd, true_and, one_mul] at h
    rw [h, mul_sub, Finset.mul_sum]
  rw [hJ, hJ]
  unfold famI
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_nbij' (fun p => fun _ => p) (fun rt => rt 0) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [SieveTree.mem_primesIco] at hp
    rw [mem_famB]
    have hpz : (p : ℝ) < xq q ^ ((t : ℝ) / DEN) := Nat.lt_ceil.1 hp.2.1
    refine ⟨fun _ => ⟨?_, hp.2.2⟩,
      fun a b hab => absurd (Fin.lt_def.1 hab) (by have := a.2; have := b.2; omega), fun i => ?_⟩
    · have h1 : xq q ^ ((t : ℝ) / DEN) ≤ xq q ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by
          rw [div_le_one hD]
          exact_mod_cast ht)
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

/-- **The top of a reversed tree.** For `f ≤ t ≤ DEN` at a large modulus: over a frozen part, the terms at the
level `x^{t/DEN}` of the chain with no prime are its terms at the floor `x^{f/DEN}` minus the term of the chain of
one prime with the cell `(f, t)`. -/
theorem dJF_level [RouteOK] {q : ℕ} (hq : Big q) (a : ZMod q) {ι : Type} (S : Finset ι) (R : ι → ℕ) {f t : ℕ}
    (hft : f ≤ t) (ht : t ≤ DEN) :
    dJF q a t S R (boxFn [] 0 rfl) =
      dJF q a f S R (boxFn [] 0 rfl) - dIF q a S R (boxFn [(f, t)] 1 rfl) := by
  unfold dJF dIF famJR famIR
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [famJ_levelN hq _ _ _ hft ht, famJ_levelN hq _ _ _ hft ht]
  ring

omit [Route] in
/-- **The search over a frozen part is sound, for any route**: `frozSolve_sound` with the route as a variable. -/
theorem frozSolve_sound_at (Rt : Route) (hRt : @RouteOK Rt) {τ : Tests} {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ}
    {ctx : Cell} (hctx : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN) (hS : @InSlab Rt ι S R ctx) {β : List Cell}
    (hτ : @SoundF Rt τ ι S R β) (St : Strat) (n : ℕ) :
    RecP (@PF Rt ι S R β) (solveG (opsK ctx β.length) τ St n) :=
  @frozSolve_sound Rt hRt τ ι S R ctx hctx hS β hτ St n

omit [Route] in
/-- **The top of a reversed tree, for any route**: `dJF_level` with the route as a variable. -/
theorem dJF_level_at (Rt : Route) (hRt : @RouteOK Rt) {q : ℕ} (hq : @Big Rt q) (a : ZMod q) {ι : Type}
    (S : Finset ι) (R : ι → ℕ) {f t : ℕ} (hft : f ≤ t) (ht : t ≤ DEN) :
    @dJF Rt q a t ι S R 0 (boxFn [] 0 rfl) =
      @dJF Rt q a f ι S R 0 (boxFn [] 0 rfl) - @dIF Rt q a ι S R 0 (boxFn [(f, t)] 1 rfl) :=
  @dJF_level Rt hRt q hq a ι S R f t hft ht

end SieveAd

#print axioms SieveAd.frozSolve_sound_at
#print axioms SieveAd.dJF_level_at
