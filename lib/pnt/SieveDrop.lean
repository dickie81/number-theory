/-
# The dropped terms' `B`-count

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The route and the grid are as in `SieveQ`, with `RouteOK`, `GridOK` and `Fits` where the Lean
takes them. `xq q = q^L`, and `cornerP z` is the set of primes of `(⌊z/4⌋, z]`.

* `card_le_Psi`, `famI_gB_le`: a family's `B`-count is at most `φ(q)⁻¹ Σ_rt Ψ(x/∏rt, rt_last)`, since the `n = Wc ∈
  (x, 2x]` with no prime factor below `z` inject into `Ψ(x/W, z)`.
* `drop2_le`, `drop4_le`: a dropped cell's `B`-count is at most `φ(q)⁻¹` times its sum over the primes of its cells
  (`SieveRough.cellP`), `Σ Ψ(x/(p₁p₂), p₂)` or `Σ Ψ(x/(p₁p₂p₃p₄), p₄)`.
* `corner_le`, `corner_ev`: for `(parQ q).Good` and `z_top² ≤ 4N₁`, a corner cell (not a candidate, not surely
  evaluable, `p₁`'s cell not inside the window) counts only the `n = p₁p₂`, both primes in `cornerP z_top`, so it is at
  most `φ(q)⁻¹|cornerP|²`; for `ε > 0` and large `q`, `z_top² ≤ 4N₁` and `n²|cornerP|² ≤ εx/log x` (`n` the grid's
  number of cells a side), by `cornerP_card_ev`.
* `D1_le`, `dropS_le_cost`, `shares_ev`, `sum_cost_div`: the dropped cells' sums are at most their certificate costs
  `cost/K` times `x/log x`, plus `δ′(1 + n²)x/log x` for `δ′ > 0` and large `x`, by `SieveRough.share2_of_cand` and
  `share4_of_counted4` simultaneously for the finitely many cells, and the costs total at most `0.88` when the
  certificate's total is at most `0.88K` (`htot`, `SieveCert.total_div_le`).
* `drop_ev`: given `htot`, for `ε > 0`, eventually `D1(g_B) ≤ φ(q)⁻¹(0.88 + ε)x/log x`.
* `sum_cost_div_of`, `drop_ev_of`, `total_div_lt`: the same with the loss as a parameter, `total/K ≤ c` in
  the reals, so `D1(g_B) ≤ φ(q)⁻¹(c + ε)x/log x`; and `total < K` gives `total/K < 1`. The `0.88` forms are their cases.

This is the loss: the shares of the dropped cells and the certificate's total bound the dropped
families' `B`-counts, and the corner near `(1/2, 1/2)` is `o(x/log x)`.

The route's numbers, the certificate's grid parameters and the certificate's total are a hypothesis (`htot`); the
library's theorem (`Linnik22250R`) instantiates the refined version of it (`SieveDrop2`).

The file imports `SieveQ.lean`.
-/
import SieveQ

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveRoute
open SieveCert (V DEN H U1 U2 cand dec inKK ne3 counted4 surelyEval cell bound2 bound4 bound6 K total cost refcost
  nC eC inKK5 ne5 counted6 dec4 refcost5 cost4)

namespace SieveDrop

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-! ### A dropped family's `B`-count, by rough numbers -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- For `x > 0` and `W > 0`, the multiples `n = Wc ∈ (x, 2x]` of `W` with no prime factor below `z` inject into
`Ψ(x/W, z)` by `n ↦ n/W`. -/
theorem card_le_Psi {x : ℝ} (hx : 0 < x) {W z : ℕ} (hW : 0 < W) :
    ((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (fun n => W ∣ n ∧ SieveTree.rough z n)).card ≤ Psi (x / W) z := by
  unfold Psi roughSet
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  refine Finset.card_le_card_of_injOn (fun n => n / W) ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    dsimp only
    rw [Nat.mul_div_cancel_left c hW]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.floor_lt (by positivity), div_lt_iff₀ hW']
      have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h4 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((W * c : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h4
      linarith
    · rw [Nat.le_floor_iff (by positivity)]
      have h3 : ((W * c : ℕ) : ℝ) ≤ 2 * x := (Nat.cast_le.2 h2).trans (Nat.floor_le (by positivity))
      push_cast at h3
      rw [mul_div_assoc', le_div_iff₀ hW']
      linarith
    · intro p hp
      by_contra hlt
      exact hr p (not_le.1 hlt) (Nat.prime_of_mem_primeFactors hp)
        (dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) W)
  · intro n₁ hn₁ n₂ hn₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hn₁ hn₂
    exact (Nat.div_left_inj hn₁.2.1 hn₂.2.1).1 h

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem gB_le (q m : ℕ) : gB q m ≤ (q.totient : ℝ)⁻¹ := by
  unfold gB
  split_ifs
  · exact le_rfl
  · positivity

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem gB_nonneg (q m : ℕ) : 0 ≤ gB q m := by
  unfold gB
  split_ifs <;> positivity

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- **A family's `B`-count.** For `q ≥ 1` and a family of tuples of primes, it is at most
`φ(q)⁻¹ Σ_rt Ψ(x/∏rt, rt_last)`. -/
theorem famI_gB_le (q : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) (hF : ∀ rt ∈ F, ∀ i, (rt i).Prime)
    (hq : 1 ≤ q) :
    famI (gB q) (N1 q) (N2 q) F ≤
      (q.totient : ℝ)⁻¹ * ∑ rt ∈ F, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last k')) : ℝ) := by
  have hx : 0 < xq q := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  unfold famI
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun rt hrt => ?_
  have hW : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hF rt hrt i).pos
  calc ∑ n ∈ Ioc (N1 q) (N2 q), gB q n *
        (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0)
      ≤ ∑ n ∈ Ioc (N1 q) (N2 q), (q.totient : ℝ)⁻¹ *
        (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (gB_le q n) (by split_ifs <;> norm_num)
    _ = (q.totient : ℝ)⁻¹ * (((Ioc (N1 q) (N2 q)).filter
          (fun n => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n)).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.card_filter]
        push_cast
        rfl
    _ ≤ (q.totient : ℝ)⁻¹ * (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last k')) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast card_le_Psi hx hW

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- A sum of a nonnegative `g` over the pairs of a family whose entries lie in `s₀`, `s₁` is at most the sum over
`s₀ × s₁`. -/
theorem sum_le_box2 {s₀ s₁ : Finset ℕ} (F : Finset (Fin 2 → ℕ)) (hF : ∀ rt ∈ F, rt 0 ∈ s₀ ∧ rt 1 ∈ s₁)
    (g : ℕ → ℕ → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    ∑ rt ∈ F, g (rt 0) (rt 1) ≤ ∑ a ∈ s₀, ∑ b ∈ s₁, g a b := by
  rw [← Finset.sum_product']
  have hinj : Set.InjOn (fun rt : Fin 2 → ℕ => (rt 0, rt 1)) F := by
    intro r₁ _ r₂ _ h
    simp only [Prod.mk.injEq] at h
    funext t
    fin_cases t
    · exact h.1
    · exact h.2
  rw [← Finset.sum_image (f := fun p : ℕ × ℕ => g p.1 p.2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hg _ _
  intro p hp
  obtain ⟨rt, hrt, rfl⟩ := Finset.mem_image.1 hp
  exact Finset.mem_product.2 (hF rt hrt)

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- The same for quadruples. -/
theorem sum_le_box4 {s₀ s₁ s₂ s₃ : Finset ℕ} (F : Finset (Fin 4 → ℕ))
    (hF : ∀ rt ∈ F, rt 0 ∈ s₀ ∧ rt 1 ∈ s₁ ∧ rt 2 ∈ s₂ ∧ rt 3 ∈ s₃) (g : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hg : ∀ a b c d, 0 ≤ g a b c d) :
    ∑ rt ∈ F, g (rt 0) (rt 1) (rt 2) (rt 3) ≤ ∑ a ∈ s₀, ∑ b ∈ s₁, ∑ c ∈ s₂, ∑ d ∈ s₃, g a b c d := by
  have hR : ∑ a ∈ s₀, ∑ b ∈ s₁, ∑ c ∈ s₂, ∑ d ∈ s₃, g a b c d =
      ∑ p ∈ s₀ ×ˢ (s₁ ×ˢ (s₂ ×ˢ s₃)), g p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product]
  rw [hR]
  have hinj : Set.InjOn (fun rt : Fin 4 → ℕ => (rt 0, rt 1, rt 2, rt 3)) F := by
    intro r₁ _ r₂ _ h
    simp only [Prod.mk.injEq] at h
    funext t
    fin_cases t
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  rw [← Finset.sum_image (f := fun p : ℕ × ℕ × ℕ × ℕ => g p.1 p.2.1 p.2.2.1 p.2.2.2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hg _ _ _ _
  intro p hp
  obtain ⟨rt, hrt, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨h0, h1, h2, h3⟩ := hF rt hrt
  simp only [Finset.mem_product]
  exact ⟨h0, h1, h2, h3⟩

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- The same for sextuples. -/
theorem sum_le_box6 {s₀ s₁ s₂ s₃ s₄ s₅ : Finset ℕ} (F : Finset (Fin 6 → ℕ))
    (hF : ∀ rt ∈ F, rt 0 ∈ s₀ ∧ rt 1 ∈ s₁ ∧ rt 2 ∈ s₂ ∧ rt 3 ∈ s₃ ∧ rt 4 ∈ s₄ ∧ rt 5 ∈ s₅)
    (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (hg : ∀ a b c d e f, 0 ≤ g a b c d e f) :
    ∑ rt ∈ F, g (rt 0) (rt 1) (rt 2) (rt 3) (rt 4) (rt 5) ≤
      ∑ a ∈ s₀, ∑ b ∈ s₁, ∑ c ∈ s₂, ∑ d ∈ s₃, ∑ e ∈ s₄, ∑ f ∈ s₅, g a b c d e f := by
  have hR : ∑ a ∈ s₀, ∑ b ∈ s₁, ∑ c ∈ s₂, ∑ d ∈ s₃, ∑ e ∈ s₄, ∑ f ∈ s₅, g a b c d e f =
      ∑ p ∈ s₀ ×ˢ (s₁ ×ˢ (s₂ ×ˢ (s₃ ×ˢ (s₄ ×ˢ s₅)))),
        g p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_product]
  rw [hR]
  have hinj : Set.InjOn (fun rt : Fin 6 → ℕ => (rt 0, rt 1, rt 2, rt 3, rt 4, rt 5)) F := by
    intro r₁ _ r₂ _ h
    simp only [Prod.mk.injEq] at h
    funext t
    fin_cases t
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2
  rw [← Finset.sum_image (f := fun p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
    g p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hg _ _ _ _ _ _
  intro p hp
  obtain ⟨rt, hrt, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hF rt hrt
  simp only [Finset.mem_product]
  exact ⟨h0, h1, h2, h3, h4, h5⟩

/-! ### The dropped cells -/

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem mem_cellP_of {q : ℕ} {c p : ℕ} (hp : p.Prime) (h : InC (xq q) c p) : p ∈ cellP (xq q) c :=
  mem_primesIn.2 ⟨hp, h.1, h.2⟩

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A dropped cell of depth 2**, for `q ≥ 1`: its `B`-count is at most `φ(q)⁻¹ Σ_{p₁, p₂} Ψ(x/(p₁p₂), p₂)` over the
cell. -/
theorem drop2_le {q : ℕ} (hq : 1 ≤ q) (i j : ℕ) :
    (parQ q).I (gB q) ((parQ q).S2c i j) ≤
      (q.totient : ℝ)⁻¹ * ∑ p₁ ∈ cellP (xq q) i, ∑ p₂ ∈ cellP (xq q) j, (Psi (xq q / (p₁ * p₂)) p₂ : ℝ) := by
  have hF : ∀ rt ∈ famSet 2 (N2 q) ((parQ q).S2c i j), ∀ t, (rt t).Prime :=
    fun rt hrt t => ((mem_famSet.1 hrt).1 t).2
  refine (famI_gB_le q _ hF hq).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h := sum_le_box2 (s₀ := cellP (xq q) i) (s₁ := cellP (xq q) j) (famSet 2 (N2 q) ((parQ q).S2c i j))
    (fun rt hrt => by
      obtain ⟨-, hi, hj⟩ := (parQ q).facts_S2c hrt
      exact ⟨mem_cellP_of (hF rt hrt 0) hi, mem_cellP_of (hF rt hrt 1) hj⟩)
    (fun a b => (Psi (xq q / (a * b)) b : ℝ)) (fun a b => Nat.cast_nonneg _)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun rt _ => ?_) h
  rw [Fin.prod_univ_two]
  push_cast
  rfl

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A dropped cell of depth 4**, for `q ≥ 1`: its `B`-count is at most `φ(q)⁻¹ Σ Ψ(x/(p₁p₂p₃p₄), p₄)` over the
cell. -/
theorem drop4_le {q : ℕ} (hq : 1 ≤ q) (i j k l : ℕ) :
    (parQ q).I (gB q) ((parQ q).S4c i j k l) ≤
      (q.totient : ℝ)⁻¹ * ∑ p₁ ∈ cellP (xq q) i, ∑ p₂ ∈ cellP (xq q) j, ∑ p₃ ∈ cellP (xq q) k,
        ∑ p₄ ∈ cellP (xq q) l, (Psi (xq q / (p₁ * p₂ * p₃ * p₄)) p₄ : ℝ) := by
  have hF : ∀ rt ∈ famSet 4 (N2 q) ((parQ q).S4c i j k l), ∀ t, (rt t).Prime :=
    fun rt hrt t => ((mem_famSet.1 hrt).1 t).2
  refine (famI_gB_le q _ hF hq).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h := sum_le_box4 (s₀ := cellP (xq q) i) (s₁ := cellP (xq q) j) (s₂ := cellP (xq q) k)
    (s₃ := cellP (xq q) l) (famSet 4 (N2 q) ((parQ q).S4c i j k l))
    (fun rt hrt => by
      obtain ⟨-, hi, hj, hk, hl, -⟩ := (parQ q).facts_S4c hrt
      exact ⟨mem_cellP_of (hF rt hrt 0) hi, mem_cellP_of (hF rt hrt 1) hj, mem_cellP_of (hF rt hrt 2) hk,
        mem_cellP_of (hF rt hrt 3) hl⟩)
    (fun a b c d => (Psi (xq q / (a * b * c * d)) d : ℝ)) (fun a b c d => Nat.cast_nonneg _)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun rt _ => ?_) h
  rw [Fin.prod_univ_four]
  push_cast
  rfl

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem mem_cellPC_of {q : ℕ} {c p : ℕ} (hp : p.Prime) (h : InCC (xq q) c p) :
    p ∈ @cellP SieveCert.Gc (xq q) c :=
  mem_primesIn.2 ⟨hp, h.1, h.2⟩

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A dropped cell of depth 6** (four fine cells, then two coarse ones), for `q ≥ 1`: its `B`-count is at most
`φ(q)⁻¹ Σ Ψ(x/(p₁⋯p₆), p₆)` over the cell. -/
theorem drop6_le {q : ℕ} (hq : 1 ≤ q) (i j k l b c : ℕ) :
    (parQ q).I (gB q) ((parQ q).S6c i j k l b c) ≤
      (q.totient : ℝ)⁻¹ * ∑ p₁ ∈ cellP (xq q) i, ∑ p₂ ∈ cellP (xq q) j, ∑ p₃ ∈ cellP (xq q) k,
        ∑ p₄ ∈ cellP (xq q) l, ∑ p₅ ∈ @cellP SieveCert.Gc (xq q) b, ∑ p₆ ∈ @cellP SieveCert.Gc (xq q) c,
          (Psi (xq q / (p₁ * p₂ * p₃ * p₄ * p₅ * p₆)) p₆ : ℝ) := by
  have hF : ∀ rt ∈ famSet 6 (N2 q) ((parQ q).S6c i j k l b c), ∀ t, (rt t).Prime :=
    fun rt hrt t => ((mem_famSet.1 hrt).1 t).2
  refine (famI_gB_le q _ hF hq).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h := sum_le_box6 (s₀ := cellP (xq q) i) (s₁ := cellP (xq q) j) (s₂ := cellP (xq q) k)
    (s₃ := cellP (xq q) l) (s₄ := @cellP SieveCert.Gc (xq q) b) (s₅ := @cellP SieveCert.Gc (xq q) c)
    (famSet 6 (N2 q) ((parQ q).S6c i j k l b c))
    (fun rt hrt => by
      obtain ⟨-, hi, hj, hk, hl, hb, hc, -⟩ := (parQ q).facts_S6c hrt
      exact ⟨mem_cellP_of (hF rt hrt 0) hi, mem_cellP_of (hF rt hrt 1) hj, mem_cellP_of (hF rt hrt 2) hk,
        mem_cellP_of (hF rt hrt 3) hl, mem_cellPC_of (hF rt hrt 4) hb, mem_cellPC_of (hF rt hrt 5) hc⟩)
    (fun a b c d e f => (Psi (xq q / (a * b * c * d * e * f)) f : ℝ)) (fun a b c d e f => Nat.cast_nonneg _)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun rt _ => ?_) h
  rw [Fin.prod_univ_six]
  push_cast
  rfl

/-- The primes of `(⌊z/4⌋, z]`, where the corner's primes lie. -/
noncomputable def cornerP (z : ℕ) : Finset ℕ := (Ioc ⌊(z : ℝ) / 4⌋₊ z).filter Nat.Prime

omit [RouteOK] [Fits] in
/-- **A corner cell** (not a candidate, not surely evaluable, `p₁`'s cell `i < n` not inside the window), on a grid with
`GridOK`, for `(parQ q).Good` and `z_top² ≤ 4N₁`: its `n` are the products `p₁p₂` of its pairs, so its `B`-count is at
most `φ(q)⁻¹ |cornerP|²`. -/
theorem corner_le {q : ℕ} (G : (parQ q).Good) (hsq : (((parQ q).ztop : ℝ)) ^ 2 ≤ 4 * N1 q) {i j : ℕ}
    (hi : i < SieveCert.n) (hW : ¬ Par.inW i) (hc : cand i j = false) (hs : Par.sE2 i j = false) :
    (parQ q).I (gB q) ((parQ q).S2c i j) ≤ (q.totient : ℝ)⁻¹ * ((cornerP (parQ q).ztop).card : ℝ) ^ 2 := by
  have hx0 : 0 < (parQ q).x := by linarith [G.hx]
  have hx1 : 1 ≤ (parQ q).x := G.hx.le
  have h2i := SieveCert.two_e_lt i hi
  have hcases : SieveCert.e i + H ≤ SieveCert.e j ∨ DEN < SieveCert.e i + 2 * SieveCert.e j := by
    simp only [cand, Par.sE2] at hc hs
    simp only [hs, Bool.not_false, Bool.and_true, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt,
      not_le, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hc
    unfold Par.inW at hW
    rcases hc with ((h | h) | h) | h
    · exact Or.inl h
    · omega
    · exact Or.inr h
    · exact absurd h hW
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  rcases hcases with h | h
  · -- empty: `p₂ ≥ x^{e_j} ≥ x^{e_i + H} > p₁`
    have : (parQ q).I (gB q) ((parQ q).S2c i j) = 0 := by
      refine famI_eq_zero _ _ _ _ fun rt hrt => False.elim ?_
      obtain ⟨hch, hCi, hCj⟩ := (parQ q).facts_S2c hrt
      have h10 : rt 1 < rt 0 := hch.1 (show (0 : Fin 2) < 1 by decide)
      have : (rt 0 : ℝ) < rt 1 := lt_of_lt_of_le hCi.2 ((Par.rpow_cell_le hx1 h).trans hCj.1)
      exact absurd h10 (not_lt.2 (by exact_mod_cast this.le))
    rw [this]
    positivity
  · -- the corner: each pair contributes at most `n = p₁p₂`
    unfold Par.I famI
    set F := famSet 2 (N2 q) ((parQ q).S2c i j) with hFdef
    have hterm : ∀ rt ∈ F, ∑ m ∈ Ioc (N1 q) (N2 q), gB q m *
        (if (∏ t, rt t) ∣ m ∧ SieveTree.rough (rt (Fin.last 1)) m then 1 else 0) ≤
          (q.totient : ℝ)⁻¹ * (if N1 q < rt 0 * rt 1 then 1 else 0) := by
      intro rt hrt
      obtain ⟨hch, hCi, hCj⟩ := (parQ q).facts_S2c hrt
      have hp : ∀ t, (rt t).Prime := fun t => ((mem_famSet.1 hrt).1 t).2
      have hW2 : (∏ t, rt t) = rt 0 * rt 1 := Fin.prod_univ_two _
      -- `p₁p₂² > N₂`
      have hbig : N2 q < rt 0 * rt 1 * rt 1 := by
        have hp4 := Par.prod4_ge hx0 hCi.1 hCj.1 hCj.1 (show (parQ q).x ^ ((0 : ℝ) / DEN) ≤ (1 : ℝ) by simp)
        have hreg := Par.rpow_region hx1 (s := SieveCert.e i + 2 * SieveCert.e j) h
        have : (N2 q : ℝ) < ((rt 0 * rt 1 * rt 1 : ℕ) : ℝ) := by
          push_cast
          refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ (hp4.trans (le_of_eq (by ring)))))
          congr 1
          push_cast
          ring
        exact_mod_cast this
      have hsub : (Ioc (N1 q) (N2 q)).filter (fun m => (∏ t, rt t) ∣ m ∧
          SieveTree.rough (rt (Fin.last 1)) m) ⊆ (Ioc (N1 q) (N2 q)).filter (fun m => m = rt 0 * rt 1) := by
        intro m hm
        rw [Finset.mem_filter] at hm ⊢
        refine ⟨hm.1, ?_⟩
        obtain ⟨⟨c, rfl⟩, hr⟩ := hm.2
        rw [hW2] at hr ⊢
        rcases Nat.lt_or_ge c 2 with hc2 | hc2
        · have hc0 : c ≠ 0 := by
            rintro rfl
            have := (Finset.mem_Ioc.1 hm.1).1
            rw [hW2] at this
            simp at this
          have : c = 1 := by omega
          subst this
          ring
        · exfalso
          have hrc : SieveTree.rough (rt 1) c := fun p hp1 hpp hpc =>
            hr p hp1 hpp (dvd_mul_of_dvd_right hpc _)
          have hmin := (SieveStops2.rough_iff_le_minFac hc2).1 hrc
          have := Nat.minFac_le (by omega : 0 < c)
          have h3 : rt 0 * rt 1 * rt 1 ≤ rt 0 * rt 1 * c := Nat.mul_le_mul_left _ (by omega)
          have := (Finset.mem_Ioc.1 hm.1).2
          rw [hW2] at this
          omega
      calc ∑ m ∈ Ioc (N1 q) (N2 q), gB q m *
            (if (∏ t, rt t) ∣ m ∧ SieveTree.rough (rt (Fin.last 1)) m then 1 else 0)
          ≤ ∑ m ∈ Ioc (N1 q) (N2 q), (q.totient : ℝ)⁻¹ *
            (if (∏ t, rt t) ∣ m ∧ SieveTree.rough (rt (Fin.last 1)) m then 1 else 0) :=
            Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right (gB_le q m) (by split_ifs <;> norm_num)
        _ = (q.totient : ℝ)⁻¹ * (((Ioc (N1 q) (N2 q)).filter (fun m => (∏ t, rt t) ∣ m ∧
              SieveTree.rough (rt (Fin.last 1)) m)).card : ℝ) := by
            rw [← Finset.mul_sum, Finset.card_filter]
            push_cast
            rfl
        _ ≤ (q.totient : ℝ)⁻¹ * (if N1 q < rt 0 * rt 1 then 1 else 0) := by
            refine mul_le_mul_of_nonneg_left ?_ hφ
            have hc := Finset.card_le_card hsub
            have hc1 : ((Ioc (N1 q) (N2 q)).filter (fun m => m = rt 0 * rt 1)).card ≤
                if N1 q < rt 0 * rt 1 then 1 else 0 := by
              split_ifs with hlt
              · refine (Finset.card_le_card (t := {rt 0 * rt 1}) fun m hm => ?_).trans
                  (Finset.card_singleton _).le
                rw [Finset.mem_filter] at hm
                exact Finset.mem_singleton.2 hm.2
              · refine Nat.le_zero.2 (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun m hm hmeq => ?_))
                have := (Finset.mem_Ioc.1 hm).1
                omega
            have := hc.trans hc1
            split_ifs at this ⊢ <;> exact_mod_cast this
    calc ∑ rt ∈ F, ∑ m ∈ Ioc (N1 q) (N2 q), gB q m *
          (if (∏ t, rt t) ∣ m ∧ SieveTree.rough (rt (Fin.last 1)) m then 1 else 0)
        ≤ ∑ rt ∈ F, (q.totient : ℝ)⁻¹ * (if N1 q < rt 0 * rt 1 then 1 else 0) := Finset.sum_le_sum hterm
      _ = (q.totient : ℝ)⁻¹ * ((F.filter (fun rt => N1 q < rt 0 * rt 1)).card : ℝ) := by
          rw [← Finset.mul_sum, Finset.card_filter]
          push_cast
          rfl
      _ ≤ (q.totient : ℝ)⁻¹ * ((cornerP (parQ q).ztop).card : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hφ
          rw [sq, ← Nat.cast_mul, ← Finset.card_product]
          refine Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun rt => (rt 0, rt 1)) ?_ ?_)
          · intro rt hrt
            rw [Finset.mem_coe, Finset.mem_filter] at hrt
            obtain ⟨hch, -, -⟩ := (parQ q).facts_S2c hrt.1
            have hp : ∀ t, (rt t).Prime := fun t => ((mem_famSet.1 hrt.1).1 t).2
            have h10 : rt 1 < rt 0 := hch.1 (show (0 : Fin 2) < 1 by decide)
            have h0z : rt 0 < (parQ q).ztop := hch.2.2 0
            have hN : N1 q < rt 0 * rt 1 := hrt.2
            -- both primes exceed `z_top/4`
            have hz4 : ((parQ q).ztop : ℝ) / 4 < rt 1 := by
              have h1 : ((N1 q : ℕ) : ℝ) < (rt 0 : ℝ) * rt 1 := by exact_mod_cast hN
              have h2 : (rt 0 : ℝ) < (parQ q).ztop := by exact_mod_cast h0z
              have h3 : (0 : ℝ) < rt 1 := by exact_mod_cast (hp 1).pos
              nlinarith
            have hz4' : ((parQ q).ztop : ℝ) / 4 < rt 0 := lt_trans hz4 (by exact_mod_cast h10)
            rw [Finset.mem_coe, Finset.mem_product]
            refine ⟨Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, h0z.le⟩, hp 0⟩,
              Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, (h10.trans h0z).le⟩, hp 1⟩⟩
            · exact (Nat.floor_lt (by positivity)).2 hz4'
            · exact (Nat.floor_lt (by positivity)).2 hz4
          · intro r₁ _ r₂ _ hr
            simp only [Prod.mk.injEq] at hr
            funext t
            fin_cases t
            · exact hr.1
            · exact hr.2

/-! ### The corner is small -/

omit [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem tendsto_xq : Tendsto xq atTop atTop :=
  (tendsto_rpow_atTop (L_pos : (0 : ℝ) < L)).comp tendsto_natCast_atTop_atTop

omit [SieveCert.GridOK] [Fits] in
/-- For a route with `RouteOK` and `q ≥ 1`, `√x ≤ z_top ≤ √(2x) + 1`. -/
theorem ztop_bounds (q : ℕ) (hq : 1 ≤ q) :
    Real.sqrt (xq q) ≤ ((parQ q).ztop : ℝ) ∧ ((parQ q).ztop : ℝ) ≤ Real.sqrt (2 * xq q) + 1 := by
  show Real.sqrt (xq q) ≤ ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ∧ ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ≤ _
  push_cast
  constructor
  · exact (Real.sqrt_le_sqrt (N2_ge q hq)).trans Real.real_sqrt_le_nat_sqrt_succ
  · have h1 : (Nat.sqrt (N2 q) : ℝ) ≤ Real.sqrt (N2 q) := Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt (N2 q) ≤ Real.sqrt (2 * xq q) := Real.sqrt_le_sqrt (N2_le q)
    linarith

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- The corner's primes number at most `12√x/log x`, for `√x ≤ z ≤ 2√x` and `x` large. -/
theorem cornerP_card_ev : ∃ X₀ : ℝ, ∀ x ≥ X₀, ∀ z : ℕ, Real.sqrt x ≤ z → (z : ℝ) ≤ 2 * Real.sqrt x →
    ((cornerP z).card : ℝ) ≤ 12 * Real.sqrt x / Real.log x := by
  obtain ⟨y₀, hy₀⟩ := card_primes_dyadic (ε := 1) one_pos
  refine ⟨max (16 * y₀ ^ 2) 16, fun x hx z hz1 hz2 => ?_⟩
  have hx16 : 16 ≤ x := le_trans (le_max_right _ _) hx
  have hsx : 4 ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hlogx : 4 * Real.log 2 ≤ Real.log x := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; linarith)
  set A : ℝ := (z : ℝ) / 4 with hA
  have hA0 : 0 < A := by rw [hA]; linarith
  have hy : y₀ ≤ A := by
    have : y₀ ≤ Real.sqrt x / 4 := by
      have h1 : Real.sqrt (16 * y₀ ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (le_trans (le_max_left _ _) hx)
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs,
        show Real.sqrt 16 = 4 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
      have := le_abs_self y₀
      linarith
    rw [hA]
    linarith
  -- `(⌊A⌋, z] = (⌊A⌋, ⌊2A⌋] ∪ (⌊2A⌋, ⌊4A⌋]`
  have hz4 : ⌊2 * (2 * A)⌋₊ = z := by
    rw [hA, show 2 * (2 * ((z : ℝ) / 4)) = (z : ℝ) by ring, Nat.floor_natCast]
  have hle1 : ⌊A⌋₊ ≤ ⌊2 * A⌋₊ := Nat.floor_le_floor (by linarith)
  have hle2 : ⌊2 * A⌋₊ ≤ z := by rw [← hz4]; exact Nat.floor_le_floor (by linarith)
  have hsplit : cornerP z ⊆ ((Ioc ⌊A⌋₊ ⌊2 * A⌋₊).filter Nat.Prime) ∪
      ((Ioc ⌊2 * A⌋₊ ⌊2 * (2 * A)⌋₊).filter Nat.Prime) := by
    intro p hp
    rw [cornerP, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [hz4, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
    by_cases h : p ≤ ⌊2 * A⌋₊
    · exact Or.inl ⟨⟨by rw [hA]; exact hp.1.1, h⟩, hp.2⟩
    · exact Or.inr ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hc1 := hy₀ A hy
  have hc2 := hy₀ (2 * A) (by linarith)
  have hcard : ((cornerP z).card : ℝ) ≤
      (1 + 1) * A / Real.log (2 * A) + (1 + 1) * (2 * A) / Real.log (2 * (2 * A)) := by
    have := Finset.card_le_card hsplit
    have h2 := Finset.card_union_le ((Ioc ⌊A⌋₊ ⌊2 * A⌋₊).filter Nat.Prime)
      ((Ioc ⌊2 * A⌋₊ ⌊2 * (2 * A)⌋₊).filter Nat.Prime)
    have h3 : ((cornerP z).card : ℝ) ≤ (((Ioc ⌊A⌋₊ ⌊2 * A⌋₊).filter Nat.Prime).card : ℝ) +
        (((Ioc ⌊2 * A⌋₊ ⌊2 * (2 * A)⌋₊).filter Nat.Prime).card : ℝ) := by exact_mod_cast this.trans h2
    linarith
  -- `log 2A ≥ (log x)/4`
  have hl2A : Real.log x / 4 ≤ Real.log (2 * A) := by
    have h1 : Real.sqrt x / 2 ≤ 2 * A := by rw [hA]; linarith
    have h2 : Real.log (Real.sqrt x / 2) = Real.log x / 2 - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by linarith)]
    have h3 := Real.log_le_log (by positivity) h1
    linarith
  have hlx : 0 < Real.log x := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith
  have hl4A : Real.log (2 * A) ≤ Real.log (2 * (2 * A)) := Real.log_le_log (by positivity) (by linarith)
  have hl2A0 : 0 < Real.log (2 * A) := by linarith
  have hb1 : (1 + 1) * A / Real.log (2 * A) ≤ 2 * A / (Real.log x / 4) := by
    rw [show (1 + 1 : ℝ) = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hl2A
  have hb2 : (1 + 1) * (2 * A) / Real.log (2 * (2 * A)) ≤ 4 * A / (Real.log x / 4) := by
    rw [show (1 + 1 : ℝ) * (2 * A) = 4 * A by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (hl2A.trans hl4A)
  have hAx : A ≤ Real.sqrt x / 2 := by rw [hA]; linarith
  have : 2 * A / (Real.log x / 4) + 4 * A / (Real.log x / 4) = 24 * A / Real.log x := by
    field_simp
    ring
  have h24 : 24 * A / Real.log x ≤ 12 * Real.sqrt x / Real.log x :=
    div_le_div_of_nonneg_right (by linarith) hlx.le
  linarith

omit [SieveCert.GridOK] [Fits] in
/-- **The corner is `o(x/log x)`.** For a route with `RouteOK`, `ε > 0` and large `q`: `z_top² ≤ 4N₁` and
`n²|cornerP(z_top)|² ≤ εx/log x`. -/
theorem corner_ev {ε : ℝ} (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop,
    (((parQ q).ztop : ℝ)) ^ 2 ≤ 4 * N1 q ∧
      (SieveCert.n : ℝ) ^ 2 * ((cornerP (parQ q).ztop).card : ℝ) ^ 2 ≤ ε * (xq q / Real.log (xq q)) := by
  obtain ⟨X₀, hX₀⟩ := cornerP_card_ev
  have hev := tendsto_xq.eventually_ge_atTop (max (max X₀ 16) (Real.exp (144 * (SieveCert.n : ℝ) ^ 2 / ε)))
  filter_upwards [hev, eventually_ge_atTop 1] with q hq hq1
  have hx16 : 16 ≤ xq q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hxX : X₀ ≤ xq q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hxe : Real.exp (144 * (SieveCert.n : ℝ) ^ 2 / ε) ≤ xq q := le_trans (le_max_right _ _) hq
  have hsx : 4 ≤ Real.sqrt (xq q) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  obtain ⟨hz1, hz2⟩ := ztop_bounds q hq1
  have hs2 : Real.sqrt (2 * xq q) = Real.sqrt 2 * Real.sqrt (xq q) := Real.sqrt_mul (by norm_num) _
  have hr2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsq_x : Real.sqrt (xq q) ^ 2 = xq q := Real.sq_sqrt (by linarith)
  have hz2' : ((parQ q).ztop : ℝ) ≤ 2 * Real.sqrt (xq q) := by nlinarith
  refine ⟨?_, ?_⟩
  · have hN1 : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    have : ((parQ q).ztop : ℝ) ≤ 3 / 2 * Real.sqrt (xq q) + 1 := by nlinarith
    have h0 : (0 : ℝ) ≤ (parQ q).ztop := Nat.cast_nonneg _
    nlinarith
  · have hc := hX₀ (xq q) hxX _ hz1 hz2'
    have hlx : 144 * (SieveCert.n : ℝ) ^ 2 / ε ≤ Real.log (xq q) := by
      rw [← Real.log_exp (144 * (SieveCert.n : ℝ) ^ 2 / ε)]
      exact Real.log_le_log (Real.exp_pos _) hxe
    have hlx0 : 0 < Real.log (xq q) := Real.log_pos (by linarith)
    have hc0 : (0 : ℝ) ≤ (cornerP (parQ q).ztop).card := Nat.cast_nonneg _
    have hsq : ((cornerP (parQ q).ztop).card : ℝ) ^ 2 ≤ 144 * xq q / Real.log (xq q) ^ 2 := by
      have h1 : ((cornerP (parQ q).ztop).card : ℝ) ^ 2 ≤ (12 * Real.sqrt (xq q) / Real.log (xq q)) ^ 2 :=
        pow_le_pow_left₀ hc0 hc 2
      rw [div_pow, mul_pow, hsq_x] at h1
      linarith
    have hn : (0 : ℝ) ≤ (SieveCert.n : ℝ) ^ 2 := by positivity
    calc (SieveCert.n : ℝ) ^ 2 * ((cornerP (parQ q).ztop).card : ℝ) ^ 2
        ≤ (SieveCert.n : ℝ) ^ 2 * (144 * xq q / Real.log (xq q) ^ 2) := mul_le_mul_of_nonneg_left hsq hn
      _ = (144 * (SieveCert.n : ℝ) ^ 2 / Real.log (xq q)) * (xq q / Real.log (xq q)) := by
          field_simp
      _ ≤ ε * (xq q / Real.log (xq q)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_iff₀ hlx0]
          rw [div_le_iff₀ hε] at hlx
          linarith

/-! ### All the dropped terms -/

/-- A cell's sum `Σ_{p₁, p₂} Ψ(x/(p₁p₂), p₂)` of depth 2. -/
noncomputable def S2 (x : ℝ) (i j : ℕ) : ℝ := ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, (Psi (x / (p₁ * p₂)) p₂ : ℝ)

/-- A cell's sum `Σ Ψ(x/(p₁p₂p₃p₄), p₄)` of depth 4. -/
noncomputable def S4 (x : ℝ) (i j k l : ℕ) : ℝ :=
  ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l, (Psi (x / (p₁ * p₂ * p₃ * p₄)) p₄ : ℝ)

/-- A cell's sum `Σ Ψ(x/(p₁⋯p₆), p₆)` of depth 6: four fine cells, then two coarse ones. -/
noncomputable def S6 (x : ℝ) (i j k l b c : ℕ) : ℝ :=
  ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
    ∑ p₅ ∈ @cellP SieveCert.Gc x b, ∑ p₆ ∈ @cellP SieveCert.Gc x c,
      (Psi (x / (p₁ * p₂ * p₃ * p₄ * p₅ * p₆)) p₆ : ℝ)

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem S2_nonneg (x : ℝ) (i j : ℕ) : 0 ≤ S2 x i j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem S4_nonneg (x : ℝ) (i j k l : ℕ) : 0 ≤ S4 x i j k l :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem S6_nonneg (x : ℝ) (i j k l b c : ℕ) : 0 ≤ S6 x i j k l b c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The dropped depth-6 cells' sums below the cell `(i, j, k, l)` of depth 4 that is decomposed. -/
noncomputable def dropS5 (x : ℝ) (i j k l : ℕ) : ℝ :=
  ∑ b ∈ range nC, (if inKK5 i j k l b = true ∧ ne5 i j k l b = true then
    ∑ c ∈ range (b + 1), (if counted6 i j k l b c = true then S6 x i j k l b c else 0) else 0)

/-- The dropped sums below the counted cell `(i, j, k, l)` of depth 4: the cell's `S4` as it is, or, when it is
decomposed one level further, its counted cells of depth 6. -/
noncomputable def dropS4 (x : ℝ) (i j k l : ℕ) : ℝ :=
  if counted4 i j k l = true then (if dec4 i j k l = true then dropS5 x i j k l else S4 x i j k l) else 0

/-- The dropped cells' sums below the cell `(i, j)`. -/
noncomputable def dropS (x : ℝ) (i j : ℕ) : ℝ :=
  (if cand i j = true ∧ dec i j = false then S2 x i j else 0) +
    (if cand i j = true ∧ dec i j = true then ∑ k ∈ range SieveCert.n,
      (if inKK i j k = true ∧ ne3 i j k = true then ∑ l ∈ range (k + 1), dropS4 x i j k l else 0) else 0)

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem dropS5_nonneg (x : ℝ) (i j k l : ℕ) : 0 ≤ dropS5 x i j k l := by
  unfold dropS5
  refine Finset.sum_nonneg fun b _ => ?_
  split_ifs
  · exact Finset.sum_nonneg fun c _ => by split_ifs <;> first | exact le_rfl | exact S6_nonneg _ _ _ _ _ _ _
  · exact le_rfl

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem dropS4_nonneg (x : ℝ) (i j k l : ℕ) : 0 ≤ dropS4 x i j k l := by
  unfold dropS4
  split_ifs <;> first | exact le_rfl | exact dropS5_nonneg _ _ _ _ _ | exact S4_nonneg _ _ _ _ _

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem dropS_nonneg (x : ℝ) (i j : ℕ) : 0 ≤ dropS x i j := by
  unfold dropS
  refine add_nonneg (by split_ifs <;> first | exact le_rfl | exact S2_nonneg _ _ _) ?_
  split_ifs
  · refine Finset.sum_nonneg fun k _ => ?_
    split_ifs
    · exact Finset.sum_nonneg fun l _ => dropS4_nonneg _ _ _ _ _
    · exact le_rfl
  · exact le_rfl

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The `B`-count of the dropped terms of depth 6 below a decomposed cell of depth 4. -/
theorem D5_le {q : ℕ} (hq : 1 ≤ q) (i j k l : ℕ) :
    (parQ q).D5 (gB q) i j k l ≤ (q.totient : ℝ)⁻¹ * dropS5 (xq q) i j k l := by
  unfold Par.D5 dropS5
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  split_ifs with hb
  · unfold Par.D6
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    split_ifs with hc
    · exact drop6_le hq i j k l b c
    · exact le_of_eq (mul_zero _).symm
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The `B`-count of the dropped terms of depth 4 below `(i, j, k)`. -/
theorem D4_le {q : ℕ} (hq : 1 ≤ q) (i j k : ℕ) (l : ℕ) :
    (if counted4 i j k l = true then
      (if dec4 i j k l = true then (parQ q).D5 (gB q) i j k l else (parQ q).I (gB q) ((parQ q).S4c i j k l))
        else 0) ≤ (q.totient : ℝ)⁻¹ * dropS4 (xq q) i j k l := by
  unfold dropS4
  split_ifs with h1 h2
  · exact D5_le hq i j k l
  · exact drop4_le hq i j k l
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [Fits] in
/-- **The dropped terms' `B`-count**, on a grid with `GridOK`, for `(parQ q).Good`, `z_top² ≤ 4N₁` and `q ≥ 1`: it is at
most `φ(q)⁻¹(Σ_{i,j} dropS + n²|cornerP|²)`. -/
theorem D1_le {q : ℕ} (G : (parQ q).Good) (hsq : (((parQ q).ztop : ℝ)) ^ 2 ≤ 4 * N1 q) (hq : 1 ≤ q) :
    (parQ q).D1 (gB q) ≤ (q.totient : ℝ)⁻¹ * (∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n,
      dropS (xq q) i j + (SieveCert.n : ℝ) ^ 2 * ((cornerP (parQ q).ztop).card : ℝ) ^ 2) := by
  set C := ((cornerP (parQ q).ztop).card : ℝ) ^ 2 with hC
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hC0 : 0 ≤ C := by positivity
  have hn2 : (SieveCert.n : ℝ) ^ 2 * C = ∑ _i ∈ range SieveCert.n, ∑ _j ∈ range SieveCert.n, C := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hn2, ← Finset.sum_add_distrib, Finset.mul_sum]
  unfold Par.D1
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hi' := Finset.mem_range.1 hi
  by_cases hW : Par.inW i
  · rw [ite_eq_left hW]
    exact Finset.sum_nonneg fun j _ => mul_nonneg hφ (add_nonneg (dropS_nonneg _ _ _) hC0)
  rw [ite_eq_right hW]
  unfold Par.D2
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  unfold dropS
  -- the cells of depth 2
  have hA : (if (cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ Par.sE2 i j = false) then
      (parQ q).I (gB q) ((parQ q).S2c i j) else 0) ≤
        (q.totient : ℝ)⁻¹ * ((if cand i j = true ∧ dec i j = false then S2 (xq q) i j else 0) + C) := by
    split_ifs with h1 h2
    · exact (drop2_le hq i j).trans (mul_le_mul_of_nonneg_left (by unfold S2; linarith) hφ)
    · rcases h1 with h1 | h1
      · exact absurd h1 h2
      · refine (corner_le G hsq hi' hW h1.1 h1.2).trans (mul_le_mul_of_nonneg_left (by linarith) hφ)
    · exact mul_nonneg hφ (add_nonneg (S2_nonneg _ _ _) hC0)
    · exact mul_nonneg hφ (by linarith)
  -- below the decomposed cells
  have hB : (if cand i j = true ∧ dec i j = true then (parQ q).D3 (gB q) i j else 0) ≤
      (q.totient : ℝ)⁻¹ * (if cand i j = true ∧ dec i j = true then ∑ k ∈ range SieveCert.n,
        (if inKK i j k = true ∧ ne3 i j k = true then ∑ l ∈ range (k + 1), dropS4 (xq q) i j k l else 0)
          else 0) := by
    split_ifs with hcd
    · unfold Par.D3
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      split_ifs with hk
      · unfold Par.D4
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun l _ => D4_le hq i j k l
      · exact le_of_eq (mul_zero _).symm
    · exact le_of_eq (mul_zero _).symm
  calc _ ≤ (q.totient : ℝ)⁻¹ * ((if cand i j = true ∧ dec i j = false then S2 (xq q) i j else 0) + C) +
        (q.totient : ℝ)⁻¹ * (if cand i j = true ∧ dec i j = true then ∑ k ∈ range SieveCert.n,
          (if inKK i j k = true ∧ ne3 i j k = true then ∑ l ∈ range (k + 1), dropS4 (xq q) i j k l else 0)
            else 0) :=
        add_le_add hA hB
    _ = _ := by ring

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A decomposed cell of depth 4: its dropped sums against its cost**, given the shares at `x`, for `δ' ≥ 0` and
`X ≥ 0`: `dropS5 ≤ (refcost5/K)X + δ' nC² X`. -/
theorem dropS5_le_cost {x δ' X : ℝ} (hδ' : 0 ≤ δ') (hX : 0 ≤ X) {i j k l : ℕ}
    (h6 : ∀ b < nC, ∀ c < nC, counted6 i j k l b c = true →
      S6 x i j k l b c ≤ ((bound6 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) (eC b) (eC c) : ℝ) / K +
        δ') * X) :
    dropS5 x i j k l ≤ (refcost5 i j k l : ℝ) / K * X + (nC : ℝ) * nC * (δ' * X) := by
  have hK : (0 : ℝ) < K := SieveCert.K_pos'
  have hδX : 0 ≤ δ' * X := mul_nonneg hδ' hX
  have hrc : (refcost5 i j k l : ℝ) / K * X = ∑ b ∈ range nC, (if inKK5 i j k l b = true ∧ ne5 i j k l b = true then
      ∑ c ∈ range (b + 1), (if counted6 i j k l b c = true then
        (bound6 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) (eC b) (eC c) : ℝ) / K * X else 0)
      else 0) := by
    rw [SieveCert.refcost5_eq]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Bool.and_eq_true]
    split_ifs
    · rw [Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> simp
    · simp
  have hcount : ∑ b ∈ range nC, ∑ _c ∈ range (b + 1), δ' * X ≤ (nC : ℝ) * nC * (δ' * X) := by
    calc ∑ b ∈ range nC, ∑ _c ∈ range (b + 1), δ' * X
        ≤ ∑ _b ∈ range nC, (nC : ℝ) * (δ' * X) := by
          refine Finset.sum_le_sum fun b hb => ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have : ((b + 1 : ℕ) : ℝ) ≤ nC := by exact_mod_cast Finset.mem_range.1 hb
          exact mul_le_mul_of_nonneg_right this hδX
      _ = (nC : ℝ) * nC * (δ' * X) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  rw [hrc]
  refine le_trans ?_ (add_le_add le_rfl hcount)
  unfold dropS5
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b hbm => ?_
  have hbn := Finset.mem_range.1 hbm
  split_ifs with hb
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c hcm => ?_
    have hcn : c < nC := by have := Finset.mem_range.1 hcm; omega
    split_ifs with hc
    · have := h6 b hbn c hcn hc
      linarith
    · linarith
  · have : 0 ≤ ∑ _c ∈ range (b + 1), δ' * X := Finset.sum_nonneg fun _ _ => hδX
    linarith

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A cell of depth 4: its dropped sums against its cost**: `dropS4 ≤ (cost4/K)X + δ'(1 + nC²)X`. -/
theorem dropS4_le_cost {x δ' X : ℝ} (hδ' : 0 ≤ δ') (hX : 0 ≤ X) {i j k l : ℕ}
    (h4 : counted4 i j k l = true →
      S4 x i j k l ≤ ((bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K + δ') * X)
    (h6 : ∀ b < nC, ∀ c < nC, counted6 i j k l b c = true →
      S6 x i j k l b c ≤ ((bound6 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) (eC b) (eC c) : ℝ) / K +
        δ') * X) :
    dropS4 x i j k l ≤ (cost4 i j k l : ℝ) / K * X + δ' * (1 + (nC : ℝ) * nC) * X := by
  have hδX : 0 ≤ δ' * X := mul_nonneg hδ' hX
  have hnn : 0 ≤ (nC : ℝ) * nC * (δ' * X) := by positivity
  have hE : δ' * (1 + (nC : ℝ) * nC) * X = δ' * X + (nC : ℝ) * nC * (δ' * X) := by ring
  unfold dropS4
  by_cases hc : counted4 i j k l = true
  · rw [ite_eq_left hc]
    by_cases hd : dec4 i j k l = true
    · rw [ite_eq_left hd, SieveCert.cost4_of_dec4 hc hd]
      have := dropS5_le_cost hδ' hX h6
      linarith
    · have hd' : dec4 i j k l = false := by simpa using hd
      rw [ite_eq_right hd, SieveCert.cost4_of_not_dec4 hc hd']
      have h4' := h4 hc
      have : ((bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K + δ') * X =
          (bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K * X + δ' * X := by ring
      linarith
  · have hc' : counted4 i j k l = false := by simpa using hc
    rw [ite_eq_right hc, SieveCert.cost4_of_not_counted4 hc']
    rw [Nat.cast_zero, zero_div, zero_mul, zero_add]
    positivity

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A cell's dropped sums against its cost**, given the shares at `x`, for `δ' ≥ 0` and `X ≥ 0`:
`dropS ≤ (cost/K)X + δ'(1 + n²(1 + nC²))X`. -/
theorem dropS_le_cost {x δ' X : ℝ} (hδ' : 0 ≤ δ') (hX : 0 ≤ X) {i j : ℕ}
    (h2 : cand i j = true → S2 x i j ≤ ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ') * X)
    (h4 : ∀ k < SieveCert.n, ∀ l < SieveCert.n, counted4 i j k l = true →
      S4 x i j k l ≤ ((bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K + δ') * X)
    (h6 : ∀ k < SieveCert.n, ∀ l < SieveCert.n, ∀ b < nC, ∀ c < nC, counted6 i j k l b c = true →
      S6 x i j k l b c ≤ ((bound6 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) (eC b) (eC c) : ℝ) / K +
        δ') * X) :
    dropS x i j ≤ (cost i j : ℝ) / K * X +
      δ' * (1 + (SieveCert.n : ℝ) * SieveCert.n * (1 + (nC : ℝ) * nC)) * X := by
  have hK : (0 : ℝ) < K := SieveCert.K_pos'
  have hn : (0 : ℝ) ≤ SieveCert.n := Nat.cast_nonneg _
  have hδX : 0 ≤ δ' * X := mul_nonneg hδ' hX
  set E4 : ℝ := δ' * (1 + (nC : ℝ) * nC) * X with hE4
  have hE40 : 0 ≤ E4 := by rw [hE4]; positivity
  have hEtot : δ' * (1 + (SieveCert.n : ℝ) * SieveCert.n * (1 + (nC : ℝ) * nC)) * X =
      δ' * X + (SieveCert.n : ℝ) * SieveCert.n * E4 := by rw [hE4]; ring
  unfold dropS
  by_cases hc : cand i j = true
  · by_cases hd : dec i j = true
    · rw [ite_eq_right (show ¬(cand i j = true ∧ dec i j = false) by simp [hd]), zero_add,
        ite_eq_left ⟨hc, hd⟩, SieveCert.cost_of_dec hc hd]
      have hrc : ((refcost i j : ℕ) : ℝ) / K * X = ∑ k ∈ range SieveCert.n,
          (if inKK i j k = true ∧ ne3 i j k = true then ∑ l ∈ range (k + 1),
            (cost4 i j k l : ℝ) / K * X else 0) := by
        rw [SieveCert.refcost_eq]
        push_cast
        rw [Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Bool.and_eq_true]
        split_ifs
        · rw [Finset.sum_div, Finset.sum_mul]
        · simp
      rw [hrc]
      have hcount : ∑ k ∈ range SieveCert.n, ∑ _l ∈ range (k + 1), E4 ≤ (SieveCert.n : ℝ) * SieveCert.n * E4 := by
        calc ∑ k ∈ range SieveCert.n, ∑ _l ∈ range (k + 1), E4
            ≤ ∑ _k ∈ range SieveCert.n, (SieveCert.n : ℝ) * E4 := by
              refine Finset.sum_le_sum fun k hk => ?_
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              have : ((k + 1 : ℕ) : ℝ) ≤ SieveCert.n := by exact_mod_cast Finset.mem_range.1 hk
              exact mul_le_mul_of_nonneg_right this hE40
          _ = (SieveCert.n : ℝ) * SieveCert.n * E4 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      have hmain : ∑ k ∈ range SieveCert.n, (if inKK i j k = true ∧ ne3 i j k = true then
            ∑ l ∈ range (k + 1), dropS4 x i j k l else 0) ≤
          ∑ k ∈ range SieveCert.n, (if inKK i j k = true ∧ ne3 i j k = true then ∑ l ∈ range (k + 1),
            (cost4 i j k l : ℝ) / K * X else 0) + ∑ k ∈ range SieveCert.n, ∑ _l ∈ range (k + 1), E4 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun k hkm => ?_
        have hkn := Finset.mem_range.1 hkm
        split_ifs with hk
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun l hlm => ?_
          have hln : l < SieveCert.n := by have := Finset.mem_range.1 hlm; omega
          have := dropS4_le_cost hδ' hX (h4 k hkn l hln) (h6 k hkn l hln)
          linarith [hE4]
        · have : 0 ≤ ∑ _l ∈ range (k + 1), E4 := Finset.sum_nonneg fun _ _ => hE40
          linarith
      have h0 : 0 ≤ δ' * X := hδX
      linarith [hmain, hcount, hEtot]
    · have hd' : dec i j = false := by simpa using hd
      rw [ite_eq_left ⟨hc, hd'⟩, ite_eq_right (show ¬(cand i j = true ∧ dec i j = true) from fun h => hd h.2),
        add_zero, SieveCert.cost_of_not_dec hc hd']
      have h2' := h2 hc
      have h4 : ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ') * X =
          (bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K * X + δ' * X := by ring
      have : 0 ≤ (SieveCert.n : ℝ) * SieveCert.n * E4 := by positivity
      linarith [hEtot]
  · have hc' : cand i j = false := by simpa using hc
    rw [ite_eq_right (show ¬(cand i j = true ∧ dec i j = false) from fun h => hc h.1),
      ite_eq_right (show ¬(cand i j = true ∧ dec i j = true) from fun h => hc h.1), add_zero]
    have hcost : cost i j = 0 := by simp [cost, hc']
    rw [hcost, Nat.cast_zero, zero_div, zero_mul, zero_add]
    positivity

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The certificate's total in the reals, with the loss as a parameter: if `total/K ≤ c` in the reals (`htot`), then for
`X ≥ 0`, `Σ_{i,j} (cost/K)X ≤ cX` (`sum_cost_div` is the case `c = 0.88`). -/
theorem sum_cost_div_of {c : ℝ} (htot : (total : ℝ) / K ≤ c) (X : ℝ) (hX : 0 ≤ X) :
    ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (cost i j : ℝ) / K * X ≤ c * X := by
  have hsum : ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (cost i j : ℝ) / K * X = (total : ℝ) / K * X := by
    rw [SieveCert.total_eq]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
  rw [hsum]
  exact mul_le_mul_of_nonneg_right htot hX

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The certificate's total in the reals: if `total ≤ 0.88K` (`htot`), then for `X ≥ 0`, `Σ_{i,j} (cost/K)X ≤ 0.88X`. -/
theorem sum_cost_div (htot : total ≤ 88 * K / 100) (X : ℝ) (hX : 0 ≤ X) :
    ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (cost i j : ℝ) / K * X ≤ 88 / 100 * X :=
  sum_cost_div_of (SieveCert.total_div_le htot) X hX

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- If `total < K` in the natural numbers, then `total/K < 1` in the reals. -/
theorem total_div_lt (htot : total < K) : (total : ℝ) / K < 1 := by
  rw [div_lt_one SieveCert.K_pos']
  exact_mod_cast htot

omit [Route] [RouteOK] [Fits] in
/-- **The shares, eventually**: on a grid with `GridOK` and `GridOKC`, for `δ' > 0` and large `x`, simultaneously, every
candidate cell's `S2`, every counted cell's `S4` and every counted cell of depth 6's `S6` are at most the certificate's
bound plus `δ'`, times `x/log x`. -/
theorem shares_ev [SieveCert.GridOKC] {δ' : ℝ} (hδ' : 0 < δ') : ∀ᶠ x : ℝ in atTop,
    ∀ i ∈ range SieveCert.n, ∀ j ∈ range SieveCert.n,
    (cand i j = true → S2 x i j ≤ ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ') * (x / Real.log x)) ∧
    ∀ k ∈ range SieveCert.n, ∀ l ∈ range SieveCert.n,
    (counted4 i j k l = true →
      S4 x i j k l ≤ ((bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K + δ') *
        (x / Real.log x)) ∧
    ∀ b ∈ range nC, ∀ c ∈ range nC, counted6 i j k l b c = true →
      S6 x i j k l b c ≤ ((bound6 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) (eC b) (eC c) : ℝ) /
        K + δ') * (x / Real.log x) := by
  rw [Filter.eventually_all_finset]
  intro i _
  rw [Filter.eventually_all_finset]
  intro j _
  refine Filter.Eventually.and ?_ ?_
  · by_cases hc : cand i j = true
    · filter_upwards [share2_of_cand hc hδ'] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hc
  · rw [Filter.eventually_all_finset]
    intro k _
    rw [Filter.eventually_all_finset]
    intro l _
    refine Filter.Eventually.and ?_ ?_
    · by_cases hc : counted4 i j k l = true
      · filter_upwards [share4_of_counted4 hc hδ'] with x hx _
        exact hx
      · exact Filter.Eventually.of_forall fun x h => absurd h hc
    · rw [Filter.eventually_all_finset]
      intro b _
      rw [Filter.eventually_all_finset]
      intro c _
      by_cases hc : counted6 i j k l b c = true
      · filter_upwards [share6_of_counted6 hc hδ'] with x hx _
        exact hx
      · exact Filter.Eventually.of_forall fun x h => absurd h hc

/-- **The dropped terms, for large `q`, with the loss as a parameter**: for a route with `RouteOK` and grids with
`GridOK` and `GridOKC` that fit (`Fits`), if `total/K ≤ c` in the reals (`htot`), then for `ε > 0`,
`D1(g_B) ≤ φ(q)⁻¹(c + ε)x/log x` (`drop_ev` is the case `c = 0.88`). -/
theorem drop_ev_of [SieveCert.GridOKC] {c : ℝ} (htot : (total : ℝ) / K ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, LargeQ q →
    (parQ q).D1 (gB q) ≤ (q.totient : ℝ)⁻¹ * ((c + ε) * (xq q / Real.log (xq q))) := by
  have hn : (0 : ℝ) < SieveCert.n := by exact_mod_cast SieveCert.n_pos
  set Mc : ℝ := 1 + (SieveCert.n : ℝ) * SieveCert.n * (1 + (nC : ℝ) * nC) with hMc
  set M : ℝ := (SieveCert.n : ℝ) * SieveCert.n * Mc with hM
  have hM0 : 0 < M := by positivity
  set δ' : ℝ := ε / (2 * M) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  filter_upwards [tendsto_xq.eventually (shares_ev hδ'0), corner_ev (half_pos hε), eventually_ge_atTop 1]
    with q hS hC hq1 hL
  have G := good_of_large hL
  set X := xq q / Real.log (xq q) with hX
  have hx1 : 1 < xq q := G.hx
  have hX0 : 0 ≤ X := div_nonneg (by linarith) (Real.log_nonneg hx1.le)
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hdrop : ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, dropS (xq q) i j ≤
      c * X + ε / 2 * X := by
    calc ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, dropS (xq q) i j
        ≤ ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n,
            ((cost i j : ℝ) / K * X + δ' * Mc * X) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          obtain ⟨h2, h46⟩ := hS i hi j hj
          exact dropS_le_cost hδ'0.le hX0 h2
            (fun k hk l hl hc => (h46 k (Finset.mem_range.2 hk) l (Finset.mem_range.2 hl)).1 hc)
            (fun k hk l hl b hb c hc' hc => (h46 k (Finset.mem_range.2 hk) l (Finset.mem_range.2 hl)).2 b
              (Finset.mem_range.2 hb) c (Finset.mem_range.2 hc') hc)
      _ = ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (cost i j : ℝ) / K * X +
            SieveCert.n * SieveCert.n * (δ' * Mc * X) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ c * X + ε / 2 * X := by
          have h1 := sum_cost_div_of htot X hX0
          have h2 : (SieveCert.n : ℝ) * SieveCert.n * (δ' * Mc * X) = ε / 2 * X := by
            rw [hδ']
            field_simp
            rw [hM]
            ring
          linarith
  calc (parQ q).D1 (gB q)
      ≤ (q.totient : ℝ)⁻¹ * (∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, dropS (xq q) i j +
          (SieveCert.n : ℝ) ^ 2 * ((cornerP (parQ q).ztop).card : ℝ) ^ 2) := D1_le G hC.1 hq1
    _ ≤ (q.totient : ℝ)⁻¹ * ((c * X + ε / 2 * X) + ε / 2 * X) :=
        mul_le_mul_of_nonneg_left (add_le_add hdrop hC.2) hφ
    _ = (q.totient : ℝ)⁻¹ * ((c + ε) * X) := by ring

/-- **The dropped terms, for large `q`**: for a route with `RouteOK` and grids with `GridOK` and `GridOKC` that fit
(`Fits`), if the certificate's total is at most `0.88K` (`htot`), then for `ε > 0`,
`D1(g_B) ≤ φ(q)⁻¹(0.88 + ε)x/log x`. -/
theorem drop_ev [SieveCert.GridOKC] (htot : total ≤ 88 * K / 100) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, LargeQ q →
    (parQ q).D1 (gB q) ≤ (q.totient : ℝ)⁻¹ * ((88 / 100 + ε) * (xq q / Real.log (xq q))) :=
  drop_ev_of (SieveCert.total_div_le htot) hε

end SieveDrop
