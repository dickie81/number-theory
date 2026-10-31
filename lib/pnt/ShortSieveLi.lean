import ShortSieveRel
import ShortSieveNode
import ShortSieveJ

/-!
# Li's Lemma 4.1 as a hypothesis, and the asymptotic formula for nodes from it

Li's Lemma 4.1 (arXiv:2308.04458v8; Baker, Harman and Pintz's Lemma 9) gives an asymptotic formula for sums over
`mnr ∈ A` with `m ~ M = x^{α₁}`, `n ~ N = x^{α₂}`, `|α₁ − α₂| < 2θ − 1`, `α₁ + α₂ > 1 − γ(θ)`, arbitrary bounded
coefficients on `m` and `n`, and a prime-factored rest `r`. The real-exponent Type II test does not reach it (two
variables near `x^{1/2}`), so it enters the proof as a hypothesis, `LiLemma41`, stated for products of primes in boxes
(the coefficients count the tuples of a group with a given product) with the comparison interval
`(x − x^{1−ρ}, x]`.

* `abs_count_sub_le_G2`: a node whose terms with product in `(x/4, 2x]` have their items grouped into `m`, `n` and
  the rest with the exponents in Lemma 4.1's region, with a margin, has the asymptotic formula: each pattern of its
  expansion into tuples of primes is a cut (`ShortSieveNode.count_eq_sum`), and a box of the cut that holds a term
  has its groups' exponents within `log 2/log x` of the term's (`ShortSieveRel.abs_card_cut_sub_le_rel`).
-/

open Finset Real Filter

namespace ShortSieveLi

open ShortSieveBoxes ShortSieveTerm ShortSieveExpand ShortSieveNode ShortSieveRel

open Classical

/-- The product of a group's coordinates. -/
noncomputable def grpProd {ι : Type*} [Fintype ι] (grp : ι → Fin 3) (i : Fin 3) (N : ι → ℕ) : ℕ :=
  ∏ j ∈ univ.filter (grp · = i), N j

/-- **Li's Lemma 4.1** (Baker, Harman and Pintz's Lemma 9) for products of primes in boxes, with the comparison
interval `(x − x^{1−ρ}, x]` (`γ = γ(θ)` of his Lemma 4.1, `γ(0.52) = 4θ − 2 = 0.08`). For primes
`x^c ≤ N_j < p_j ≤ M_j` grouped into `m` (group `0`), `n` (group `1`) and the rest (group `2`), each group's products
in a dyadic range, and the groups' lower ends `x^{α₁}`, `x^{α₂}` with `|α₁ − α₂| ≤ 2θ − 1 − η` and
`α₁ + α₂ ≥ 1 − γ + η`: the box's tuples with product in `(x − y, x]`, `x^θ ≤ y ≤ x^{1−ρ}`, number
`(y/x^{1−ρ})(1 + o(1))` times those with product in `(x − x^{1−ρ}, x]`, uniformly in the box. -/
def LiLemma41 (θ γ ρ : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (grp : ι → Fin 3) (c η ε : ℝ), 0 < c → 0 < η → 0 < ε →
    ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ N M : ι → ℕ,
      (∀ j, x ^ c ≤ N j) → (∀ j, N j ≤ M j) → (∀ i, grpProd grp i M ≤ 2 * grpProd grp i N) →
      |Real.log (grpProd grp 0 N) / Real.log x - Real.log (grpProd grp 1 N) / Real.log x| ≤ 2 * θ - 1 - η →
      1 - γ + η ≤ Real.log (grpProd grp 0 N) / Real.log x + Real.log (grpProd grp 1 N) / Real.log x →
      |(#{g ∈ ShortSieveTypeII.tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) * #{g ∈ ShortSieveTypeII.tuples N M | x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧
          ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
        ε * (y / x ^ (1 - ρ)) * #{g ∈ ShortSieveTypeII.tuples N M | x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧
          ((∏ j, g j : ℕ) : ℝ) ≤ x}

/-- Membership in the tuples of a box. -/
theorem mem_tuples {ι : Type*} [Fintype ι] [DecidableEq ι] {N M g : ι → ℕ} :
    g ∈ ShortSieveTypeII.tuples N M ↔ ∀ j, N j < g j ∧ g j ≤ M j ∧ (g j).Prime := by
  simp only [ShortSieveTypeII.tuples, Fintype.mem_piFinset, ShortSieveTypeII.box, mem_filter, mem_Ioc, and_assoc]

/-- The `log` of a group's product of items is `log x` times the group's exponent. -/
theorem log_grp_prod {k m G : ℕ} (grp : Fin k ⊕ Fin m → Fin G) {x : ℝ} (hx : 1 < x)
    {v : (Fin k → ℕ) × (Fin m → ℕ)} (hv1 : ∀ a, 0 < v.1 a) (hv2 : ∀ i, 0 < v.2 i) (g : Fin G) :
    Real.log ((∏ a ∈ univ.filter (fun a => grp (Sum.inl a) = g), (v.1 a : ℝ)) *
      ∏ j ∈ univ.filter (fun j => grp (Sum.inr j) = g), (v.2 j : ℝ)) = Real.log x * grpExp grp g (expo x v) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hP1 : 0 < ∏ a ∈ univ.filter (fun a => grp (Sum.inl a) = g), (v.1 a : ℝ) :=
    prod_pos fun a _ => by exact_mod_cast hv1 a
  have hP2 : 0 < ∏ j ∈ univ.filter (fun j => grp (Sum.inr j) = g), (v.2 j : ℝ) :=
    prod_pos fun j _ => by exact_mod_cast hv2 j
  rw [Real.log_mul hP1.ne' hP2.ne', Real.log_prod (fun a _ => by exact_mod_cast (hv1 a).ne'),
    Real.log_prod (fun j _ => by exact_mod_cast (hv2 j).ne'), grpExp, sum_filter, sum_filter, sum_filter,
    Fintype.sum_sum_type, mul_add, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun t _ => ?_
    simp only [expo, Sum.elim_inl]
    split_ifs
    · field_simp
    · simp
  · refine sum_congr rfl fun t _ => ?_
    simp only [expo, Sum.elim_inr]
    split_ifs
    · field_simp
    · simp

/-- The grouping of an expanded tuple: every prime of block `i` in the group of the rough item `i`. -/
def liftGrp {k m : ℕ} (len : Fin m → ℕ) (grp : Fin k ⊕ Fin m → Fin 3) : Idx k m len → Fin 3 :=
  Sum.elim (fun a => grp (Sum.inl a)) fun ij => grp (Sum.inr ij.1)


/-- A group's product over a box's lower corners is at least `1` when they are positive. -/
theorem one_le_grpProd {ι : Type*} [Fintype ι] (grp : ι → Fin 3) (i : Fin 3) {N : ι → ℕ} (hN : ∀ j, 1 ≤ N j) :
    1 ≤ grpProd grp i N :=
  Finset.one_le_prod fun j _ => hN j

/-- **A box that holds a term has its groups' exponents near the term's.** If `N_j < g_j ≤ M_j ≤ 2^{1/d} N_j`
(`d = #ι`), each group's product over `N` is within a factor `2` of the group's product over `g`. -/
theorem grpProd_le_prod_le {ι : Type*} [Fintype ι] (grp : ι → Fin 3) (i : Fin 3) {N M g : ι → ℕ}
    (hNg : ∀ j, N j ≤ g j) (hgM : ∀ j, g j ≤ M j)
    (hMN : ∀ j, (M j : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / Fintype.card ι) * N j) (hd : 0 < Fintype.card ι) :
    (grpProd grp i N : ℝ) ≤ ∏ j ∈ univ.filter (grp · = i), (g j : ℝ) ∧
      ∏ j ∈ univ.filter (grp · = i), (g j : ℝ) ≤ 2 * grpProd grp i N ∧
      (grpProd grp i M : ℝ) ≤ 2 * grpProd grp i N := by
  set d := Fintype.card ι with hd_def
  set r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / d) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow (by norm_num) (by positivity)
  have hrd : r ^ d = 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div_mul_cancel (by positivity),
      Real.rpow_one]
  set S := univ.filter (grp · = i) with hS
  have hpow : r ^ S.card ≤ 2 := by rw [← hrd]; exact pow_le_pow_right₀ hr1 (card_le_univ S)
  have hM : (grpProd grp i M : ℝ) ≤ 2 * grpProd grp i N := by
    unfold grpProd
    push_cast
    calc ∏ j ∈ S, (M j : ℝ) ≤ ∏ j ∈ S, (r * N j) := prod_le_prod₀ (fun j _ => by positivity) fun j _ => hMN j
      _ = r ^ S.card * ∏ j ∈ S, (N j : ℝ) := by rw [prod_mul_distrib, prod_const]
      _ ≤ 2 * ∏ j ∈ S, (N j : ℝ) := mul_le_mul_of_nonneg_right hpow (prod_nonneg fun j _ => by positivity)
  have h1 : (grpProd grp i N : ℝ) ≤ ∏ j ∈ S, (g j : ℝ) := by
    unfold grpProd
    push_cast
    exact prod_le_prod₀ (fun j _ => by positivity) fun j _ => by exact_mod_cast hNg j
  have h2 : ∏ j ∈ S, (g j : ℝ) ≤ grpProd grp i M := by
    unfold grpProd
    push_cast
    exact prod_le_prod₀ (fun j _ => by positivity) fun j _ => by exact_mod_cast hgM j
  exact ⟨h1, h2.trans hM, hM⟩

/-- **The asymptotic formula for a node from Li's Lemma 4.1.** Let `N` have `k ≥ 1` primes and `m ≥ 1` rough items,
conditions whose coefficients are not all equal, and for large `x` its terms' primes above `x^c` and rough items
above `1`. If for large `x` every term with product in `(x/4, 2x]` has its items grouped by `grp` into `m`, `n` and
the rest with exponents in Lemma 4.1's region with margin `η`, then there is `C` such that for `ε ∈ (0, 1]`, large `x`
and `x^θ ≤ y ≤ x^{1−ρ}`, the node's terms in `(x − y, x]` number `(y/x^{1−ρ})` times those in `(x − x^{1−ρ}, x]`, up
to `ε` relatively and `C y/log² x`. -/
theorem abs_count_sub_le_G2 (N : Node) (hk : 0 < N.k) (hm : 0 < N.m) {c θ γ ρ η : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hη : 0 < η) (hLi : LiLemma41 θ γ ρ)
    (hcond : ∀ C ∈ N.conds, ∃ u w : Fin N.k ⊕ Fin N.m, Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w)
    (hbig : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i)
    (grp : Fin N.k ⊕ Fin N.m → Fin 3)
    (hreg : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, x / 4 < (prodP v : ℝ) → (prodP v : ℝ) ≤ 2 * x →
      |grpExp grp 0 (expo x v) - grpExp grp 1 (expo x v)| ≤ 2 * θ - 1 - η ∧
        1 - γ + η ≤ grpExp grp 0 (expo x v) + grpExp grp 1 (expo x v)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(N.count x y : ℝ) - y / x ^ (1 - ρ) * N.count x (x ^ (1 - ρ))| ≤
        ε * (y / x ^ (1 - ρ)) * N.count x (x ^ (1 - ρ)) + C * y / Real.log x ^ 2 := by
  set P := Fintype.piFinset fun _ : Fin N.m => Icc 1 ⌊1 / c⌋₊ with hP
  have hpat : ∀ len ∈ P, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y →
      y ≤ x ^ (1 - ρ) →
      |(#{g ∈ cut c (N.atoms len) x | x - y < ((∏ t, g t : ℕ) : ℝ) ∧ ((∏ t, g t : ℕ) : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) * #{g ∈ cut c (N.atoms len) x | x - x ^ (1 - ρ) < ((∏ t, g t : ℕ) : ℝ) ∧
          ((∏ t, g t : ℕ) : ℝ) ≤ x}| ≤
        ε * (y / x ^ (1 - ρ)) * #{g ∈ cut c (N.atoms len) x | x - x ^ (1 - ρ) < ((∏ t, g t : ℕ) : ℝ) ∧
          ((∏ t, g t : ℕ) : ℝ) ≤ x} + C * y / Real.log x ^ 2 := by
    intro len hlen
    have hlen1 : ∀ i, 0 < len i := fun i => (mem_Icc.1 (Fintype.mem_piFinset.1 hlen i)).1
    have hd : 0 < Fintype.card (Idx N.k N.m len) := Fintype.card_pos_iff.2 ⟨Sum.inl ⟨0, hk⟩⟩
    refine abs_card_cut_sub_le_rel (Sum.inl ⟨0, hk⟩) hc hc1 hρ hρc (N.atoms len) (atoms_ne N hk hlen1 hcond)
      fun ε hε => ?_
    -- Li's Lemma 4.1 on the boxes, with half the margin
    have hev : ∀ᶠ x : ℝ in atTop, Real.log 2 / Real.log x ≤ η / 4 := by
      have h := Real.tendsto_log_atTop.eventually_ge_atTop (4 * Real.log 2 / η)
      filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
      have hlx : 0 < Real.log x := Real.log_pos hx1
      rw [div_le_iff₀ hlx]
      rw [div_le_iff₀ hη] at hx
      linarith
    filter_upwards [hLi (Idx N.k N.m len) (liftGrp len grp) (c / 2) (η / 2) ε (by positivity) (by positivity) hε,
      hreg, hev, eventually_ge_atTop (2 : ℝ)] with x hLx hregx hδ hx2
    intro y hy1 hy2 N' M' hN' hNM hMN ⟨g₀, hg₀, hlo, hhi, hg₀box⟩
    have hx1 : 1 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have hprodcast : ((∏ t, g₀ t : ℕ) : ℝ) = ∏ t, (g₀ t : ℝ) := by push_cast; rfl
    have hterm := contract_mem_terms N hk hm hlen1 hg₀ (by rw [hprodcast]; exact hhi)
    have hP' : (prodP (contract g₀) : ℝ) = ∏ t, (g₀ t : ℝ) := by rw [prodP_contract, hprodcast]
    obtain ⟨hr1, hr2⟩ := hregx _ hterm (by rw [hP']; exact hlo) (by rw [hP']; exact hhi)
    have hgp : ∀ t, (g₀ t).Prime := fun t => (mem_tuples.1 hg₀box t).2.2
    have hc1' : ∀ a, 0 < (contract g₀).1 a := fun a => (hgp _).pos
    have hc2' : ∀ i, 0 < (contract g₀).2 i := fun i => by
      show 0 < ∏ j, block g₀ i j
      exact prod_pos fun j _ => (hgp _).pos
    have hN1 : ∀ j, 1 ≤ N' j := fun j => by
      have : (1 : ℝ) ≤ N' j := le_trans (Real.one_le_rpow hx1.le (by positivity)) (hN' j)
      exact_mod_cast this
    -- each group's exponent over the box's lower corners is within `log 2/log x` of the term's
    have hgrp : ∀ i : Fin 3, grpExp grp i (expo x (contract g₀)) - η / 4 ≤
        Real.log (grpProd (liftGrp len grp) i N') / Real.log x ∧
        Real.log (grpProd (liftGrp len grp) i N') / Real.log x ≤ grpExp grp i (expo x (contract g₀)) := by
      intro i
      obtain ⟨hb1, hb2, -⟩ := grpProd_le_prod_le (liftGrp len grp) i (fun j => (mem_tuples.1 hg₀box j).1.le)
        (fun j => (mem_tuples.1 hg₀box j).2.1) hMN hd
      have hpg := prod_group grp g₀ i
      have hlog := log_grp_prod grp hx1 hc1' hc2' i
      have hpos : (0 : ℝ) < grpProd (liftGrp len grp) i N' := by
        exact_mod_cast lt_of_lt_of_le one_pos (one_le_grpProd _ i hN1)
      set Q := ∏ t ∈ univ.filter (liftGrp len grp · = i), (g₀ t : ℝ) with hQ
      have hQe : Real.log Q = Real.log x * grpExp grp i (expo x (contract g₀)) := by
        rw [← hlog, ← hpg]
        rfl
      have hQ0 : 0 < Q := lt_of_lt_of_le hpos hb1
      have hl1 : Real.log (grpProd (liftGrp len grp) i N') ≤ Real.log Q := Real.log_le_log hpos hb1
      have hl2 : Real.log Q ≤ Real.log 2 + Real.log (grpProd (liftGrp len grp) i N') := by
        rw [← Real.log_mul (by norm_num) hpos.ne']
        exact Real.log_le_log hQ0 hb2
      constructor
      · rw [le_div_iff₀ hlx]
        rw [div_le_iff₀ hlx] at hδ
        nlinarith
      · rw [div_le_iff₀ hlx]
        nlinarith
    obtain ⟨h0a, h0b⟩ := hgrp 0
    obtain ⟨h1a, h1b⟩ := hgrp 1
    refine hLx y hy1 hy2 N' M' (fun j => ?_) hNM (fun i => ?_) ?_ ?_
    · exact hN' j
    · obtain ⟨-, -, hb3⟩ := grpProd_le_prod_le (liftGrp len grp) i (fun j => (mem_tuples.1 hg₀box j).1.le)
        (fun j => (mem_tuples.1 hg₀box j).2.1) hMN hd
      exact_mod_cast hb3
    · rw [abs_le] at hr1 ⊢
      constructor <;> linarith [hr1.1, hr1.2]
    · linarith
  choose! Cf hCf using hpat
  refine ⟨∑ len ∈ P, Cf len, fun ε hε hε1 => ?_⟩
  filter_upwards [count_eq_sum N hc hbig, (eventually_all_finset P).2 fun len hlen => hCf len hlen ε hε hε1]
    with x hsum hall y hy1 hy2
  rw [hsum y, hsum (x ^ (1 - ρ)), mul_sum, mul_sum, ← sum_sub_distrib, sum_mul, sum_div, ← sum_add_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun len hlen => hall len hlen y hy1 hy2)


/-- **A node's terms in the comparison interval number `O(x^{1−ρ}/log x)`**, for `0 < c < 1` and `12ρ < c`, when
its terms' primes exceed `x^c` and its rough items `1`: each pattern of its expansion is a set of tuples of primes in
`(x^c, x²)` (`ShortSieveRel.card_tuples_B_le`). -/
theorem count_B_le (N : Node) {c ρ : ℝ} (hc : 0 < c) (hc1 : c < 1) (hρ : 0 < ρ) (hρc : 12 * ρ < c)
    (hbig : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in atTop, (N.count x (x ^ (1 - ρ)) : ℝ) ≤ C * x ^ (1 - ρ) / Real.log x := by
  set P := Fintype.piFinset fun _ : Fin N.m => Icc 1 ⌊1 / c⌋₊ with hP
  have hpat : ∀ len ∈ P, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in atTop,
      (#((Fintype.piFinset fun _ : Idx N.k N.m len => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime).filter
        fun g => x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) : ℝ) ≤
        C * x ^ (1 - ρ) / Real.log x := fun len _ => card_tuples_B_le _ hc hc1 hρ hρc
  choose! Cf hCf0 hCf using hpat
  refine ⟨∑ len ∈ P, Cf len, sum_nonneg fun len hlen => hCf0 len hlen, ?_⟩
  filter_upwards [count_eq_sum N hc hbig, (eventually_all_finset P).2 hCf] with x hsum hall
  rw [hsum, sum_mul, sum_div]
  refine sum_le_sum fun len hlen => le_trans ?_ (hall len hlen)
  refine Nat.cast_le.2 (card_le_card fun g hg => ?_)
  obtain ⟨hgc, hB⟩ := mem_filter.1 hg
  exact mem_filter.2 ⟨(mem_filter.1 hgc).1, hB⟩

/-- **The asymptotic formula for a node from Li's Lemma 4.1, with error `ε y/log x`**: `abs_count_sub_le_G2` with
the node's count in the comparison interval bounded by `count_B_le`. -/
theorem abs_count_sub_le_G2_eps (N : Node) (hk : 0 < N.k) (hm : 0 < N.m) {c θ γ ρ η : ℝ} (hc : 0 < c)
    (hc1 : c < 1) (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hη : 0 < η) (hLi : LiLemma41 θ γ ρ)
    (hcond : ∀ C ∈ N.conds, ∃ u w : Fin N.k ⊕ Fin N.m, Sum.elim C.e C.f u ≠ Sum.elim C.e C.f w)
    (hbig : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, (∀ a, x ^ c < v.1 a) ∧ ∀ i, 1 < v.2 i)
    (grp : Fin N.k ⊕ Fin N.m → Fin 3)
    (hreg : ∀ᶠ x in atTop, ∀ v ∈ N.terms x, x / 4 < (prodP v : ℝ) → (prodP v : ℝ) ≤ 2 * x →
      |grpExp grp 0 (expo x v) - grpExp grp 1 (expo x v)| ≤ 2 * θ - 1 - η ∧
        1 - γ + η ≤ grpExp grp 0 (expo x v) + grpExp grp 1 (expo x v)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(N.count x y : ℝ) - y / x ^ (1 - ρ) * N.count x (x ^ (1 - ρ))| ≤ ε * y / Real.log x := by
  intro ε hε
  obtain ⟨C, hC⟩ := abs_count_sub_le_G2 N hk hm hc hc1.le hρ hρc hη hLi hcond hbig grp hreg
  obtain ⟨CB, hCB0, hCB⟩ := count_B_le N hc hc1 hρ hρc hbig
  set ε' : ℝ := min 1 (ε / (2 * (CB + 1))) with hε'
  have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
  have hev : ∀ᶠ x : ℝ in atTop, |C| ≤ ε / 2 * Real.log x :=
    (Real.tendsto_log_atTop.const_mul_atTop (by positivity : 0 < ε / 2)).eventually_ge_atTop _
  filter_upwards [hC ε' hε'0 (min_le_left _ _), hCB, hev, eventually_gt_atTop (1 : ℝ)] with x hx hxB hxl hx1
  intro y hy1 hy2
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 θ) hy1
  have hy₁ : 0 < x ^ (1 - ρ) := Real.rpow_pos_of_pos hx0 _
  have h1 : ε' * (y / x ^ (1 - ρ)) * N.count x (x ^ (1 - ρ)) ≤ ε / 2 * y / Real.log x := by
    have hle : ε' * (CB + 1) ≤ ε / 2 := by
      have := min_le_right 1 (ε / (2 * (CB + 1)))
      calc ε' * (CB + 1) ≤ ε / (2 * (CB + 1)) * (CB + 1) := by gcongr
        _ = ε / 2 := by field_simp
    calc ε' * (y / x ^ (1 - ρ)) * N.count x (x ^ (1 - ρ))
        ≤ ε' * (y / x ^ (1 - ρ)) * (CB * x ^ (1 - ρ) / Real.log x) := by gcongr
      _ = ε' * CB * y / Real.log x := by field_simp
      _ ≤ ε' * (CB + 1) * y / Real.log x := by gcongr; linarith
      _ ≤ ε / 2 * y / Real.log x := by gcongr
  have h2 : C * y / Real.log x ^ 2 ≤ ε / 2 * y / Real.log x := by
    rw [div_le_div_iff₀ (by positivity) hlx]
    have h3 : C ≤ ε / 2 * Real.log x := le_trans (le_abs_self C) hxl
    calc C * y * Real.log x = C * (y * Real.log x) := by ring
      _ ≤ ε / 2 * Real.log x * (y * Real.log x) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ε / 2 * y * Real.log x ^ 2 := by ring
  calc _ ≤ _ := hx y hy1 hy2
    _ ≤ ε / 2 * y / Real.log x + ε / 2 * y / Real.log x := add_le_add h1 h2
    _ = ε * y / Real.log x := by ring


/-! ### Li's Lemmas 3.1 and 3.2 -/

/-- Li's level `ν(α) = min(2(θ − α)/(2h − 1), γ)` for `α ∈ I_h = [1/2 − 2h(θ − 1/2), 1/2 − (2h − 2)(θ − 1/2)]`,
`h ≥ 1` (his (3) and (4)), with `h = ⌊(1/2 − α)/(2θ − 1)⌋ + 1`: at an endpoint shared by `I_h` and `I_{h+1}` this
takes `I_{h+1}`, the smaller value `2θ − 1`. -/
noncomputable def liNu (θ γ α : ℝ) : ℝ :=
  min (2 * (θ - α) / (2 * ((⌊(1 / 2 - α) / (2 * θ - 1)⌋₊ : ℝ) + 1) - 1)) γ

/-- The `S(A_{∏g}, x^ν)` of a box's tuples, summed: Li's Type I sums. -/
noncomputable def typeISum {ι : Type*} [Fintype ι] [DecidableEq ι] (ν x y : ℝ) (N M : ι → ℕ) : ℝ :=
  ∑ g ∈ ShortSieveTypeII.tuples N M, (ShortSieveJ.sA ν x y g : ℝ)

/-- **Li's Lemma 3.1** (Baker, Harman and Pintz's Lemma 12) for products of primes in boxes, with the comparison
interval `(x − x^{1−ρ}, x]` and `α*` replaced by its upper bound `1/2` (his `D′₀`). For primes `x^c ≤ N_j < p_j ≤ M_j`
grouped into `m` (group `0`) and `n` (group `1`), each group's products in a dyadic range, with lower ends `x^{α₁}`,
`x^{α₂}`, `α₁ ≤ 1/2` and `α₂ ≤ min((3θ − 1)/2, (1 + θ)/5) − η`, and `0 < ν ≤ ν(α₁)`: the box's sums of
`S(A_{mn}, x^ν)`, `A = (x − y, x]`, `x^θ ≤ y ≤ x^{1−ρ}`, are `(y/x^{1−ρ})(1 + o(1))` times those of
`S(B_{mn}, x^ν)`, uniformly in the box and `ν`. -/
def LiLemma31 (θ γ ρ : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (role : ι → Fin 3) (c η ε : ℝ), 0 < c → 0 < η → 0 < ε →
    ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ ν : ℝ, ∀ N M : ι → ℕ,
      (∀ j, role j ≠ 2) → (∀ j, x ^ c ≤ N j) → (∀ j, N j ≤ M j) →
      (∀ i, grpProd role i M ≤ 2 * grpProd role i N) →
      Real.log (grpProd role 0 N) / Real.log x ≤ 1 / 2 →
      Real.log (grpProd role 1 N) / Real.log x ≤ min ((3 * θ - 1) / 2) ((1 + θ) / 5) - η →
      0 < ν → ν ≤ liNu θ γ (Real.log (grpProd role 0 N) / Real.log x) →
      |typeISum ν x y N M - y / x ^ (1 - ρ) * typeISum ν x (x ^ (1 - ρ)) N M| ≤
        ε * (y / x ^ (1 - ρ)) * typeISum ν x (x ^ (1 - ρ)) N M

/-- **Li's Lemma 3.2** (Baker, Harman and Pintz's Lemma 13) for products of primes in boxes, with the comparison
interval `(x − x^{1−ρ}, x]` and `α*` replaced by `1/2` (his `D′₁ ∪ D′₂`). For primes grouped into `m`, `n₁`, `n₂`
(groups `0`, `1`, `2`) with lower ends `x^{α₁}`, `x^{α₂}`, `x^{α₃}`, `α₁ ≤ 1/2`, and either
`α₃ ≤ (3θ − 1)/4 − η`, `2α₂ + α₃ ≤ θ − η`, `2α₂ + 3α₃ ≤ (1 + θ)/2 − η`, or `α₂ ≤ (1 − θ)/2`,
`α₃ ≤ (3θ − 1)/8 − η`, and `0 < ν ≤ ν(α₁)`: the box's sums of `S(A_{mn₁n₂}, x^ν)` are `(y/x^{1−ρ})(1 + o(1))` times
those of `S(B_{mn₁n₂}, x^ν)`, uniformly. -/
def LiLemma32 (θ γ ρ : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (role : ι → Fin 3) (c η ε : ℝ), 0 < c → 0 < η → 0 < ε →
    ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ ν : ℝ, ∀ N M : ι → ℕ,
      (∀ j, x ^ c ≤ N j) → (∀ j, N j ≤ M j) → (∀ i, grpProd role i M ≤ 2 * grpProd role i N) →
      Real.log (grpProd role 0 N) / Real.log x ≤ 1 / 2 →
      ((Real.log (grpProd role 2 N) / Real.log x ≤ (3 * θ - 1) / 4 - η ∧
          2 * (Real.log (grpProd role 1 N) / Real.log x) + Real.log (grpProd role 2 N) / Real.log x ≤ θ - η ∧
          2 * (Real.log (grpProd role 1 N) / Real.log x) + 3 * (Real.log (grpProd role 2 N) / Real.log x) ≤
            (1 + θ) / 2 - η) ∨
        (Real.log (grpProd role 1 N) / Real.log x ≤ (1 - θ) / 2 ∧
          Real.log (grpProd role 2 N) / Real.log x ≤ (3 * θ - 1) / 8 - η)) →
      0 < ν → ν ≤ liNu θ γ (Real.log (grpProd role 0 N) / Real.log x) →
      |typeISum ν x y N M - y / x ^ (1 - ρ) * typeISum ν x (x ^ (1 - ρ)) N M| ≤
        ε * (y / x ^ (1 - ρ)) * typeISum ν x (x ^ (1 - ρ)) N M

end ShortSieveLi

#print axioms ShortSieveLi.log_grp_prod
#print axioms ShortSieveLi.abs_count_sub_le_G2
#print axioms ShortSieveLi.count_B_le
#print axioms ShortSieveLi.abs_count_sub_le_G2_eps
