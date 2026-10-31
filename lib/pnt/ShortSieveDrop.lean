import ShortSieveBuch
import ShortSieveLong
import SieveBox

/-!
# Upper bounds for the certificate's dropped nodes in the comparison interval

A node that the certificate drops enters Li's identity with a plus sign, so only an upper bound for its count in the
comparison interval `B = (x − x^{1−ρ}, x]` is needed, of the form `(bound + δ)·x^{1−ρ}/log x`, with the certificate's
cell bound: `ω*` at most `Ω` on the cell, times the weights of the cell's coordinates.

* `count_le_sum_cof`: the rough cofactor `ρ_c` of a node's terms is counted by `Ψ` in a short interval
  (`ShortSieveLong.psi_le`). Suppose every term has its cofactor's sifting prime at least `x^{lo}`, the cofactor at
  least that prime and `ω*` at most `Ω` at the term. Then the count is at most `(Ω + ε)·x^{1−ρ}` times the sum of
  `1/(P log p_{s(c)})` over a set containing the terms' other items (`outer`), where `P` is their product.
* `evLe_box`: on a box of primes `x^{lo_j} ≤ p_j < x^{hi_j}`, the sum of `∏_j 1/p_j`, with `log x/(p_j log p_j)` in
  place of `1/p_j` for `j ∈ E`, is at most the product of `log hi_j − log lo_j`, with `1/lo_j − 1/hi_j` for `j ∈ E`,
  plus `o(1)` (`SieveRough.evLe_sum_inv`, `evLe_sum_inv_log`).
* `count_le_drop1`: a node with one rough item, its cofactor: the count is at most `(ΩP + δ)·x^{1−ρ}/log x` when
  `P` bounds the `limsup` of `Σ log x/(∏p · log p_{s(0)})` over the node's prime tuples.
* `sum_inv_rough_le`: the reciprocals of the integers of `[Ylo, Yhi]` free of primes below `z` sum to at most
  `(Ω + ε)((1 + η) log(Yhi/Ylo) + 2η)/log z`, by `ShortSieveLong.psi_le` on the pieces `(Ylo λ^{i−1}, Ylo λ^i]`,
  `λ = 1 + η`.
* `count_le_drop2`: a node with two rough items, as in the role reversals: the cofactor, and an item `γ` whose size
  is fixed by a coordinate `log((∏_{j ∈ J} p_j)·γ)/log x ∈ [lo₀, hi₀]`. The count is at most
  `(Ωc Ωg (hi₀ − lo₀) P + δ)·x^{1−ρ}/log x`, with `P` bounding `Σ (log x)²/(∏p · log p_{s(c)} · log p_{s(g)})`.
-/

open Finset Real Filter

namespace ShortSieveDrop

open ShortSieveNode ShortSieveExpand ShortSieveBuch

open Classical

/-! ### The cofactor -/

/-- The other items of a pair: the cofactor `ρ_c` replaced by `1`. -/
def outer {k m : ℕ} (c : Fin m) (v : (Fin k → ℕ) × (Fin m → ℕ)) : (Fin k → ℕ) × (Fin m → ℕ) :=
  (v.1, Function.update v.2 c 1)

theorem prodP_outer {k m : ℕ} (c : Fin m) (v : (Fin k → ℕ) × (Fin m → ℕ)) :
    prodP (outer c v) * v.2 c = prodP v := by
  unfold prodP outer
  dsimp only
  rw [mul_assoc, Finset.prod_update_of_mem (mem_univ c), one_mul,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ c) v.2, mul_comm (v.2 c)]

/-- A rough number in the sense of `SieveTree.rough` has all its prime factors at least `z`. -/
theorem le_of_mem_primeFactors {z n : ℕ} (h : SieveTree.rough z n) {p : ℕ} (hp : p ∈ n.primeFactors) : z ≤ p := by
  by_contra hlt
  exact h p (not_le.1 hlt) (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- **One fiber of the cofactor.** The terms of a node in `(x − y, x]` whose other items are `w` number at most
`Ψ(x/P, y/P; p_{s(c)})`, `P` the product of `w`: their cofactors are distinct rough numbers in `((x − y)/P, x/P]`. -/
theorem card_fiber_le (N : Node) (c : Fin N.m) {x y : ℝ} (hyx : y ≤ x)
    (S : Finset ((Fin N.k → ℕ) × (Fin N.m → ℕ)))
    (hS : ∀ v ∈ S, v ∈ pairs N.k N.m ⌊x⌋₊ ∧ (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) ∧ N.InI x y v.1 v.2)
    (w : (Fin N.k → ℕ) × (Fin N.m → ℕ)) :
    #{v ∈ S | outer c v = w} ≤ ShortSieveLong.Psi (x / prodP w) (y / prodP w) (w.1 (N.s c)) := by
  unfold ShortSieveLong.Psi ShortSieveLong.roughSet
  refine card_le_card_of_injOn (fun v => v.2 c) (fun v hv => ?_) (fun v hv v' hv' he => ?_)
  · rw [mem_coe, mem_filter] at hv
    obtain ⟨hvS, hvw⟩ := hv
    obtain ⟨-, hr, hI⟩ := hS v hvS
    obtain ⟨-, hlo, hhi⟩ := hI
    have hP := prodP_outer c v
    rw [hvw] at hP
    have hv0 : (0 : ℝ) < prodP v := lt_of_le_of_lt (by linarith) hlo
    have hw0 : (0 : ℝ) < prodP w := by
      rcases Nat.eq_zero_or_pos (prodP w) with h | h
      · rw [← hP, h, zero_mul, Nat.cast_zero] at hv0; exact absurd hv0 (lt_irrefl 0)
      · exact_mod_cast h
    have hPc : (prodP v : ℝ) = prodP w * v.2 c := by rw [← hP]; push_cast; ring
    rw [mem_coe, mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, fun p hp => ?_⟩
    · have h1 : x / prodP w - y / prodP w < v.2 c := by
        rw [← sub_div, div_lt_iff₀ hw0]; rw [hPc] at hlo; linarith
      have h2 : (⌊x / prodP w - y / prodP w⌋₊ : ℝ) < v.2 c :=
        lt_of_le_of_lt (Nat.floor_le (by rw [← sub_div]; exact div_nonneg (by linarith) hw0.le)) h1
      exact_mod_cast h2
    · apply Nat.le_floor
      rw [le_div_iff₀ hw0]; rw [hPc] at hhi; linarith
    · rw [← hvw]
      exact le_of_mem_primeFactors (hr c) hp
  · rw [mem_coe, mem_filter] at hv hv'
    have h1 := hv.2
    have h2 := hv'.2
    unfold outer at h1 h2
    rw [← h2, Prod.mk.injEq] at h1
    obtain ⟨e1, e2⟩ := h1
    refine Prod.ext e1 (funext fun i => ?_)
    by_cases hi : i = c
    · subst hi; exact he
    · have := congrFun e2 i
      simpa [Function.update_of_ne hi] using this

/-- **The cofactor's count.** Let `0 < lo`, `0 < ρ` with `12ρ < lo`, `0 ≤ Ω` and `ε > 0`. Suppose that, for large
`x`, every term `v` of the node in `(x − x^{1−ρ}, x]` has its other items `outer c v` in `Out x`, its cofactor's
sifting prime `p = v.1 (s c)` at least `x^{lo}`, the cofactor at least `p`, and `ω*(log(x/P)/log p) ≤ Ω`, with `P`
the product of the other items. Then for large `x` the count is at most
`(Ω + ε)·x^{1−ρ}·Σ_{w ∈ Out x} 1/(P(w) log p(w))`. -/
theorem count_le_sum_cof (N : Node) (c : Fin N.m) {lo ρ Ω ε : ℝ} (hlo : 0 < lo) (hρ : 0 < ρ)
    (hρlo : 12 * ρ < lo) (hΩ : 0 ≤ Ω) (hε : 0 < ε)
    (Out : ℝ → Finset ((Fin N.k → ℕ) × (Fin N.m → ℕ)))
    (hterm : ∀ᶠ x : ℝ in atTop, ∀ v ∈ pairs N.k N.m ⌊x⌋₊, (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) →
      N.InI x (x ^ (1 - ρ)) v.1 v.2 → outer c v ∈ Out x ∧ x ^ lo ≤ v.1 (N.s c) ∧ (v.1 (N.s c) : ℝ) ≤ v.2 c ∧
        SieveCert.omegaC (Real.log (x / prodP (outer c v)) / Real.log (v.1 (N.s c))) ≤ Ω) :
    ∀ᶠ x : ℝ in atTop, (N.count x (x ^ (1 - ρ)) : ℝ) ≤
      (Ω + ε) * x ^ (1 - ρ) * ∑ w ∈ Out x, 1 / ((prodP w : ℝ) * Real.log (w.1 (N.s c))) := by
  set σ : ℝ := ρ / lo with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hρ.le hlo.le
  have hσ12 : σ < 1 / 12 := by rw [hσ, div_lt_iff₀ hlo]; linarith
  obtain ⟨z₀, hz₀⟩ := ShortSieveLong.psi_le hσ0 hσ12 (1 / lo) hε
  have hxρ : ∀ᶠ x : ℝ in atTop, x ^ (-ρ) ≤ 1 / 2 :=
    (tendsto_rpow_neg_atTop hρ).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hterm, eventually_ge_atTop 1, hxρ,
    (tendsto_rpow_atTop hlo).eventually_ge_atTop ((max z₀ 2 : ℕ) : ℝ)] with x hx hx1 hxρ hxz
  have hx0 : 0 < x := by linarith
  have hy : x ^ (1 - ρ) = x ^ (-ρ) * x := by rw [sub_eq_add_neg, add_comm, Real.rpow_add hx0, Real.rpow_one]
  have hxρ0 : 0 ≤ x ^ (-ρ) := Real.rpow_nonneg hx0.le _
  have hyx : x ^ (1 - ρ) ≤ x := by rw [hy]; nlinarith
  unfold Node.count
  set S := {v ∈ pairs N.k N.m ⌊x⌋₊ | (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) ∧
    N.InI x (x ^ (1 - ρ)) v.1 v.2} with hSdef
  have hS : ∀ v ∈ S, v ∈ pairs N.k N.m ⌊x⌋₊ ∧ (∀ i, SieveTree.rough (v.1 (N.s i)) (v.2 i)) ∧
      N.InI x (x ^ (1 - ρ)) v.1 v.2 := fun v hv => by
    rw [hSdef, mem_filter_inst] at hv
    exact ⟨hv.1, hv.2.1, hv.2.2⟩
  have hmaps : (S : Set ((Fin N.k → ℕ) × (Fin N.m → ℕ))).MapsTo (outer c) (Out x) := fun v hv =>
    (hx v (hS v hv).1 (hS v hv).2.1 (hS v hv).2.2).1
  rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum, mul_sum]
  refine sum_le_sum fun w _ => ?_
  have hnn : 0 ≤ (Ω + ε) * x ^ (1 - ρ) * (1 / ((prodP w : ℝ) * Real.log (w.1 (N.s c)))) :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _))
      (div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)))
  rcases Finset.eq_empty_or_nonempty {v ∈ S | outer c v = w} with he | ⟨v, hv⟩
  · rw [he, card_empty, Nat.cast_zero]; exact hnn
  have hvw := (mem_filter.1 hv).2
  obtain ⟨hvp, hvr, hvI⟩ := hS v (mem_filter.1 hv).1
  obtain ⟨-, hzlo, hzc, hω⟩ := hx v hvp hvr hvI
  rw [hvw] at hω
  have hw1 : w.1 = v.1 := by rw [← hvw]; rfl
  rw [← hw1] at hzlo hzc hω
  set z := w.1 (N.s c) with hz
  have hP := prodP_outer c v
  rw [hvw] at hP
  have hz2 : (2 : ℝ) ≤ z := le_trans (by exact_mod_cast le_max_right z₀ 2) (le_trans hxz hzlo)
  have hz0 : (0 : ℝ) < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hvx : (prodP v : ℝ) ≤ x := hvI.2.2
  have hcpos : (1 : ℝ) ≤ v.2 c := by linarith
  have hw0 : (0 : ℝ) < prodP w := by
    rcases Nat.eq_zero_or_pos (prodP w) with h | h
    · have : (prodP v : ℝ) = 0 := by rw [← hP, h, zero_mul, Nat.cast_zero]
      linarith [hvI.2.1]
    · exact_mod_cast h
  have hw1' : (1 : ℝ) ≤ prodP w := by
    have : 1 ≤ prodP w := by exact_mod_cast hw0
    exact_mod_cast this
  have hPc : (prodP v : ℝ) = prodP w * v.2 c := by rw [← hP]; push_cast; ring
  have hX2 : 2 ≤ x / prodP w := by
    rw [le_div_iff₀ hw0]
    nlinarith
  have hcard := card_fiber_le N c hyx S hS w
  have hzz : z₀ ≤ z := by
    have h1 : ((max z₀ 2 : ℕ) : ℝ) ≤ z := le_trans hxz hzlo
    have h2 : max z₀ 2 ≤ z := by exact_mod_cast h1
    exact le_trans (le_max_left _ _) h2
  -- `z^{−σ} ≤ x^{−ρ}`
  have hlzx : lo * Real.log x ≤ Real.log z := by
    rw [← Real.log_rpow hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hzlo
  have hzσ : (z : ℝ) ^ (-σ) ≤ x ^ (-ρ) := by
    rw [Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.2
    have : σ * (lo * Real.log x) = ρ * Real.log x := by rw [hσ]; field_simp
    nlinarith
  have hψ := hz₀ z hzz (x / prodP w) (x ^ (1 - ρ) / prodP w) hX2
    (by rw [hy, mul_div_assoc]; exact mul_le_mul_of_nonneg_right hzσ (div_nonneg hx0.le hw0.le))
    (by rw [hy, mul_div_assoc]; nlinarith [div_nonneg hx0.le hw0.le])
    (by
      have h1 : Real.log (x / prodP w) ≤ Real.log x :=
        Real.log_le_log (div_pos hx0 hw0) (div_le_self hx0.le hw1')
      have h2 : Real.log x ≤ 1 / lo * Real.log z := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlo]; linarith
      linarith)
  calc (#{v ∈ S | outer c v = w} : ℝ) ≤ ShortSieveLong.Psi (x / prodP w) (x ^ (1 - ρ) / prodP w) z := by
        exact_mod_cast hcard
    _ ≤ (SieveCert.omegaC (Real.log (x / prodP w) / Real.log z) + ε) * (x ^ (1 - ρ) / prodP w) /
        Real.log z := hψ
    _ ≤ (Ω + ε) * (x ^ (1 - ρ) / prodP w) / Real.log z := by
        apply div_le_div_of_nonneg_right _ hlz.le
        exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (Real.rpow_nonneg hx0.le _) hw0.le)
    _ = (Ω + ε) * x ^ (1 - ρ) * (1 / ((prodP w : ℝ) * Real.log z)) := by
        field_simp

/-! ### The primes of a box -/

/-- **The prime sums of a box.** On the box `x^{lo_j} ≤ p_j < x^{hi_j}` (`0 < lo_j ≤ hi_j`), the sum of
`∏_j φ_j(p_j)`, with `φ_j(p) = log x/(p log p)` for `j ∈ E` and `1/p` otherwise, is at most the product of
`1/lo_j − 1/hi_j` for `j ∈ E` and `log hi_j − log lo_j` otherwise, plus `o(1)`. -/
theorem evLe_box {k : ℕ} (lo hi : Fin k → ℝ) (hlo : ∀ j, 0 < lo j) (hlohi : ∀ j, lo j ≤ hi j)
    (E : Finset (Fin k)) :
    SieveRough.EvLe (fun x => ∑ p ∈ Fintype.piFinset fun j => SieveRough.primesIn (x ^ lo j) (x ^ hi j),
        ∏ j, if j ∈ E then Real.log x / ((p j : ℝ) * Real.log (p j)) else 1 / (p j : ℝ))
      (∏ j, if j ∈ E then 1 / lo j - 1 / hi j else Real.log (hi j) - Real.log (lo j)) := by
  have hS : ∀ j, SieveRough.EvLe (fun x => ∑ p ∈ SieveRough.primesIn (x ^ lo j) (x ^ hi j),
      if j ∈ E then Real.log x / ((p : ℝ) * Real.log p) else 1 / (p : ℝ))
      (if j ∈ E then 1 / lo j - 1 / hi j else Real.log (hi j) - Real.log (lo j)) := by
    intro j
    by_cases hj : j ∈ E
    · simp only [hj, ite_true]
      intro δ hδ
      filter_upwards [SieveRough.evLe_sum_inv_log (hlo j) (hlohi j) δ hδ] with x hx
      rw [Finset.mul_sum] at hx
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) hx
      rw [mul_one_div]
    · simp only [hj, ite_false]
      exact SieveRough.evLe_sum_inv (hlo j) (hlohi j)
  have hP0 : ∀ j, 0 ≤ if j ∈ E then 1 / lo j - 1 / hi j else Real.log (hi j) - Real.log (lo j) := by
    intro j
    split_ifs
    · have := one_div_le_one_div_of_le (hlo j) (hlohi j); linarith
    · have := Real.log_le_log (hlo j) (hlohi j); linarith
  have hS0 : ∀ j, ∀ᶠ x : ℝ in atTop, 0 ≤ ∑ p ∈ SieveRough.primesIn (x ^ lo j) (x ^ hi j),
      if j ∈ E then Real.log x / ((p : ℝ) * Real.log p) else 1 / (p : ℝ) := by
    intro j
    filter_upwards [eventually_ge_atTop 1] with x hx
    refine Finset.sum_nonneg fun p _ => ?_
    split_ifs
    · exact div_nonneg (Real.log_nonneg hx) (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
    · positivity
  have h := SieveRough.EvLe.prod _ _ hP0 hS0 hS
  intro δ hδ
  filter_upwards [h δ hδ] with x hx
  rw [← Finset.prod_univ_sum (fun j => SieveRough.primesIn (x ^ lo j) (x ^ hi j))
    (fun j p => if j ∈ E then Real.log x / ((p : ℝ) * Real.log p) else 1 / (p : ℝ))]
  exact hx

/-- **The finish.** Let `W, P ≥ 0`. If for every `ε > 0` eventually `F ≤ (W + ε)·g·R` with `g ≥ 0`, and
`limsup R ≤ P`, then for every `δ > 0` eventually `F ≤ (WP + δ)·g`. -/
theorem evLe_finish {F R g : ℝ → ℝ} {W P : ℝ} (hW : 0 ≤ W) (hP : 0 ≤ P) (hR : SieveRough.EvLe R P)
    (hg : ∀ᶠ x : ℝ in atTop, 0 ≤ g x)
    (hF : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, F x ≤ (W + ε) * g x * R x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, F x ≤ (W * P + δ) * g x := by
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min 1 (δ / (2 * (P + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := by rw [hε]; exact min_le_left _ _
  have hεP : ε * P ≤ δ / 2 := by
    have h := min_le_right 1 (δ / (2 * (P + 1)))
    rw [← hε] at h
    calc ε * P ≤ δ / (2 * (P + 1)) * P := mul_le_mul_of_nonneg_right h hP
      _ ≤ δ / (2 * (P + 1)) * (P + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = δ / 2 := by field_simp
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁, δ₁ = δ / (2 * (W + 1)) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  have hWδ : (W + 1) * δ₁ = δ / 2 := by rw [hδ₁]; field_simp
  filter_upwards [hF ε hε0, hR δ₁ hδ₁0, hg] with x hFx hRx hgx
  have hk : (W + ε) * (P + δ₁) ≤ W * P + δ := by nlinarith
  calc F x ≤ (W + ε) * g x * R x := hFx
    _ ≤ (W + ε) * g x * (P + δ₁) := mul_le_mul_of_nonneg_left hRx (by positivity)
    _ = (W + ε) * (P + δ₁) * g x := by ring
    _ ≤ (W * P + δ) * g x := mul_le_mul_of_nonneg_right hk hgx

/-! ### Dropped nodes with one rough item -/

/-- **A dropped node with one rough item** (the cofactor, sifted by `p_{s(0)}`). Let `0 < lo`, `0 < ρ` with
`12ρ < lo`, `0 ≤ Ω` and `0 ≤ P`. Suppose that for large `x` every term of the node in `(x − x^{1−ρ}, x]` has its
primes in `PB x`, its cofactor's sifting prime at least `x^{lo}` and at most the cofactor, and
`ω*(log(x/∏p)/log p_{s(0)}) ≤ Ω`, and that `limsup Σ_{p ∈ PB x} log x/(∏p · log p_{s(0)}) ≤ P`. Then for every
`δ > 0`, eventually the count is at most `(ΩP + δ)·x^{1−ρ}/log x`. -/
theorem count_le_drop1 {k : ℕ} (s : Fin 1 → Fin k) (conds : List (Cond k 1)) {lo ρ Ω P : ℝ} (hlo : 0 < lo)
    (hρ : 0 < ρ) (hρlo : 12 * ρ < lo) (hΩ : 0 ≤ Ω) (hP : 0 ≤ P) (PB : ℝ → Finset (Fin k → ℕ))
    (hterm : ∀ᶠ x : ℝ in atTop, ∀ v ∈ pairs k 1 ⌊x⌋₊, SieveTree.rough (v.1 (s 0)) (v.2 0) →
      (⟨k, 1, s, conds⟩ : Node).InI x (x ^ (1 - ρ)) v.1 v.2 → v.1 ∈ PB x ∧ x ^ lo ≤ v.1 (s 0) ∧
        (v.1 (s 0) : ℝ) ≤ v.2 0 ∧ SieveCert.omegaC (Real.log (x / ∏ j, (v.1 j : ℝ)) / Real.log (v.1 (s 0))) ≤ Ω)
    (hPB : SieveRough.EvLe (fun x => ∑ p ∈ PB x, Real.log x / ((∏ j, (p j : ℝ)) * Real.log (p (s 0)))) P)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ((⟨k, 1, s, conds⟩ : Node).count x (x ^ (1 - ρ)) : ℝ) ≤
      (Ω * P + δ) * (x ^ (1 - ρ) / Real.log x) := by
  set N : Node := ⟨k, 1, s, conds⟩ with hN
  have hone : ∀ v : (Fin k → ℕ) × (Fin 1 → ℕ), outer 0 v = (v.1, fun _ => 1) := fun v => by
    unfold outer
    congr 1
    funext i
    rw [Fin.fin_one_eq_zero i, Function.update_self]
  have hprod : ∀ p : Fin k → ℕ, ((prodP (p, fun _ : Fin 1 => 1) : ℕ) : ℝ) = ∏ j, (p j : ℝ) := fun p => by
    unfold prodP
    push_cast
    simp
  refine evLe_finish hΩ hP hPB ?_ (fun ε hε => ?_) hδ
  · filter_upwards [eventually_ge_atTop 1] with x hx
    exact div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hx)
  have h := count_le_sum_cof N (0 : Fin 1) hlo hρ hρlo hΩ hε (fun x => PB x ×ˢ {fun _ => 1}) (by
    filter_upwards [hterm] with x hx v hv hr hI
    obtain ⟨h1, h2, h3, h4⟩ := hx v hv (hr 0) hI
    refine ⟨?_, h2, h3, ?_⟩
    · rw [hone, mem_product, mem_singleton]; exact ⟨h1, rfl⟩
    · rw [hone, hprod]; exact h4)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hsum : ∑ w ∈ PB x ×ˢ {fun _ : Fin 1 => 1}, 1 / ((prodP w : ℝ) * Real.log (w.1 (s 0))) =
      (∑ p ∈ PB x, Real.log x / ((∏ j, (p j : ℝ)) * Real.log (p (s 0)))) / Real.log x := by
    rw [Finset.sum_product, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_singleton, hprod, eq_div_iff hlx.ne', one_div_mul_eq_div]
  refine le_trans hx (le_of_eq ?_)
  rw [hsum]
  ring

/-! ### Reciprocals of rough numbers -/

/-- `η/log(1 + η) ≤ 1 + η` for `η > 0`. -/
theorem div_log_le {η : ℝ} (hη : 0 < η) : η / Real.log (1 + η) ≤ 1 + η := by
  have h1 : 0 < 1 + η := by linarith
  have hl : η / (1 + η) ≤ Real.log (1 + η) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
    rw [Real.log_inv] at h
    have e : (1 + η)⁻¹ - 1 = -(η / (1 + η)) := by field_simp; ring
    linarith
  have hl0 : 0 < Real.log (1 + η) := Real.log_pos (by linarith)
  rw [div_le_iff₀ hl0]
  calc η = η / (1 + η) * (1 + η) := by field_simp
    _ ≤ Real.log (1 + η) * (1 + η) := mul_le_mul_of_nonneg_right hl h1.le
    _ = (1 + η) * Real.log (1 + η) := mul_comm _ _

/-- **Reciprocals of rough numbers.** Let `U` be real, `ε > 0` and `0 < η ≤ 1`. There is `z₀` such that for
`z ≥ z₀`, `2 ≤ Ylo ≤ Yhi` with `log Yhi ≤ U log z`, and `ω*(log X/log z) ≤ Ω` for `X ∈ [Ylo, Yhi]`, every set of
integers in `[Ylo, Yhi]` free of primes below `z` has `Σ 1/γ ≤ (Ω + ε)((1 + η) log(Yhi/Ylo) + 2η)/log z`. The proof
cuts `(Ylo/λ, Yhi]` at `Ylo λ^{i−1}`, `λ = 1 + η`, and counts each piece by `ShortSieveLong.psi_le`. -/
theorem sum_inv_rough_le (U : ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ Ylo Yhi Ω : ℝ, 2 ≤ Ylo → Ylo ≤ Yhi → Real.log Yhi ≤ U * Real.log z →
      (∀ X, Ylo ≤ X → X ≤ Yhi → SieveCert.omegaC (Real.log X / Real.log z) ≤ Ω) →
      ∀ G : Finset ℕ, (∀ γ ∈ G, Ylo ≤ γ ∧ (γ : ℝ) ≤ Yhi ∧ SieveTree.rough z γ) →
        ∑ γ ∈ G, (1 : ℝ) / γ ≤ (Ω + ε) * ((1 + η) * Real.log (Yhi / Ylo) + 2 * η) / Real.log z := by
  obtain ⟨z₁, hz₁⟩ := ShortSieveLong.psi_le (σ := 1 / 24) (by norm_num) (by norm_num) U hε
  set lam : ℝ := 1 + η with hlam
  have hlam1 : 1 < lam := by linarith
  have hlam0 : 0 < lam := by linarith
  have hll : 0 < Real.log lam := Real.log_pos hlam1
  refine ⟨max (max z₁ ⌈(lam / η) ^ (24 : ℝ)⌉₊) 2, fun z hz Ylo Yhi Ω hYlo hYY hYU hΩ G hG => ?_⟩
  have hzz₁ : z₁ ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans (le_max_right _ _) hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  -- `z^{−1/24} ≤ 1 − 1/λ`
  have hzσ : (z : ℝ) ^ (-(1 / 24 : ℝ)) ≤ 1 - 1 / lam := by
    have h1 : (lam / η) ^ (24 : ℝ) ≤ z := le_trans (Nat.le_ceil _)
      (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz)
    have h2 : lam / η ≤ (z : ℝ) ^ (1 / 24 : ℝ) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 24)
      rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel (by norm_num), Real.rpow_one] at h3
    have h4 : (z : ℝ) ^ (-(1 / 24 : ℝ)) = 1 / (z : ℝ) ^ (1 / 24 : ℝ) := by
      rw [Real.rpow_neg hz0.le, inv_eq_one_div]
    have e : 1 - 1 / lam = η / lam := by rw [hlam]; field_simp; ring
    rw [h4, e, div_le_div_iff₀ (by positivity) hlam0, one_mul]
    rwa [div_le_iff₀ hη, mul_comm] at h2
  have hΩ0 : 0 ≤ Ω := le_trans (SieveRough.omegaC_nonneg _) (hΩ Ylo le_rfl hYY)
  -- the pieces
  set X₀ : ℝ := Ylo / lam with hX₀
  have hX₀0 : 0 < X₀ := div_pos (by linarith) hlam0
  set n : ℕ := ⌈Real.log (Yhi / Ylo) / Real.log lam⌉₊ with hn
  set idx : ℕ → ℕ := fun γ => ⌈Real.log (γ / X₀) / Real.log lam⌉₊ - 1 with hidx
  have hpiece : ∀ γ ∈ G, idx γ ∈ range (n + 1) ∧ X₀ * lam ^ idx γ < γ ∧ (γ : ℝ) ≤ X₀ * lam ^ (idx γ + 1) := by
    intro γ hγ
    obtain ⟨h1, h2, -⟩ := hG γ hγ
    have hγ0 : (0 : ℝ) < γ := by linarith
    set t := Real.log (γ / X₀) / Real.log lam with ht
    have ht1 : 1 ≤ t := by
      rw [ht, le_div_iff₀ hll, one_mul]
      apply Real.log_le_log hlam0
      rw [le_div_iff₀ hX₀0, hX₀, mul_div_cancel₀ _ hlam0.ne']
      exact h1
    have hc1 : 1 ≤ ⌈t⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      intro h; rw [Nat.ceil_eq_zero] at h; linarith)
    have hidxt : (idx γ : ℝ) + 1 = ⌈t⌉₊ := by
      have e : idx γ + 1 = ⌈t⌉₊ := by simp only [hidx]; rw [← ht]; omega
      exact_mod_cast e
    have hlt : (idx γ : ℝ) < t := by
      have := Nat.ceil_lt_add_one (by linarith : 0 ≤ t); linarith
    have hle : t ≤ (idx γ : ℝ) + 1 := by rw [hidxt]; exact Nat.le_ceil t
    have hlogγ : Real.log (γ / X₀) = t * Real.log lam := by rw [ht]; field_simp
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_range, Nat.lt_succ_iff]
      have htn : t ≤ (n : ℝ) + 1 := by
        have hn' : Real.log (Yhi / Ylo) / Real.log lam ≤ n := Nat.le_ceil _
        have h3 : Real.log (γ / X₀) ≤ Real.log (Yhi / Ylo) + Real.log lam := by
          rw [← Real.log_mul (div_pos (by linarith) (by linarith)).ne' hlam0.ne']
          apply Real.log_le_log (div_pos hγ0 hX₀0)
          rw [hX₀, div_div_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by linarith)]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hlam0.le) (by linarith)
        rw [ht, div_le_iff₀ hll]
        rw [div_le_iff₀ hll] at hn'
        nlinarith
      have h4 : (idx γ : ℝ) < n + 1 := by linarith
      have h5 : idx γ < n + 1 := by exact_mod_cast h4
      omega
    · have h3 : Real.log (X₀ * lam ^ idx γ) < Real.log γ := by
        rw [Real.log_mul hX₀0.ne' (by positivity), Real.log_pow]
        have : Real.log γ = Real.log (γ / X₀) + Real.log X₀ := by
          rw [Real.log_div hγ0.ne' hX₀0.ne']; ring
        rw [this, hlogγ]
        nlinarith
      exact (Real.log_lt_log_iff (by positivity) hγ0).1 h3
    · have h3 : Real.log γ ≤ Real.log (X₀ * lam ^ (idx γ + 1)) := by
        rw [Real.log_mul hX₀0.ne' (by positivity), Real.log_pow]
        have : Real.log γ = Real.log (γ / X₀) + Real.log X₀ := by
          rw [Real.log_div hγ0.ne' hX₀0.ne']; ring
        rw [this, hlogγ]
        push_cast
        nlinarith
      exact (Real.log_le_log_iff hγ0 (by positivity)).1 h3
  -- each piece
  have hone : ∀ i ∈ range (n + 1), ∑ γ ∈ G with idx γ = i, (1 : ℝ) / γ ≤ (Ω + ε) * η / Real.log z := by
    intro i _
    rcases Finset.eq_empty_or_nonempty {γ ∈ G | idx γ = i} with he | ⟨γ₀, hγ₀⟩
    · rw [he, sum_empty]; positivity
    set T : ℝ := min (X₀ * lam ^ (i + 1)) Yhi with hT
    have hXi0 : 0 < X₀ * lam ^ i := by positivity
    have hmem : ∀ γ ∈ {γ ∈ G | idx γ = i}, X₀ * lam ^ i < γ ∧ (γ : ℝ) ≤ T ∧ SieveTree.rough z γ := by
      intro γ hγ
      rw [mem_filter] at hγ
      obtain ⟨-, h1, h2⟩ := hpiece γ hγ.1
      rw [hγ.2] at h1 h2
      exact ⟨h1, le_min h2 (hG γ hγ.1).2.1, (hG γ hγ.1).2.2⟩
    have hTlo : Ylo ≤ T := le_trans (hG γ₀ (mem_filter.1 hγ₀).1).1 (hmem γ₀ hγ₀).2.1
    have hTX : T ≤ X₀ * lam ^ i * lam := by rw [hT, mul_assoc, ← pow_succ]; exact min_le_left _ _
    have hTY : T ≤ Yhi := min_le_right _ _
    have hT2 : 2 ≤ T := le_trans hYlo hTlo
    have hT0 : 0 < T := by linarith
    -- the piece lies in `(T/λ, T]`
    have hcard : #{γ ∈ G | idx γ = i} ≤ ShortSieveLong.Psi T (T * (1 - 1 / lam)) z := by
      unfold ShortSieveLong.Psi ShortSieveLong.roughSet
      refine card_le_card_of_injOn id (fun γ hγ => ?_) (fun _ _ _ _ h => h)
      obtain ⟨h1, h2, h3⟩ := hmem γ hγ
      rw [mem_coe, mem_filter, mem_Ioc]
      refine ⟨⟨?_, Nat.le_floor h2⟩, fun p hp => le_of_mem_primeFactors h3 hp⟩
      have e : T - T * (1 - 1 / lam) = T / lam := by field_simp; ring
      rw [e]
      have h4 : T / lam ≤ X₀ * lam ^ i := by rw [div_le_iff₀ hlam0]; exact hTX
      have h5 : (⌊T / lam⌋₊ : ℝ) < γ :=
        lt_of_le_of_lt (Nat.floor_le (div_pos hT0 hlam0).le) (lt_of_le_of_lt h4 h1)
      exact_mod_cast h5
    have hψ := hz₁ z hzz₁ T (T * (1 - 1 / lam)) hT2
      (by rw [mul_comm T]; exact mul_le_mul_of_nonneg_right hzσ hT0.le)
      (by
        have : 1 - 1 / lam ≤ 1 / 2 := by
          have := one_div_le_one_div_of_le hlam0 (by linarith : lam ≤ 2)
          linarith
        nlinarith)
      (le_trans (Real.log_le_log hT0 hTY) hYU)
    have hωT := hΩ T hTlo hTY
    calc ∑ γ ∈ G with idx γ = i, (1 : ℝ) / γ ≤ ∑ γ ∈ G with idx γ = i, 1 / (X₀ * lam ^ i) :=
          sum_le_sum fun γ hγ => one_div_le_one_div_of_le hXi0 (hmem γ hγ).1.le
      _ = #{γ ∈ G | idx γ = i} / (X₀ * lam ^ i) := by rw [sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ShortSieveLong.Psi T (T * (1 - 1 / lam)) z / (X₀ * lam ^ i) := by
          apply div_le_div_of_nonneg_right _ hXi0.le; exact_mod_cast hcard
      _ ≤ (SieveCert.omegaC (Real.log T / Real.log z) + ε) * (T * (1 - 1 / lam)) / Real.log z /
          (X₀ * lam ^ i) := div_le_div_of_nonneg_right hψ hXi0.le
      _ ≤ (Ω + ε) * (X₀ * lam ^ i * lam * (1 - 1 / lam)) / Real.log z / (X₀ * lam ^ i) := by
          apply div_le_div_of_nonneg_right _ hXi0.le
          apply div_le_div_of_nonneg_right _ hlz.le
          have h1 : 0 ≤ 1 - 1 / lam := by
            rw [sub_nonneg, div_le_one hlam0]; exact hlam1.le
          exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right hTX h1)
            (mul_nonneg hT0.le h1) (by linarith)
      _ = (Ω + ε) * η / Real.log z := by
          rw [hlam]; field_simp; ring
  -- the sum
  rw [← sum_fiberwise_of_maps_to (g := idx) (t := range (n + 1)) fun γ hγ => (hpiece γ hγ).1]
  calc ∑ i ∈ range (n + 1), ∑ γ ∈ G with idx γ = i, (1 : ℝ) / γ ≤ ∑ i ∈ range (n + 1), (Ω + ε) * η / Real.log z :=
        sum_le_sum hone
    _ = (n + 1) * ((Ω + ε) * η / Real.log z) := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (Ω + ε) * ((1 + η) * Real.log (Yhi / Ylo) + 2 * η) / Real.log z := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hlz]
        have hL : 0 ≤ Real.log (Yhi / Ylo) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
        have hn1 : (n : ℝ) ≤ Real.log (Yhi / Ylo) / Real.log lam + 1 := by
          have := Nat.ceil_lt_add_one (div_nonneg hL hll.le); rw [← hn] at this; linarith
        have hdl := div_log_le hη
        rw [← hlam] at hdl
        have h1 : (n + 1) * η ≤ (1 + η) * Real.log (Yhi / Ylo) + 2 * η := by
          have h2 : Real.log (Yhi / Ylo) / Real.log lam * η = Real.log (Yhi / Ylo) * (η / Real.log lam) := by ring
          have h3 : Real.log (Yhi / Ylo) * (η / Real.log lam) ≤ Real.log (Yhi / Ylo) * (1 + η) :=
            mul_le_mul_of_nonneg_left hdl hL
          nlinarith
        nlinarith

/-! ### Dropped nodes with two rough items -/

/-- The items `1` at `c` and `γ` at the other place of `Fin 2`. -/
def itemsOf (c : Fin 2) (γ : ℕ) : Fin 2 → ℕ := fun i => if i = c then 1 else γ

theorem update_eq_itemsOf {c g : Fin 2} (hcg : c ≠ g) (ρ : Fin 2 → ℕ) :
    Function.update ρ c 1 = itemsOf c (ρ g) := by
  funext i
  unfold itemsOf
  by_cases hi : i = c
  · subst hi; simp
  · have hig : i = g := by fin_cases i <;> fin_cases c <;> fin_cases g <;> simp_all
    rw [Function.update_of_ne hi, ite_eq_right hi, hig]

theorem cast_prodP_itemsOf {k : ℕ} (c : Fin 2) (p : Fin k → ℕ) (γ : ℕ) :
    ((prodP (p, itemsOf c γ) : ℕ) : ℝ) = (∏ j, (p j : ℝ)) * γ := by
  have h : ∏ i, itemsOf c γ i = γ := by fin_cases c <;> simp [itemsOf, Fin.prod_univ_two]
  unfold prodP
  dsimp only
  rw [h]
  push_cast
  ring

/-- The rough items of a product coordinate: the `γ ≤ x` with `x^{lo₀} ≤ (∏_{j ∈ J} p_j)·γ ≤ x^{hi₀}`, at least `z`
and free of primes below `z`. -/
noncomputable def gams {k : ℕ} (J : Finset (Fin k)) (lo₀ hi₀ x : ℝ) (p : Fin k → ℕ) (z : ℕ) : Finset ℕ :=
  (Icc 1 ⌊x⌋₊).filter fun γ => x ^ lo₀ ≤ (∏ j ∈ J, (p j : ℝ)) * γ ∧ (∏ j ∈ J, (p j : ℝ)) * γ ≤ x ^ hi₀ ∧
    (z : ℝ) ≤ γ ∧ SieveTree.rough z γ

/-- **The rough items of a product coordinate.** Let `0 < lo`, `0 < lo₀ ≤ hi₀`, `0 < e ≤ 1` and `Ωg ≥ 0`. There is
`z₀` such that for `x ≥ e¹`, `z₀ ≤ x^{lo} ≤ z`, all `p_j ≥ 1` and `ω*(log X/log z) ≤ Ωg` for
`X ∈ [x^{lo₀}, x^{hi₀}]/∏_{j ∈ J} p_j`, the reciprocals of `gams` sum to at most
`(Ωg + e)((1 + e)(hi₀ − lo₀) + 2e)·log x/log z` (`sum_inv_rough_le`). -/
theorem sum_gams_le {k : ℕ} (J : Finset (Fin k)) {lo lo₀ hi₀ e Ωg : ℝ} (hlo : 0 < lo) (hlo₀ : 0 < lo₀)
    (hlohi₀ : lo₀ ≤ hi₀) (he0 : 0 < e) (he1 : e ≤ 1) (hΩg : 0 ≤ Ωg) :
    ∃ z₀ : ℕ, ∀ x : ℝ, Real.exp 1 ≤ x → ∀ (p : Fin k → ℕ) (z : ℕ), (z₀ : ℝ) ≤ x ^ lo → x ^ lo ≤ z →
      (∀ j, 1 ≤ p j) → (∀ X, x ^ lo₀ / ∏ j ∈ J, (p j : ℝ) ≤ X → X ≤ x ^ hi₀ / ∏ j ∈ J, (p j : ℝ) →
        SieveCert.omegaC (Real.log X / Real.log z) ≤ Ωg) →
      ∑ γ ∈ gams J lo₀ hi₀ x p z, (1 : ℝ) / γ ≤
        (Ωg + e) * ((1 + e) * (hi₀ - lo₀) + 2 * e) * (Real.log x / Real.log z) := by
  obtain ⟨z₁, hz₁⟩ := sum_inv_rough_le (hi₀ / lo) he0 he0 he1
  refine ⟨max z₁ 2, fun x hxe p z hxz hpz hp1 hpω => ?_⟩
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos) hxe
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hQ1 : (1 : ℝ) ≤ ∏ j ∈ J, (p j : ℝ) := Finset.one_le_prod₀ fun j _ => by exact_mod_cast hp1 j
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∏ j ∈ J, (p j : ℝ) := ⟨_, rfl⟩
  rw [← hQ] at hQ1 hpω
  have hQ0 : 0 < Q := by linarith
  have hzx : ((max z₁ 2 : ℕ) : ℝ) ≤ z := le_trans hxz hpz
  have hz2 : (2 : ℝ) ≤ z := le_trans (by exact_mod_cast le_max_right z₁ 2) hzx
  have hzz₁ : z₁ ≤ z := le_trans (le_max_left _ _) (by exact_mod_cast hzx)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlzx : lo * Real.log x ≤ Real.log z := by
    rw [← Real.log_rpow hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hpz
  have hnn : 0 ≤ (Ωg + e) * ((1 + e) * (hi₀ - lo₀) + 2 * e) * (Real.log x / Real.log z) := by
    have : 0 ≤ hi₀ - lo₀ := by linarith
    have : 0 ≤ Real.log x / Real.log z := div_nonneg (by linarith) hlz.le
    positivity
  obtain ⟨Ylo, hYlo⟩ : ∃ Ylo, Ylo = max (x ^ lo₀ / Q) z := ⟨_, rfl⟩
  obtain ⟨Yhi, hYhi⟩ : ∃ Yhi, Yhi = x ^ hi₀ / Q := ⟨_, rfl⟩
  have hmem : ∀ γ ∈ gams J lo₀ hi₀ x p z, Ylo ≤ γ ∧ (γ : ℝ) ≤ Yhi ∧ SieveTree.rough z γ := by
    intro γ hγ
    unfold gams at hγ
    rw [mem_filter, ← hQ] at hγ
    obtain ⟨-, h1, h2, h3, h4⟩ := hγ
    refine ⟨?_, ?_, h4⟩
    · rw [hYlo]; refine max_le ?_ h3
      rw [div_le_iff₀ hQ0, mul_comm]; exact h1
    · rw [hYhi, le_div_iff₀ hQ0, mul_comm]; exact h2
  by_cases hY : Ylo ≤ Yhi
  · have hY2 : 2 ≤ Ylo := by rw [hYlo]; exact le_trans hz2 (le_max_right _ _)
    have hYU : Real.log Yhi ≤ hi₀ / lo * Real.log z := by
      have h1 : Real.log Yhi ≤ hi₀ * Real.log x := by
        rw [← Real.log_rpow hx0, hYhi]
        exact Real.log_le_log (by positivity) (div_le_self (Real.rpow_nonneg hx0.le _) hQ1)
      have h2 : hi₀ * Real.log x ≤ hi₀ / lo * Real.log z := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlo]
        nlinarith [mul_le_mul_of_nonneg_left hlzx (by linarith : (0 : ℝ) ≤ hi₀)]
      linarith
    have hω : ∀ X, Ylo ≤ X → X ≤ Yhi → SieveCert.omegaC (Real.log X / Real.log z) ≤ Ωg := fun X h1 h2 =>
      hpω X (le_trans (by rw [hYlo]; exact le_max_left _ _) h1) (by rw [← hYhi]; exact h2)
    have hsum := hz₁ z hzz₁ Ylo Yhi Ωg hY2 hY hYU hω _ hmem
    have hL : Real.log (Yhi / Ylo) ≤ (hi₀ - lo₀) * Real.log x := by
      have hlo0 : 0 < x ^ lo₀ / Q := by positivity
      have h1 : Yhi / Ylo ≤ Yhi / (x ^ lo₀ / Q) :=
        div_le_div_of_nonneg_left (by linarith) hlo0 (by rw [hYlo]; exact le_max_left _ _)
      have h2 : Yhi / (x ^ lo₀ / Q) = x ^ (hi₀ - lo₀) := by
        rw [hYhi, Real.rpow_sub hx0]; field_simp
      rw [← Real.log_rpow hx0, ← h2]
      exact Real.log_le_log (div_pos (by linarith) (by linarith)) h1
    have hk : (1 + e) * Real.log (Yhi / Ylo) + 2 * e ≤ ((1 + e) * (hi₀ - lo₀) + 2 * e) * Real.log x := by
      nlinarith
    calc ∑ γ ∈ gams J lo₀ hi₀ x p z, (1 : ℝ) / γ ≤
        (Ωg + e) * ((1 + e) * Real.log (Yhi / Ylo) + 2 * e) / Real.log z := hsum
      _ ≤ (Ωg + e) * (((1 + e) * (hi₀ - lo₀) + 2 * e) * Real.log x) / Real.log z :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by linarith)) hlz.le
      _ = (Ωg + e) * ((1 + e) * (hi₀ - lo₀) + 2 * e) * (Real.log x / Real.log z) := by ring
  · have he : gams J lo₀ hi₀ x p z = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro γ hγ
      obtain ⟨h1, h2, -⟩ := hmem γ hγ
      exact hY (le_trans h1 h2)
    rw [he, sum_empty]
    exact hnn

/-- The outer items of a node with two rough items, summed: from the bound for `gams` at each `p`. -/
theorem sum_outer2_le {k : ℕ} (s : Fin 2 → Fin k) (c g : Fin 2) (J : Finset (Fin k)) (lo₀ hi₀ x K : ℝ)
    (hlx : 0 < Real.log x) (PB : Finset (Fin k → ℕ))
    (hγ : ∀ p ∈ PB, ∑ γ ∈ gams J lo₀ hi₀ x p (p (s g)), (1 : ℝ) / γ ≤ K * (Real.log x / Real.log (p (s g)))) :
    ∑ w ∈ (PB.sigma fun p => gams J lo₀ hi₀ x p (p (s g))).image (fun q => (q.1, itemsOf c q.2)),
      1 / ((prodP w : ℝ) * Real.log (w.1 (s c))) ≤
      K / Real.log x * ∑ p ∈ PB,
        Real.log x ^ 2 / ((∏ j, (p j : ℝ)) * Real.log (p (s c)) * Real.log (p (s g))) := by
  refine le_trans (Finset.sum_image_le_of_nonneg fun w _ =>
    div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))) ?_
  rw [Finset.sum_sigma, Finset.mul_sum]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨A, hA⟩ : ∃ A, A = 1 / ((∏ j, (p j : ℝ)) * Real.log (p (s c))) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact div_nonneg zero_le_one (mul_nonneg (Finset.prod_nonneg fun j _ => Nat.cast_nonneg _)
      (Real.log_natCast_nonneg _))
  have hterm : ∀ γ ∈ gams J lo₀ hi₀ x p (p (s g)),
      1 / ((prodP (p, itemsOf c γ) : ℝ) * Real.log (p (s c))) = A * (1 / (γ : ℝ)) := fun γ _ => by
    rw [cast_prodP_itemsOf, hA, div_mul_div_comm, one_mul, mul_right_comm]
  calc ∑ γ ∈ gams J lo₀ hi₀ x p (p (s g)), 1 / ((prodP (p, itemsOf c γ) : ℝ) * Real.log (p (s c))) =
      A * ∑ γ ∈ gams J lo₀ hi₀ x p (p (s g)), (1 : ℝ) / γ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl hterm
    _ ≤ A * (K * (Real.log x / Real.log (p (s g)))) := mul_le_mul_of_nonneg_left (hγ p hp) hA0
    _ = K / Real.log x * (Real.log x ^ 2 / ((∏ j, (p j : ℝ)) * Real.log (p (s c)) * Real.log (p (s g)))) := by
        rw [hA]
        field_simp

/-- A choice of `e`: for `A, B, w ≥ 0` and `ε > 0` there is `0 < e ≤ 1` with
`(A + e)(B + e)((1 + e)w + 2e) ≤ ABw + ε`. -/
theorem exists_small {A B w ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hw : 0 ≤ w) (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ (A + e) * ((B + e) * ((1 + e) * w + 2 * e)) ≤ A * B * w + ε := by
  obtain ⟨M, hM⟩ : ∃ M, M = A * B * (w + 2) + (A + B + 1) * w + (A + B + 1) * (w + 2) + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  refine ⟨min 1 (ε / M), lt_min one_pos (div_pos hε hM0), min_le_left _ _, ?_⟩
  obtain ⟨e, he⟩ : ∃ e, e = min 1 (ε / M) := ⟨_, rfl⟩
  rw [← he]
  have he0 : 0 < e := by rw [he]; exact lt_min one_pos (div_pos hε hM0)
  have he1 : e ≤ 1 := by rw [he]; exact min_le_left _ _
  have heM : e * M ≤ ε := by
    have := min_le_right 1 (ε / M)
    rw [← he] at this
    calc e * M ≤ ε / M * M := mul_le_mul_of_nonneg_right this hM0.le
      _ = ε := div_mul_cancel₀ _ hM0.ne'
  have h1 : (A + e) * (B + e) ≤ A * B + e * (A + B + 1) := by nlinarith
  have h2 : 0 ≤ (1 + e) * w + 2 * e := by positivity
  have hee : e * e ≤ e := by nlinarith
  have hAB : 0 ≤ (A + B + 1) * (w + 2) := by positivity
  have h3 : (A * B + e * (A + B + 1)) * ((1 + e) * w + 2 * e) ≤ A * B * w + e * (M - 1) := by
    rw [hM]
    nlinarith [mul_le_mul_of_nonneg_right hee hAB]
  calc (A + e) * ((B + e) * ((1 + e) * w + 2 * e)) = (A + e) * (B + e) * ((1 + e) * w + 2 * e) := by ring
    _ ≤ (A * B + e * (A + B + 1)) * ((1 + e) * w + 2 * e) := mul_le_mul_of_nonneg_right h1 h2
    _ ≤ A * B * w + e * (M - 1) := h3
    _ ≤ A * B * w + ε := by nlinarith

/-- **A dropped node with two rough items**: the cofactor `ρ_c`, sifted by `p_{s(c)}`, and `γ = ρ_g` (`g ≠ c`),
sifted by `p_{s(g)}`, whose size is fixed by a product coordinate `x^{lo₀} ≤ (∏_{j ∈ J} p_j)·γ ≤ x^{hi₀}`, as in
the role reversals. Let `0 < lo`, `0 < ρ` with `12ρ < lo`, `0 < lo₀ ≤ hi₀`, and `Ωc, Ωg, P ≥ 0`. Suppose that for
large `x`:
* every term of the node in `(x − x^{1−ρ}, x]` has its primes in `PB x`, `x^{lo} ≤ p_{s(c)} ≤ ρ_c`,
  `p_{s(g)} ≤ γ`, its product coordinate in `[x^{lo₀}, x^{hi₀}]`, and `ω*(log(x/(∏p·γ))/log p_{s(c)}) ≤ Ωc`;
* every `p ∈ PB x` has `p_{s(g)} ≥ x^{lo}`, all `p_j ≥ 1`, and `ω*(log X/log p_{s(g)}) ≤ Ωg` for
  `X ∈ [x^{lo₀}, x^{hi₀}]/∏_{j ∈ J} p_j`;
and that `limsup Σ_{p ∈ PB x} (log x)²/(∏p · log p_{s(c)} · log p_{s(g)}) ≤ P`. Then for every `δ > 0`, eventually
the count is at most `(Ωc Ωg (hi₀ − lo₀) P + δ)·x^{1−ρ}/log x`. -/
theorem count_le_drop2 {k : ℕ} (s : Fin 2 → Fin k) (conds : List (Cond k 2)) {c g : Fin 2} (hcg : c ≠ g)
    (J : Finset (Fin k)) {lo lo₀ hi₀ ρ Ωc Ωg P : ℝ} (hlo : 0 < lo) (hρ : 0 < ρ) (hρlo : 12 * ρ < lo)
    (hlo₀ : 0 < lo₀) (hlohi₀ : lo₀ ≤ hi₀) (hΩc : 0 ≤ Ωc) (hΩg : 0 ≤ Ωg) (hP : 0 ≤ P)
    (PB : ℝ → Finset (Fin k → ℕ))
    (hterm : ∀ᶠ x : ℝ in atTop, ∀ v ∈ pairs k 2 ⌊x⌋₊, (∀ i, SieveTree.rough (v.1 (s i)) (v.2 i)) →
      (⟨k, 2, s, conds⟩ : Node).InI x (x ^ (1 - ρ)) v.1 v.2 → v.1 ∈ PB x ∧ x ^ lo ≤ v.1 (s c) ∧
        (v.1 (s c) : ℝ) ≤ v.2 c ∧ (v.1 (s g) : ℝ) ≤ v.2 g ∧ x ^ lo₀ ≤ (∏ j ∈ J, (v.1 j : ℝ)) * v.2 g ∧
        (∏ j ∈ J, (v.1 j : ℝ)) * v.2 g ≤ x ^ hi₀ ∧
        SieveCert.omegaC (Real.log (x / ((∏ j, (v.1 j : ℝ)) * v.2 g)) / Real.log (v.1 (s c))) ≤ Ωc)
    (hPB : ∀ᶠ x : ℝ in atTop, ∀ p ∈ PB x, x ^ lo ≤ p (s g) ∧ (∀ j, 1 ≤ p j) ∧
      ∀ X, x ^ lo₀ / ∏ j ∈ J, (p j : ℝ) ≤ X → X ≤ x ^ hi₀ / ∏ j ∈ J, (p j : ℝ) →
        SieveCert.omegaC (Real.log X / Real.log (p (s g))) ≤ Ωg)
    (hF : SieveRough.EvLe (fun x => ∑ p ∈ PB x,
      Real.log x ^ 2 / ((∏ j, (p j : ℝ)) * Real.log (p (s c)) * Real.log (p (s g)))) P)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ((⟨k, 2, s, conds⟩ : Node).count x (x ^ (1 - ρ)) : ℝ) ≤
      (Ωc * Ωg * (hi₀ - lo₀) * P + δ) * (x ^ (1 - ρ) / Real.log x) := by
  have hw0 : 0 ≤ hi₀ - lo₀ := by linarith
  refine evLe_finish (mul_nonneg (mul_nonneg hΩc hΩg) hw0) hP hF ?_ (fun ε hε => ?_) hδ
  · filter_upwards [eventually_ge_atTop 1] with x hx
    exact div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hx)
  obtain ⟨e, he0, he1, hKe⟩ := exists_small hΩc hΩg hw0 hε
  obtain ⟨K, hK⟩ : ∃ K, K = (Ωg + e) * ((1 + e) * (hi₀ - lo₀) + 2 * e) := ⟨_, rfl⟩
  rw [← hK] at hKe
  obtain ⟨z₀, hz₀⟩ := sum_gams_le J hlo hlo₀ hlohi₀ he0 he1 hΩg
  have h := count_le_sum_cof ⟨k, 2, s, conds⟩ c hlo hρ hρlo hΩc he0
    (fun x => ((PB x).sigma fun p => gams J lo₀ hi₀ x p (p (s g))).image fun q => (q.1, itemsOf c q.2)) (by
      filter_upwards [hterm] with x hx v hv hr hI
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx v hv hr hI
      have hout : outer c v = (v.1, itemsOf c (v.2 g)) := by
        unfold outer; rw [update_eq_itemsOf hcg]
      refine ⟨?_, h2, h3, ?_⟩
      · rw [hout, mem_image]
        refine ⟨⟨v.1, v.2 g⟩, mem_sigma.2 ⟨h1, ?_⟩, rfl⟩
        unfold gams
        rw [mem_filter, mem_Icc]
        exact ⟨((mem_pairs.1 hv).2 g), h5, h6, h4, hr g⟩
      · rw [hout, cast_prodP_itemsOf]; exact h7)
  filter_upwards [h, hPB, eventually_ge_atTop (Real.exp 1),
    (tendsto_rpow_atTop hlo).eventually_ge_atTop (z₀ : ℝ)] with x hx hPBx hxe hxz
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos) hxe
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hsum := sum_outer2_le s c g J lo₀ hi₀ x K hlx (PB x) fun p hp => by
    obtain ⟨hpg, hp1, hpω⟩ := hPBx p hp
    rw [hK]
    exact hz₀ x hxe p (p (s g)) hxz hpg hp1 hpω
  have hF0 : 0 ≤ ∑ p ∈ PB x,
      Real.log x ^ 2 / ((∏ j, (p j : ℝ)) * Real.log (p (s c)) * Real.log (p (s g))) :=
    Finset.sum_nonneg fun p _ => div_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg fun j _ => Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) (Real.log_natCast_nonneg _))
  have hy0 : 0 ≤ x ^ (1 - ρ) := Real.rpow_nonneg (by linarith) _
  refine le_trans hx (le_trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hy0)) ?_)
  obtain ⟨F, hF⟩ : ∃ F, F = ∑ p ∈ PB x,
      Real.log x ^ 2 / ((∏ j, (p j : ℝ)) * Real.log (p (s c)) * Real.log (p (s g))) := ⟨_, rfl⟩
  rw [← hF] at hF0 ⊢
  have e1 : (Ωc + e) * x ^ (1 - ρ) * (K / Real.log x * F) = (Ωc + e) * K * (x ^ (1 - ρ) / Real.log x) * F := by
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKe (div_nonneg hy0 hlx.le)) hF0

end ShortSieveDrop

#print axioms ShortSieveDrop.count_le_sum_cof
#print axioms ShortSieveDrop.evLe_box
#print axioms ShortSieveDrop.count_le_drop1
#print axioms ShortSieveDrop.sum_inv_rough_le
#print axioms ShortSieveDrop.count_le_drop2
