import ShortSieveLower
import ShortSieveTree

/-!
# Li's third sum, split into the certificate's root cells

`Σ₃ = Σ_p Σ_{L_p ≤ q < p} S(I_{pq}, q)` (`ShortSieveLower.sThree`). For a prime `q`, the `m` free of primes below
`q` are `1` and the `m ≥ q`.

* `sThree_eq`: `Σ₃ = R₁ + Σ_p Σ_q #{m ≥ q}`, where `R₁` counts the products `pq ∈ I` (`rOne`).
* `OK_rOne`: `R₁` has no loss. In the comparison interval its `p` and `q` both lie in `((x − y₁)/√x, √x]`, so it is
  at most `(y₁/√x + 1)² = O(x^{1−2ρ})`.
* `count_eq_n2`, `bigThree_eq_n2`: the terms `m ≥ q` over pairs of primes `(p, q)` with a predicate (`n2`), and the
  node `⟨2, 1, (· ↦ 1), conds⟩` whose conditions are that predicate and `q ≤ m`. Li's pairs in logarithms
  (`PhiL`): `x^{ν(0)} ≤ p ≤ √x`, `x^{ν(α_p)} ≤ q < p`, `pq² ≤ x` (the terms with `pq² > x` are empty).
* `bigThree_eq_cells`: at `θ = 13/25`, `γ = 2/25`, the cells `(k/50, (k + 1)/50] × [j/50, (j + 1)/50)` of
  `(α_p, α_q)`, `2 ≤ k ≤ 24`, `2 ≤ j ≤ 12` in Li's region `C` and `12 ≤ k ≤ 24`, `10 ≤ j ≤ 16` outside it (`RegC`:
  `α_p + 3α_q < 1` for `α_p ≤ 2/5`, `2α_q < α_p` above). Every cell of `α_p` lies in one piece of Li's level
  (`liNu_cell`), so each cell is a node with log-linear conditions (`cellConds`); its level condition is
  `log q ≥ (2/25) log x` on `k = 23` and `2 log p + (2h − 1) log q ≥ (26/25) log x`, `h = ⌊(26 − k)/2⌋`, elsewhere.
* `primes_of_cells`: given Li's Lemma 3.1 and every cell `OK` with loss `L`, `π(x) − π(x − y) ≥ (1 − ΣL − ε) y/log x`
  for `x^{13/25} ≤ y ≤ x^{1−ρ}` (`ShortSieveLower.primes_lower`, with `ν(α) ≤ α` on `[ν(0), 1/2]`: `liNu_le_self`).
-/
open Finset Real Filter

namespace ShortSieveThree

open ShortSieveTop ShortSieveLower ShortSieveTree ShortSieveLi

open Classical

/-- The terms of `S(I_{pq}, q)` with `m ≥ q`. -/
noncomputable def sBig (p q : ℕ) (x y : ℝ) : ℕ :=
  #{m ∈ Icc 1 ⌊x⌋₊ | q ≤ m ∧ SieveTree.rough q m ∧ x - y < ((p * q * m : ℕ) : ℝ) ∧ ((p * q * m : ℕ) : ℝ) ≤ x}

/-- `S(I_{pq}, q) = [pq ∈ I] + #{m ≥ q}` for a prime `q` and `x ≥ 1`. -/
theorem sD_eq (p : ℕ) {q : ℕ} (hq : q.Prime) {x : ℝ} (hx : 1 ≤ x) (y : ℝ) :
    sD (p * q) q x y = (if x - y < ((p * q : ℕ) : ℝ) ∧ ((p * q : ℕ) : ℝ) ≤ x then 1 else 0) + sBig p q x y := by
  unfold sD sBig
  rw [← card_filter_add_card_filter_not (fun m => m = 1)]
  congr 1
  · -- the term `m = 1`
    split_ifs with hw
    · rw [card_eq_one]
      refine ⟨1, ?_⟩
      ext m
      simp only [mem_filter, mem_Icc, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl
        refine ⟨⟨⟨le_rfl, Nat.one_le_iff_ne_zero.2 ?_⟩, fun r _ hr hd => hr.one_lt.ne' (Nat.dvd_one.1 hd), ?_⟩, rfl⟩
        · intro h; rw [Nat.floor_eq_zero] at h; linarith
        · simpa using hw
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro m hm hm1
      rw [mem_filter] at hm
      subst hm1
      exact hw (by simpa using hm.2.2)
  · -- the terms `m ≥ q`
    congr 1
    ext m
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hm, hr, hw⟩, hm1⟩
      refine ⟨hm, ?_, hr, hw⟩
      have hmp := Nat.minFac_prime hm1
      have h1 : q ≤ Nat.minFac m := by
        by_contra hlt
        exact hr _ (not_le.1 hlt) hmp (Nat.minFac_dvd m)
      exact le_trans h1 (Nat.minFac_le (by omega))
    · rintro ⟨hm, hqm, hr, hw⟩
      exact ⟨⟨hm, hr, hw⟩, by have := hq.two_le; omega⟩

/-- The products `pq ∈ I` of Li's third sum. -/
noncomputable def rOne (θ γ x y : ℝ) : ℕ :=
  ∑ p ∈ SieveTree.primesIco ⌈x ^ liNu θ γ 0⌉₊ (⌊Real.sqrt x⌋₊ + 1), ∑ q ∈ SieveTree.primesIco (lev θ γ x p) p,
    if x - y < ((p * q : ℕ) : ℝ) ∧ ((p * q : ℕ) : ℝ) ≤ x then 1 else 0

/-- The terms `m ≥ q` of Li's third sum. -/
noncomputable def bigThree (θ γ x y : ℝ) : ℕ :=
  ∑ p ∈ SieveTree.primesIco ⌈x ^ liNu θ γ 0⌉₊ (⌊Real.sqrt x⌋₊ + 1), ∑ q ∈ SieveTree.primesIco (lev θ γ x p) p,
    sBig p q x y

/-- **Li's third sum, split by the cofactor.** `Σ₃ = R₁ + Σ_p Σ_q #{m ≥ q}` for `x ≥ 1`. -/
theorem sThree_eq (θ γ : ℝ) {x : ℝ} (hx : 1 ≤ x) (y : ℝ) :
    sThree θ γ x y = rOne θ γ x y + bigThree θ γ x y := by
  unfold sThree rOne bigThree
  rw [← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun q hq => ?_
  exact sD_eq p (mem_filter.1 hq).2 hx y

/-- **The products have no loss.** For `0 < ρ < 1/2`, `R₁` is `OK` for `σ = 1` with loss `0`. -/
theorem OK_rOne {θ θ' γ ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2) : OK θ' ρ 1 (fun x y => (rOne θ γ x y : ℝ)) 0 := by
  refine OK_of_drop (fun _ _ => Nat.cast_nonneg _) fun δ hδ => ?_
  filter_upwards [eventually_gt_atTop 1, ShortSieveLower.eventually_log_le (r := ρ) (δ := δ / 4) hρ (by linarith),
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - ρ)).eventually_ge_atTop 1] with x hx1 hlx hxr
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos hx1
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = x ^ (1 - ρ) := ⟨_, rfl⟩
  rw [← hy₁]
  have hy₁0 : 0 < y₁ := by rw [hy₁]; exact Real.rpow_pos_of_pos hx0 _
  have hy₁x : y₁ ≤ x := by
    rw [hy₁]
    calc x ^ (1 - ρ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ = x := Real.rpow_one x
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlo0 : 0 ≤ (x - y₁) / Real.sqrt x := div_nonneg (by linarith) hs0.le
  obtain ⟨I, hI⟩ : ∃ I, I = Ioc ⌊(x - y₁) / Real.sqrt x⌋₊ ⌊Real.sqrt x⌋₊ := ⟨_, rfl⟩
  have hI' : ∀ r : ℕ, (x - y₁) / Real.sqrt x < r → (r : ℝ) ≤ Real.sqrt x → r ∈ I := fun r h1 h2 => by
    rw [hI, mem_Ioc]
    exact ⟨(Nat.floor_lt hlo0).2 h1, Nat.le_floor h2⟩
  -- the pairs lie in `I × I`
  have hmem : ∀ p ∈ SieveTree.primesIco ⌈x ^ liNu θ γ 0⌉₊ (⌊Real.sqrt x⌋₊ + 1),
      ∀ q ∈ SieveTree.primesIco (lev θ γ x p) p, x - y₁ < ((p * q : ℕ) : ℝ) → p ∈ I ∧ q ∈ I := by
    intro p hp q hq hw
    rw [SieveTree.primesIco, mem_filter, mem_Ico] at hp hq
    have hpx : (p : ℝ) ≤ Real.sqrt x :=
      le_trans (Nat.cast_le.2 (Nat.lt_succ_iff.1 hp.1.2)) (Nat.floor_le hs0.le)
    have hqp : (q : ℝ) ≤ p := by exact_mod_cast hq.1.2.le
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.2.pos
    push_cast at hw
    have hq1 : (x - y₁) / Real.sqrt x < q := by
      rw [div_lt_iff₀ hs0]
      calc x - y₁ < p * q := hw
        _ ≤ Real.sqrt x * q := mul_le_mul_of_nonneg_right hpx hq0.le
        _ = q * Real.sqrt x := mul_comm _ _
    exact ⟨hI' p (lt_of_lt_of_le hq1 hqp) hpx, hI' q hq1 (le_trans hqp hpx)⟩
  -- so `R₁ ≤ #I²`
  have hcount : rOne θ γ x y₁ ≤ #I * #I := by
    unfold rOne
    simp only [← card_filter]
    rw [← card_sigma, ← card_product]
    refine card_le_card_of_injOn (fun pq => (pq.1, pq.2)) (fun pq hpq => ?_) (fun a _ b _ h => ?_)
    · rw [mem_coe, mem_sigma, mem_filter] at hpq
      have := hmem pq.1 hpq.1 pq.2 hpq.2.1 hpq.2.2.1
      rw [mem_coe, mem_product]
      exact this
    · simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.1 (heq_of_eq h.2)
  -- `#I ≤ y₁/√x + 1 ≤ 2x^{1/2−ρ}`
  have hcardI : (#I : ℝ) ≤ 2 * x ^ (1 / 2 - ρ) := by
    have hle : ⌊(x - y₁) / Real.sqrt x⌋₊ ≤ ⌊Real.sqrt x⌋₊ := Nat.floor_le_floor (by
      rw [div_le_iff₀ hs0, hsq]; linarith)
    rw [hI, Nat.card_Ioc, Nat.cast_sub hle]
    have h1 : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le hs0.le
    have h2 : (x - y₁) / Real.sqrt x - 1 < ⌊(x - y₁) / Real.sqrt x⌋₊ := by
      have := Nat.lt_floor_add_one ((x - y₁) / Real.sqrt x); linarith
    have hy₁s : y₁ / Real.sqrt x = x ^ (1 / 2 - ρ) := by
      rw [hy₁, Real.sqrt_eq_rpow, ← Real.rpow_sub hx0]; congr 1; ring
    have hdiff : Real.sqrt x - (x - y₁) / Real.sqrt x = y₁ / Real.sqrt x := by
      field_simp; linarith
    linarith
  have hcI0 : (0 : ℝ) ≤ #I := Nat.cast_nonneg _
  have hx2 : x ^ (1 / 2 - ρ) * x ^ (1 / 2 - ρ) = x ^ (1 - 2 * ρ) := by rw [← Real.rpow_add hx0]; ring_nf
  have hx3 : x ^ (1 - 2 * ρ) * x ^ ρ = y₁ := by rw [hy₁, ← Real.rpow_add hx0]; ring_nf
  have h4 : 0 ≤ x ^ (1 - 2 * ρ) := Real.rpow_nonneg hx0.le _
  calc (rOne θ γ x y₁ : ℝ) ≤ (#I : ℝ) * #I := by exact_mod_cast hcount
    _ ≤ (2 * x ^ (1 / 2 - ρ)) * (2 * x ^ (1 / 2 - ρ)) := mul_le_mul hcardI hcardI hcI0 (by positivity)
    _ = 4 * x ^ (1 - 2 * ρ) := by rw [← hx2]; ring
    _ ≤ (0 + δ) * (y₁ / Real.log x) := by
        rw [zero_add, ← hx3, mul_div_assoc', le_div_iff₀ hlx0]
        nlinarith [mul_le_mul_of_nonneg_left hlx h4]

/-! ### Pairs of primes with a cofactor as a node -/

/-- The terms `m ≥ q` over the pairs of primes `p, q ≤ x` with `Φ p q`. -/
noncomputable def n2 (Φ : ℕ → ℕ → Prop) (x y : ℝ) : ℕ :=
  ∑ p ∈ SieveTypeIIU.primesLe ⌊x⌋₊, ∑ q ∈ SieveTypeIIU.primesLe ⌊x⌋₊, if Φ p q then sBig p q x y else 0

open ShortSieveNode in
/-- **A node of two primes and a cofactor.** If the conditions of the node `⟨2, 1, (· ↦ 1), conds⟩` (the cofactor
sifted by the second prime) hold exactly when `Φ p q` and the cofactor is at least `q`, its count is `n2 Φ`. -/
theorem count_eq_n2 (conds : List (Cond 2 1)) (Φ : ℕ → ℕ → Prop) (x y : ℝ)
    (h : ∀ p q ρ : ℕ, p.Prime → q.Prime → 1 ≤ ρ → ((∀ C ∈ conds, C.Holds x ![p, q] ![ρ]) ↔ Φ p q ∧ q ≤ ρ)) :
    (⟨2, 1, fun _ => 1, conds⟩ : Node).count x y = n2 Φ x y := by
  set L := SieveTypeIIU.primesLe ⌊x⌋₊ with hL
  set M : (ℕ × ℕ) → Finset ℕ := fun pq => {m ∈ Icc 1 ⌊x⌋₊ | pq.2 ≤ m ∧ SieveTree.rough pq.2 m ∧
    x - y < ((pq.1 * pq.2 * m : ℕ) : ℝ) ∧ ((pq.1 * pq.2 * m : ℕ) : ℝ) ≤ x} with hM
  have hn2 : n2 Φ x y = #(((L ×ˢ L).filter fun pq => Φ pq.1 pq.2).sigma M) := by
    unfold n2
    rw [card_sigma, sum_filter, sum_product]
    rfl
  rw [hn2]
  unfold Node.count
  refine card_nbij' (fun v => ⟨(v.1 0, v.1 1), v.2 0⟩) (fun w => (![w.1.1, w.1.2], ![w.2]))
    (fun v hv => ?_) (fun w hw => ?_) (fun v _ => ?_) (fun w _ => ?_)
  · rw [mem_coe, ShortSieveBuch.mem_filter_inst] at hv
    obtain ⟨hvp, hr, hI⟩ := hv
    obtain ⟨hcond, hlo, hhi⟩ := hI
    have hv1 : v.1 = ![v.1 0, v.1 1] := by funext i; fin_cases i <;> rfl
    have hv2 : v.2 = ![v.2 0] := by funext i; fin_cases i; rfl
    rw [hv1, hv2] at hcond
    obtain ⟨hp, hρ⟩ := ShortSieveBuch.mem_pairs.1 hvp
    obtain ⟨hΦ, hqρ⟩ := (h _ _ _ (hp 0).2 (hp 1).2 (hρ 0).1).1 hcond
    have hprod : prodP v = v.1 0 * v.1 1 * v.2 0 := by
      unfold prodP; rw [Fin.prod_univ_two, Fin.prod_univ_one]
    rw [mem_coe, mem_sigma, mem_filter, mem_product, hM, mem_filter, mem_Icc]
    refine ⟨⟨⟨?_, ?_⟩, hΦ⟩, hρ 0, hqρ, hr 0, ?_, ?_⟩
    · rw [hL, SieveTypeIIU.mem_primesLe]; exact ⟨(hp 0).1, (hp 0).2⟩
    · rw [hL, SieveTypeIIU.mem_primesLe]; exact ⟨(hp 1).1, (hp 1).2⟩
    · rw [← hprod]; exact hlo
    · rw [← hprod]; exact hhi
  · rw [mem_coe, mem_sigma, mem_filter, mem_product, hM, mem_filter, mem_Icc] at hw
    obtain ⟨⟨⟨hp, hq⟩, hΦ⟩, hρ, hqρ, hr, hlo, hhi⟩ := hw
    rw [hL, SieveTypeIIU.mem_primesLe] at hp hq
    rw [mem_coe, ShortSieveBuch.mem_filter_inst, ShortSieveBuch.mem_pairs]
    have hprod : prodP (![w.1.1, w.1.2], ![w.2]) = w.1.1 * w.1.2 * w.2 := by
      unfold prodP; rw [Fin.prod_univ_two, Fin.prod_univ_one]; rfl
    refine ⟨⟨fun a => ?_, fun i => ?_⟩, fun i => ?_, (h _ _ _ hp.2 hq.2 hρ.1).2 ⟨hΦ, hqρ⟩, ?_, ?_⟩
    · fin_cases a
      · exact ⟨hp.1, hp.2⟩
      · exact ⟨hq.1, hq.2⟩
    · fin_cases i; exact hρ
    · fin_cases i; exact hr
    · rw [hprod]; exact hlo
    · rw [hprod]; exact hhi
  · ext i <;> fin_cases i <;> rfl
  · rfl

/-- Predicates that agree on pairs of primes give the same `n2`. -/
theorem n2_congr {Φ Φ' : ℕ → ℕ → Prop} {x : ℝ} (y : ℝ) (h : ∀ p q, p.Prime → q.Prime → (Φ p q ↔ Φ' p q)) :
    n2 Φ x y = n2 Φ' x y := by
  unfold n2
  refine sum_congr rfl fun p hp => sum_congr rfl fun q hq => ?_
  rw [SieveTypeIIU.mem_primesLe] at hp hq
  exact if_congr (h p q hp.2 hq.2) rfl rfl

/-- Splitting `n2` by a predicate. -/
theorem n2_split (Φ Ψ : ℕ → ℕ → Prop) (x y : ℝ) :
    n2 Φ x y = n2 (fun p q => Φ p q ∧ Ψ p q) x y + n2 (fun p q => Φ p q ∧ ¬Ψ p q) x y := by
  unfold n2
  rw [← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun q _ => ?_
  by_cases hΦ : Φ p q <;> by_cases hΨ : Ψ p q <;> simp [hΦ, hΨ]

/-- **Cells.** If every pair of primes with `Φ` lies in exactly one cell `c ∈ S`, `n2 Φ` is the sum over the
cells. -/
theorem n2_eq_sum {ι : Type*} (S : Finset ι) (Φ : ℕ → ℕ → Prop) (Ψ : ι → ℕ → ℕ → Prop) (x y : ℝ)
    (h : ∀ p q, p.Prime → q.Prime → Φ p q → ∃ c ∈ S, Ψ c p q ∧ ∀ c' ∈ S, Ψ c' p q → c' = c) :
    n2 Φ x y = ∑ c ∈ S, n2 (fun p q => Φ p q ∧ Ψ c p q) x y := by
  unfold n2
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun q hq => ?_
  rw [SieveTypeIIU.mem_primesLe] at hp hq
  by_cases hΦ : Φ p q
  · obtain ⟨c, hc, hΨ, huniq⟩ := h p q hp.2 hq.2 hΦ
    rw [sum_eq_single c (fun c' hc' hne => ?_) (fun hc' => absurd hc hc')]
    · simp [hΦ, hΨ]
    · have : ¬Ψ c' p q := fun h' => hne (huniq c' hc' h')
      simp [this]
  · simp [hΦ]

/-- No terms `m ≥ q` when `pq² > x`. -/
theorem sBig_eq_zero {p q : ℕ} {x : ℝ} (y : ℝ) (h : x < ((p * q * q : ℕ) : ℝ)) : sBig p q x y = 0 := by
  unfold sBig
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro m - ⟨hqm, -, -, hm⟩
  have h1 : p * q * q ≤ p * q * m := Nat.mul_le_mul_left _ hqm
  have h2 : ((p * q * q : ℕ) : ℝ) ≤ ((p * q * m : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-- `n2` over pairs `p ∈ P`, `q ∈ Q p` inside the primes up to `x`. -/
theorem n2_mem (P : Finset ℕ) (Q : ℕ → Finset ℕ) (Ψ : ℕ → ℕ → Prop) {x : ℝ} (y : ℝ)
    (hP : P ⊆ SieveTypeIIU.primesLe ⌊x⌋₊) (hQ : ∀ p ∈ P, Q p ⊆ SieveTypeIIU.primesLe ⌊x⌋₊) :
    n2 (fun p q => p ∈ P ∧ q ∈ Q p ∧ Ψ p q) x y = ∑ p ∈ P, ∑ q ∈ Q p, if Ψ p q then sBig p q x y else 0 := by
  unfold n2
  refine (sum_subset hP fun p _ hp => sum_eq_zero fun q _ => by simp [hp]).symm.trans ?_
  refine sum_congr rfl fun p hp => ?_
  refine (sum_subset (hQ p hp) fun q _ hq => by simp [hq]).symm.trans ?_
  exact sum_congr rfl fun q hq => by simp [hp, hq]

/-- The pairs of Li's third sum, in logarithms: `x^{ν(0)} ≤ p ≤ √x`, `x^{ν(α_p)} ≤ q < p` and `pq² ≤ x`. -/
def PhiL (θ γ x : ℝ) (p q : ℕ) : Prop :=
  liNu θ γ 0 * Real.log x ≤ Real.log p ∧ 2 * Real.log p ≤ Real.log x ∧
    liNu θ γ (Real.log p / Real.log x) * Real.log x ≤ Real.log q ∧ Real.log q < Real.log p ∧
    Real.log p + 2 * Real.log q ≤ Real.log x

theorem phiL_iff (θ γ : ℝ) {x : ℝ} (hx : 1 < x) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    PhiL θ γ x p q ↔ p ∈ SieveTree.primesIco ⌈x ^ liNu θ γ 0⌉₊ (⌊Real.sqrt x⌋₊ + 1) ∧
      q ∈ SieveTree.primesIco (lev θ γ x p) p ∧ ¬x < ((p * q * q : ℕ) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have h1 : ∀ (a : ℝ) (n : ℕ), (0 : ℝ) < n → (⌈x ^ a⌉₊ ≤ n ↔ a * Real.log x ≤ Real.log n) := fun a n hn => by
    rw [Nat.ceil_le, ← Real.log_le_log_iff (Real.rpow_pos_of_pos hx0 a) hn, Real.log_rpow hx0]
  have h2 : p < ⌊Real.sqrt x⌋₊ + 1 ↔ 2 * Real.log p ≤ Real.log x := by
    rw [Nat.lt_succ_iff, Nat.le_floor_iff (Real.sqrt_nonneg x), ← Real.log_le_log_iff hp0 (Real.sqrt_pos.2 hx0),
      Real.log_sqrt hx0.le]
    constructor <;> intro h <;> linarith
  have h3 : q < p ↔ Real.log q < Real.log p := by
    rw [Real.log_lt_log_iff hq0 hp0, Nat.cast_lt]
  have h4 : ¬x < ((p * q * q : ℕ) : ℝ) ↔ Real.log p + 2 * Real.log q ≤ Real.log x := by
    rw [not_lt, ← Real.log_le_log_iff (by exact_mod_cast Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hq.pos) hx0]
    push_cast
    rw [Real.log_mul (mul_pos hp0 hq0).ne' hq0.ne', Real.log_mul hp0.ne' hq0.ne']
    constructor <;> intro h <;> linarith
  unfold PhiL lev
  rw [SieveTree.primesIco, SieveTree.primesIco, mem_filter, mem_filter, mem_Ico, mem_Ico, h1 _ _ hp0, h1 _ _ hq0,
    h2, h3, h4]
  tauto

/-- **Li's third sum as pairs of primes.** `Σ_p Σ_q #{m ≥ q} = n2 (PhiL θ γ x)` for `x > 1`. -/
theorem bigThree_eq_n2 (θ γ : ℝ) {x : ℝ} (hx : 1 < x) (y : ℝ) : bigThree θ γ x y = n2 (PhiL θ γ x) x y := by
  have hsq : ⌊Real.sqrt x⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (Real.sqrt_le_self_iff.2 (Or.inr hx.le))
  have hP : SieveTree.primesIco ⌈x ^ liNu θ γ 0⌉₊ (⌊Real.sqrt x⌋₊ + 1) ⊆ SieveTypeIIU.primesLe ⌊x⌋₊ := by
    intro p hp
    rw [SieveTree.primesIco, mem_filter, mem_Ico] at hp
    rw [SieveTypeIIU.mem_primesLe]
    exact ⟨by omega, hp.2⟩
  have hQ : ∀ p ∈ SieveTree.primesIco ⌈x ^ liNu θ γ 0⌉₊ (⌊Real.sqrt x⌋₊ + 1),
      SieveTree.primesIco (lev θ γ x p) p ⊆ SieveTypeIIU.primesLe ⌊x⌋₊ := by
    intro p hp q hq
    rw [SieveTree.primesIco, mem_filter, mem_Ico] at hp hq
    rw [SieveTypeIIU.mem_primesLe]
    exact ⟨by omega, hq.2⟩
  rw [n2_congr y fun p q hp hq => phiL_iff θ γ hx hp hq, n2_mem _ _ _ y hP hQ]
  unfold bigThree
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  by_cases h : x < ((p * q * q : ℕ) : ℝ)
  · simp [sBig_eq_zero y h]
  · simp only [h, not_false_eq_true, ↓reduceIte]

/-! ### The root cells at `θ = 13/25`, `γ = 2/25` -/

open ShortSieveNode

/-- The condition `e₀ log p + e₁ log q + f log ρ ≤ c log x` on two primes and a cofactor (`<` when `strict`). -/
noncomputable def lc (e₀ e₁ f c : ℝ) (strict : Bool) : Cond 2 1 :=
  ⟨![e₀, e₁], ![f], fun x => c * Real.log x, strict⟩

theorem holds_lc_lt {e₀ e₁ f c x : ℝ} {p q ρ : ℕ} : (lc e₀ e₁ f c true).Holds x ![p, q] ![ρ] ↔
    e₀ * Real.log p + e₁ * Real.log q + f * Real.log ρ < c * Real.log x := by
  simp only [lc, Cond.Holds, Cond.val, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, ↓reduceIte]

theorem holds_lc_le {e₀ e₁ f c x : ℝ} {p q ρ : ℕ} : (lc e₀ e₁ f c false).Holds x ![p, q] ![ρ] ↔
    e₀ * Real.log p + e₁ * Real.log q + f * Real.log ρ ≤ c * Real.log x := by
  simp only [lc, Cond.Holds, Cond.val, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Bool.false_eq_true, ↓reduceIte]

/-- Li's level on the cell `(k/50, (k + 1)/50]` of `α_p`, as a condition: `log q ≥ (2/25) log x` on `k = 23`, where
the level is `γ`, and `2 log p + (2h − 1) log q ≥ (26/25) log x`, `h = ⌊(26 − k)/2⌋`, on the others. -/
noncomputable def nuCond (k : ℕ) : Cond 2 1 :=
  if k = 23 then lc 0 (-1) 0 (-(2 / 25)) false
  else lc (-2) (1 - 2 * (((26 - k) / 2 : ℕ) : ℝ)) 0 (-(26 / 25)) false

/-- The region-`C` condition on the cell `k`: `log p + 3 log q < log x` for `k ≤ 19` (`α_p ≤ 2/5`), else
`2 log q < log p`. -/
noncomputable def regCond (k : ℕ) : Cond 2 1 :=
  if k ≤ 19 then lc 1 3 0 1 true else lc (-1) 2 0 0 true

/-- The conditions of the root cell `(k/50, (k + 1)/50] × [j/50, (j + 1)/50)` of `(α_p, α_q)` in region `C` (`r`) or
outside it (`¬r`): the cell, `α_p ≥ ν(0) = 26/625`, `q < p`, `pq² ≤ x`, Li's level, the region, and `q ≤ ρ`. -/
noncomputable def cellConds (k j : ℕ) (r : Bool) : List (Cond 2 1) :=
  [lc (-50) 0 0 (-k) true, lc 50 0 0 (k + 1) false, lc 0 (-50) 0 (-j) false, lc 0 50 0 (j + 1) true,
    lc (-1) 0 0 (-(26 / 625)) false, lc (-1) 1 0 0 true, lc 1 2 0 1 false, nuCond k,
    if r then regCond k else (regCond k).neg, lc 0 1 (-1) 0 false]

/-- The root cell as a node: primes `p` (index 0) and `q` (index 1), the cofactor sifted by `q`. -/
noncomputable def cell (k j : ℕ) (r : Bool) : Node := ⟨2, 1, fun _ => 1, cellConds k j r⟩

/-- The cell `(k/50, (k + 1)/50] × [j/50, (j + 1)/50)` of `(α_p, α_q)`, in logarithms. -/
def InCell (x : ℝ) (k j p q : ℕ) : Prop :=
  k * Real.log x < 50 * Real.log p ∧ 50 * Real.log p ≤ (k + 1) * Real.log x ∧
    j * Real.log x ≤ 50 * Real.log q ∧ 50 * Real.log q < (j + 1) * Real.log x

/-- Li's region `C` in `(α_p, α_q)`: `α_p + 3α_q < 1` for `α_p ≤ 2/5`, `2α_q < α_p` above. -/
def RegC (x : ℝ) (p q : ℕ) : Prop :=
  (5 * Real.log p ≤ 2 * Real.log x ∧ Real.log p + 3 * Real.log q < Real.log x) ∨
    (2 * Real.log x < 5 * Real.log p ∧ 2 * Real.log q < Real.log p)

/-- The cells: `2 ≤ k ≤ 24`, `2 ≤ j ≤ 12` in region `C`, `12 ≤ k ≤ 24`, `10 ≤ j ≤ 16` outside it. -/
def cells (r : Bool) : Finset (ℕ × ℕ) := if r then Icc 2 24 ×ˢ Icc 2 12 else Icc 12 24 ×ˢ Icc 10 16

theorem liNu_zero : liNu (13 / 25) (2 / 25) 0 = 26 / 625 := by
  unfold liNu
  have : ⌊(1 / 2 - 0 : ℝ) / (2 * (13 / 25) - 1)⌋₊ = 12 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  rw [this]
  norm_num

/-- Li's level on the cell `k`, `2 ≤ k ≤ 24`, of `α = P/L`. -/
theorem liNu_cell {k : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ 24) {L P Q : ℝ} (hL : 0 < L) (h1 : k * L < 50 * P)
    (h2 : 50 * P ≤ (k + 1) * L) :
    liNu (13 / 25) (2 / 25) (P / L) * L ≤ Q ↔
      if k = 23 then 2 / 25 * L ≤ Q else 26 / 25 * L ≤ 2 * P + (2 * (((26 - k) / 2 : ℕ) : ℝ) - 1) * Q := by
  set h := (26 - k) / 2 with hh
  have hh1 : 1 ≤ h := by omega
  have hpar : 2 * h + k = 26 ∨ 2 * h + k = 25 := by omega
  have hpar' : 2 * (h : ℝ) + k = 26 ∨ 2 * (h : ℝ) + k = 25 := by
    rcases hpar with e | e
    · left; exact_mod_cast e
    · right; exact_mod_cast e
  have hα1 : (k : ℝ) / 50 < P / L := by rw [div_lt_div_iff₀ (by norm_num) hL]; linarith
  have hα2 : P / L ≤ ((k : ℝ) + 1) / 50 := by rw [div_le_div_iff₀ hL (by norm_num)]; linarith
  rw [ShortSieveRoot.liNu_eq_nuPiece (θ := 13 / 25) (γ := 2 / 25) (h := h) (by norm_num) hh1
    (by rcases hpar' with e | e <;> linarith) (by rcases hpar' with e | e <;> linarith)]
  unfold ShortSieveRoot.nuPiece
  have hh1' : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hd : 0 < 2 * (h : ℝ) - 1 := by linarith
  have hPL : P / L * L = P := div_mul_cancel₀ P hL.ne'
  split_ifs with hk23
  · have h1' : h = 1 := by omega
    have h1'' : (h : ℝ) = 1 := by exact_mod_cast h1'
    have hk' : (k : ℝ) = 23 := by exact_mod_cast hk23
    rw [min_eq_right (by rw [h1'']; rw [hk'] at hα2; linarith)]
  · have h28 : 28 ≤ k + 4 * h := by omega
    have h28' : (28 : ℝ) ≤ k + 4 * h := by exact_mod_cast h28
    rw [min_eq_left (by rw [div_le_iff₀ hd]; nlinarith)]
    have key : 2 * (13 / 25 - P / L) / (2 * (h : ℝ) - 1) * L = (26 / 25 * L - 2 * P) / (2 * h - 1) := by
      field_simp
      ring
    rw [key, div_le_iff₀ hd]
    constructor <;> intro h' <;> nlinarith

/-- The region condition of the cell `k` is region `C`. -/
theorem regCond_iff {k : ℕ} {x : ℝ} (hlx : 0 < Real.log x) {p q ρ : ℕ} (h1 : k * Real.log x < 50 * Real.log p)
    (h2 : 50 * Real.log p ≤ (k + 1) * Real.log x) : (regCond k).Holds x ![p, q] ![ρ] ↔ RegC x p q := by
  unfold regCond RegC
  split_ifs with hk
  · rw [holds_lc_lt]
    have hk' : (k : ℝ) ≤ 19 := by exact_mod_cast hk
    have h5 : 5 * Real.log p ≤ 2 * Real.log x := by nlinarith
    constructor
    · intro h; left; exact ⟨h5, by linarith⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> linarith
  · rw [holds_lc_lt]
    have hk' : (20 : ℝ) ≤ k := by exact_mod_cast (by omega : 20 ≤ k)
    have h5 : 2 * Real.log x < 5 * Real.log p := by nlinarith
    constructor
    · intro h; right; exact ⟨h5, by linarith⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> linarith

/-- The conditions of the cell `(k, j)` are the pairs of Li's third sum in that cell and region, with `q ≤ ρ`. -/
theorem cell_iff {k j : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ 24) (r : Bool) {x : ℝ} (hx : 1 < x) {p q ρ : ℕ}
    (hq : q.Prime) (hρ : 1 ≤ ρ) :
    (∀ C ∈ cellConds k j r, C.Holds x ![p, q] ![ρ]) ↔
      ((PhiL (13 / 25) (2 / 25) x p q ∧ (if r then RegC x p q else ¬RegC x p q)) ∧ InCell x k j p q) ∧ q ≤ ρ := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hqρ : q ≤ ρ ↔ Real.log q ≤ Real.log ρ := by rw [Real.log_le_log_iff hq0 hρ0, Nat.cast_le]
  have hk24 : (k : ℝ) ≤ 24 := by exact_mod_cast hk
  simp only [cellConds, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, holds_lc_lt,
    holds_lc_le]
  unfold PhiL InCell
  rw [liNu_zero]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    have c1 : k * Real.log x < 50 * Real.log p := by linarith
    have c2 : 50 * Real.log p ≤ (k + 1) * Real.log x := by linarith
    have hnu := liNu_cell hk2 hk hlx c1 c2 (Q := Real.log q)
    have hreg := regCond_iff (q := q) (ρ := ρ) hlx c1 c2
    refine ⟨⟨⟨⟨by linarith, by nlinarith, hnu.2 ?_, by linarith, by linarith⟩, ?_⟩, c1, c2, by linarith,
      by linarith⟩, hqρ.2 (by linarith)⟩
    · unfold nuCond at a8
      split_ifs at a8 ⊢ with hk23
      · rw [holds_lc_le] at a8; linarith
      · rw [holds_lc_le] at a8; linarith
    · cases r
      · simp only [Bool.false_eq_true, ↓reduceIte] at a9 ⊢
        rwa [holds_neg, hreg] at a9
      · simp only [↓reduceIte] at a9 ⊢
        rwa [hreg] at a9
  · rintro ⟨⟨⟨⟨b1, b2, b3, b4, b5⟩, b6⟩, c1, c2, c3, c4⟩, b7⟩
    have hnu := liNu_cell hk2 hk hlx c1 c2 (Q := Real.log q)
    have hreg := regCond_iff (q := q) (ρ := ρ) hlx c1 c2
    have b7' := hqρ.1 b7
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_,
      by linarith⟩
    · have h8 := hnu.1 b3
      unfold nuCond
      split_ifs at h8 ⊢ with hk23
      · rw [holds_lc_le]; linarith
      · rw [holds_lc_le]; linarith
    · cases r
      · simp only [Bool.false_eq_true, ↓reduceIte] at b6 ⊢
        rwa [holds_neg, hreg]
      · simp only [↓reduceIte] at b6 ⊢
        rwa [hreg]

/-- Every pair of Li's third sum lies in exactly one cell of `cells r`, `r` its region. -/
theorem exists_cell {x : ℝ} (hx : 1 < x) {p q : ℕ} (r : Bool)
    (h : PhiL (13 / 25) (2 / 25) x p q ∧ (if r then RegC x p q else ¬RegC x p q)) :
    ∃ c ∈ cells r, InCell x c.1 c.2 p q ∧ ∀ c' ∈ cells r, InCell x c'.1 c'.2 p q → c' = c := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, hr⟩ := h
  rw [liNu_zero] at h1
  have hP2 : Real.log p / Real.log x ≤ 1 / 2 := by rw [div_le_iff₀ hlx]; linarith
  have hnu := ShortSieveTypeI.le_liNu (θ := 13 / 25) (γ := 2 / 25) (by norm_num) (by norm_num) hP2
  have hQ : Real.log x / 25 ≤ Real.log q := by nlinarith
  set t := 50 * Real.log p / Real.log x with ht
  set u := 50 * Real.log q / Real.log x with hu
  have ht1 : 2 < t := by rw [ht, lt_div_iff₀ hlx]; linarith
  have ht2 : t ≤ 25 := by rw [ht, div_le_iff₀ hlx]; linarith
  have hu1 : 2 ≤ u := by rw [hu, le_div_iff₀ hlx]; linarith
  have hu2 : u < 17 := by rw [hu, div_lt_iff₀ hlx]; linarith
  -- the region's bounds
  have hreg : (r = true → u < 13) ∧ (r = false → 12 < t ∧ 10 ≤ u) := by
    cases r
    · simp only [Bool.false_eq_true, ↓reduceIte, RegC, not_or, not_and, not_lt] at hr
      refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      by_cases hA : 5 * Real.log p ≤ 2 * Real.log x
      · have := hr.1 hA
        constructor
        · rw [ht, lt_div_iff₀ hlx]; linarith
        · rw [hu, le_div_iff₀ hlx]; linarith
      · have hA' : 2 * Real.log x < 5 * Real.log p := not_le.1 hA
        have := hr.2 hA'
        constructor
        · rw [ht, lt_div_iff₀ hlx]; linarith
        · rw [hu, le_div_iff₀ hlx]; linarith
    · simp only [↓reduceIte, RegC] at hr
      refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
      rw [hu, div_lt_iff₀ hlx]
      rcases hr with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  set k := ⌈t⌉₊ - 1 with hk
  set j := ⌊u⌋₊ with hj
  have hc1 : 2 < ⌈t⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast ht1)
  have hc2 : ⌈t⌉₊ ≤ 25 := Nat.ceil_le.2 (by exact_mod_cast ht2)
  have hkR : (k : ℝ) = ⌈t⌉₊ - 1 := by rw [hk, Nat.cast_sub (by omega), Nat.cast_one]
  have hk1 : (k : ℝ) < t := by rw [hkR]; linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ t)]
  have hk2 : t ≤ k + 1 := by rw [hkR]; linarith [Nat.le_ceil t]
  have hj1 : (j : ℝ) ≤ u := Nat.floor_le (by linarith)
  have hj2 : u < j + 1 := Nat.lt_floor_add_one u
  have hj3 : 2 ≤ j := Nat.le_floor (by exact_mod_cast hu1)
  have hcell : InCell x k j p q := by
    rw [ht] at hk1 hk2
    rw [hu] at hj1 hj2
    exact ⟨(lt_div_iff₀ hlx).1 hk1, (div_le_iff₀ hlx).1 hk2, (le_div_iff₀ hlx).1 hj1, (div_lt_iff₀ hlx).1 hj2⟩
  refine ⟨(k, j), ?_, hcell, fun c' _ hc' => ?_⟩
  · cases r
    · obtain ⟨h12, h10⟩ := hreg.2 rfl
      have : 12 < ⌈t⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast h12)
      have : 10 ≤ j := Nat.le_floor (by exact_mod_cast h10)
      have : j < 17 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast hu2)
      simp only [cells, Bool.false_eq_true, ↓reduceIte, mem_product, mem_Icc]
      omega
    · have : j < 13 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast hreg.1 rfl)
      simp only [cells, ↓reduceIte, mem_product, mem_Icc]
      omega
  · obtain ⟨k', j'⟩ := c'
    obtain ⟨a1, a2, a3, a4⟩ := hc'
    obtain ⟨b1, b2, b3, b4⟩ := hcell
    have e1 : (k' : ℝ) < k + 1 :=
      lt_of_mul_lt_mul_right (by linarith : (k' : ℝ) * Real.log x < (k + 1) * Real.log x) hlx.le
    have e2 : (k : ℝ) < k' + 1 :=
      lt_of_mul_lt_mul_right (by linarith : (k : ℝ) * Real.log x < (k' + 1) * Real.log x) hlx.le
    have e3 : (j' : ℝ) < j + 1 :=
      lt_of_mul_lt_mul_right (by linarith : (j' : ℝ) * Real.log x < (j + 1) * Real.log x) hlx.le
    have e4 : (j : ℝ) < j' + 1 :=
      lt_of_mul_lt_mul_right (by linarith : (j : ℝ) * Real.log x < (j' + 1) * Real.log x) hlx.le
    have f1 : k' < k + 1 := by exact_mod_cast e1
    have f2 : k < k' + 1 := by exact_mod_cast e2
    have f3 : j' < j + 1 := by exact_mod_cast e3
    have f4 : j < j' + 1 := by exact_mod_cast e4
    simp only [Prod.mk.injEq]
    omega

/-- **The root cells.** At `θ = 13/25`, `γ = 2/25` and `x > 1`, the terms `m ≥ q` of Li's third sum are the counts of
the root cells: `253` in region `C` and `91` outside it. -/
theorem bigThree_eq_cells {x : ℝ} (hx : 1 < x) (y : ℝ) :
    bigThree (13 / 25) (2 / 25) x y =
      ∑ c ∈ cells true, (cell c.1 c.2 true).count x y + ∑ c ∈ cells false, (cell c.1 c.2 false).count x y := by
  have key : ∀ r : Bool,
      n2 (fun p q => PhiL (13 / 25) (2 / 25) x p q ∧ (if r then RegC x p q else ¬RegC x p q)) x y =
        ∑ c ∈ cells r, (cell c.1 c.2 r).count x y := fun r => by
    rw [n2_eq_sum (cells r) _ (fun c p q => InCell x c.1 c.2 p q) x y fun p q _ _ h => exists_cell hx r h]
    refine sum_congr rfl fun c hc => ?_
    have hk : 2 ≤ c.1 ∧ c.1 ≤ 24 := by
      cases r <;> simp only [cells, Bool.false_eq_true, ↓reduceIte, mem_product, mem_Icc] at hc <;> omega
    exact (count_eq_n2 _ _ x y fun p q ρ _ hq hρ => cell_iff hk.1 hk.2 r hx hq hρ).symm
  rw [bigThree_eq_n2 _ _ hx, n2_split _ (RegC x), ← key true, ← key false]
  simp only [↓reduceIte, Bool.false_eq_true]

/-- **Li's third sum from its root cells.** If every root cell is `OK` for `σ = 1` with loss `L r c`, so is `Σ₃`,
with the sum of the losses. -/
theorem OK_sThree {θ ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2) (hθρ : θ ≤ 1 - ρ) (L : Bool → ℕ × ℕ → ℝ)
    (h : ∀ r, ∀ c ∈ cells r, OK θ ρ 1 (fun x y => ((cell c.1 c.2 r).count x y : ℝ)) (L r c)) :
    OK θ ρ 1 (fun x y => (sThree (13 / 25) (2 / 25) x y : ℝ))
      (∑ c ∈ cells true, L true c + ∑ c ∈ cells false, L false c) := by
  have h3 := OK_add (OK_rOne (θ := 13 / 25) (γ := 2 / 25) hρ hρ2)
    (OK_add (OK_sum (cells true) _ _ hθρ (h true)) (OK_sum (cells false) _ _ hθρ (h false)))
  rw [zero_add] at h3
  refine OK_congr ?_ hθρ h3
  filter_upwards [eventually_gt_atTop 1] with x hx y _ _
  rw [sThree_eq _ _ hx.le, bigThree_eq_cells hx]
  push_cast
  ring

/-- `ν(α) ≤ α` on `[ν(0), 1/2]` at `θ = 13/25`, `γ = 2/25`. -/
theorem liNu_le_self : ∀ α ∈ Set.Icc (liNu (13 / 25) (2 / 25) 0) (1 / 2), liNu (13 / 25) (2 / 25) α ≤ α := by
  rintro α ⟨h1, -⟩
  rw [liNu_zero] at h1
  by_cases hα : 2 / 25 ≤ α
  · exact le_trans (min_le_right _ _) hα
  · have hα' : α < 2 / 25 := not_le.1 hα
    unfold liNu
    have ht : (1 / 2 - α) / (2 * (13 / 25 : ℝ) - 1) = 25 * (1 / 2 - α) := by
      rw [show (2 * (13 / 25 : ℝ) - 1) = 1 / 25 by norm_num]; ring
    rw [ht]
    refine le_trans (min_le_left _ _) ?_
    by_cases hα6 : α ≤ 3 / 50
    · have hn : 11 ≤ ⌊25 * (1 / 2 - α)⌋₊ := Nat.le_floor (by push_cast; linarith)
      have hn' : (11 : ℝ) ≤ ⌊25 * (1 / 2 - α)⌋₊ := by exact_mod_cast hn
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    · have hn : 10 ≤ ⌊25 * (1 / 2 - α)⌋₊ := Nat.le_floor (by push_cast; linarith)
      have hn' : (10 : ℝ) ≤ ⌊25 * (1 / 2 - α)⌋₊ := by exact_mod_cast hn
      rw [div_le_iff₀ (by linarith)]
      nlinarith

/-- **Primes in short intervals from the root cells.** At `θ = 13/25`, `γ = 2/25`, given Li's Lemma 3.1 and every root
cell `OK` with loss `L r c`: `π(x) − π(x − y) ≥ (1 − Σ L − ε) y/log x` for `x^{13/25} ≤ y ≤ x^{1−ρ}`. -/
theorem primes_of_cells {ρ : ℝ} (hLi : LiLemma31 (13 / 25) (2 / 25) ρ) (hρ : 0 < ρ) (hρθ : 12 * ρ < 1 / 25)
    (L : Bool → ℕ × ℕ → ℝ)
    (h : ∀ r, ∀ c ∈ cells r, OK (13 / 25) ρ 1 (fun x y => ((cell c.1 c.2 r).count x y : ℝ)) (L r c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ (13 / 25 : ℝ) ≤ y → y ≤ x ^ (1 - ρ) →
      (1 - (∑ c ∈ cells true, L true c + ∑ c ∈ cells false, L false c) - ε) * y / Real.log x ≤
        ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
  have hOK := OK_sThree (θ := 13 / 25) hρ (by linarith) (by linarith) L h
  refine primes_lower hLi (by norm_num) (by norm_num) (by norm_num) (by norm_num) hρ (by linarith) liNu_le_self ?_
  intro ε hε
  filter_upwards [hOK ε hε] with x hx y hy1 hy2
  have := hx y hy1 hy2
  linarith

end ShortSieveThree

#print axioms ShortSieveThree.sThree_eq
#print axioms ShortSieveThree.OK_rOne
#print axioms ShortSieveThree.bigThree_eq_cells
#print axioms ShortSieveThree.primes_of_cells
