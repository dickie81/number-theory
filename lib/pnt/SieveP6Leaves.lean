/-
# Proposition 6 with the bilinear estimate: the large leaves

Plain statements. `T w J j` are `SieveLeaf`'s ranges, `wS₁`, `wS₂`, `wl₁`, `wl₂`, `wf`, `wf₂` and `Rs` are Brun's
weights and the sifted indicator of `SieveTypeIBBrun`, at the levels `lev k J j = k + 2j`; `rng`, `dwR`, `dv` and `gU`
are `SieveTypeIBLeaf`'s, `Jw w` and `rem` are `SieveProp6`'s.

* `Rs_T_eq`: for `w ≥ 1` with `w^{2^{−J}} ≤ 2`, the sifted indicator of the ranges is `1[m has no prime factor below
  ⌈w⌉]`.
* `count_eq_rsum`: a leaf's count `Σ_{n∈(N₁,N₂]} dw(n)·1[d ∣ n, n has no prime factor below w]`, for `d ≥ 1` with no
  prime factor below `w`, is `Σ_{m≤N₂} rng(d, m)R(m)dw(dm)` with `R` the sifted indicator.
* `wf_inj`: on indices whose sets lie in the ranges and have the sizes they record, `σ ↦ f_σ` is injective.
* `wf_le`: for `w ≥ 1`, the moduli of the weights above and below are at most `w^{2k+4}`.
* `W_le`: `Σ|λ_σ| + Σ|λ_x| ≤ 2·rem`, since the weights below number at most `J + 1` times the weights above
  (`card_wS₂_le`).
* `V_le`: `Σ|λ_σ|/f_σ + Σ|λ_x|/f_x ≤ (J + 2)∏_j ∏_{p∈T_j} (1 + 1/p)`. `prod_T_one_add_le`: for `w ≥ 1` and `C₀`
  bounding the sums `Σ 1/p` over the ranges `rng A`, the product is at most `e^{C₀(⌊log₂⌊log₂ w⌋⌋ + 1)}`, since a
  range with a prime has `2^{2^j} < w` (`card_nonempty_le`). `V_poly_le`: for `1 ≤ w ≤ x`,
  `(Jw(w) + 2)e^{C₀(⌊log₂⌊log₂ w⌋⌋ + 1)} ≤ (3 + 4 log x)^{2m+2}`, `m = ⌈C₀/log 2⌉`.
* `abs_gap_le`: for `w ≥ 2` with `w^{2^{−J}} ≤ 2`, `k ≥ 1` even and `2C₀² ≤ (k + 1)(k + 2)`, the weights' gap
  `|Σ λ_σ gU(f_σ)/f_σ − Σ λ_x gU(f_x)/f_x|` is at most `ζ(k)q/(φ(q) log w)` (`gap_eq`, `SieveLeaf.leaf_gap`,
  `SieveLeaf.prod_T_le`).
* `fibre_wS₁_le`, `fibre_wS₂_le`: for a set `Y` of decreasing tuples of primes, the pairs `(y, σ)` with `∏y·f_σ = d`
  number at most `d(d)`, and the pairs `(y, x)` with `∏y·f_x = d` at most `(J + 1)d(d)`. `card_fibre_le_one`: a
  decreasing tuple of primes is determined by its product.
* `W_le_rpow`, `V_le_rpow`, `fibres_le_rpow`: the three bounds at a power of `x`, for `J = Jw w`.
* `leaves_chain`: `SieveTypeIBAsym.leaves_ib` with these weights, at `w = ⌈q^{εw}⌉`, `J = Jw w` and
  `(2k + 4)εw ≤ 1/16`, for two sets of decreasing tuples of primes in `[w, ⌊2q^L⌋]`: the leaves `d = ∏y₁∏y₂` total at
  most `ζ(k)(N₂ − N₁)/(φ(q) log w)·Σ 1/d + q^{L−δ}/φ(q)` in absolute value.

The file imports `SieveP6Chain.lean`, `SieveTypeIBAsym.lean` and `SieveTypeIBBrun.lean`.
-/
import SieveP6Chain
import SieveTypeIBAsym
import SieveTypeIBBrun

open Real Finset SieveFamily SieveTree SieveChain SieveBrun SieveTypeIBLeaf SieveTypeIBBrun

namespace SieveP6Leaves

/-! ### A leaf's count -/

/-- The sifted indicator of the ranges is `1[m has no prime factor below ⌈w⌉]`. -/
theorem Rs_T_eq {w : ℝ} (hw : 1 ≤ w) {J : ℕ} (hJ : w ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (m : ℕ) :
    Rs (SieveLeaf.T w J) m = if rough ⌈w⌉₊ m then 1 else 0 := by
  have hiff := SieveLeaf.sifted_iff hw hJ m
  unfold Rs
  by_cases h : rough ⌈w⌉₊ m
  · rw [ite_eq_left h]
    refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun p hp => ?_
    have : ¬ p ∣ m := hiff.2 h j p hp
    simp [ind, this]
  · rw [ite_eq_right h]
    have h' : ¬ ∀ j, ∀ p ∈ SieveLeaf.T w J j, ¬ p ∣ m := fun h'' => h (hiff.1 h'')
    push Not at h'
    obtain ⟨j, p, hp, hpm⟩ := h'
    refine Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero hp ?_)
    simp [ind, hpm]

/-- **A leaf's count.** For `d ≥ 1` with no prime factor below `w ≥ 1` and `w^{2^{−J}} ≤ 2`:
`Σ_{n∈(N₁,N₂]} dw(n)·1[d ∣ n, n has no prime factor below w] = Σ_{m≤N₂} rng(d, m)R(m)dw(dm)`. -/
theorem count_eq_rsum (q : ℕ) [NeZero q] (a : ZMod q) (N₁ N₂ : ℕ) {d w J : ℕ} (hd : 1 ≤ d) (hw : 1 ≤ w)
    (hJ : (w : ℝ) ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (hdw : rough w d) :
    ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if d ∣ n ∧ rough w n then 1 else 0) =
      ((∑ m ∈ Finset.range (N₂ + 1), rng N₁ N₂ d m * Rs (SieveLeaf.T (w : ℝ) J) m * dwR q a (d * m) : ℝ) :
        ℂ) := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  rw [sum_mult_eq (dw q a) (by omega) hdw, Finset.sum_filter]
  push_cast
  have hR : ∀ m, Rs (SieveLeaf.T (w : ℝ) J) m = if rough w m then 1 else 0 := fun m => by
    rw [Rs_T_eq hw' hJ m, Nat.ceil_natCast]
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 N₂) (s₂ := Finset.range (N₂ + 1))]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [hR m, rng, dw_eq]
    have hr : (∀ p' < w, p'.Prime → ¬ p' ∣ m) ↔ rough w m := Iff.rfl
    by_cases h1 : rough w m <;> by_cases h2 : N₁ < d * m ∧ d * m ≤ N₂ <;>
      simp [h1, h2, hr, dwR]
  · intro m hm
    rw [Finset.mem_Icc] at hm
    exact Finset.mem_range.2 (by omega)
  · intro m _ hm
    have hm0 : m = 0 := by
      rw [Finset.mem_Icc] at hm
      by_contra h
      exact hm ⟨by omega, by
        have := Finset.mem_range.1 ‹m ∈ Finset.range (N₂ + 1)›
        omega⟩
    subst hm0
    simp [rng]

/-! ### Brun's weights over the ranges -/

section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An index of the weights above has, at each range, a set of the size it records. -/
theorem card_of_mem_wS₁ {T : ι → Finset ℕ} {k : ι → ℕ} {σ : Idx ι} (hσ : σ ∈ wS₁ T k) (j : ι) :
    (σ j).2.card = (σ j).1 := by
  have h := Fintype.mem_piFinset.1 hσ j
  rw [Ftr, Finset.mem_sigma] at h
  exact (Finset.mem_powersetCard.1 h.2).2

/-- A prime of a range divides `f_σ` iff it is in `σ`'s set at that range. -/
theorem dvd_wf_iff {T : ι → Finset ℕ} (hT : ∀ j, ∀ p ∈ T j, p.Prime) (hdisj : (Set.univ : Set ι).PairwiseDisjoint T)
    {σ : Idx ι} (hσ : ∀ j, (σ j).2 ⊆ T j) {j : ι} {p : ℕ} (hp : p ∈ T j) : p ∣ wf σ ↔ p ∈ (σ j).2 := by
  have hpp := hT j p hp
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 h
    obtain ⟨p', hp', hd⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hi
    have hp'p := (Nat.prime_dvd_prime_iff_eq hpp (hT i p' (hσ i hp'))).1 hd
    subst hp'p
    by_cases hij : i = j
    · subst hij
      exact hp'
    · exact absurd (Finset.disjoint_left.1 (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) (hσ i hp')) (by
        simpa using hp)
  · intro h
    exact dvd_trans (Finset.dvd_prod_of_mem _ h) (Finset.dvd_prod_of_mem (fun i => ∏ p ∈ (σ i).2, p)
      (Finset.mem_univ j))

/-- **The moduli of the weights are distinct**: on indices whose sets lie in the ranges and have the recorded sizes,
`σ ↦ f_σ` is injective. -/
theorem wf_inj {T : ι → Finset ℕ} (hT : ∀ j, ∀ p ∈ T j, p.Prime) (hdisj : (Set.univ : Set ι).PairwiseDisjoint T)
    {σ σ' : Idx ι} (hσ : ∀ j, (σ j).2 ⊆ T j) (hσ' : ∀ j, (σ' j).2 ⊆ T j)
    (hc : ∀ j, (σ j).2.card = (σ j).1) (hc' : ∀ j, (σ' j).2.card = (σ' j).1) (h : wf σ = wf σ') : σ = σ' := by
  funext j
  have hset : (σ j).2 = (σ' j).2 := by
    ext p
    constructor
    · intro hp
      have hpT := hσ j hp
      rw [← dvd_wf_iff hT hdisj hσ' hpT, ← h, dvd_wf_iff hT hdisj hσ hpT]
      exact hp
    · intro hp
      have hpT := hσ' j hp
      rw [← dvd_wf_iff hT hdisj hσ hpT, h, dvd_wf_iff hT hdisj hσ' hpT]
      exact hp
  have hfst : (σ j).1 = (σ' j).1 := by rw [← hc j, ← hc' j, hset]
  exact Sigma.ext hfst (heq_of_eq hset)

end Weights

/-! ### The weights' sizes -/

section Counts

theorem Fes_sub_Ftr {T : Finset ℕ} {k : ℕ} {b : Σ _ : ℕ, Finset ℕ} (hb : b ∈ Fes T k) : b ∈ Ftr T k := by
  rw [Fes, Finset.mem_sigma, Finset.mem_singleton] at hb
  rw [Ftr, Finset.mem_sigma, Finset.mem_range]
  exact ⟨by rw [hb.1]; exact Nat.lt_succ_self k, hb.2⟩

/-- `Σ_σ |λ_σ| = ∏_j Σ_{i ≤ k_j} C(|T_j|, i)`. -/
theorem sum_abs_wl₁ {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Finset ℕ) (k : ι → ℕ) :
    ∑ σ ∈ wS₁ T k, |wl₁ σ| = ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T j).card.choose i : ℝ) := by
  have e : ∀ σ : Idx ι, |wl₁ σ| = ∏ j, |(-1 : ℝ) ^ (σ j).1| := fun σ => by rw [wl₁, Finset.abs_prod]
  rw [Finset.sum_congr rfl fun σ _ => e σ, wS₁,
    ← Finset.prod_univ_sum (fun j => Ftr (T j) (k j)) fun _ (b : Σ _ : ℕ, Finset ℕ) => |(-1 : ℝ) ^ b.1|]
  exact Finset.prod_congr rfl fun j _ => abs_Ftr (T j) (k j)

/-- The weights below number at most `|ι| + 1` times the weights above. -/
theorem card_wS₂_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Finset ℕ) (k : ι → ℕ) :
    (wS₂ T k).card ≤ (Fintype.card ι + 1) * (wS₁ T k).card := by
  have hcorr : ∀ j, corr T k j ⊆ wS₁ T k := fun j σ hσ => by
    rw [corr, Fintype.mem_piFinset] at hσ
    rw [wS₁, Fintype.mem_piFinset]
    intro i
    have h := hσ i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self] at h
      exact Fes_sub_Ftr h
    · rw [Function.update_of_ne hij] at h
      exact h
  have h1 : (wS₂ T k).card ≤ (wS₁ T k).card + Fintype.card ι * (wS₁ T k).card := by
    rw [wS₂]
    refine (Finset.card_union_le _ _).trans (add_le_add (Finset.card_map _).le ?_)
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ j ∈ (univ : Finset ι), ((corr T k j).map (embS j)).card ≤ ∑ _j ∈ (univ : Finset ι), (wS₁ T k).card :=
          Finset.sum_le_sum fun j _ => by rw [Finset.card_map]; exact Finset.card_le_card (hcorr j)
      _ = Fintype.card ι * (wS₁ T k).card := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc (wS₂ T k).card ≤ (wS₁ T k).card + Fintype.card ι * (wS₁ T k).card := h1
    _ = (Fintype.card ι + 1) * (wS₁ T k).card := by ring

/-- A decreasing tuple of primes has its entries as its product's prime factors. -/
theorem primeFactors_prod_eq {K : ℕ} {y : Fin K → ℕ} (hy : Function.Injective y) (hp : ∀ i, (y i).Prime) :
    (∏ i, y i).primeFactors = Finset.univ.image y := by
  have e : ∏ u, y u = ∏ p ∈ Finset.univ.image y, p :=
    (Finset.prod_image (f := fun p => p) (fun u _ v _ h => hy h)).symm
  rw [e]
  exact Nat.primeFactors_prod fun p hp' => by
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp'
    exact hp u

/-- A decreasing tuple of primes is determined by its product. -/
theorem eq_of_prod_eq {K : ℕ} {y y' : Fin K → ℕ} (hy : StrictAnti y) (hy' : StrictAnti y') (hp : ∀ i, (y i).Prime)
    (hp' : ∀ i, (y' i).Prime) (h : ∏ i, y i = ∏ i, y' i) : y = y' := by
  rw [← SieveStops2.desc_image hy, ← SieveStops2.desc_image hy', ← primeFactors_prod_eq hy.injective hp,
    ← primeFactors_prod_eq hy'.injective hp', h]

/-- A product of primes at least `w` has no prime factor below `w`. -/
theorem rough_prod {K : ℕ} {y : Fin K → ℕ} {w : ℕ} (hp : ∀ i, (y i).Prime) (hw : ∀ i, w ≤ y i) :
    rough w (∏ i, y i) := by
  intro p hpw hpp hd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hd
  have := (Nat.prime_dvd_prime_iff_eq hpp (hp i)).1 hi
  have := hw i
  omega

theorem one_le_prod {K : ℕ} {y : Fin K → ℕ} (hp : ∀ i, (y i).Prime) : 1 ≤ ∏ i, y i :=
  Finset.one_le_prod fun i _ => (hp i).one_lt.le

theorem rough_mul {w a b : ℕ} (ha : rough w a) (hb : rough w b) : rough w (a * b) := by
  intro p hpw hpp hd
  rcases (Nat.Prime.dvd_mul hpp).1 hd with h | h
  · exact ha p hpw hpp h
  · exact hb p hpw hpp h

end Counts

/-! ### The weights over the ranges, with the levels `k + 2j` -/

section Ranges

/-- The levels `k_j = k + 2j`. -/
def lev (k J : ℕ) (j : Fin J) : ℕ := k + 2 * (j : ℕ)

/-- A prime of the `j`-th range is below `w^{2^{−j}}`. -/
theorem lt_of_mem_T {w : ℝ} (hw : 1 ≤ w) {J : ℕ} {j : Fin J} {p : ℕ} (hp : p ∈ SieveLeaf.T w J j) :
    (p : ℝ) < w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := by
  have h := (SieveRanges.mem_rng.1 hp).2.2
  rwa [SieveRanges.sq_rpow_half (by linarith) (j : ℕ)] at h

/-- `∏_j (w^{2^{−j}})^{k + 2j} ≤ w^{2k+4}`, for `w ≥ 1`. -/
theorem prod_levels_le {w : ℝ} (hw : 1 ≤ w) (J k : ℕ) :
    ∏ j : Fin J, (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ lev k J j ≤ w ^ ((2 * k + 4 : ℕ) : ℝ) := by
  have hw0 : 0 < w := by linarith
  have h3 : ∏ j : Fin J, (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ lev k J j =
      w ^ (∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * ((k : ℝ) + 2 * (j : ℕ))) := by
    rw [Real.rpow_sum_of_pos hw0]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le, lev]
    push_cast
    ring_nf
  rw [h3]
  apply Real.rpow_le_rpow_of_exponent_le hw
  push_cast
  exact SieveProp6.sum_levels_exp_le J k

/-- A set of a range's primes with at most `k + 2j` elements has product at most `(w^{2^{−j}})^{k+2j}`. -/
theorem prod_le_of_sub_T {w : ℝ} (hw : 1 ≤ w) {J : ℕ} (j : Fin J) {s : Finset ℕ} (hs : s ⊆ SieveLeaf.T w J j)
    {k : ℕ} (hsk : s.card ≤ lev k J j) :
    ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ lev k J j := by
  have hb : 1 ≤ w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := Real.one_le_rpow hw (by positivity)
  push_cast
  calc ∏ p ∈ s, (p : ℝ) ≤ ∏ _p ∈ s, w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) :=
        Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p) fun p hp => (lt_of_mem_T hw (hs hp)).le
    _ = (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ s.card := Finset.prod_const _
    _ ≤ (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ lev k J j := pow_le_pow_right₀ hb hsk

/-- An index of the weights above or below has, at each range, at most `k + 2j` primes of the range. -/
theorem sub_card_of_mem {w : ℝ} {J k : ℕ} {σ : Idx (Fin J)}
    (hσ : ∀ j, σ j ∈ Ftr (SieveLeaf.T w J j) (lev k J j) ∨ σ j ∈ Fes (SieveLeaf.T w J j) (lev k J j)) (j : Fin J) :
    (σ j).2 ⊆ SieveLeaf.T w J j ∧ (σ j).2.card ≤ lev k J j ∧ (σ j).2.card = (σ j).1 := by
  rcases hσ j with h | h
  · rw [Ftr, Finset.mem_sigma] at h
    obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 h.2
    exact ⟨h1, by rw [h2]; exact Nat.lt_succ_iff.1 (Finset.mem_range.1 h.1), h2⟩
  · rw [Fes, Finset.mem_sigma] at h
    obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 h.2
    rw [Finset.mem_singleton] at h
    exact ⟨h1, by rw [h2, h.1], h2⟩

/-- The indices of the weights below, through their second part. -/
theorem mem_wS₂_cases {w : ℝ} {J k : ℕ} {x : Option (Fin J) × Idx (Fin J)}
    (hx : x ∈ wS₂ (SieveLeaf.T w J) (lev k J)) :
    ∀ j, x.2 j ∈ Ftr (SieveLeaf.T w J j) (lev k J j) ∨ x.2 j ∈ Fes (SieveLeaf.T w J j) (lev k J j) := by
  rw [wS₂, Finset.mem_union] at hx
  rcases hx with hx | hx
  · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_map.1 hx
    exact fun j => Or.inl (Fintype.mem_piFinset.1 hσ j)
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_map.1 hi
    intro j
    have h := Fintype.mem_piFinset.1 hσ j
    by_cases hij : j = i
    · subst hij
      rw [Function.update_self] at h
      exact Or.inr h
    · rw [Function.update_of_ne hij] at h
      exact Or.inl h

/-- **The moduli's size**: for `w ≥ 1`, `f_σ ≤ w^{2k+4}` for every index of the weights above or below. -/
theorem wf_le {w : ℝ} (hw : 1 ≤ w) {J k : ℕ} {σ : Idx (Fin J)}
    (hσ : ∀ j, σ j ∈ Ftr (SieveLeaf.T w J j) (lev k J j) ∨ σ j ∈ Fes (SieveLeaf.T w J j) (lev k J j)) :
    (wf σ : ℝ) ≤ w ^ ((2 * k + 4 : ℕ) : ℝ) := by
  have hb : ∀ j : Fin J, ((∏ p ∈ (σ j).2, p : ℕ) : ℝ) ≤ (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ lev k J j := fun j => by
    obtain ⟨h1, h2, -⟩ := sub_card_of_mem hσ j
    exact prod_le_of_sub_T hw j h1 h2
  refine le_trans ?_ (prod_levels_le hw J k)
  rw [wf]
  push_cast
  exact Finset.prod_le_prod₀ (fun j _ => Finset.prod_nonneg fun p _ => Nat.cast_nonneg p) fun j _ => by
    have := hb j
    push_cast at this
    exact this

theorem abs_wl₁ {ι : Type*} [Fintype ι] (σ : Idx ι) : |wl₁ σ| = 1 := by
  rw [wl₁, Finset.abs_prod]
  exact Finset.prod_eq_one fun j _ => by simp

theorem abs_wl₂ {ι : Type*} [Fintype ι] [DecidableEq ι] (x : Option ι × Idx ι) : |wl₂ x| = 1 := by
  rcases x with ⟨_ | j, σ⟩
  · exact abs_wl₁ σ
  · simp only [wl₂, abs_neg, Finset.abs_prod]
    exact Finset.prod_eq_one fun j _ => by simp

/-- A sum over the sets of a truncation is at most the sum over all subsets, for nonnegative terms. -/
theorem sum_Ftr_le (T : Finset ℕ) (k : ℕ) (g : Finset ℕ → ℝ) (hg : ∀ s, 0 ≤ g s) :
    ∑ b ∈ Ftr T k, g b.2 ≤ ∑ s ∈ T.powerset, g s := by
  have hinj : Set.InjOn (fun b : Σ _ : ℕ, Finset ℕ => b.2) (Ftr T k : Set (Σ _ : ℕ, Finset ℕ)) := by
    intro b hb b' hb' h
    have hc : ∀ b ∈ Ftr T k, b.2.card = b.1 := fun b hb => by
      rw [Ftr, Finset.mem_sigma] at hb
      exact (Finset.mem_powersetCard.1 hb.2).2
    exact Sigma.ext (by rw [← hc b hb, ← hc b' hb']; exact congrArg Finset.card h) (heq_of_eq h)
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s _ _ => hg s
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hs
  exact Finset.mem_powerset.2 (mem_Ftr_sub hb)

theorem sum_Fes_le (T : Finset ℕ) (k : ℕ) (g : Finset ℕ → ℝ) (hg : ∀ s, 0 ≤ g s) :
    ∑ b ∈ Fes T k, g b.2 ≤ ∑ s ∈ T.powerset, g s := by
  rw [Fes, Finset.sum_sigma, Finset.sum_singleton]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_powerset.2 (Finset.mem_powersetCard.1 hs).1)
    fun s _ _ => hg s

/-- **The weights above, divided by their moduli**: `Σ_σ |λ_σ|/f_σ ≤ ∏_j ∏_{p∈T_j} (1 + 1/p)`. -/
theorem sum_wS₁_div_le {w : ℝ} (J k : ℕ) :
    ∑ σ ∈ wS₁ (SieveLeaf.T w J) (lev k J), |wl₁ σ| / (wf σ : ℝ) ≤
      ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := by
  have e : ∀ σ : Idx (Fin J), |wl₁ σ| / (wf σ : ℝ) = ∏ j, ∏ p ∈ (σ j).2, 1 / (p : ℝ) := fun σ => by
    rw [abs_wl₁, wf]
    push_cast
    rw [one_div, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← Finset.prod_inv_distrib]; simp
  rw [Finset.sum_congr rfl fun σ _ => e σ, wS₁,
    ← Finset.prod_univ_sum (fun j => Ftr (SieveLeaf.T w J j) (lev k J j)) fun _ (b : Σ _ : ℕ, Finset ℕ) =>
      ∏ p ∈ b.2, 1 / (p : ℝ)]
  refine Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun b _ => by positivity) fun j _ => ?_
  rw [Finset.prod_one_add]
  exact sum_Ftr_le _ _ (fun s => ∏ p ∈ s, 1 / (p : ℝ)) fun s => by positivity

/-- **The weights below, divided by their moduli**: `Σ_x |λ_x|/f_x ≤ (J + 1)∏_j ∏_{p∈T_j} (1 + 1/p)`. -/
theorem sum_wS₂_div_le {w : ℝ} (J k : ℕ) :
    ∑ x ∈ wS₂ (SieveLeaf.T w J) (lev k J), |wl₂ x| / (wf₂ x : ℝ) ≤
      (J + 1) * ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := by
  have e : ∀ σ : Idx (Fin J), 1 / (wf σ : ℝ) = ∏ j, ∏ p ∈ (σ j).2, 1 / (p : ℝ) := fun σ => by
    rw [wf]
    push_cast
    rw [one_div, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← Finset.prod_inv_distrib]; simp
  have hcorr : ∀ j, ∑ σ ∈ corr (SieveLeaf.T w J) (lev k J) j, 1 / (wf σ : ℝ) ≤
      ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := by
    intro j
    rw [Finset.sum_congr rfl fun σ _ => e σ, corr,
      ← Finset.prod_univ_sum (Function.update (fun i => Ftr (SieveLeaf.T w J i) (lev k J i)) j
        (Fes (SieveLeaf.T w J j) (lev k J j))) fun _ (b : Σ _ : ℕ, Finset ℕ) => ∏ p ∈ b.2, 1 / (p : ℝ)]
    refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun b _ => by positivity) fun i _ => ?_
    rw [Finset.prod_one_add]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact sum_Fes_le _ _ (fun s => ∏ p ∈ s, 1 / (p : ℝ)) fun s => by positivity
    · rw [Function.update_of_ne hij]
      exact sum_Ftr_le _ _ (fun s => ∏ p ∈ s, 1 / (p : ℝ)) fun s => by positivity
  have h1 : ∑ σ ∈ wS₁ (SieveLeaf.T w J) (lev k J), 1 / (wf σ : ℝ) ≤
      ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := by
    have := sum_wS₁_div_le (w := w) J k
    simpa only [abs_wl₁] using this
  have hdisj : Disjoint ((wS₁ (SieveLeaf.T w J) (lev k J)).map embN)
      (univ.biUnion fun j => (corr (SieveLeaf.T w J) (lev k J) j).map (embS j)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨σ, -, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx'
    obtain ⟨τ, -, h⟩ := Finset.mem_map.1 hj
    exact Option.some_ne_none j (Prod.mk.inj h).1
  have hpd : Set.PairwiseDisjoint (↑(univ : Finset (Fin J)))
      fun j => (corr (SieveLeaf.T w J) (lev k J) j).map (embS j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨σ, -, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨τ, -, h⟩ := Finset.mem_map.1 hx'
    exact hij (Option.some_injective _ (Prod.mk.inj h).1).symm
  have hx : ∀ x : Option (Fin J) × Idx (Fin J), |wl₂ x| / (wf₂ x : ℝ) = 1 / (wf₂ x : ℝ) := fun x => by
    rw [abs_wl₂]
  rw [Finset.sum_congr rfl fun x _ => hx x, wS₂, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_biUnion hpd]
  have h2 : ∑ j : Fin J, ∑ x ∈ (corr (SieveLeaf.T w J) (lev k J) j).map (embS j), 1 / (wf₂ x : ℝ) ≤
      J * ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := by
    calc _ ≤ ∑ _j : Fin J, ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) :=
          Finset.sum_le_sum fun j _ => by rw [Finset.sum_map]; exact hcorr j
      _ = J * ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1' : ∑ σ ∈ wS₁ (SieveLeaf.T w J) (lev k J), 1 / (wf₂ (embN σ) : ℝ) ≤
      ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := h1
  linarith

/-- **The weights' total mass**: `Σ|λ_σ| + Σ|λ_x| ≤ 2·rem`. -/
theorem W_le (w : ℝ) (J k : ℕ) :
    ∑ σ ∈ wS₁ (SieveLeaf.T w J) (lev k J), |wl₁ σ| + ∑ x ∈ wS₂ (SieveLeaf.T w J) (lev k J), |wl₂ x| ≤
      2 * SieveProp6.rem w J k := by
  have h1 := sum_abs_wl₁ (SieveLeaf.T w J) (lev k J)
  have hc1 : ∑ σ ∈ wS₁ (SieveLeaf.T w J) (lev k J), |wl₁ σ| = ((wS₁ (SieveLeaf.T w J) (lev k J)).card : ℝ) := by
    simp [abs_wl₁]
  have hc2 : ∑ x ∈ wS₂ (SieveLeaf.T w J) (lev k J), |wl₂ x| = ((wS₂ (SieveLeaf.T w J) (lev k J)).card : ℝ) := by
    simp [abs_wl₂]
  have h2 : ((wS₂ (SieveLeaf.T w J) (lev k J)).card : ℝ) ≤ (J + 1) * (wS₁ (SieveLeaf.T w J) (lev k J)).card := by
    have := card_wS₂_le (SieveLeaf.T w J) (lev k J)
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hR : SieveProp6.rem w J k = (J + 1) * ((wS₁ (SieveLeaf.T w J) (lev k J)).card : ℝ) := by
    rw [SieveProp6.rem, ← hc1, h1]
    simp only [lev, mul_one]
  have h0 : 0 ≤ (J : ℝ) * (wS₁ (SieveLeaf.T w J) (lev k J)).card := by positivity
  rw [hc1, hc2, hR]
  linarith

/-- **The weights divided by their moduli**: `Σ|λ_σ|/f_σ + Σ|λ_x|/f_x ≤ (J + 2)∏_j ∏_{p∈T_j} (1 + 1/p)`. -/
theorem V_le (w : ℝ) (J k : ℕ) :
    ∑ σ ∈ wS₁ (SieveLeaf.T w J) (lev k J), |wl₁ σ| / (wf σ : ℝ) +
        ∑ x ∈ wS₂ (SieveLeaf.T w J) (lev k J), |wl₂ x| / (wf₂ x : ℝ) ≤
      (J + 2) * ∏ j : Fin J, ∏ p ∈ SieveLeaf.T w J j, (1 + 1 / (p : ℝ)) := by
  have h1 := sum_wS₁_div_le (w := w) J k
  have h2 := sum_wS₂_div_le (w := w) J k
  linarith

/-- A range with a prime has `2^{2^j} < w`. -/
theorem two_pow_lt_of_mem_T {w : ℝ} (hw : 1 ≤ w) {J : ℕ} {j : Fin J} {p : ℕ} (hp : p ∈ SieveLeaf.T w J j) :
    (2 : ℝ) ^ (2 ^ (j : ℕ)) < w := by
  have hw0 : 0 < w := by linarith
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (SieveLeaf.prime_of_mem_T hp).two_le
  have h3 : (2 : ℝ) < w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := lt_of_le_of_lt h2 (lt_of_mem_T hw hp)
  have h4 : (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (2 ^ (j : ℕ)) = w := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
    have : (1 / 2 : ℝ) ^ (j : ℕ) * ((2 ^ (j : ℕ) : ℕ) : ℝ) = 1 := by
      push_cast
      rw [← mul_pow]
      norm_num
    rw [this, Real.rpow_one]
  calc (2 : ℝ) ^ (2 ^ (j : ℕ)) < (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (2 ^ (j : ℕ)) :=
        pow_lt_pow_left₀ h3 (by norm_num) (by positivity)
    _ = w := h4

/-- At most `⌊log₂⌊log₂ w⌋⌋ + 1` of the ranges have a prime. -/
theorem card_nonempty_le {w : ℕ} (hw : 1 ≤ w) (J : ℕ) :
    ((univ : Finset (Fin J)).filter fun j => (SieveLeaf.T (w : ℝ) J j).Nonempty).card ≤
      Nat.log 2 (Nat.log 2 w) + 1 := by
  have hsub : ((univ : Finset (Fin J)).filter fun j => (SieveLeaf.T (w : ℝ) J j).Nonempty).map Fin.valEmbedding ⊆
      Finset.range (Nat.log 2 (Nat.log 2 w) + 1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨p, hp⟩ := (Finset.mem_filter.1 hj).2
    have h := two_pow_lt_of_mem_T (by exact_mod_cast hw) hp
    have h' : 2 ^ (2 ^ (j : ℕ)) < w := by exact_mod_cast h
    have hl : 2 ^ (j : ℕ) ≤ Nat.log 2 w := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 h'.le
    have hl0 : Nat.log 2 w ≠ 0 := by have := Nat.one_le_two_pow (n := (j : ℕ)); omega
    have hj' : (j : ℕ) ≤ Nat.log 2 (Nat.log 2 w) := (Nat.le_log_iff_pow_le (by norm_num) hl0).2 hl
    rw [Finset.mem_range, Fin.valEmbedding_apply]
    omega
  have := Finset.card_le_card hsub
  rwa [Finset.card_map, Finset.card_range] at this

/-- `∏_j ∏_{p∈T_j} (1 + 1/p) ≤ e^{C₀(⌊log₂⌊log₂ w⌋⌋ + 1)}`. -/
theorem prod_T_one_add_le {w : ℕ} (hw : 1 ≤ w) (J : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) :
    ∏ j : Fin J, ∏ p ∈ SieveLeaf.T (w : ℝ) J j, (1 + 1 / (p : ℝ)) ≤
      Real.exp C₀ ^ (Nat.log 2 (Nat.log 2 w) + 1) := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj : ∀ j : Fin J, ∏ p ∈ SieveLeaf.T (w : ℝ) J j, (1 + 1 / (p : ℝ)) ≤
      if (SieveLeaf.T (w : ℝ) J j).Nonempty then Real.exp C₀ else 1 := by
    intro j
    split_ifs with hne
    · calc ∏ p ∈ SieveLeaf.T (w : ℝ) J j, (1 + 1 / (p : ℝ))
          ≤ ∏ p ∈ SieveLeaf.T (w : ℝ) J j, Real.exp (1 / (p : ℝ)) :=
            Finset.prod_le_prod₀ (fun p _ => by positivity) fun p _ => by
              have := Real.add_one_le_exp (1 / (p : ℝ))
              linarith
        _ = Real.exp (∑ p ∈ SieveLeaf.T (w : ℝ) J j, 1 / (p : ℝ)) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp C₀ := Real.exp_le_exp.2 (hC _ (Real.one_le_rpow hw' (by positivity)))
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.prod_empty]
  calc ∏ j : Fin J, ∏ p ∈ SieveLeaf.T (w : ℝ) J j, (1 + 1 / (p : ℝ))
      ≤ ∏ j : Fin J, (if (SieveLeaf.T (w : ℝ) J j).Nonempty then Real.exp C₀ else 1) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.prod_nonneg fun p _ => by positivity) fun j _ => hj j
    _ = Real.exp C₀ ^ ((univ : Finset (Fin J)).filter fun j => (SieveLeaf.T (w : ℝ) J j).Nonempty).card := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    _ ≤ Real.exp C₀ ^ (Nat.log 2 (Nat.log 2 w) + 1) :=
        pow_le_pow_right₀ (Real.one_le_exp hC₀) (card_nonempty_le hw J)

/-- `⌊log₂ w⌋ ≤ 2 log x` for `1 ≤ w ≤ x`. -/
theorem log2_le {w : ℕ} (hw : 1 ≤ w) {x : ℝ} (hwx : (w : ℝ) ≤ x) : (Nat.log 2 w : ℝ) ≤ 2 * Real.log x := by
  have h1 : 2 ^ Nat.log 2 w ≤ w := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ) ^ Nat.log 2 w) ≤ x := le_trans (by exact_mod_cast h1) hwx
  have h3 : (Nat.log 2 w : ℝ) * Real.log 2 ≤ Real.log x := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have : 0 ≤ (Nat.log 2 w : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- For `1 ≤ w ≤ x`: `(Jw(w) + 2)·e^{C₀(⌊log₂⌊log₂ w⌋⌋ + 1)} ≤ (3 + 4 log x)^{2m+2}`, `m = ⌈C₀/log 2⌉`. -/
theorem V_poly_le {w : ℕ} (hw : 1 ≤ w) {x : ℝ} (hwx : (w : ℝ) ≤ x) (C₀ : ℝ) :
    ((SieveProp6.Jw w : ℝ) + 2) * Real.exp C₀ ^ (Nat.log 2 (Nat.log 2 w) + 1) ≤
      (3 + 4 * Real.log x) ^ (2 * ⌈C₀ / Real.log 2⌉₊ + 2) := by
  set ℓ := Nat.log 2 w with hℓdef
  set t := Nat.log 2 ℓ with htdef
  set m := ⌈C₀ / Real.log 2⌉₊ with hmdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp C₀ ≤ 2 ^ m := by
    have hC : C₀ ≤ m * Real.log 2 := by
      have := Nat.le_ceil (C₀ / Real.log 2)
      rwa [div_le_iff₀ hlog2] at this
    calc Real.exp C₀ ≤ Real.exp (m * Real.log 2) := Real.exp_le_exp.2 hC
      _ = 2 ^ m := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h2t : (2 : ℝ) ^ (t + 1) ≤ 2 * ℓ + 2 := by
    have : 2 ^ (t + 1) ≤ 2 * ℓ + 2 := by
      rcases Nat.eq_zero_or_pos ℓ with h0 | h0
      · rw [htdef, h0]
        simp
      · have : 2 ^ t ≤ ℓ := Nat.pow_log_le_self 2 (by omega : ℓ ≠ 0)
        rw [pow_succ]
        omega
    exact_mod_cast this
  have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hw) hwx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hℓ : (ℓ : ℝ) ≤ 2 * Real.log x := log2_le hw hwx
  have hJ : (SieveProp6.Jw w : ℝ) + 2 = 2 * ℓ + 4 := by
    rw [SieveProp6.Jw]
    push_cast
    ring
  have hB : 2 * (ℓ : ℝ) + 4 ≤ 2 * (3 + 4 * Real.log x) := by linarith
  have hC : (2 : ℝ) ≤ 3 + 4 * Real.log x := by linarith
  calc ((SieveProp6.Jw w : ℝ) + 2) * Real.exp C₀ ^ (t + 1)
      ≤ (2 * ℓ + 4) * ((2 : ℝ) ^ m) ^ (t + 1) := by
        rw [hJ]
        gcongr
    _ = (2 * ℓ + 4) * ((2 : ℝ) ^ (t + 1)) ^ m := by ring
    _ ≤ (2 * ℓ + 4) * (2 * ℓ + 4) ^ m := by
        gcongr
        linarith
    _ = (2 * ℓ + 4) ^ (m + 1) := by ring
    _ ≤ (2 * (3 + 4 * Real.log x)) ^ (m + 1) := by gcongr
    _ ≤ ((3 + 4 * Real.log x) * (3 + 4 * Real.log x)) ^ (m + 1) := by gcongr
    _ = (3 + 4 * Real.log x) ^ (2 * m + 2) := by
        rw [← pow_two, ← pow_mul, show 2 * (m + 1) = 2 * m + 2 by ring]

theorem esym_congr {T : Finset ℕ} {x y : ℕ → ℝ} (h : ∀ p ∈ T, x p = y p) (m : ℕ) : esym T x m = esym T y m := by
  unfold esym
  exact Finset.sum_congr rfl fun s hs => Finset.prod_congr rfl fun p hp => h p ((Finset.mem_powersetCard.1 hs).1 hp)

theorem trunc_congr {T : Finset ℕ} {x y : ℕ → ℝ} (h : ∀ p ∈ T, x p = y p) (k : ℕ) :
    SieveBrun.trunc T x k = SieveBrun.trunc T y k := by
  unfold SieveBrun.trunc
  exact Finset.sum_congr rfl fun i _ => by rw [esym_congr h]

/-- **The weights' gap**: for `w ≥ 2` with `w^{2^{−J}} ≤ 2`,
`|Σ λ_σ gU(f_σ)/f_σ − Σ λ_x gU(f_x)/f_x| ≤ ζ(k)·q/(φ(q) log w)`. -/
theorem abs_gap_le {w J q : ℕ} (hw : 2 ≤ w) (hJ : (w : ℝ) ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (hq : 0 < q) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k)
    (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    |∑ σ ∈ wS₁ (SieveLeaf.T w J) (lev k J), wl₁ σ * gU q (wf σ) / (wf σ : ℝ) -
        ∑ x ∈ wS₂ (SieveLeaf.T w J) (lev k J), wl₂ x * gU q (wf₂ x) / (wf₂ x : ℝ)| ≤
      SieveProp6.zeta C₀ k * (q / (q.totient * Real.log w)) := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hg : ∀ j : Fin J, ∀ p ∈ SieveLeaf.T (w : ℝ) J j, gU q p / (p : ℝ) = SieveLeaf.g q p := by
    intro j p hp
    have hpp := SieveLeaf.prime_of_mem_T hp
    unfold gU SieveLeaf.g
    by_cases hd : p ∣ q
    · rw [ite_eq_left hd, ite_eq_right (by rw [ZMod.isUnit_prime_iff_not_dvd hpp]; exact not_not.2 hd)]
      simp
    · rw [ite_eq_right hd, ite_eq_left ((ZMod.isUnit_prime_iff_not_dvd hpp).2 hd)]
  rw [gap_eq]
  have e : ∑ j, esym (SieveLeaf.T (w : ℝ) J j) (fun p => gU q p / (p : ℝ)) (lev k J j) *
        ∏ i ∈ univ.erase j, SieveBrun.trunc (SieveLeaf.T (w : ℝ) J i) (fun p => gU q p / (p : ℝ)) (lev k J i) =
      ∑ j : Fin J, esym (SieveLeaf.T (w : ℝ) J j) (SieveLeaf.g q) (k + 2 * (j : ℕ)) *
        ∏ i ∈ Finset.univ.erase j, SieveBrun.trunc (SieveLeaf.T (w : ℝ) J i) (SieveLeaf.g q) (k + 2 * (i : ℕ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [esym_congr (hg j)]
    exact congrArg _ (Finset.prod_congr rfl fun i _ => trunc_congr (hg i) _)
  rw [e]
  have hnn : 0 ≤ ∑ j : Fin J, esym (SieveLeaf.T (w : ℝ) J j) (SieveLeaf.g q) (k + 2 * (j : ℕ)) *
      ∏ i ∈ Finset.univ.erase j, SieveBrun.trunc (SieveLeaf.T (w : ℝ) J i) (SieveLeaf.g q) (k + 2 * (i : ℕ)) := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ (Finset.prod_nonneg fun i _ => ?_)
    · exact Finset.sum_nonneg fun s _ => Finset.prod_nonneg fun p _ => SieveLeaf.g_nonneg q p
    · have hk' : Even (k + 2 * (i : ℕ)) := by rcases hk with ⟨r, hr⟩; exact ⟨r + i, by omega⟩
      have h := (trunc_bounds (T := SieveLeaf.T (w : ℝ) J i) (y := SieveLeaf.g q)
        (fun p _ => SieveLeaf.g_nonneg q p)
        (fun p hp => SieveLeaf.g_le_one (SieveLeaf.prime_of_mem_T hp).one_lt.le) hk' (by omega)).2
      refine le_trans (Finset.prod_nonneg fun p hp => ?_) h
      have := SieveLeaf.g_le_one (q := q) (SieveLeaf.prime_of_mem_T hp).one_lt.le
      linarith
  rw [abs_of_nonneg hnn]
  have hG := SieveLeaf.leaf_gap hw' J q hC₀ hC hk hkC
  have hV := SieveLeaf.prod_T_le hw hJ hq
  have hζ := SieveProp6.zeta_nonneg hC₀ k
  calc _ ≤ (∏ j : Fin J, ∏ p ∈ SieveLeaf.T (w : ℝ) J j, (1 - SieveLeaf.g q p)) * SieveProp6.zeta C₀ k := hG
    _ ≤ (q / (q.totient * Real.log w)) * SieveProp6.zeta C₀ k := mul_le_mul_of_nonneg_right hV hζ
    _ = SieveProp6.zeta C₀ k * (q / (q.totient * Real.log w)) := mul_comm _ _

/-! ### The fibres -/

theorem one_le_wf {ι : Type*} [Fintype ι] {T : ι → Finset ℕ} (hT : ∀ j, ∀ p ∈ T j, p.Prime) {σ : Idx ι}
    (hσ : ∀ j, (σ j).2 ⊆ T j) : 1 ≤ wf σ :=
  Finset.one_le_prod fun j _ => Finset.one_le_prod fun p hp => (hT j p (hσ j hp)).one_lt.le

/-- **The fibres of the weights above**: for a set `Y` of decreasing tuples of primes, the pairs `(y, σ)` with
`∏y · f_σ = d` number at most `d(d)`. -/
theorem fibre_wS₁_le {w : ℝ} (hw : 1 ≤ w) {J k K : ℕ} (Y : Finset (Fin K → ℕ))
    (hY : ∀ y ∈ Y, StrictAnti y ∧ ∀ i, (y i).Prime) (d : ℕ) :
    ∑ x ∈ (Y ×ˢ wS₁ (SieveLeaf.T w J) (lev k J)).filter (fun x => (∏ i, x.1 i) * wf x.2 = d), |wl₁ x.2| ≤
      (d.divisors.card : ℝ) := by
  have hT : ∀ j, ∀ p ∈ SieveLeaf.T w J j, p.Prime := fun j p hp => SieveLeaf.prime_of_mem_T hp
  have hdisj := SieveLeaf.T_disjoint hw J
  simp only [abs_wl₁, Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_cast
  refine Finset.card_le_card_of_injOn (fun x => wf x.2) (fun x hx => ?_) (fun x hx x' hx' h => ?_)
  · obtain ⟨hm, hd⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
    have h1 := one_le_prod (hY _ (Finset.mem_product.1 hm).1).2
    have h2 := one_le_wf hT (sub_of_mem_wS₁ (Finset.mem_product.1 hm).2)
    have hd0 : d ≠ 0 := by rw [← hd]; positivity
    exact Nat.mem_divisors.2 ⟨Dvd.intro_left _ hd, hd0⟩
  · obtain ⟨hm, hd⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
    obtain ⟨hm', hd'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx')
    obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hm
    obtain ⟨hy', hσ'⟩ := Finset.mem_product.1 hm'
    have h' : wf x.2 = wf x'.2 := h
    have hσσ : x.2 = x'.2 := wf_inj hT hdisj (sub_of_mem_wS₁ hσ) (sub_of_mem_wS₁ hσ') (card_of_mem_wS₁ hσ)
      (card_of_mem_wS₁ hσ') h'
    have hpos : 0 < wf x.2 := one_le_wf hT (sub_of_mem_wS₁ hσ)
    have hprod : ∏ i, x.1 i = ∏ i, x'.1 i := by
      rw [← h'] at hd'
      exact Nat.eq_of_mul_eq_mul_right hpos (hd.trans hd'.symm)
    exact Prod.ext (eq_of_prod_eq (hY _ hy).1 (hY _ hy').1 (hY _ hy).2 (hY _ hy').2 hprod) hσσ

/-- **The fibres of the weights below**: for a set `Y` of decreasing tuples of primes, the pairs `(y, x)` with
`∏y · f_x = d` number at most `(J + 1)d(d)`. -/
theorem fibre_wS₂_le {w : ℝ} (hw : 1 ≤ w) {J k K : ℕ} (Y : Finset (Fin K → ℕ))
    (hY : ∀ y ∈ Y, StrictAnti y ∧ ∀ i, (y i).Prime) (d : ℕ) :
    ∑ x ∈ (Y ×ˢ wS₂ (SieveLeaf.T w J) (lev k J)).filter (fun x => (∏ i, x.1 i) * wf₂ x.2 = d), |wl₂ x.2| ≤
      (J + 1) * (d.divisors.card : ℝ) := by
  have hT : ∀ j, ∀ p ∈ SieveLeaf.T w J j, p.Prime := fun j p hp => SieveLeaf.prime_of_mem_T hp
  have hdisj := SieveLeaf.T_disjoint hw J
  simp only [abs_wl₂, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : ((Y ×ˢ wS₂ (SieveLeaf.T w J) (lev k J)).filter (fun x => (∏ i, x.1 i) * wf₂ x.2 = d)).card ≤
      ((univ : Finset (Option (Fin J))) ×ˢ d.divisors).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x.2.1, wf₂ x.2)) (fun x hx => ?_) (fun x hx x' hx' h => ?_)
    · obtain ⟨hm, hd⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      have h1 := one_le_prod (hY _ (Finset.mem_product.1 hm).1).2
      have h2 := one_le_wf hT (sub_of_mem_wS₂ (Finset.mem_product.1 hm).2)
      have hd0 : d ≠ 0 := by rw [← hd]; positivity
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Nat.mem_divisors.2 ⟨Dvd.intro_left _ hd, hd0⟩⟩
    · obtain ⟨hm, hd⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      obtain ⟨hm', hd'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx')
      obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hm
      obtain ⟨hy', hσ'⟩ := Finset.mem_product.1 hm'
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have hc1 := fun j => (sub_card_of_mem (mem_wS₂_cases hσ) j).2.2
      have hc2 := fun j => (sub_card_of_mem (mem_wS₂_cases hσ') j).2.2
      have hσσ : x.2.2 = x'.2.2 := wf_inj hT hdisj (sub_of_mem_wS₂ hσ) (sub_of_mem_wS₂ hσ') hc1 hc2 h2
      have hpos : 0 < wf₂ x.2 := one_le_wf hT (sub_of_mem_wS₂ hσ)
      have hprod : ∏ i, x.1 i = ∏ i, x'.1 i := by
        rw [← h2] at hd'
        exact Nat.eq_of_mul_eq_mul_right hpos (hd.trans hd'.symm)
      exact Prod.ext (eq_of_prod_eq (hY _ hy).1 (hY _ hy').1 (hY _ hy).2 (hY _ hy').2 hprod) (Prod.ext h1 hσσ)
  rw [Finset.card_product, Finset.card_univ, Fintype.card_option, Fintype.card_fin] at hc
  exact_mod_cast hc

/-- The decreasing tuples of primes with a given product number at most one. -/
theorem card_fibre_le_one {K : ℕ} (Y : Finset (Fin K → ℕ)) (hY : ∀ y ∈ Y, StrictAnti y ∧ ∀ i, (y i).Prime)
    (d : ℕ) : (Y.filter (fun y => ∏ i, y i = d)).card ≤ 1 :=
  Finset.card_le_one.2 fun y hy y' hy' => by
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    obtain ⟨hy1', hy2'⟩ := Finset.mem_filter.1 hy'
    exact eq_of_prod_eq (hY y hy1).1 (hY y' hy1').1 (hY y hy1).2 (hY y' hy1').2 (hy2.trans hy2'.symm)

end Ranges

/-! ### The weights' bounds at a power of `x` -/

/-- The weights' total mass at `2 ≤ w ≤ 2x^{εw}`, `(2k + 4)εw ≤ 1/16`: at most `x^{1/4}` once
`24·2^{2k+7} ≤ x^{1/8}`. -/
theorem W_le_rpow {x εw : ℝ} (hx1 : 1 ≤ x) (hεw : 0 < εw) {k : ℕ} (hεwk : (2 * k + 4) * εw ≤ 1 / 16)
    (hWx : 24 * 2 ^ (2 * k + 7) ≤ x ^ (1 / 8 : ℝ)) {w : ℕ} (hw2 : 2 ≤ w) (hw2x : (w : ℝ) ≤ 2 * x ^ εw) :
    ∑ σ ∈ wS₁ (SieveLeaf.T (w : ℝ) (SieveProp6.Jw w)) (lev k (SieveProp6.Jw w)), |wl₁ σ| +
      ∑ z ∈ wS₂ (SieveLeaf.T (w : ℝ) (SieveProp6.Jw w)) (lev k (SieveProp6.Jw w)), |wl₂ z| ≤ x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  obtain ⟨-, h2J, hJ3⟩ := SieveProp6.Jw_spec hw2
  set J := SieveProp6.Jw w with hJdef
  have hk4 : (4 : ℝ) ≤ 2 * k + 4 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hεw1 : εw ≤ 1 / 64 := by
    have : 4 * εw ≤ (2 * k + 4) * εw := mul_le_mul_of_nonneg_right hk4 hεw.le
    linarith
  have h1 := W_le (w : ℝ) J k
  have h2 := SieveProp6.rem_le hw1 J k
  have h3 : ((J : ℝ) + 1) * 2 ^ J * (w : ℝ) ^ ((2 * k + 4 : ℕ) : ℝ) ≤ 12 * (w : ℝ) ^ (2 * k + 7) := by
    rw [Real.rpow_natCast]
    calc ((J : ℝ) + 1) * 2 ^ J * (w : ℝ) ^ (2 * k + 4) ≤ (3 * w) * (4 * w ^ 2) * (w : ℝ) ^ (2 * k + 4) := by
          gcongr
      _ = 12 * (w : ℝ) ^ (2 * k + 7) := by ring
  have h4 : (w : ℝ) ^ (2 * k + 7) ≤ 2 ^ (2 * k + 7) * x ^ (((2 * k + 7 : ℕ) : ℝ) * εw) := by
    calc (w : ℝ) ^ (2 * k + 7) ≤ (2 * x ^ εw) ^ (2 * k + 7) := by gcongr
      _ = 2 ^ (2 * k + 7) * x ^ (((2 * k + 7 : ℕ) : ℝ) * εw) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ εw), ← Real.rpow_mul hx0.le, mul_comm εw]
  have h5 : x ^ (((2 * k + 7 : ℕ) : ℝ) * εw) ≤ x ^ (1 / 8 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    push_cast
    linarith
  have h6 : x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ) = x ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  have h7 : 0 ≤ x ^ (((2 * k + 7 : ℕ) : ℝ) * εw) := by positivity
  calc _ ≤ 2 * SieveProp6.rem (w : ℝ) J k := h1
    _ ≤ 2 * (12 * (2 ^ (2 * k + 7) * x ^ (((2 * k + 7 : ℕ) : ℝ) * εw))) := by
        have h8 := h2.trans h3
        have h9 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 12)
        linarith
    _ = 24 * 2 ^ (2 * k + 7) * x ^ (((2 * k + 7 : ℕ) : ℝ) * εw) := by ring
    _ ≤ x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ) := by gcongr
    _ = x ^ (1 / 4 : ℝ) := h6

/-- The weights divided by their moduli at `1 ≤ w ≤ x`: at most `x^c` once `(3 + 4 log x)^{2m+2} ≤ x^c`,
`m = ⌈C₀/log 2⌉`. -/
theorem V_le_rpow {x c : ℝ} {w : ℕ} (hw : 1 ≤ w) (hwx : (w : ℝ) ≤ x) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) (k : ℕ)
    (hVx : (3 + 4 * Real.log x) ^ (2 * ⌈C₀ / Real.log 2⌉₊ + 2) ≤ x ^ c) :
    ∑ σ ∈ wS₁ (SieveLeaf.T (w : ℝ) (SieveProp6.Jw w)) (lev k (SieveProp6.Jw w)), |wl₁ σ| / (wf σ : ℝ) +
      ∑ z ∈ wS₂ (SieveLeaf.T (w : ℝ) (SieveProp6.Jw w)) (lev k (SieveProp6.Jw w)), |wl₂ z| / (wf₂ z : ℝ) ≤
        x ^ c := by
  have h1 := V_le (w : ℝ) (SieveProp6.Jw w) k
  have h2 := prod_T_one_add_le hw (SieveProp6.Jw w) hC₀ hC
  have h3 := V_poly_le hw hwx C₀
  calc _ ≤ ((SieveProp6.Jw w : ℝ) + 2) *
        ∏ j : Fin (SieveProp6.Jw w), ∏ p ∈ SieveLeaf.T (w : ℝ) (SieveProp6.Jw w) j, (1 + 1 / (p : ℝ)) := h1
    _ ≤ ((SieveProp6.Jw w : ℝ) + 2) * Real.exp C₀ ^ (Nat.log 2 (Nat.log 2 w) + 1) := by gcongr
    _ ≤ (3 + 4 * Real.log x) ^ (2 * ⌈C₀ / Real.log 2⌉₊ + 2) := h3
    _ ≤ x ^ c := hVx

/-- The fibres at `1 ≤ w ≤ x`: for decreasing tuples of primes with `∏y ≤ P` and `P·x^{2k+4} ≤ x^D`, both fibre sums
are at most `x^{c₁}` once `C_{ε'} ≤ 3^n`, `ε'D ≤ c₁/2` and `(3 + 4 log x)^{n+1} ≤ x^{c₁/2}`. -/
theorem fibres_le_rpow {x c₁ ε' D : ℝ} {n K k : ℕ} (hx1 : 1 ≤ x) {w : ℕ} (hw : 1 ≤ w) (hwx : (w : ℝ) ≤ x)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1) (hε'D : ε' * D ≤ c₁ / 2) (hn : LinnikPower.Cdiv ε' ≤ 3 ^ n)
    (hFx : (3 + 4 * Real.log x) ^ (n + 1) ≤ x ^ (c₁ / 2)) (Y : Finset (Fin K → ℕ))
    (hY : ∀ y ∈ Y, StrictAnti y ∧ ∀ i, (y i).Prime) {P : ℝ} (hYP : ∀ y ∈ Y, ((∏ i, y i : ℕ) : ℝ) ≤ P)
    (hPD : P * x ^ ((2 * k + 4 : ℕ) : ℝ) ≤ x ^ D) :
    (∀ d, ∑ z ∈ (Y ×ˢ wS₁ (SieveLeaf.T (w : ℝ) (SieveProp6.Jw w)) (lev k (SieveProp6.Jw w))).filter
      (fun z => (∏ i, z.1 i) * wf z.2 = d), |wl₁ z.2| ≤ x ^ c₁) ∧
    (∀ d, ∑ z ∈ (Y ×ˢ wS₂ (SieveLeaf.T (w : ℝ) (SieveProp6.Jw w)) (lev k (SieveProp6.Jw w))).filter
      (fun z => (∏ i, z.1 i) * wf₂ z.2 = d), |wl₂ z.2| ≤ x ^ c₁) := by
  have hx0 : 0 < x := by linarith
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  set J := SieveProp6.Jw w with hJdef
  have hfmaxx : (w : ℝ) ^ ((2 * k + 4 : ℕ) : ℝ) ≤ x ^ ((2 * k + 4 : ℕ) : ℝ) :=
    Real.rpow_le_rpow (by positivity) hwx (by positivity)
  have hlogJ : (J : ℝ) + 1 ≤ 3 + 4 * Real.log x := by
    have h := log2_le hw hwx
    have e : (J : ℝ) = 2 * (Nat.log 2 w : ℝ) + 2 := by rw [hJdef, SieveProp6.Jw]; push_cast; ring
    linarith
  have hfib : ∀ d : ℕ, (∃ y ∈ Y, ∃ f : ℕ, (f : ℝ) ≤ (w : ℝ) ^ ((2 * k + 4 : ℕ) : ℝ) ∧ (∏ i, y i) * f = d) →
      (J + 1) * (d.divisors.card : ℝ) ≤ x ^ c₁ := by
    rintro d ⟨y, hy, f, hf, hd⟩
    have hdx : (d : ℝ) ≤ x ^ D := by
      rw [← hd]
      push_cast
      have hf' : (f : ℝ) ≤ x ^ ((2 * k + 4 : ℕ) : ℝ) := le_trans hf hfmaxx
      have hyP := hYP y hy
      push_cast at hyP
      exact le_trans (mul_le_mul hyP hf' (Nat.cast_nonneg _) (le_trans (by positivity) hyP)) hPD
    have hdiv := LinnikPower.card_divisors_le hε'0 hε'1 d
    have hdε : (d : ℝ) ^ ε' ≤ x ^ (c₁ / 2) := by
      calc (d : ℝ) ^ ε' ≤ (x ^ D) ^ ε' := Real.rpow_le_rpow (Nat.cast_nonneg _) hdx hε'0.le
        _ = x ^ (ε' * D) := by rw [← Real.rpow_mul hx0.le, mul_comm]
        _ ≤ x ^ (c₁ / 2) := Real.rpow_le_rpow_of_exponent_le hx1 hε'D
    have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h3 : (3 : ℝ) ^ n ≤ (3 + 4 * Real.log x) ^ n := pow_le_pow_left₀ (by norm_num) (by linarith) n
    have hC1 : 1 ≤ LinnikPower.Cdiv ε' := LinnikPower.one_le_Cdiv hε'0 hε'1
    calc (J + 1) * (d.divisors.card : ℝ) ≤ (3 + 4 * Real.log x) * (LinnikPower.Cdiv ε' * x ^ (c₁ / 2)) := by
          gcongr
          exact hdiv.trans (mul_le_mul_of_nonneg_left hdε (by linarith))
      _ ≤ (3 + 4 * Real.log x) * ((3 + 4 * Real.log x) ^ n * x ^ (c₁ / 2)) := by gcongr; linarith
      _ = (3 + 4 * Real.log x) ^ (n + 1) * x ^ (c₁ / 2) := by ring
      _ ≤ x ^ (c₁ / 2) * x ^ (c₁ / 2) := by gcongr
      _ = x ^ c₁ := by rw [← Real.rpow_add hx0]; ring_nf
  refine ⟨fun d => ?_, fun d => ?_⟩
  · by_cases he : ((Y ×ˢ wS₁ (SieveLeaf.T (w : ℝ) J) (lev k J)).filter (fun z => (∏ i, z.1 i) * wf z.2 = d)).Nonempty
    · obtain ⟨z, hz⟩ := he
      obtain ⟨hzm, hzd⟩ := Finset.mem_filter.1 hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.1 hzm
      have h := hfib d ⟨z.1, hz1, wf z.2, wf_le hw1 (fun j => Or.inl (Fintype.mem_piFinset.1 hz2 j)), hzd⟩
      have h1 := fibre_wS₁_le hw1 (J := J) (k := k) Y hY d
      have h0 : 0 ≤ (J : ℝ) * (d.divisors.card : ℝ) := by positivity
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 he, Finset.sum_empty]
      positivity
  · by_cases he : ((Y ×ˢ wS₂ (SieveLeaf.T (w : ℝ) J) (lev k J)).filter (fun z => (∏ i, z.1 i) * wf₂ z.2 = d)).Nonempty
    · obtain ⟨z, hz⟩ := he
      obtain ⟨hzm, hzd⟩ := Finset.mem_filter.1 hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.1 hzm
      have h := hfib d ⟨z.1, hz1, wf₂ z.2, wf_le hw1 (mem_wS₂_cases hz2), hzd⟩
      have h1 := fibre_wS₂_le hw1 (J := J) (k := k) Y hY d
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 he, Finset.sum_empty]
      positivity

/-! ### The leaves of a family -/

open Classical Filter in
/-- **The large leaves of a family, with Brun's weights.** Let `L > 2`, `0 ≤ δ' < a ≤ L − 2`, `0 < b ≤ L`, `Λ₀ ≥ 0`,
`εw > 0`, and the levels `k + 2j` with `k ≥ 1` even, `2C₀² ≤ (k + 1)(k + 2)` and `(2k + 4)εw ≤ 1/16`, `C₀` bounding the
sums `Σ 1/p` over the ranges. There are `δ > 0` and `q₀` such that for `q ≥ q₀`, `a` a unit, `w = ⌈q^{εw}⌉`, and two
sets `Y₁`, `Y₂` of decreasing tuples of primes in `[w, ⌊2q^L⌋]` with comparisons `Pr` as in
`SieveTypeIBAsym.leaves_ib` and the sizes `∏y₁·w^{2k+4} ≤ q^{L−1−a}`, `∏y₁·w^{2k+4}·(∏y₂)² ≤ q^{L−b}`,
`q^{L−1−δ'} ≤ ∏y₁∏y₂`: the leaves `d = ∏y₁∏y₂`, counted by `Σ_{n∈(⌊q^L⌋, ⌊2q^L⌋]} dw(n)·1[d ∣ n, n has no prime
factor below w]`, total at most `ζ(k)(N₂ − N₁)/(φ(q) log w)·Σ 1/d + q^{L−δ}/φ(q)` in absolute value. -/
theorem leaves_chain {L : ℝ} (hL : 2 < L) {a b δ' εw Λ₀ : ℝ} (hδ' : 0 ≤ δ') (hab : δ' < a) (haL : a ≤ L - 2)
    (hb : 0 < b) (hbL : b ≤ L) (hεw : 0 < εw) (hΛ₀ : 0 ≤ Λ₀) (K₁ K₂ J₀ : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ SieveRanges.rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hεwk : (2 * k + 4) * εw ≤ 1 / 16) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a' : ZMod q), IsUnit a' →
    ∀ (Y₁ : Finset (Fin K₁ → ℕ)) (Y₂ : Finset (Fin K₂ → ℕ)),
      (∀ y ∈ Y₁, StrictAnti y ∧ ∀ i, (y i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ y i ∧ y i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
      (∀ y ∈ Y₂, StrictAnti y ∧ ∀ i, (y i).Prime ∧ ⌈(q : ℝ) ^ εw⌉₊ ≤ y i ∧ y i ≤ ⌊2 * (q : ℝ) ^ L⌋₊) →
    ∀ {M : ℕ}, M ≤ J₀ → ∀ (cc : Fin M → ℝ) (e₁ : Fin M → Fin K₁ → ℝ) (e₂ : Fin M → Fin K₂ → ℝ)
      (Pr : Fin M → (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → Prop),
      (∀ j y₁ y₂, (0 < cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) → Pr j y₁ y₂) ∧
        (Pr j y₁ y₂ → 0 ≤ cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) →
      (∀ j, ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂,
        cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) ≤ Λ₀ * Real.log q) →
      (∀ j, (∃ i, e₁ j i = 1 ∨ e₁ j i = -1) ∨ ∃ i, e₂ j i = 1 ∨ e₂ j i = -1) →
      (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∀ j, Pr j y₁ y₂) →
        ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i, y₁ i : ℕ) : ℝ) * (⌈(q : ℝ) ^ εw⌉₊ : ℝ) ^ (2 * k + 4) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤
          (q : ℝ) ^ (L - b) ∧
        (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ)) →
      ‖∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℂ) else 0) *
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊, dw q a' n *
            (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough ⌈(q : ℝ) ^ εw⌉₊ n then 1 else 0)‖ ≤
        SieveProp6.zeta C₀ k * (((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) /
            (q.totient * Real.log (⌈(q : ℝ) ^ εw⌉₊ : ℝ))) *
          ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) /
            (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) +
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  -- the constants
  have hk4 : (4 : ℝ) ≤ 2 * k + 4 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hεw1 : εw ≤ 1 / 64 := by
    have : 4 * εw ≤ (2 * k + 4) * εw := mul_le_mul_of_nonneg_right hk4 hεw.le
    linarith
  set B : ℝ := Real.log (L + 1) - Real.log εw + 1 with hBdef
  have hB : 1 ≤ B := by
    have : Real.log εw ≤ Real.log (L + 1) := Real.log_le_log hεw (by linarith)
    linarith
  obtain ⟨hs0, -, -, -, -⟩ := SieveTypeIBAsym.sIB_spec hab hb hεw J₀
  set s := SieveTypeIBAsym.sIB a b δ' εw J₀ with hsdef
  set c₁ : ℝ := s / 8 with hc₁def
  have hc₁0 : 0 < c₁ := by positivity
  obtain ⟨δ, hδ, q₀, H⟩ := SieveTypeIBAsym.leaves_ib hL hδ' hab haL hb hbL hεw hΛ₀ hB K₁ K₂ J₀ hc₁0.le
    (by rw [hc₁def]; linarith)
  -- the divisor bound's exponent
  set D : ℝ := (L + 1) * K₁ + (2 * k + 4) with hDdef
  have hD0 : 0 < D := by have : (0 : ℝ) ≤ (L + 1) * K₁ := by positivity
                         linarith
  set ε' : ℝ := min 1 (c₁ / (2 * D)) with hε'def
  have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'D : ε' * D ≤ c₁ / 2 := by
    have h := min_le_right 1 (c₁ / (2 * D))
    rw [← hε'def] at h
    calc ε' * D ≤ c₁ / (2 * D) * D := mul_le_mul_of_nonneg_right h hD0.le
      _ = c₁ / 2 := by field_simp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, LinnikPower.Cdiv ε' ≤ 3 ^ n :=
    (pow_unbounded_of_one_lt _ (by norm_num : (1 : ℝ) < 3)).imp fun _ h => h.le
  set m := ⌈C₀ / Real.log 2⌉₊ with hmdef
  -- the eventual conditions
  have hev : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 2 ≤ x ^ (1 - εw) ∧
      (∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ (L + 1)), 1 / (p : ℝ) ≤ B) ∧
      (3 + 4 * Real.log x) ^ (2 * m + 2) ≤ x ^ c₁ ∧ 24 * 2 ^ (2 * k + 7) ≤ x ^ (1 / 8 : ℝ) ∧
      (3 + 4 * Real.log x) ^ (n + 1) ≤ x ^ (c₁ / 2) := by
    have h1 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - εw)).eventually_ge_atTop 2
    have h2 := SieveRough.evLe_sum_inv hεw (by linarith : εw ≤ L + 1) 1 one_pos
    have h3 := SieveTypeIIU.ev_log_pow_le (2 * m + 2) hc₁0
    have h4 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop
      (24 * 2 ^ (2 * k + 7) : ℝ)
    have h5 := SieveTypeIIU.ev_log_pow_le (n + 1) (by positivity : (0 : ℝ) < c₁ / 2)
    filter_upwards [eventually_ge_atTop (3 : ℝ), h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5 hx6
    exact ⟨hx1, hx2, by rw [hBdef]; linarith, hx4, hx5, hx6⟩
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ, hδ, max q₀ q₁, ?_⟩
  intro q _ hq a' ha' Y₁ Y₂ hY₁ hY₂ M hM cc e₁ e₂ Pr hPr hΛ hpiv hgeo
  obtain ⟨hx3, hx1w, hsumB, hVx, hWx, hFx⟩ := hq₁ q (le_trans (le_max_right _ _) hq)
  have hq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hq
  set x : ℝ := (q : ℝ) with hxdef
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hxe1 : 1 ≤ x ^ εw := Real.one_le_rpow hx1 hεw.le
  set w : ℕ := ⌈x ^ εw⌉₊ with hwdef
  have hw2 : 2 ≤ w := Nat.lt_ceil.2 (by exact_mod_cast Real.one_lt_rpow (by linarith) hεw)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
  have hwle : (w : ℝ) ≤ x ^ εw + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hxx : x ^ εw + 1 ≤ x := by
    have e : x ^ (1 - εw) * x ^ εw = x := by rw [← Real.rpow_add hx0]; simp
    calc x ^ εw + 1 ≤ 2 * x ^ εw := by linarith
      _ ≤ x ^ (1 - εw) * x ^ εw := mul_le_mul_of_nonneg_right hx1w (by positivity)
      _ = x := e
  have hwx : (w : ℝ) ≤ x := le_trans hwle hxx
  have hw2x : (w : ℝ) ≤ 2 * x ^ εw := by linarith
  have hxw : x ^ εw ≤ w := Nat.le_ceil _
  set J : ℕ := SieveProp6.Jw w with hJdef
  obtain ⟨hJw, h2J, hJ3⟩ := SieveProp6.Jw_spec hw2
  set N₁ : ℕ := ⌊x ^ L⌋₊ with hN₁def
  set N₂ : ℕ := ⌊2 * x ^ L⌋₊ with hN₂def
  have hxL : 0 ≤ x ^ L := by positivity
  have hN : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hxL1 : x ^ (L + 1) = x * x ^ L := by rw [Real.rpow_add hx0, Real.rpow_one, mul_comm]
  have hxL0 : 0 < x ^ L := by positivity
  have hN₂x' : (N₂ : ℝ) < x ^ (L + 1) := by
    have h1 : (N₂ : ℝ) ≤ 2 * x ^ L := Nat.floor_le (by positivity)
    have h2 := mul_lt_mul_of_pos_right (by linarith : (2 : ℝ) < x) hxL0
    rw [hxL1]
    linarith
  have hN₂x : (N₂ : ℝ) ≤ x ^ (L + 1) := hN₂x'.le
  -- the entries
  have hent : ∀ {K : ℕ} (Y : Finset (Fin K → ℕ)),
      (∀ y ∈ Y, StrictAnti y ∧ ∀ i, (y i).Prime ∧ w ≤ y i ∧ y i ≤ N₂) →
      Y ⊆ Fintype.piFinset fun _ => SieveRough.primesIn (x ^ εw) (x ^ (L + 1)) := by
    intro K Y hY y hy
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨hp, hwy, hyN⟩ := (hY y hy).2 i
    have h1 : x ^ εw ≤ (y i : ℝ) := le_trans hxw (by exact_mod_cast hwy)
    have h2 : (y i : ℝ) ≤ N₂ := by exact_mod_cast hyN
    exact SieveRough.mem_primesIn.2 ⟨hp, h1, lt_of_le_of_lt h2 hN₂x'⟩
  have hYp₁ : ∀ y ∈ Y₁, StrictAnti y ∧ ∀ i, (y i).Prime := fun y hy => ⟨(hY₁ y hy).1, fun i => ((hY₁ y hy).2 i).1⟩
  have hYp₂ : ∀ y ∈ Y₂, StrictAnti y ∧ ∀ i, (y i).Prime := fun y hy => ⟨(hY₂ y hy).1, fun i => ((hY₂ y hy).2 i).1⟩
  -- the weights
  have hT : ∀ j, ∀ p ∈ SieveLeaf.T (w : ℝ) J j, p.Prime := fun j p hp => SieveLeaf.prime_of_mem_T hp
  have hdisj := SieveLeaf.T_disjoint hw1 J
  have hkk : ∀ j : Fin J, Even (lev k J j) := fun j => by
    rcases hk with ⟨r, hr⟩
    exact ⟨r + j, by rw [lev]; omega⟩
  have hkk1 : ∀ j : Fin J, 1 ≤ lev k J j := fun j => by rw [lev]; omega
  set fmax : ℝ := (w : ℝ) ^ ((2 * k + 4 : ℕ) : ℝ) with hfmaxdef
  have hfmax1 : 1 ≤ fmax := Real.one_le_rpow hw1 (by positivity)
  have hfmaxx : fmax ≤ x ^ ((2 * k + 4 : ℕ) : ℝ) := Real.rpow_le_rpow (by positivity) hwx (by positivity)
  have hS₁ : ∀ σ ∈ wS₁ (SieveLeaf.T (w : ℝ) J) (lev k J),
      ∀ j, σ j ∈ Ftr (SieveLeaf.T (w : ℝ) J j) (lev k J j) ∨ σ j ∈ Fes (SieveLeaf.T (w : ℝ) J j) (lev k J j) :=
    fun σ hσ j => Or.inl (Fintype.mem_piFinset.1 hσ j)
  -- the weights' bounds
  have hYP : ∀ y ∈ Y₁, ((∏ i, y i : ℕ) : ℝ) ≤ x ^ ((L + 1) * K₁) := fun y hy => by
    push_cast
    calc ∏ i, (y i : ℝ) ≤ ∏ _i : Fin K₁, x ^ (L + 1) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ =>
            le_trans (by exact_mod_cast ((hY₁ y hy).2 i).2.2) hN₂x
      _ = x ^ ((L + 1) * K₁) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
            ← Real.rpow_mul hx0.le]
  have hPD : x ^ ((L + 1) * K₁) * x ^ ((2 * k + 4 : ℕ) : ℝ) ≤ x ^ D := by
    rw [← Real.rpow_add hx0, hDdef]
    push_cast
    exact le_refl _
  obtain ⟨hMf₁, hMf₂⟩ := fibres_le_rpow hx1 (by omega : 1 ≤ w) hwx hε'0 hε'1 hε'D hn hFx Y₁ hYp₁ hYP hPD
  have hW := W_le_rpow hx1 hεw hεwk hWx hw2 hw2x
  have hV := V_le_rpow (by omega : 1 ≤ w) hwx hC₀ hC k hVx
  -- the estimate
  have hmain := H q hq₀ a' ha' (fun _ => SieveRough.primesIn (x ^ εw) (x ^ (L + 1)))
    (fun _ => SieveRough.primesIn (x ^ εw) (x ^ (L + 1)))
    (fun _ p hp => (SieveRough.mem_primesIn.1 hp).2.1) (fun _ p hp => (SieveRough.mem_primesIn.1 hp).2.1)
    (fun _ => hsumB) (fun _ => hsumB) Y₁ Y₂ (hent Y₁ fun y hy => ⟨(hY₁ y hy).1, (hY₁ y hy).2⟩)
    (hent Y₂ fun y hy => ⟨(hY₂ y hy).1, (hY₂ y hy).2⟩)
    (fun d => le_trans (by exact_mod_cast card_fibre_le_one Y₂ hYp₂ d) (Real.one_le_rpow hx1 hc₁0.le))
    hM cc e₁ e₂ Pr hPr hΛ hpiv (Rs (SieveLeaf.T (w : ℝ) J)) (wS₁ (SieveLeaf.T (w : ℝ) J) (lev k J)) wf wl₁
    (wS₂ (SieveLeaf.T (w : ℝ) J) (lev k J)) wf₂ wl₂ (fun σ hσ => one_le_wf hT (sub_of_mem_wS₁ hσ))
    (fun z hz => one_le_wf hT (sub_of_mem_wS₂ hz)) (R_le _ _ hkk hkk1 hT hdisj) (le_R _ _ hkk hkk1 hT hdisj)
    fmax hfmax1 (fun σ hσ => wf_le hw1 (hS₁ σ hσ)) (fun z hz => wf_le hw1 (mem_wS₂_cases hz)) hMf₁ hMf₂ hW
    hV (fun y₁ hy₁ y₂ hy₂ hP => by
      rw [hfmaxdef, Real.rpow_natCast]
      exact hgeo y₁ hy₁ y₂ hy₂ hP)
  -- the leaf counts
  have hconv : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a' n * (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough w n then 1 else 0) =
        ((∑ m ∈ Finset.range (N₂ + 1), rng N₁ N₂ ((∏ i, y₁ i) * ∏ i, y₂ i) m * Rs (SieveLeaf.T (w : ℝ) J) m *
          dwR q a' ((∏ i, y₁ i) * (∏ i, y₂ i) * m) : ℝ) : ℂ) := by
    intro y₁ hy₁ y₂ hy₂
    have hp₁ := fun i => ((hY₁ y₁ hy₁).2 i).1
    have hp₂ := fun i => ((hY₂ y₂ hy₂).2 i).1
    have h1 := one_le_prod hp₁
    have h2 := one_le_prod hp₂
    exact count_eq_rsum q a' N₁ N₂ (Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by omega))) (by omega) hJw
      (rough_mul (rough_prod hp₁ fun i => ((hY₁ y₁ hy₁).2 i).2.1) (rough_prod hp₂ fun i => ((hY₂ y₂ hy₂).2 i).2.1))
  have hLHS : (∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℂ) else 0) *
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a' n * (if (∏ i, y₁ i) * (∏ i, y₂ i) ∣ n ∧ rough w n then 1 else 0)) =
      ((∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) *
        ∑ m ∈ Finset.range (N₂ + 1), rng N₁ N₂ ((∏ i, y₁ i) * ∏ i, y₂ i) m * Rs (SieveLeaf.T (w : ℝ) J) m *
          dwR q a' ((∏ i, y₁ i) * (∏ i, y₂ i) * m) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y₁ hy₁ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y₂ hy₂ => ?_
    rw [hconv y₁ hy₁ y₂ hy₂, Complex.ofReal_mul, Complex.ofReal_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hLHS, Complex.norm_real, Real.norm_eq_abs]
  refine hmain.trans ?_
  -- the main term
  have hgap := abs_gap_le hw2 hJw (NeZero.pos q) hC₀ hC hk hk1 hkC
  have hsum : 0 ≤ ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) /
      (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      div_nonneg (Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num) (Nat.cast_nonneg _)
  have hNN : (0 : ℝ) ≤ (N₂ : ℝ) - N₁ := by
    have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
    linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast hw2)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hmt := mul_le_mul_of_nonneg_left hgap (div_nonneg hNN hx0.le)
  have e : ((N₂ : ℝ) - N₁) / x * (SieveProp6.zeta C₀ k * (x / (q.totient * Real.log w))) =
      SieveProp6.zeta C₀ k * (((N₂ : ℝ) - N₁) / (q.totient * Real.log w)) := by
    field_simp
  rw [e] at hmt
  have := mul_le_mul_of_nonneg_right hmt hsum
  linarith

end SieveP6Leaves
