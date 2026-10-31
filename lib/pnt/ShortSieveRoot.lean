import ShortSieveTypeI
import ShortSieveDrop

/-!
# The root terms of Li's decomposition

Li's decomposition (his (9)) starts `S(A, x^{1/2}) = S(A, x^{ν(0)}) − Σ_{p₁} S(A_{p₁}, x^{ν(α₁)}) + Σ₃`, with
`ν(α) = liNu θ γ α` and `α₁ = log p₁/log x`. The first two sums are Type I sums, the second one at a level that
varies with `p₁`. Their asymptotic formulas, from Li's Lemma 3.1 as a hypothesis:

* `abs_S1_sub_le`: `S(A, x^ν)` for `0 < ν ≤ ν(0)`: the lemma with no primes, and `S(B, x^ν) ≪ x^{1−ρ}/log x`.
* `abs_S2_sub_le`: `Σ_{x^a < p ≤ x^b} S(A_p, x^{ν(log p/log x)})` for a level `ν` that is nonincreasing, Lipschitz
  and at most Li's on `(a, b]`, as on each piece of `liNu`. The primes are cut into blocks `(X_i, X_{i+1}]`,
  `X_i = x^a (3/2)^i` (`sum_blocks`). On a block the level lies between its values at the two ends, and the lemma
  applies at both (`li_one`, `abs_block_pos_le`). The `v` counted at the lower level but not at the upper one have
  their least prime factor in `[z, 2^K z]`, `z` the lower level (`sA_sub_le`), so in the comparison interval the gap
  is `O(y/log² x)` per unit of `Σ 1/p` (`sB_gap_le`, from Chebyshev's `θ(t) ≤ t log 4`). The first block, where the
  lemma may not apply at the upper level, is `O(y/log² x)` by the lemma at a constant level below both
  (`abs_block_zero_le`).
* `abs_S2_liNu_sub_le`: the second sum with Li's level `liNu θ γ` on `(x^{a₀}, x^{1/2}]`: on each piece
  `(1/2 − h(2θ − 1), 1/2 − (h − 1)(2θ − 1)]` the level is `min(2(θ − α)/(2h − 1), γ)` (`liNu_eq_nuPiece`), which is
  nonincreasing, `2`-Lipschitz and at least `2θ − 1`, so `abs_S2_sub_le` applies piece by piece.
-/

open Finset Real Filter

namespace ShortSieveRoot

open ShortSieveJ ShortSieveLi

open Classical

/-! ### Counts in the comparison interval -/

/-- `S(A_{∏g}, x^ν)` is at most `Ψ(x/P, y/P; ⌈x^ν⌉)`, `P = ∏ g ≥ 1`. -/
theorem sA_le_psi {ι : Type*} [Fintype ι] [DecidableEq ι] (ν x y : ℝ) (hyx : y ≤ x) (g : ι → ℕ)
    (hg : 0 < ∏ j, g j) :
    sA ν x y g ≤ ShortSieveLong.Psi (x / ((∏ j, g j : ℕ) : ℝ)) (y / ((∏ j, g j : ℕ) : ℝ)) ⌈x ^ ν⌉₊ := by
  unfold sA ShortSieveLong.Psi ShortSieveLong.roughSet
  refine card_le_card_of_injOn id (fun v hv => ?_) (fun _ _ _ _ h => h)
  rw [mem_coe, mem_filter] at hv
  obtain ⟨-, hr, hlo, hhi⟩ := hv
  have hP0 : (0 : ℝ) < ((∏ j, g j : ℕ) : ℝ) := by exact_mod_cast hg
  rw [Nat.cast_mul] at hlo hhi
  rw [mem_coe, mem_filter, mem_Ioc]
  refine ⟨⟨?_, ?_⟩, fun q hq => ShortSieveDrop.le_of_mem_primeFactors hr hq⟩
  · have h1 : x / ((∏ j, g j : ℕ) : ℝ) - y / ((∏ j, g j : ℕ) : ℝ) < v := by
      rw [← sub_div, div_lt_iff₀ hP0]; linarith
    have h2 : (⌊x / ((∏ j, g j : ℕ) : ℝ) - y / ((∏ j, g j : ℕ) : ℝ)⌋₊ : ℝ) < v :=
      lt_of_le_of_lt (Nat.floor_le (by rw [← sub_div]; exact div_nonneg (by linarith) hP0.le)) h1
    exact_mod_cast h2
  · apply Nat.le_floor
    simp only [id]
    rw [le_div_iff₀ hP0]
    linarith

/-- **Rough numbers at a level, uniformly.** Let `0 < ν₁`, `0 < ρ` with `12ρ < ν₁`, and `c > 0`. For large `x`, every
level `ν ∈ [ν₁, 1]` and `1 ≤ P ≤ x^{1−c}`: `Ψ(x/P, x^{1−ρ}/P; ⌈x^ν⌉) ≤ 2(x^{1−ρ}/P)/(ν log x)`
(`ShortSieveLong.psi_le`, with `ω* ≤ 1`). -/
theorem psi_level_le {ν₁ ρ c : ℝ} (hν₁ : 0 < ν₁) (hρ : 0 < ρ) (hρν : 12 * ρ < ν₁) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ ν P : ℝ, ν₁ ≤ ν → ν ≤ 1 → 1 ≤ P → P ≤ x ^ (1 - c) →
      (ShortSieveLong.Psi (x / P) (x ^ (1 - ρ) / P) ⌈x ^ ν⌉₊ : ℝ) ≤ 2 * (x ^ (1 - ρ) / P) / (ν * Real.log x) := by
  set σ : ℝ := ρ / ν₁ with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hρ.le hν₁.le
  have hσ12 : σ < 1 / 12 := by rw [hσ, div_lt_iff₀ hν₁]; linarith
  obtain ⟨z₀, hz₀⟩ := ShortSieveLong.psi_le hσ0 hσ12 (1 / ν₁) one_pos
  have hxρ : ∀ᶠ x : ℝ in atTop, x ^ (-ρ) ≤ 1 / 2 :=
    (tendsto_rpow_neg_atTop hρ).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_gt_atTop 1, hxρ, (tendsto_rpow_atTop hν₁).eventually_ge_atTop (z₀ : ℝ),
    (tendsto_rpow_atTop hc).eventually_ge_atTop 2] with x hx1 hxρ hxz hxc ν P hν1 hν hP1 hPc
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hP0 : 0 < P := by linarith
  have hz : x ^ ν ≤ (⌈x ^ ν⌉₊ : ℝ) := Nat.le_ceil _
  have hxν : x ^ ν₁ ≤ x ^ ν := Real.rpow_le_rpow_of_exponent_le hx1.le hν1
  have hzpos : (0 : ℝ) < ⌈x ^ ν⌉₊ := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hz
  have hlz : ν * Real.log x ≤ Real.log ⌈x ^ ν⌉₊ := by
    rw [← Real.log_rpow hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hz
  have hνlx : 0 < ν * Real.log x := mul_pos (by linarith) hlx
  have hy : x ^ (1 - ρ) = x ^ (-ρ) * x := by rw [sub_eq_add_neg, add_comm, Real.rpow_add hx0, Real.rpow_one]
  -- `x/P ≥ x^c ≥ 2`
  have hX2 : 2 ≤ x / P := by
    have hxP : x ^ c ≤ x / P := by
      rw [le_div_iff₀ hP0]
      calc x ^ c * P ≤ x ^ c * x ^ (1 - c) := mul_le_mul_of_nonneg_left hPc (Real.rpow_nonneg hx0.le _)
        _ = x := by rw [← Real.rpow_add hx0]; norm_num
    linarith
  have hzz : z₀ ≤ ⌈x ^ ν⌉₊ := by
    have : (z₀ : ℝ) ≤ ⌈x ^ ν⌉₊ := le_trans hxz (le_trans hxν hz)
    exact_mod_cast this
  have hzσ : ((⌈x ^ ν⌉₊ : ℕ) : ℝ) ^ (-σ) ≤ x ^ (-ρ) := by
    have h1 : ν₁ * Real.log x ≤ Real.log ⌈x ^ ν⌉₊ := le_trans (mul_le_mul_of_nonneg_right hν1 hlx.le) hlz
    have h2 : σ * (ν₁ * Real.log x) = ρ * Real.log x := by rw [hσ]; field_simp
    have h3 : Real.log ⌈x ^ ν⌉₊ * (-σ) ≤ Real.log x * (-ρ) := by nlinarith
    calc ((⌈x ^ ν⌉₊ : ℕ) : ℝ) ^ (-σ) = Real.exp (Real.log ⌈x ^ ν⌉₊ * (-σ)) := Real.rpow_def_of_pos hzpos _
      _ ≤ Real.exp (Real.log x * (-ρ)) := Real.exp_le_exp.2 h3
      _ = x ^ (-ρ) := (Real.rpow_def_of_pos hx0 _).symm
  have hψ := hz₀ ⌈x ^ ν⌉₊ hzz (x / P) (x ^ (1 - ρ) / P) hX2
    (by rw [hy, mul_div_assoc]; exact mul_le_mul_of_nonneg_right hzσ (div_nonneg hx0.le hP0.le))
    (by rw [hy, mul_div_assoc]; nlinarith [div_nonneg hx0.le hP0.le])
    (by
      have h1 : Real.log (x / P) ≤ Real.log x := Real.log_le_log (div_pos hx0 hP0) (div_le_self hx0.le hP1)
      have h2 : Real.log x ≤ 1 / ν₁ * Real.log ⌈x ^ ν⌉₊ := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hν₁]
        nlinarith [mul_le_mul_of_nonneg_right hν1 hlx.le]
      linarith)
  have hH0 : 0 ≤ x ^ (1 - ρ) / P := div_nonneg (Real.rpow_nonneg hx0.le _) hP0.le
  calc (ShortSieveLong.Psi (x / P) (x ^ (1 - ρ) / P) ⌈x ^ ν⌉₊ : ℝ) ≤
      (SieveCert.omegaC (Real.log (x / P) / Real.log ⌈x ^ ν⌉₊) + 1) * (x ^ (1 - ρ) / P) /
        Real.log ⌈x ^ ν⌉₊ := hψ
    _ ≤ 2 * (x ^ (1 - ρ) / P) / Real.log ⌈x ^ ν⌉₊ := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        have := SieveRough.omegaC_le_one (Real.log (x / P) / Real.log ⌈x ^ ν⌉₊)
        exact mul_le_mul_of_nonneg_right (by linarith) hH0
    _ ≤ 2 * (x ^ (1 - ρ) / P) / (ν * Real.log x) :=
        div_le_div_of_nonneg_left (by positivity) hνlx hlz

/-! ### The first root term -/

/-- `S(A, x^ν)`: the `n ∈ (x − y, x]` free of primes below `x^ν`, as Li's Type I sum with no primes. -/
noncomputable def sOne (ν x y : ℝ) : ℕ := sA ν x y (Fin.elim0 : Fin 0 → ℕ)

/-- **The first root term.** With Li's Lemma 3.1 (`θ > 1/3`), for `0 < ν ≤ ν(0)` and `12ρ < ν ≤ 1`, there is `C` with:
for every `ε ∈ (0, 1]`, for large `x` and `y ∈ [x^θ, x^{1−ρ}]`,
`|S(A, x^ν) − (y/x^{1−ρ}) S(B, x^ν)| ≤ εC y/log x`. -/
theorem abs_S1_sub_le {θ γ ρ ν : ℝ} (hLi : LiLemma31 θ γ ρ) (hθ : 1 / 3 < θ) (hρ : 0 < ρ) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) (hρν : 12 * ρ < ν) (hν : ν ≤ liNu θ γ 0) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(sOne ν x y : ℝ) - y / x ^ (1 - ρ) * sOne ν x (x ^ (1 - ρ))| ≤ ε * C * y / Real.log x := by
  refine ⟨2 / ν, fun ε hε _ => ?_⟩
  set η : ℝ := min ((3 * θ - 1) / 2) ((1 + θ) / 5) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hL := hLi (Fin 0) Fin.elim0 1 η ε one_pos hη0 hε
  have hB := psi_level_le hν0 hρ hρν (c := 1) one_pos
  filter_upwards [hL, hB, eventually_gt_atTop 1] with x hx hxB hx1 y hy1 hy2
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hgrp : ∀ i : Fin 3, grpProd (Fin.elim0 : Fin 0 → Fin 3) i (Fin.elim0 : Fin 0 → ℕ) = 1 := fun i => by
    unfold grpProd; simp
  have htup : typeISum ν x y (Fin.elim0 : Fin 0 → ℕ) Fin.elim0 = sOne ν x y ∧
      typeISum ν x (x ^ (1 - ρ)) (Fin.elim0 : Fin 0 → ℕ) Fin.elim0 = sOne ν x (x ^ (1 - ρ)) := by
    have hu : ShortSieveTypeII.tuples (Fin.elim0 : Fin 0 → ℕ) Fin.elim0 = {Fin.elim0} := by
      ext g
      simp only [mem_singleton]
      constructor
      · intro _; funext i; exact i.elim0
      · intro _; rw [mem_tuples]; intro j; exact j.elim0
    unfold typeISum sOne
    rw [hu, sum_singleton, sum_singleton]
    exact ⟨rfl, rfl⟩
  have h := hx y hy1 hy2 ν Fin.elim0 Fin.elim0 (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (fun i => by simp [grpProd]) (by simp [grpProd])
    (by simp only [grpProd, univ_eq_empty, filter_empty, prod_empty, Nat.cast_one, Real.log_one, zero_div, hη,
      sub_self, le_refl]) hν0
    (by simpa [grpProd] using hν)
  rw [htup.1, htup.2] at h
  -- `S(B, x^ν) ≤ 2x^{1−ρ}/(ν log x)`
  have hS : (sOne ν x (x ^ (1 - ρ)) : ℝ) ≤ 2 * x ^ (1 - ρ) / (ν * Real.log x) := by
    have h1 := sA_le_psi ν x (x ^ (1 - ρ)) (by
      calc x ^ (1 - ρ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        _ = x := Real.rpow_one x) (Fin.elim0 : Fin 0 → ℕ) (by simp)
    have h2 := hxB ν 1 le_rfl hν1 le_rfl (by simp)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Nat.cast_one, div_one] at h1 h2
    unfold sOne
    calc (sA ν x (x ^ (1 - ρ)) Fin.elim0 : ℝ) ≤ ShortSieveLong.Psi x (x ^ (1 - ρ)) ⌈x ^ ν⌉₊ := by exact_mod_cast h1
      _ ≤ 2 * x ^ (1 - ρ) / (ν * Real.log x) := h2
  have hc0 : 0 ≤ y / x ^ (1 - ρ) := div_nonneg (by linarith [Real.rpow_nonneg hx0.le θ]) (Real.rpow_nonneg hx0.le _)
  calc |(sOne ν x y : ℝ) - y / x ^ (1 - ρ) * sOne ν x (x ^ (1 - ρ))| ≤
      ε * (y / x ^ (1 - ρ)) * sOne ν x (x ^ (1 - ρ)) := h
    _ ≤ ε * (y / x ^ (1 - ρ)) * (2 * x ^ (1 - ρ) / (ν * Real.log x)) :=
        mul_le_mul_of_nonneg_left hS (mul_nonneg hε.le hc0)
    _ = ε * (2 / ν) * y / Real.log x := by
        have : x ^ (1 - ρ) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
        field_simp

/-! ### Levels -/

/-- A higher level sifts more: `S(A_{∏g}, x^{ν′}) ≤ S(A_{∏g}, x^ν)` for `ν ≤ ν′`, `x ≥ 1`. -/
theorem sA_anti {ι : Type*} [Fintype ι] [DecidableEq ι] {ν ν' x : ℝ} (hx : 1 ≤ x) (h : ν ≤ ν') (y : ℝ)
    (g : ι → ℕ) : sA ν' x y g ≤ sA ν x y g := by
  unfold sA
  refine card_le_card fun v hv => ?_
  rw [mem_filter] at hv ⊢
  refine ⟨hv.1, ShortSieveBuch.rough_mono hv.2.1 (Nat.ceil_le_ceil ?_), hv.2.2⟩
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- **The gap between two levels.** The `v` counted at the level `x^ν` but not at `x^{ν′}` have their least prime
factor `q ∈ [⌈x^ν⌉, ⌈x^{ν′}⌉)` and `v/q` free of primes below `x^ν`: the difference of the counts is at most
`Σ_q S(A_{∏g·q}, x^ν)`. -/
theorem sA_sub_le {n : ℕ} {ν ν' x : ℝ} (hx : 1 ≤ x) (h : ν ≤ ν') (y : ℝ) (g : Fin n → ℕ) :
    (sA ν x y g : ℝ) - sA ν' x y g ≤
      ∑ q ∈ (Ico ⌈x ^ ν⌉₊ ⌈x ^ ν'⌉₊).filter Nat.Prime, (sA ν x y (Fin.snoc g q) : ℝ) := by
  set z := ⌈x ^ ν⌉₊ with hz
  set z' := ⌈x ^ ν'⌉₊ with hz'
  have hzz : z ≤ z' := Nat.ceil_le_ceil (Real.rpow_le_rpow_of_exponent_le hx h)
  set W : ℕ → Prop := fun n => x - y < (n : ℝ) ∧ (n : ℝ) ≤ x with hW
  set D := {v ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough z v ∧ ¬ SieveTree.rough z' v ∧ W ((∏ j, g j) * v)} with hD
  -- the difference is the count of `D`
  have hdiff : (sA ν x y g : ℝ) - sA ν' x y g ≤ #D := by
    have hsplit : sA ν x y g ≤ sA ν' x y g + #D := by
      unfold sA
      rw [← hz, ← hz']
      calc #{v ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough z v ∧ W ((∏ j, g j) * v)} ≤
          #({v ∈ Icc 1 ⌊x⌋₊ | SieveTree.rough z' v ∧ W ((∏ j, g j) * v)} ∪ D) := by
            refine card_le_card fun v hv => ?_
            rw [mem_filter] at hv
            rw [mem_union, mem_filter, hD, mem_filter]
            by_cases h' : SieveTree.rough z' v
            · exact Or.inl ⟨hv.1, h', hv.2.2⟩
            · exact Or.inr ⟨hv.1, hv.2.1, h', hv.2.2⟩
        _ ≤ _ := card_union_le _ _
    have : ((sA ν x y g : ℕ) : ℝ) ≤ (sA ν' x y g : ℝ) + (#D : ℝ) := by exact_mod_cast hsplit
    linarith
  refine le_trans hdiff ?_
  -- by the least prime factor
  have hmaps : (D : Set ℕ).MapsTo Nat.minFac ((Ico z z').filter Nat.Prime) := by
    intro v hv
    rw [mem_coe, hD, mem_filter, mem_Icc] at hv
    obtain ⟨⟨hv1, -⟩, hr, hr', -⟩ := hv
    have hv1' : v ≠ 1 := by
      rintro rfl
      exact hr' fun p _ hp hdvd => hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
    have hmp := Nat.minFac_prime hv1'
    rw [mem_coe, mem_filter, mem_Ico]
    refine ⟨⟨?_, ?_⟩, hmp⟩
    · by_contra hlt
      exact hr _ (not_le.1 hlt) hmp (Nat.minFac_dvd v)
    · by_contra hle
      apply hr'
      intro p hp hpp hdvd
      have := Nat.minFac_le_of_dvd hpp.two_le hdvd
      omega
  rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine sum_le_sum fun q hq => ?_
  have hqp : q.Prime := (mem_filter.1 hq).2
  have hprod : ∏ j, Fin.snoc g q j = (∏ j, g j) * q := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  unfold sA
  rw [hprod, ← hz]
  refine Nat.cast_le.2 (card_le_card_of_injOn (fun v => v / q) (fun v hv => ?_) (fun v hv v' hv' he => ?_))
  · rw [mem_coe, mem_filter, hD, mem_filter, mem_Icc] at hv
    obtain ⟨⟨⟨hv1, hvx⟩, hr, -, hw⟩, hvq⟩ := hv
    have hdvd : q ∣ v := hvq ▸ Nat.minFac_dvd v
    have hv0 : 0 < v / q := Nat.div_pos (Nat.le_of_dvd hv1 hdvd) hqp.pos
    rw [mem_coe, mem_filter, mem_Icc]
    refine ⟨⟨hv0, le_trans (Nat.div_le_self v q) hvx⟩, fun p hp hpp hpd => ?_, ?_⟩
    · exact hr p hp hpp (dvd_trans hpd (Nat.div_dvd_of_dvd hdvd))
    · rw [mul_assoc, Nat.mul_div_cancel' hdvd]; exact hw
  · rw [mem_coe, mem_filter] at hv hv'
    have h1 : q ∣ v := hv.2 ▸ Nat.minFac_dvd v
    have h2 : q ∣ v' := hv'.2 ▸ Nat.minFac_dvd v'
    exact (Nat.div_left_inj h1 h2).1 he

/-- **Chebyshev's bound for a short range of primes.** For `2 ≤ z`, `Σ_{z ≤ q < z′} 1/q ≤ log 4 · z′/(z log z)`, from
`θ(z′) ≤ z′ log 4` (`Chebyshev.theta_le_log4_mul_x`). -/
theorem sum_inv_primes_Ico_le {z z' : ℕ} (hz : 2 ≤ z) :
    ∑ q ∈ (Ico z z').filter Nat.Prime, (1 : ℝ) / q ≤ Real.log 4 * z' / (z * Real.log z) := by
  set Q := (Ico z z').filter Nat.Prime with hQ
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hmem : ∀ q ∈ Q, z ≤ q ∧ q < z' ∧ q.Prime := fun q hq => by
    rw [hQ, mem_filter, mem_Ico] at hq; exact ⟨hq.1.1, hq.1.2, hq.2⟩
  -- `#Q · log z ≤ θ(z′) ≤ z′ log 4`
  have hθ : (#Q : ℝ) * Real.log z ≤ Real.log 4 * z' := by
    calc (#Q : ℝ) * Real.log z = ∑ q ∈ Q, Real.log z := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ Q, Real.log q := sum_le_sum fun q hq =>
          Real.log_le_log hz0 (by exact_mod_cast (hmem q hq).1)
      _ ≤ Chebyshev.theta z' := by
          unfold Chebyshev.theta
          rw [Nat.floor_natCast]
          refine sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) (fun q _ _ => Real.log_natCast_nonneg q)
          obtain ⟨h1, h2, h3⟩ := hmem q hq
          rw [mem_filter, mem_Ioc]
          exact ⟨⟨h3.pos, h2.le⟩, h3⟩
      _ ≤ Real.log 4 * z' := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
  calc ∑ q ∈ Q, (1 : ℝ) / q ≤ ∑ q ∈ Q, 1 / (z : ℝ) := sum_le_sum fun q hq =>
        one_div_le_one_div_of_le hz0 (by exact_mod_cast (hmem q hq).1)
    _ = (#Q : ℝ) / z := by rw [sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ Real.log 4 * z' / (z * Real.log z) := by
        rw [div_le_div_iff₀ hz0 (mul_pos hz0 hlz)]
        nlinarith

/-- **The sandwich.** If `a_A ∈ [l_A, u_A]`, `a_B ∈ [l_B, u_B]` with `0 ≤ l_B ≤ u_B`, and `l_A, u_A` are within
`εc l_B`, `εc u_B` of `c l_B`, `c u_B` (`c, ε ≥ 0`), then `|a_A − c a_B| ≤ c(u_B − l_B) + εc u_B`. -/
theorem abs_sub_le_of_sandwich {aA aB lA uA lB uB c ε : ℝ} (h1 : lA ≤ aA) (h2 : aA ≤ uA) (h3 : lB ≤ aB)
    (h4 : aB ≤ uB) (hl : |lA - c * lB| ≤ ε * c * lB) (hu : |uA - c * uB| ≤ ε * c * uB) (hc : 0 ≤ c)
    (hε : 0 ≤ ε) (hlu : lB ≤ uB) :
    |aA - c * aB| ≤ c * (uB - lB) + ε * c * uB := by
  have hl' := abs_le.1 hl
  have hu' := abs_le.1 hu
  have hcl : c * lB ≤ c * aB := mul_le_mul_of_nonneg_left h3 hc
  have hcu : c * aB ≤ c * uB := mul_le_mul_of_nonneg_left h4 hc
  have hεc : ε * c * lB ≤ ε * c * uB := mul_le_mul_of_nonneg_left hlu (mul_nonneg hε hc)
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Blocks -/

/-- The block of `t > X₀` for the ratio `λ > 1`: the `i` with `X₀λ^i < t ≤ X₀λ^{i+1}`. -/
noncomputable def blockIdx (X₀ lam t : ℝ) : ℕ := ⌈Real.log (t / X₀) / Real.log lam⌉₊ - 1

theorem blockIdx_spec {X₀ lam t : ℝ} (hX₀ : 0 < X₀) (hlam : 1 < lam) (ht : X₀ < t) :
    X₀ * lam ^ blockIdx X₀ lam t < t ∧ t ≤ X₀ * lam ^ (blockIdx X₀ lam t + 1) := by
  have hll : 0 < Real.log lam := Real.log_pos hlam
  have ht0 : 0 < t := by linarith
  set u := Real.log (t / X₀) / Real.log lam with hu
  have hu0 : 0 < u := div_pos (Real.log_pos (by rw [one_lt_div hX₀]; exact ht)) hll
  have hc1 : 1 ≤ ⌈u⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  have hidx : (blockIdx X₀ lam t : ℝ) + 1 = ⌈u⌉₊ := by
    have e : blockIdx X₀ lam t + 1 = ⌈u⌉₊ := by unfold blockIdx; rw [← hu]; omega
    exact_mod_cast e
  have hlt : (blockIdx X₀ lam t : ℝ) < u := by
    have := Nat.ceil_lt_add_one hu0.le; linarith
  have hle : u ≤ (blockIdx X₀ lam t : ℝ) + 1 := by rw [hidx]; exact Nat.le_ceil u
  have hlog : Real.log t = Real.log X₀ + u * Real.log lam := by
    rw [hu, div_mul_cancel₀ _ hll.ne', Real.log_div ht0.ne' hX₀.ne']; ring
  constructor
  · rw [← Real.log_lt_log_iff (by positivity) ht0, Real.log_mul hX₀.ne' (by positivity), Real.log_pow, hlog]
    nlinarith
  · rw [← Real.log_le_log_iff ht0 (by positivity), Real.log_mul hX₀.ne' (by positivity), Real.log_pow, hlog]
    push_cast
    nlinarith

theorem blockIdx_eq {X₀ lam t : ℝ} (hX₀ : 0 < X₀) (hlam : 1 < lam) {i : ℕ} (h1 : X₀ * lam ^ i < t)
    (h2 : t ≤ X₀ * lam ^ (i + 1)) : blockIdx X₀ lam t = i := by
  have hll : 0 < Real.log lam := Real.log_pos hlam
  have ht0 : 0 < t := lt_trans (by positivity) h1
  have hlog1 : Real.log X₀ + i * Real.log lam < Real.log t := by
    have := Real.log_lt_log (by positivity) h1
    rwa [Real.log_mul hX₀.ne' (by positivity), Real.log_pow] at this
  have hlog2 : Real.log t ≤ Real.log X₀ + (i + 1) * Real.log lam := by
    have := Real.log_le_log ht0 h2
    rw [Real.log_mul hX₀.ne' (by positivity), Real.log_pow] at this
    push_cast at this
    exact this
  have hu1 : (i : ℝ) < Real.log (t / X₀) / Real.log lam := by
    rw [lt_div_iff₀ hll, Real.log_div ht0.ne' hX₀.ne']; linarith
  have hu2 : Real.log (t / X₀) / Real.log lam ≤ (i : ℝ) + 1 := by
    rw [div_le_iff₀ hll, Real.log_div ht0.ne' hX₀.ne']; linarith
  have hc : ⌈Real.log (t / X₀) / Real.log lam⌉₊ = i + 1 := by
    refine le_antisymm (Nat.ceil_le.2 (by push_cast; exact hu2)) (Nat.succ_le_of_lt ?_)
    exact Nat.lt_ceil.2 hu1
  unfold blockIdx
  rw [hc, Nat.add_sub_cancel]

/-! ### The comparison interval: one prime and the gap between two levels -/

/-- **One prime in the comparison interval.** For `0 < ν₁`, `12ρ < ν₁`, `b < 1`: for large `x`, every `g` with
`1 ≤ g 0 ≤ x^b` and level `ν ∈ [ν₁, 1]` has `S(B_{g 0}, x^ν) ≤ 2x^{1−ρ}/(g 0 · ν₁ log x)`. -/
theorem sB_one_le {ν₁ ρ b : ℝ} (hν₁ : 0 < ν₁) (hρ : 0 < ρ) (hρν : 12 * ρ < ν₁) (hb : b < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (g : Fin 1 → ℕ) (ν : ℝ), 1 ≤ g 0 → (g 0 : ℝ) ≤ x ^ b → ν₁ ≤ ν → ν ≤ 1 →
      (sA ν x (x ^ (1 - ρ)) g : ℝ) ≤ 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) := by
  filter_upwards [psi_level_le hν₁ hρ hρν (c := 1 - b) (by linarith), eventually_gt_atTop 1] with x hx hx1
    g ν hg1 hgb hν1 hν
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hprod : ∏ j, g j = g 0 := Fin.prod_univ_one g
  have hg0 : (1 : ℝ) ≤ g 0 := by exact_mod_cast hg1
  have h1 := sA_le_psi ν x (x ^ (1 - ρ)) (le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
    (le_of_eq (Real.rpow_one x))) g (by rw [hprod]; omega)
  rw [hprod] at h1
  have h2 := hx ν (g 0) hν1 hν hg0 (le_trans hgb (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)))
  calc (sA ν x (x ^ (1 - ρ)) g : ℝ) ≤ ShortSieveLong.Psi (x / g 0) (x ^ (1 - ρ) / g 0) ⌈x ^ ν⌉₊ := by
        exact_mod_cast h1
    _ ≤ 2 * (x ^ (1 - ρ) / g 0) / (ν * Real.log x) := h2
    _ ≤ 2 * (x ^ (1 - ρ) / g 0) / (ν₁ * Real.log x) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_right hν1 hlx.le)
    _ = 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) := by
        have : (g 0 : ℝ) ≠ 0 := by linarith
        field_simp

/-- **The gap between two levels in the comparison interval.** For `0 < ν₁`, `12ρ < ν₁` and `b + ν₂ < 1`: for large
`x`, every `g` with `1 ≤ g 0 ≤ x^b` and levels `ν₁ ≤ ν ≤ ν′ ≤ ν₂` with `x^{ν′} ≤ R x^ν` have
`S(B_{g 0}, x^ν) − S(B_{g 0}, x^{ν′}) ≤ 2x^{1−ρ}/(g 0 · ν₁ log x) · log 4 (R + 1)/(ν₁ log x)`. -/
theorem sB_gap_le {ν₁ ν₂ ρ b R : ℝ} (hν₁ : 0 < ν₁) (hρ : 0 < ρ) (hρν : 12 * ρ < ν₁) (hb : 0 ≤ b)
    (hbν : b + ν₂ < 1) (hR : 0 ≤ R) :
    ∀ᶠ x : ℝ in atTop, ∀ (g : Fin 1 → ℕ) (ν ν' : ℝ), 1 ≤ g 0 → (g 0 : ℝ) ≤ x ^ b → ν₁ ≤ ν → ν ≤ ν' →
      ν' ≤ ν₂ → x ^ ν' ≤ R * x ^ ν →
      (sA ν x (x ^ (1 - ρ)) g : ℝ) - sA ν' x (x ^ (1 - ρ)) g ≤
        2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) * (Real.log 4 * (R + 1) / (ν₁ * Real.log x)) := by
  set c : ℝ := (1 - b - ν₂) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hν2 : ν₂ ≤ 1 := by linarith
  filter_upwards [psi_level_le hν₁ hρ hρν hc0, eventually_gt_atTop 1,
    (tendsto_rpow_atTop hc0).eventually_ge_atTop 2, (tendsto_rpow_atTop hν₁).eventually_ge_atTop 2]
    with x hx hx1 hxc hxν g ν ν' hg1 hgb hν1 hνν hν' hR'
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hg0 : (1 : ℝ) ≤ g 0 := by exact_mod_cast hg1
  have hy0 : 0 ≤ x ^ (1 - ρ) := Real.rpow_nonneg hx0.le _
  set z := ⌈x ^ ν⌉₊ with hz
  set z' := ⌈x ^ ν'⌉₊ with hz'
  have hxz : x ^ ν ≤ (z : ℝ) := Nat.le_ceil _
  have hxz' : (z' : ℝ) ≤ x ^ ν' + 1 := (Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)).le
  have hxν' : x ^ ν₁ ≤ x ^ ν := Real.rpow_le_rpow_of_exponent_le hx1.le hν1
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) ≤ z := by linarith
    exact_mod_cast this
  have hz0 : (0 : ℝ) < z := by linarith
  have hlz : ν₁ * Real.log x ≤ Real.log z := by
    rw [← Real.log_rpow hx0]
    exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) (le_trans hxν' hxz)
  -- each `q` of the gap
  have hterm : ∀ q ∈ (Ico z z').filter Nat.Prime, (sA ν x (x ^ (1 - ρ)) (Fin.snoc g q) : ℝ) ≤
      2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) * (1 / q) := by
    intro q hq
    rw [mem_filter, mem_Ico] at hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.2.one_lt.le
    have hqz : (q : ℝ) ≤ x ^ ν' + 1 := le_trans (by exact_mod_cast hq.1.2.le) hxz'
    have hprod : ∏ j, Fin.snoc g q j = g 0 * q := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.prod_univ_one]
    have hP1 : (1 : ℝ) ≤ g 0 * q := one_le_mul_of_one_le_of_one_le hg0 hq1
    -- `g 0 · q ≤ x^{b + ν₂} · 2 ≤ x^{1 − c}`
    have hPc : (g 0 : ℝ) * q ≤ x ^ (1 - c) := by
      have h1 : x ^ ν' ≤ x ^ ν₂ := Real.rpow_le_rpow_of_exponent_le hx1.le hν'
      have h2 : (1 : ℝ) ≤ x ^ ν₂ := Real.one_le_rpow hx1.le (by linarith)
      have h3 : (q : ℝ) ≤ 2 * x ^ ν₂ := by linarith
      have h4 : x ^ b * (2 * x ^ ν₂) ≤ x ^ (1 - c) := by
        have e : x ^ (1 - c) = x ^ (b + ν₂) * x ^ c := by
          rw [← Real.rpow_add hx0]; congr 1; rw [hc]; ring
        rw [e, Real.rpow_add hx0]
        nlinarith [Real.rpow_nonneg hx0.le b, Real.rpow_nonneg hx0.le ν₂, mul_nonneg (Real.rpow_nonneg hx0.le b)
          (Real.rpow_nonneg hx0.le ν₂)]
      calc (g 0 : ℝ) * q ≤ x ^ b * (2 * x ^ ν₂) :=
            mul_le_mul hgb h3 (by linarith) (Real.rpow_nonneg hx0.le _)
        _ ≤ x ^ (1 - c) := h4
    have h1 := sA_le_psi ν x (x ^ (1 - ρ)) (le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
      (le_of_eq (Real.rpow_one x))) (Fin.snoc g q) (by rw [hprod]; exact Nat.mul_pos (by omega) hq.2.pos)
    rw [hprod] at h1
    push_cast at h1
    have h2 := hx ν (g 0 * q) hν1 (le_trans hνν (le_trans hν' hν2)) hP1 hPc
    calc (sA ν x (x ^ (1 - ρ)) (Fin.snoc g q) : ℝ) ≤
        ShortSieveLong.Psi (x / (g 0 * q)) (x ^ (1 - ρ) / (g 0 * q)) ⌈x ^ ν⌉₊ := by exact_mod_cast h1
      _ ≤ 2 * (x ^ (1 - ρ) / (g 0 * q)) / (ν * Real.log x) := h2
      _ ≤ 2 * (x ^ (1 - ρ) / (g 0 * q)) / (ν₁ * Real.log x) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_right hν1 hlx.le)
      _ = 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) * (1 / q) := by
          have : (g 0 : ℝ) ≠ 0 := by linarith
          have : (q : ℝ) ≠ 0 := by linarith
          field_simp
  -- the sum over `q`
  have hsum := sum_inv_primes_Ico_le (z' := z') hz2
  have hzz : (z' : ℝ) / z ≤ R + 1 := by
    rw [div_le_iff₀ hz0]
    have h1 : x ^ ν' + 1 ≤ R * x ^ ν + x ^ ν := by
      have : (1 : ℝ) ≤ x ^ ν := Real.one_le_rpow hx1.le (by linarith)
      linarith
    nlinarith
  have hA : 0 ≤ 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) := by positivity
  calc (sA ν x (x ^ (1 - ρ)) g : ℝ) - sA ν' x (x ^ (1 - ρ)) g ≤
      ∑ q ∈ (Ico z z').filter Nat.Prime, (sA ν x (x ^ (1 - ρ)) (Fin.snoc g q) : ℝ) :=
        sA_sub_le hx1.le hνν _ g
    _ ≤ ∑ q ∈ (Ico z z').filter Nat.Prime, 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) * (1 / q) :=
        sum_le_sum hterm
    _ = 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) * ∑ q ∈ (Ico z z').filter Nat.Prime, (1 : ℝ) / q := by
        rw [mul_sum]
    _ ≤ 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) * (Real.log 4 * z' / (z * Real.log z)) :=
        mul_le_mul_of_nonneg_left hsum hA
    _ ≤ 2 * x ^ (1 - ρ) / (g 0 * (ν₁ * Real.log x)) * (Real.log 4 * (R + 1) / (ν₁ * Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
        have e : Real.log 4 * z' / (z * Real.log z) = Real.log 4 * (z' / z) / Real.log z := by
          field_simp
        rw [e]
        calc Real.log 4 * (z' / z) / Real.log z ≤ Real.log 4 * (R + 1) / Real.log z :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzz hl4.le)
                (le_trans (mul_pos hν₁ hlx).le hlz)
          _ ≤ Real.log 4 * (R + 1) / (ν₁ * Real.log x) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hlz

/-! ### The second root term -/

/-- The second root term on `(x^a, x^b]`: `Σ_{x^a < p ≤ x^b} S(A_p, x^{ν(log p/log x)})`, over one-prime tuples. -/
noncomputable def sTwo (ν : ℝ → ℝ) (a b x y : ℝ) : ℝ :=
  ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊),
    (sA (ν (Real.log (g 0) / Real.log x)) x y g : ℝ)

/-- The tuples of one prime in `(N, M]`. -/
theorem mem_tuples_one {N M : ℕ} {g : Fin 1 → ℕ} :
    g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M) ↔ N < g 0 ∧ g 0 ≤ M ∧ (g 0).Prime := by
  rw [mem_tuples, Fin.forall_fin_one]

/-- **The blocks.** With `λ = 3/2` and `X_i = x^a λ^i`, the one-prime tuples of `(x^a, x^b]` are those of the blocks
`(⌊X_i⌋, ⌊min(X_{i+1}, x^b)⌋]`, `i ≤ n = ⌈(b − a) log x/log λ⌉`. -/
theorem sum_blocks (F : (Fin 1 → ℕ) → ℝ) {x a b : ℝ} (hx : 1 < x) :
    ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊), F g =
      ∑ i ∈ range (⌈(b - a) * Real.log x / Real.log (3 / 2)⌉₊ + 1),
        ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a * (3 / 2) ^ i⌋₊)
          (fun _ => ⌊min (x ^ a * (3 / 2) ^ (i + 1)) (x ^ b)⌋₊), F g := by
  have hx0 : 0 < x := by linarith
  have hX₀ : 0 < x ^ a := Real.rpow_pos_of_pos hx0 _
  have hlam : (1 : ℝ) < 3 / 2 := by norm_num
  have hll : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos hlam
  set n := ⌈(b - a) * Real.log x / Real.log (3 / 2)⌉₊ with hn
  set idx : (Fin 1 → ℕ) → ℕ := fun g => blockIdx (x ^ a) (3 / 2) (g 0) with hidx
  -- a prime of the range is above `x^a`
  have hbig : ∀ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊),
      x ^ a < g 0 ∧ (g 0 : ℝ) ≤ x ^ b := fun g hg => by
    rw [mem_tuples_one] at hg
    exact ⟨Nat.lt_of_floor_lt hg.1, le_trans (Nat.cast_le.2 hg.2.1) (Nat.floor_le (le_of_lt (by positivity)))⟩
  have hmaps : ∀ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊),
      idx g ∈ range (n + 1) := fun g hg => by
    obtain ⟨h1, h2⟩ := hbig g hg
    rw [mem_range, Nat.lt_succ_iff]
    simp only [hidx, blockIdx]
    have h3 : Real.log (g 0 / x ^ a) / Real.log (3 / 2) ≤ (b - a) * Real.log x / Real.log (3 / 2) := by
      apply div_le_div_of_nonneg_right _ hll.le
      rw [Real.log_div (lt_trans hX₀ h1).ne' hX₀.ne', Real.log_rpow hx0, sub_mul]
      have := Real.log_le_log (lt_trans hX₀ h1) h2
      rw [Real.log_rpow hx0] at this
      linarith
    exact le_trans (Nat.sub_le _ _) (Nat.ceil_le_ceil h3)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun i hi => sum_congr ?_ fun _ _ => rfl
  have hXi : 0 ≤ x ^ a * (3 / 2) ^ i := mul_nonneg hX₀.le (by positivity)
  ext g
  rw [mem_filter]
  constructor
  · rintro ⟨hg, hgi⟩
    obtain ⟨h1, h2⟩ := hbig g hg
    obtain ⟨h3, h4⟩ := blockIdx_spec hX₀ hlam h1
    simp only [hidx] at hgi
    rw [hgi] at h3 h4
    exact mem_tuples_one.2 ⟨(Nat.floor_lt hXi).2 h3, Nat.le_floor (le_min h4 h2), (mem_tuples_one.1 hg).2.2⟩
  · intro hg
    obtain ⟨h1, h2, h3⟩ := mem_tuples_one.1 hg
    have h1' : x ^ a * (3 / 2) ^ i < g 0 := Nat.lt_of_floor_lt h1
    have h2' : (g 0 : ℝ) ≤ min (x ^ a * (3 / 2) ^ (i + 1)) (x ^ b) :=
      le_trans (Nat.cast_le.2 h2) (Nat.floor_le (le_min (mul_nonneg hX₀.le (by positivity))
        (Real.rpow_nonneg hx0.le _)))
    have hXa : x ^ a ≤ x ^ a * (3 / 2) ^ i := le_mul_of_one_le_right hX₀.le (one_le_pow₀ hlam.le)
    refine ⟨mem_tuples_one.2 ⟨(Nat.floor_lt hX₀.le).2 (lt_of_le_of_lt hXa h1'),
      Nat.le_floor (le_trans h2' (min_le_right _ _)), h3⟩, ?_⟩
    simp only [hidx]
    exact blockIdx_eq hX₀ hlam h1' (le_trans h2' (min_le_left _ _))

/-- **A block, between two levels.** If the level of every tuple of the box lies in `[ν₋, ν₊]` and Li's estimate
holds at both ends, the box's sum at the variable level is within `c(T_B(ν₋) − T_B(ν₊)) + εc T_B(ν₋)` of `c` times
its sum in the comparison interval (`T_B` the box's `typeISum` there). -/
theorem abs_block_le {x y y₁ c ε νp νm : ℝ} {N M : Fin 1 → ℕ} (ν : (Fin 1 → ℕ) → ℝ) (hx : 1 ≤ x)
    (hlev : ∀ g ∈ ShortSieveTypeII.tuples N M, νm ≤ ν g ∧ ν g ≤ νp) (hνmp : νm ≤ νp) (hc : 0 ≤ c)
    (hε : 0 ≤ ε)
    (hLp : |typeISum νp x y N M - c * typeISum νp x y₁ N M| ≤ ε * c * typeISum νp x y₁ N M)
    (hLm : |typeISum νm x y N M - c * typeISum νm x y₁ N M| ≤ ε * c * typeISum νm x y₁ N M) :
    |∑ g ∈ ShortSieveTypeII.tuples N M, (sA (ν g) x y g : ℝ) -
        c * ∑ g ∈ ShortSieveTypeII.tuples N M, (sA (ν g) x y₁ g : ℝ)| ≤
      c * (typeISum νm x y₁ N M - typeISum νp x y₁ N M) + ε * c * typeISum νm x y₁ N M := by
  unfold typeISum at *
  refine abs_sub_le_of_sandwich ?_ ?_ ?_ ?_ hLp hLm hc hε ?_
  · exact sum_le_sum fun g hg => Nat.cast_le.2 (sA_anti hx (hlev g hg).2 y g)
  · exact sum_le_sum fun g hg => Nat.cast_le.2 (sA_anti hx (hlev g hg).1 y g)
  · exact sum_le_sum fun g hg => Nat.cast_le.2 (sA_anti hx (hlev g hg).2 y₁ g)
  · exact sum_le_sum fun g hg => Nat.cast_le.2 (sA_anti hx (hlev g hg).1 y₁ g)
  · exact sum_le_sum fun g _ => Nat.cast_le.2 (sA_anti hx hνmp y₁ g)

/-- Li's Lemma 3.1 on a block of one prime `(N, M]`, `x^{c₀} ≤ N ≤ M ≤ 2N ≤ …`, `N ≤ x^{1/2}`, as the variable `m`. -/
theorem li_one {θ γ ρ c₀ η ε x y ν₀ : ℝ} {N M : ℕ}
    (hx : ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ ν : ℝ, ∀ N M : Fin 1 → ℕ,
      (∀ j, (fun _ : Fin 1 => (0 : Fin 3)) j ≠ 2) → (∀ j, x ^ c₀ ≤ N j) → (∀ j, N j ≤ M j) →
      (∀ i, grpProd (fun _ : Fin 1 => (0 : Fin 3)) i M ≤ 2 * grpProd (fun _ : Fin 1 => (0 : Fin 3)) i N) →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x ≤ 1 / 2 →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 1 N) / Real.log x ≤
        min ((3 * θ - 1) / 2) ((1 + θ) / 5) - η →
      0 < ν → ν ≤ liNu θ γ (Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x) →
      |typeISum ν x y N M - y / x ^ (1 - ρ) * typeISum ν x (x ^ (1 - ρ)) N M| ≤
        ε * (y / x ^ (1 - ρ)) * typeISum ν x (x ^ (1 - ρ)) N M)
    (hy1 : x ^ θ ≤ y) (hy2 : y ≤ x ^ (1 - ρ)) (hη : η ≤ min ((3 * θ - 1) / 2) ((1 + θ) / 5))
    (hN : x ^ c₀ ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N) (hN2 : Real.log N / Real.log x ≤ 1 / 2)
    (hν0 : 0 < ν₀) (hν : ν₀ ≤ liNu θ γ (Real.log N / Real.log x)) :
    |typeISum ν₀ x y (fun _ : Fin 1 => N) (fun _ => M) -
        y / x ^ (1 - ρ) * typeISum ν₀ x (x ^ (1 - ρ)) (fun _ : Fin 1 => N) (fun _ => M)| ≤
      ε * (y / x ^ (1 - ρ)) * typeISum ν₀ x (x ^ (1 - ρ)) (fun _ : Fin 1 => N) (fun _ => M) := by
  have h0 : ∀ L : ℕ, grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 (fun _ => L) = L := fun L => by
    unfold grpProd; simp
  have h12 : ∀ (L : ℕ) (i : Fin 3), i ≠ 0 → grpProd (fun _ : Fin 1 => (0 : Fin 3)) i (fun _ => L) = 1 :=
    fun L i hi => by
      unfold grpProd
      rw [Finset.filter_false_of_mem fun j _ => Ne.symm hi, prod_empty]
  refine hx y hy1 hy2 ν₀ (fun _ => N) (fun _ => M) (fun _ => by simp) (fun _ => hN) (fun _ => hNM)
    (fun i => ?_) (by rw [h0]; exact hN2) (by rw [h12 N 1 (by decide)]; simpa using hη) hν0 (by rw [h0]; exact hν)
  by_cases hi : i = 0
  · subst hi; rw [h0, h0]; exact hM
  · rw [h12 M i hi, h12 N i hi]; norm_num

/-- The reciprocals of the one-prime tuples of `(N, M]`, `N ≥ 1`: at most `log 4 (M + 1)/((N + 1) log(N + 1))`. -/
theorem sum_inv_tuples_one_le {N M : ℕ} (hN : 1 ≤ N) :
    ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M), (1 : ℝ) / (g 0) ≤
      Real.log 4 * (M + 1 : ℕ) / ((N + 1 : ℕ) * Real.log (N + 1 : ℕ)) := by
  have hinj : Set.InjOn (fun g : Fin 1 → ℕ => g 0)
      (ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M) : Set (Fin 1 → ℕ)) := by
    intro g _ g' _ h
    funext j
    rw [Fin.fin_one_eq_zero j]
    exact h
  rw [← sum_image (f := fun p : ℕ => (1 : ℝ) / p) (g := fun g : Fin 1 → ℕ => g 0) hinj]
  refine le_trans (sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity))
    (sum_inv_primes_Ico_le (z := N + 1) (z' := M + 1) (by omega))
  obtain ⟨g, hg, rfl⟩ := mem_image.1 hp
  obtain ⟨h1, h2, h3⟩ := mem_tuples_one.1 hg
  rw [mem_filter, mem_Ico]
  exact ⟨⟨h1, by omega⟩, h3⟩

/-- **A regular block.** On a block `(N, M]` with `x^a < N`, `x^{a/2} ≤ N ≤ M ≤ 2N` and `M ≤ x^b`, the level lies
between its values at the two ends. Li's Lemma 3.1 at both (`li_one`) and the bounds `sB_one_le`, `sB_gap_le`
give the block's error. -/
theorem abs_block_pos_le {θ γ ρ a b νmin νmax K η ε x y : ℝ} {N M : ℕ} (ν : ℝ → ℝ) (hb : b ≤ 1 / 2)
    (hanti : AntitoneOn ν (Set.Icc a b))
    (hli : ∀ α ∈ Set.Ioc a b, ν α ≤ liNu θ γ α) (hmin : ∀ α ∈ Set.Icc a b, νmin ≤ ν α)
    (hmax : ∀ α ∈ Set.Icc a b, ν α ≤ νmax) (hνmin : 0 < νmin) (hνmax : νmax ≤ 1)
    (hlip : ∀ α ∈ Set.Icc a b, ∀ α' ∈ Set.Icc a b, α ≤ α' → ν α - ν α' ≤ K * (α' - α)) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hx1 : 1 < x) (hNa : x ^ a < N) (hNc : x ^ (a / 2) ≤ N) (hNM : N ≤ M) (hM2 : M ≤ 2 * N)
    (hMb : (M : ℝ) ≤ x ^ b)
    (hL : ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ ν : ℝ, ∀ N M : Fin 1 → ℕ,
      (∀ j, (fun _ : Fin 1 => (0 : Fin 3)) j ≠ 2) → (∀ j, x ^ (a / 2) ≤ N j) → (∀ j, N j ≤ M j) →
      (∀ i, grpProd (fun _ : Fin 1 => (0 : Fin 3)) i M ≤ 2 * grpProd (fun _ : Fin 1 => (0 : Fin 3)) i N) →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x ≤ 1 / 2 →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 1 N) / Real.log x ≤
        min ((3 * θ - 1) / 2) ((1 + θ) / 5) - η →
      0 < ν → ν ≤ liNu θ γ (Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x) →
      |typeISum ν x y N M - y / x ^ (1 - ρ) * typeISum ν x (x ^ (1 - ρ)) N M| ≤
        ε * (y / x ^ (1 - ρ)) * typeISum ν x (x ^ (1 - ρ)) N M)
    (hη : η ≤ min ((3 * θ - 1) / 2) ((1 + θ) / 5)) (hy1 : x ^ θ ≤ y) (hy2 : y ≤ x ^ (1 - ρ))
    (hone : ∀ (g : Fin 1 → ℕ) (ν : ℝ), 1 ≤ g 0 → (g 0 : ℝ) ≤ x ^ b → min νmin (2 * θ - 1) ≤ ν → ν ≤ 1 →
      (sA ν x (x ^ (1 - ρ)) g : ℝ) ≤ 2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x)))
    (hgap : ∀ (g : Fin 1 → ℕ) (ν ν' : ℝ), 1 ≤ g 0 → (g 0 : ℝ) ≤ x ^ b → min νmin (2 * θ - 1) ≤ ν → ν ≤ ν' →
      ν' ≤ νmax → x ^ ν' ≤ 2 ^ K * x ^ ν →
      (sA ν x (x ^ (1 - ρ)) g : ℝ) - sA ν' x (x ^ (1 - ρ)) g ≤
        2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x)) *
          (Real.log 4 * (2 ^ K + 1) / (min νmin (2 * θ - 1) * Real.log x))) :
    |∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M),
        (sA (ν (Real.log (g 0) / Real.log x)) x y g : ℝ) -
      y / x ^ (1 - ρ) * ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M),
        (sA (ν (Real.log (g 0) / Real.log x)) x (x ^ (1 - ρ)) g : ℝ)| ≤
      y / x ^ (1 - ρ) * ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M),
        2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x)) *
          (Real.log 4 * (2 ^ K + 1) / (min νmin (2 * θ - 1) * Real.log x)) +
      ε * (y / x ^ (1 - ρ)) * ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M),
        2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x)) := by
  set T := ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M) with hT
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hc : 0 ≤ y / x ^ (1 - ρ) :=
    div_nonneg (le_trans (Real.rpow_nonneg hx0.le _) hy1) (Real.rpow_nonneg hx0.le _)
  have hνL : min νmin (2 * θ - 1) ≤ νmin := min_le_left _ _
  rcases Finset.eq_empty_or_nonempty T with he | ⟨g₀, hg₀⟩
  · rw [he]; simp
  obtain ⟨hg1, hg2, -⟩ := mem_tuples_one.1 hg₀
  have hN0 : (0 : ℝ) < N := lt_trans (Real.rpow_pos_of_pos hx0 _) hNa
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hNb : (N : ℝ) ≤ x ^ b := le_trans hNM' hMb
  -- the exponents of the ends
  have hαN : a < Real.log N / Real.log x ∧ Real.log N / Real.log x ≤ b := by
    constructor
    · rw [lt_div_iff₀ hlx, ← Real.log_rpow hx0]; exact Real.log_lt_log (Real.rpow_pos_of_pos hx0 _) hNa
    · rw [div_le_iff₀ hlx, ← Real.log_rpow hx0]; exact Real.log_le_log hN0 hNb
  have hαNM : Real.log N / Real.log x ≤ Real.log M / Real.log x :=
    div_le_div_of_nonneg_right (Real.log_le_log hN0 hNM') hlx.le
  have hαM : Real.log M / Real.log x ≤ b := by
    rw [div_le_iff₀ hlx, ← Real.log_rpow hx0]; exact Real.log_le_log (by linarith) hMb
  have hIN : Real.log N / Real.log x ∈ Set.Icc a b := ⟨hαN.1.le, hαN.2⟩
  have hIM : Real.log M / Real.log x ∈ Set.Icc a b := ⟨le_trans hαN.1.le hαNM, hαM⟩
  set νp := ν (Real.log N / Real.log x) with hνp
  set νm := ν (Real.log M / Real.log x) with hνm
  have hνmp : νm ≤ νp := hanti hIN hIM hαNM
  have hlev : ∀ g ∈ T, νm ≤ ν (Real.log (g 0) / Real.log x) ∧ ν (Real.log (g 0) / Real.log x) ≤ νp := by
    intro g hg
    obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
    have h1' : (N : ℝ) ≤ g 0 := by exact_mod_cast h1.le
    have h2' : (g 0 : ℝ) ≤ M := by exact_mod_cast h2
    have hl1 : Real.log N / Real.log x ≤ Real.log (g 0) / Real.log x :=
      div_le_div_of_nonneg_right (Real.log_le_log hN0 h1') hlx.le
    have hl2 : Real.log (g 0) / Real.log x ≤ Real.log M / Real.log x :=
      div_le_div_of_nonneg_right (Real.log_le_log (by linarith) h2') hlx.le
    have hIg : Real.log (g 0) / Real.log x ∈ Set.Icc a b := ⟨le_trans hIN.1 hl1, le_trans hl2 hαM⟩
    exact ⟨hanti hIg hIM hl2, hanti hIN hIg hl1⟩
  have hp0 : 0 < νp := lt_of_lt_of_le hνmin (hmin _ hIN)
  have hm0 : 0 < νm := lt_of_lt_of_le hνmin (hmin _ hIM)
  have hN2 : Real.log N / Real.log x ≤ 1 / 2 := le_trans hαN.2 hb
  have hLp := li_one hL hy1 hy2 hη hNc hNM hM2 hN2 hp0 (hli _ ⟨hαN.1, hαN.2⟩)
  have hLm := li_one hL hy1 hy2 hη hNc hNM hM2 hN2 hm0 (le_trans hνmp (hli _ ⟨hαN.1, hαN.2⟩))
  have hblk := abs_block_le (y₁ := x ^ (1 - ρ)) (fun g => ν (Real.log (g 0) / Real.log x)) hx1.le hlev hνmp hc hε
    hLp hLm
  refine le_trans hblk (add_le_add (mul_le_mul_of_nonneg_left ?_ hc) (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg hε hc)))
  · -- the gap
    unfold typeISum
    rw [← sum_sub_distrib]
    refine sum_le_sum fun g hg => ?_
    obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
    have hgb : (g 0 : ℝ) ≤ x ^ b := le_trans (by exact_mod_cast h2) hMb
    -- `x^{ν₊} ≤ 2^K x^{ν₋}`
    have hR : x ^ νp ≤ 2 ^ K * x ^ νm := by
      have hl := hlip _ hIN _ hIM hαNM
      have hMN : Real.log M / Real.log x - Real.log N / Real.log x ≤ Real.log 2 / Real.log x := by
        rw [← sub_div]
        apply div_le_div_of_nonneg_right _ hlx.le
        rw [← Real.log_div (by linarith) hN0.ne']
        apply Real.log_le_log (div_pos (by linarith) hN0)
        rw [div_le_iff₀ hN0]
        exact_mod_cast hM2
      have hd : νp - νm ≤ K * Real.log 2 / Real.log x := by
        calc νp - νm ≤ K * (Real.log M / Real.log x - Real.log N / Real.log x) := hl
          _ ≤ K * (Real.log 2 / Real.log x) := mul_le_mul_of_nonneg_left hMN hK
          _ = K * Real.log 2 / Real.log x := by ring
      have h2K : x ^ (K * Real.log 2 / Real.log x) = 2 ^ K := by
        rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos two_pos]
        congr 1
        field_simp
      calc x ^ νp = x ^ (νp - νm) * x ^ νm := by rw [← Real.rpow_add hx0]; ring_nf
        _ ≤ x ^ (K * Real.log 2 / Real.log x) * x ^ νm :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1.le hd) (Real.rpow_nonneg hx0.le _)
        _ = 2 ^ K * x ^ νm := by rw [h2K]
    exact hgap g νm νp (by omega) hgb (le_trans hνL (hmin _ hIM)) hνmp (hmax _ hIN) hR
  · unfold typeISum
    refine sum_le_sum fun g hg => ?_
    obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
    have hgb : (g 0 : ℝ) ≤ x ^ b := le_trans (by exact_mod_cast h2) hMb
    exact hone g νm (by omega) hgb (le_trans hνL (hmin _ hIM)) (le_trans (hmax _ hIM) hνmax)

/-- **The first block.** On `(N, M]` with `x^a < N + 1`, `x^{a/2} ≤ N ≤ M ≤ 2N` and `M ≤ x^b`, Li's Lemma 3.1 at
the constant level `min(νmin, 2θ − 1)`, below every level of the block and below Li's (`ShortSieveTypeI.le_liNu`),
bounds both counts: the error is at most `3c` times the block's bound in the comparison interval. -/
theorem abs_block_zero_le {θ γ ρ a b νmin η ε x y : ℝ} {N M : ℕ} (ν : ℝ → ℝ) (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    (hγ : 2 * θ - 1 ≤ γ) (ha : 0 < a) (hb : b ≤ 1 / 2) (hmin : ∀ α ∈ Set.Icc a b, νmin ≤ ν α)
    (hνmin : 0 < νmin) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hx1 : 1 < x) (hNa : x ^ a < N + 1) (hNc : x ^ (a / 2) ≤ N)
    (hNM : N ≤ M) (hM2 : M ≤ 2 * N) (hMb : (M : ℝ) ≤ x ^ b)
    (hL : ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ ν : ℝ, ∀ N M : Fin 1 → ℕ,
      (∀ j, (fun _ : Fin 1 => (0 : Fin 3)) j ≠ 2) → (∀ j, x ^ (a / 2) ≤ N j) → (∀ j, N j ≤ M j) →
      (∀ i, grpProd (fun _ : Fin 1 => (0 : Fin 3)) i M ≤ 2 * grpProd (fun _ : Fin 1 => (0 : Fin 3)) i N) →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x ≤ 1 / 2 →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 1 N) / Real.log x ≤
        min ((3 * θ - 1) / 2) ((1 + θ) / 5) - η →
      0 < ν → ν ≤ liNu θ γ (Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x) →
      |typeISum ν x y N M - y / x ^ (1 - ρ) * typeISum ν x (x ^ (1 - ρ)) N M| ≤
        ε * (y / x ^ (1 - ρ)) * typeISum ν x (x ^ (1 - ρ)) N M)
    (hη : η ≤ min ((3 * θ - 1) / 2) ((1 + θ) / 5)) (hy1 : x ^ θ ≤ y) (hy2 : y ≤ x ^ (1 - ρ))
    (hone : ∀ (g : Fin 1 → ℕ) (ν : ℝ), 1 ≤ g 0 → (g 0 : ℝ) ≤ x ^ b → min νmin (2 * θ - 1) ≤ ν → ν ≤ 1 →
      (sA ν x (x ^ (1 - ρ)) g : ℝ) ≤ 2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x))) :
    |∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M),
        (sA (ν (Real.log (g 0) / Real.log x)) x y g : ℝ) -
      y / x ^ (1 - ρ) * ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M),
        (sA (ν (Real.log (g 0) / Real.log x)) x (x ^ (1 - ρ)) g : ℝ)| ≤
      3 * (y / x ^ (1 - ρ)) * ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M),
        2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x)) := by
  set T := ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M) with hT
  set νL := min νmin (2 * θ - 1) with hνLdef
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hc : 0 ≤ y / x ^ (1 - ρ) :=
    div_nonneg (le_trans (Real.rpow_nonneg hx0.le _) hy1) (Real.rpow_nonneg hx0.le _)
  have hνL0 : 0 < νL := lt_min hνmin (by linarith)
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hx1.le (by linarith)) hNc
  have hNb : (N : ℝ) ≤ x ^ b := le_trans (by exact_mod_cast hNM) hMb
  have hN2 : Real.log N / Real.log x ≤ 1 / 2 := by
    rw [div_le_iff₀ hlx]
    calc Real.log N ≤ Real.log (x ^ b) := Real.log_le_log (by linarith) hNb
      _ = b * Real.log x := Real.log_rpow hx0 _
      _ ≤ 1 / 2 * Real.log x := mul_le_mul_of_nonneg_right hb hlx.le
  have hli : νL ≤ liNu θ γ (Real.log N / Real.log x) :=
    le_trans (min_le_right _ _) (ShortSieveTypeI.le_liNu hθ hγ hN2)
  have hlev : ∀ g ∈ T, νL ≤ ν (Real.log (g 0) / Real.log x) := by
    intro g hg
    obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
    have h1' : x ^ a < g 0 := lt_of_lt_of_le hNa (by exact_mod_cast h1)
    have h2' : (g 0 : ℝ) ≤ x ^ b := le_trans (by exact_mod_cast h2) hMb
    have hg0 : (0 : ℝ) < g 0 := lt_trans (Real.rpow_pos_of_pos hx0 _) h1'
    refine le_trans (min_le_left _ _) (hmin _ ⟨?_, ?_⟩)
    · rw [le_div_iff₀ hlx, ← Real.log_rpow hx0]; exact (Real.log_lt_log (Real.rpow_pos_of_pos hx0 _) h1').le
    · rw [div_le_iff₀ hlx, ← Real.log_rpow hx0]; exact Real.log_le_log hg0 h2'
  have hLu := li_one hL hy1 hy2 hη hNc hNM hM2 hN2 hνL0 hli
  unfold typeISum at hLu
  -- both counts are at most the counts at the level `νL`
  set uA := ∑ g ∈ T, (sA νL x y g : ℝ) with huA
  set uB := ∑ g ∈ T, (sA νL x (x ^ (1 - ρ)) g : ℝ) with huB
  have hA0 : 0 ≤ ∑ g ∈ T, (sA (ν (Real.log (g 0) / Real.log x)) x y g : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hB0 : 0 ≤ ∑ g ∈ T, (sA (ν (Real.log (g 0) / Real.log x)) x (x ^ (1 - ρ)) g : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hAu : ∑ g ∈ T, (sA (ν (Real.log (g 0) / Real.log x)) x y g : ℝ) ≤ uA :=
    sum_le_sum fun g hg => Nat.cast_le.2 (sA_anti hx1.le (hlev g hg) y g)
  have hBu : ∑ g ∈ T, (sA (ν (Real.log (g 0) / Real.log x)) x (x ^ (1 - ρ)) g : ℝ) ≤ uB :=
    sum_le_sum fun g hg => Nat.cast_le.2 (sA_anti hx1.le (hlev g hg) _ g)
  have huAB : uA ≤ (1 + ε) * (y / x ^ (1 - ρ)) * uB := by
    have := (abs_le.1 hLu).2; linarith
  have huB0 : 0 ≤ uB := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hone' : uB ≤ ∑ g ∈ T, 2 * x ^ (1 - ρ) / (g 0 * (νL * Real.log x)) := by
    refine sum_le_sum fun g hg => ?_
    obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
    exact hone g νL (by omega) (le_trans (by exact_mod_cast h2) hMb) le_rfl
      (le_trans (min_le_right _ _) (by linarith))
  have hcB : (y / x ^ (1 - ρ)) * uB ≤ (y / x ^ (1 - ρ)) * ∑ g ∈ T, 2 * x ^ (1 - ρ) / (g 0 * (νL * Real.log x)) :=
    mul_le_mul_of_nonneg_left hone' hc
  have hcuB : 0 ≤ (y / x ^ (1 - ρ)) * uB := mul_nonneg hc huB0
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hBu hc]
  · nlinarith [mul_nonneg hc hB0]

/-- The reciprocals of the one-prime tuples of `(x^a, x^b]` are at most those of the primes of `[x^a, x^{b+1})`. -/
theorem sum_inv_big_le {x a b : ℝ} (hx : 1 < x) :
    ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊), (1 : ℝ) / (g 0) ≤
      ∑ p ∈ SieveRough.primesIn (x ^ a) (x ^ (b + 1)), (1 : ℝ) / p := by
  have hx0 : 0 < x := by linarith
  have hinj : Set.InjOn (fun g : Fin 1 → ℕ => g 0)
      (ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊) : Set (Fin 1 → ℕ)) := by
    intro g _ g' _ h
    funext j
    rw [Fin.fin_one_eq_zero j]
    exact h
  rw [← sum_image (f := fun p : ℕ => (1 : ℝ) / p) (g := fun g : Fin 1 → ℕ => g 0) hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  obtain ⟨g, hg, rfl⟩ := mem_image.1 hp
  obtain ⟨h1, h2, h3⟩ := mem_tuples_one.1 hg
  rw [SieveRough.mem_primesIn]
  refine ⟨h3, (Nat.lt_of_floor_lt h1).le, ?_⟩
  calc (g 0 : ℝ) ≤ x ^ b := le_trans (Nat.cast_le.2 h2) (Nat.floor_le (Real.rpow_nonneg hx0.le _))
    _ < x ^ (b + 1) := Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)

/-- `Σ_g A/(g₀ B) = (A/B) Σ_g 1/g₀`. -/
theorem sum_div_mul_eq (T : Finset (Fin 1 → ℕ)) (A B : ℝ) :
    ∑ g ∈ T, A / ((g 0 : ℝ) * B) = A / B * ∑ g ∈ T, (1 : ℝ) / (g 0) := by
  rw [mul_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [div_mul_div_comm, mul_one, mul_comm B]

/-- The blocks of the second root term, one by one: the first block within `y D₀/log² x`, every block within
`y (D₁/log² x + εD₂/log x)` times its sum of `1/p`. -/
theorem abs_block_i_le {θ γ ρ a b νmin νmax K η ε x y D₀ D₁ D₂ : ℝ} (ν : ℝ → ℝ) (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    (hγ : 2 * θ - 1 ≤ γ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2) (hanti : AntitoneOn ν (Set.Icc a b))
    (hli : ∀ α ∈ Set.Ioc a b, ν α ≤ liNu θ γ α) (hmin : ∀ α ∈ Set.Icc a b, νmin ≤ ν α)
    (hmax : ∀ α ∈ Set.Icc a b, ν α ≤ νmax) (hνmin : 0 < νmin) (hνmax : νmax ≤ 1)
    (hlip : ∀ α ∈ Set.Icc a b, ∀ α' ∈ Set.Icc a b, α ≤ α' → ν α - ν α' ≤ K * (α' - α)) (hK : 0 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx1 : 1 < x) (hxa2 : 2 ≤ x ^ (a / 2))
    (hL : ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) → ∀ ν : ℝ, ∀ N M : Fin 1 → ℕ,
      (∀ j, (fun _ : Fin 1 => (0 : Fin 3)) j ≠ 2) → (∀ j, x ^ (a / 2) ≤ N j) → (∀ j, N j ≤ M j) →
      (∀ i, grpProd (fun _ : Fin 1 => (0 : Fin 3)) i M ≤ 2 * grpProd (fun _ : Fin 1 => (0 : Fin 3)) i N) →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x ≤ 1 / 2 →
      Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 1 N) / Real.log x ≤
        min ((3 * θ - 1) / 2) ((1 + θ) / 5) - η →
      0 < ν → ν ≤ liNu θ γ (Real.log (grpProd (fun _ : Fin 1 => (0 : Fin 3)) 0 N) / Real.log x) →
      |typeISum ν x y N M - y / x ^ (1 - ρ) * typeISum ν x (x ^ (1 - ρ)) N M| ≤
        ε * (y / x ^ (1 - ρ)) * typeISum ν x (x ^ (1 - ρ)) N M)
    (hη : η ≤ min ((3 * θ - 1) / 2) ((1 + θ) / 5)) (hy1 : x ^ θ ≤ y) (hy2 : y ≤ x ^ (1 - ρ))
    (hone : ∀ (g : Fin 1 → ℕ) (ν : ℝ), 1 ≤ g 0 → (g 0 : ℝ) ≤ x ^ b → min νmin (2 * θ - 1) ≤ ν → ν ≤ 1 →
      (sA ν x (x ^ (1 - ρ)) g : ℝ) ≤ 2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x)))
    (hgap : ∀ (g : Fin 1 → ℕ) (ν ν' : ℝ), 1 ≤ g 0 → (g 0 : ℝ) ≤ x ^ b → min νmin (2 * θ - 1) ≤ ν → ν ≤ ν' →
      ν' ≤ νmax → x ^ ν' ≤ 2 ^ K * x ^ ν →
      (sA ν x (x ^ (1 - ρ)) g : ℝ) - sA ν' x (x ^ (1 - ρ)) g ≤
        2 * x ^ (1 - ρ) / (g 0 * (min νmin (2 * θ - 1) * Real.log x)) *
          (Real.log 4 * (2 ^ K + 1) / (min νmin (2 * θ - 1) * Real.log x)))
    (hD₀ : D₀ = 12 * Real.log 4 / (min νmin (2 * θ - 1) * a))
    (hD₁ : D₁ = 2 * (Real.log 4 * (2 ^ K + 1)) / (min νmin (2 * θ - 1) * min νmin (2 * θ - 1)))
    (hD₂ : D₂ = 2 / min νmin (2 * θ - 1)) (i : ℕ) :
    |∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a * (3 / 2) ^ i⌋₊)
        (fun _ => ⌊min (x ^ a * (3 / 2) ^ (i + 1)) (x ^ b)⌋₊), (sA (ν (Real.log (g 0) / Real.log x)) x y g : ℝ) -
      y / x ^ (1 - ρ) * ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a * (3 / 2) ^ i⌋₊)
        (fun _ => ⌊min (x ^ a * (3 / 2) ^ (i + 1)) (x ^ b)⌋₊),
          (sA (ν (Real.log (g 0) / Real.log x)) x (x ^ (1 - ρ)) g : ℝ)| ≤
      (if i = 0 then y * D₀ / Real.log x ^ 2 else 0) +
        y * (D₁ / Real.log x ^ 2 + ε * D₂ / Real.log x) *
          ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a * (3 / 2) ^ i⌋₊)
            (fun _ => ⌊min (x ^ a * (3 / 2) ^ (i + 1)) (x ^ b)⌋₊), (1 : ℝ) / (g 0) := by
  obtain ⟨νL, hνL⟩ : ∃ νL, νL = min νmin (2 * θ - 1) := ⟨_, rfl⟩
  rw [← hνL] at hone hgap hD₀ hD₁ hD₂
  have hνL0 : 0 < νL := by rw [hνL]; exact lt_min hνmin (by linarith)
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hxa : x ^ a = x ^ (a / 2) * x ^ (a / 2) := by rw [← Real.rpow_add hx0]; ring_nf
  have hxa4 : 4 ≤ x ^ a := by rw [hxa]; nlinarith
  have hxaN : x ^ (a / 2) ≤ x ^ a - 1 := by rw [hxa]; nlinarith
  have hy₁0 : 0 < x ^ (1 - ρ) := Real.rpow_pos_of_pos hx0 _
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg hx0.le _) hy1
  have hc : 0 ≤ y / x ^ (1 - ρ) := div_nonneg hy0 hy₁0.le
  have hcy : y / x ^ (1 - ρ) * x ^ (1 - ρ) = y := div_mul_cancel₀ _ hy₁0.ne'
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hD₂0 : 0 ≤ D₂ := by rw [hD₂]; positivity
  have hD₁0 : 0 ≤ D₁ := by rw [hD₁]; positivity
  obtain ⟨N, hN⟩ : ∃ N, N = ⌊x ^ a * (3 / 2) ^ i⌋₊ := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = ⌊min (x ^ a * (3 / 2) ^ (i + 1)) (x ^ b)⌋₊ := ⟨_, rfl⟩
  rw [← hN, ← hM]
  obtain ⟨T, hT⟩ : ∃ T, T = ShortSieveTypeII.tuples (fun _ : Fin 1 => N) (fun _ => M) := ⟨_, rfl⟩
  rw [← hT]
  have hS0 : 0 ≤ ∑ g ∈ T, (1 : ℝ) / (g 0) := sum_nonneg fun _ _ => by positivity
  have hnn : 0 ≤ y * (D₁ / Real.log x ^ 2 + ε * D₂ / Real.log x) * ∑ g ∈ T, (1 : ℝ) / (g 0) := by
    have h1 : 0 ≤ D₁ / Real.log x ^ 2 := div_nonneg hD₁0 (sq_nonneg _)
    have h2 : 0 ≤ ε * D₂ / Real.log x := div_nonneg (mul_nonneg hε.le hD₂0) hlx.le
    exact mul_nonneg (mul_nonneg hy0 (add_nonneg h1 h2)) hS0
  have hXi0 : 0 ≤ x ^ a * (3 / 2) ^ i := mul_nonneg (Real.rpow_nonneg hx0.le _) (by positivity)
  have hXi : x ^ a ≤ x ^ a * (3 / 2) ^ i := le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _)
    (one_le_pow₀ (by norm_num))
  have hNlo : x ^ a * (3 / 2) ^ i - 1 ≤ N := by
    have := Nat.lt_floor_add_one (x ^ a * (3 / 2) ^ i); rw [← hN] at this; linarith
  have hMhi : (M : ℝ) ≤ min (x ^ a * (3 / 2) ^ (i + 1)) (x ^ b) := by
    rw [hM]; exact Nat.floor_le (le_min (mul_nonneg (Real.rpow_nonneg hx0.le _) (by positivity))
      (Real.rpow_nonneg hx0.le _))
  have hMb : (M : ℝ) ≤ x ^ b := le_trans hMhi (min_le_right _ _)
  have hNc : x ^ (a / 2) ≤ N := by linarith
  have hM2 : M ≤ 2 * N := by
    have h1 : (M : ℝ) ≤ 3 / 2 * (x ^ a * (3 / 2) ^ i) := by
      have := le_trans hMhi (min_le_left _ _); rw [pow_succ] at this; linarith
    have h2 : (M : ℝ) ≤ 2 * N := by nlinarith
    exact_mod_cast h2
  by_cases hNM : N ≤ M
  swap
  · have he : T = ∅ := by
      rw [hT, Finset.eq_empty_iff_forall_notMem]
      intro g hg
      obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
      omega
    rw [he]
    simp only [sum_empty, mul_zero, sub_zero, abs_zero, add_zero]
    split_ifs
    · rw [hD₀]; positivity
    · exact le_rfl
  rcases Nat.eq_zero_or_pos i with hi | hi
  · -- the first block
    subst hi
    have hNa : x ^ a < N + 1 := by
      have := Nat.lt_floor_add_one (x ^ a * (3 / 2) ^ 0); rw [← hN] at this; simpa using this
    have hb0 := abs_block_zero_le ν hθ hθ1 hγ ha hb hmin hνmin hε.le hε1 hx1 hNa hNc hNM hM2 hMb hL hη hy1 hy2
      (by rw [← hνL]; exact hone)
    rw [← hνL, ← hT, sum_div_mul_eq] at hb0
    refine le_trans hb0 (le_trans ?_ (le_add_of_nonneg_right hnn))
    rw [ite_eq_left rfl]
    have hN1 : 1 ≤ N := by
      have : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hx1.le (by linarith)) hNc
      exact_mod_cast this
    have hS := sum_inv_tuples_one_le (M := M) hN1
    rw [← hT] at hS
    have hlN : a * Real.log x ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [← Real.log_rpow hx0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) (by push_cast; exact hNa.le)
    have hN1' : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hS' : ∑ g ∈ T, (1 : ℝ) / (g 0) ≤ 2 * Real.log 4 / (a * Real.log x) := by
      refine le_trans hS ?_
      have hMN : ((M + 1 : ℕ) : ℝ) ≤ 2 * (N + 1 : ℕ) := by exact_mod_cast (by omega : M + 1 ≤ 2 * (N + 1))
      rw [div_le_div_iff₀ (mul_pos hN1' (lt_of_lt_of_le (mul_pos ha hlx) hlN)) (mul_pos ha hlx)]
      calc Real.log 4 * ((M + 1 : ℕ) : ℝ) * (a * Real.log x) ≤
          Real.log 4 * (2 * (N + 1 : ℕ)) * Real.log ((N + 1 : ℕ) : ℝ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hMN hl4) hlN (by positivity) (by positivity)
        _ = 2 * Real.log 4 * (((N + 1 : ℕ) : ℝ) * Real.log ((N + 1 : ℕ) : ℝ)) := by ring
    have hk : 0 ≤ 3 * (y / x ^ (1 - ρ)) * (2 * x ^ (1 - ρ) / (νL * Real.log x)) := by positivity
    calc 3 * (y / x ^ (1 - ρ)) * (2 * x ^ (1 - ρ) / (νL * Real.log x) * ∑ g ∈ T, (1 : ℝ) / (g 0)) =
        3 * (y / x ^ (1 - ρ)) * (2 * x ^ (1 - ρ) / (νL * Real.log x)) * ∑ g ∈ T, (1 : ℝ) / (g 0) := by ring
      _ ≤ 3 * (y / x ^ (1 - ρ)) * (2 * x ^ (1 - ρ) / (νL * Real.log x)) * (2 * Real.log 4 / (a * Real.log x)) :=
          mul_le_mul_of_nonneg_left hS' hk
      _ = y * D₀ / Real.log x ^ 2 := by
          rw [hD₀]
          have : x ^ (1 - ρ) ≠ 0 := hy₁0.ne'
          field_simp
          ring
  · -- a regular block
    have hNa : x ^ a < N := by
      have h1 : x ^ a * (3 / 2) ≤ x ^ a * (3 / 2) ^ i :=
        mul_le_mul_of_nonneg_left (le_self_pow₀ (by norm_num) hi.ne') (Real.rpow_nonneg hx0.le _)
      linarith
    have hbp := abs_block_pos_le ν hb hanti hli hmin hmax hνmin hνmax hlip hK hε.le hx1 hNa hNc hNM hM2
      hMb hL hη hy1 hy2 (by rw [← hνL]; exact hone) (by rw [← hνL]; exact hgap)
    rw [← hνL, ← hT] at hbp
    refine le_trans hbp (le_of_eq ?_)
    rw [ite_eq_right hi.ne', zero_add]
    have e1 : ∑ g ∈ T, 2 * x ^ (1 - ρ) / (g 0 * (νL * Real.log x)) *
        (Real.log 4 * (2 ^ K + 1) / (νL * Real.log x)) =
        2 * x ^ (1 - ρ) / (νL * Real.log x) * (Real.log 4 * (2 ^ K + 1) / (νL * Real.log x)) *
          ∑ g ∈ T, (1 : ℝ) / (g 0) := by
      rw [← sum_mul, sum_div_mul_eq]; ring
    rw [e1, sum_div_mul_eq, hD₁, hD₂]
    have : x ^ (1 - ρ) ≠ 0 := hy₁0.ne'
    field_simp

/-- **The second root term.** With Li's Lemma 3.1 (`1/2 < θ ≤ 1`, `2θ − 1 ≤ γ`), let `0 < a < b ≤ 1/2` and let the
level `ν` be nonincreasing on `[a, b]`, at most Li's on `(a, b]`, between `νmin > 0` and `νmax` with `b + νmax < 1`,
and `K`-Lipschitz; let `12ρ < min(νmin, 2θ − 1)`. There is `C` with: for every `ε ∈ (0, 1]`, for large `x` and
`y ∈ [x^θ, x^{1−ρ}]`, `|Σ₂(A) − (y/x^{1−ρ}) Σ₂(B)| ≤ εC y/log x`, where
`Σ₂ = Σ_{x^a < p ≤ x^b} S(·_p, x^{ν(log p/log x)})`. -/
theorem abs_S2_sub_le {θ γ ρ a b νmin νmax K : ℝ} (hLi : LiLemma31 θ γ ρ) (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    (hγ : 2 * θ - 1 ≤ γ) (hρ : 0 < ρ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2) (ν : ℝ → ℝ)
    (hanti : AntitoneOn ν (Set.Icc a b)) (hli : ∀ α ∈ Set.Ioc a b, ν α ≤ liNu θ γ α)
    (hmin : ∀ α ∈ Set.Icc a b, νmin ≤ ν α) (hmax : ∀ α ∈ Set.Icc a b, ν α ≤ νmax) (hνmin : 0 < νmin)
    (hρν : 12 * ρ < min νmin (2 * θ - 1)) (hbν : b + νmax < 1) (hK : 0 ≤ K)
    (hlip : ∀ α ∈ Set.Icc a b, ∀ α' ∈ Set.Icc a b, α ≤ α' → ν α - ν α' ≤ K * (α' - α)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |sTwo ν a b x y - y / x ^ (1 - ρ) * sTwo ν a b x (x ^ (1 - ρ))| ≤ ε * C * y / Real.log x := by
  have hνL0 : 0 < min νmin (2 * θ - 1) := lt_min hνmin (by linarith)
  have hνmax : νmax ≤ 1 := by linarith
  obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = Real.log (b + 1) - Real.log a + 1 := ⟨_, rfl⟩
  have hSp0 : 0 ≤ Sp := by
    have := Real.log_le_log ha (by linarith : a ≤ b + 1)
    rw [hSp]; linarith
  obtain ⟨D₀, hD₀⟩ : ∃ D₀, D₀ = 12 * Real.log 4 / (min νmin (2 * θ - 1) * a) := ⟨_, rfl⟩
  obtain ⟨D₁, hD₁⟩ : ∃ D₁,
    D₁ = 2 * (Real.log 4 * (2 ^ K + 1)) / (min νmin (2 * θ - 1) * min νmin (2 * θ - 1)) := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂, D₂ = 2 / min νmin (2 * θ - 1) := ⟨_, rfl⟩
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hD₀0 : 0 ≤ D₀ := by rw [hD₀]; positivity
  have hD₁0 : 0 ≤ D₁ := by rw [hD₁]; positivity
  have hD₂0 : 0 ≤ D₂ := by rw [hD₂]; positivity
  refine ⟨D₂ * Sp + 1, fun ε hε hε1 => ?_⟩
  obtain ⟨η, hη⟩ : ∃ η, η = min ((3 * θ - 1) / 2) ((1 + θ) / 5) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min (by linarith) (by linarith)
  have hL := hLi (Fin 1) (fun _ => 0) (a / 2) η ε (by linarith) hη0 hε
  have hone := sB_one_le hνL0 hρ hρν (b := b) (by linarith)
  have hgap := sB_gap_le hνL0 hρ hρν (ν₂ := νmax) (R := 2 ^ K) (by linarith) hbν (by positivity)
  have hSum := SieveRough.evLe_sum_inv ha (by linarith : a ≤ b + 1) 1 one_pos
  filter_upwards [hL, hone, hgap, hSum, eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by linarith : 0 < a / 2)).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop ((D₀ + D₁ * Sp) / ε)] with x hLx honex hgapx hSumx hx1 hxa2 hlogx
    y hy1 hy2
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg hx0.le _) hy1
  unfold sTwo
  rw [sum_blocks _ hx1, sum_blocks _ hx1, mul_sum, ← sum_sub_distrib]
  obtain ⟨n, hn⟩ : ∃ n, n = ⌈(b - a) * Real.log x / Real.log (3 / 2)⌉₊ := ⟨_, rfl⟩
  rw [← hn]
  have hblk := fun i (_ : i ∈ range (n + 1)) => abs_block_i_le ν hθ hθ1 hγ ha hab hb hanti hli hmin hmax hνmin
    hνmax hlip hK hε hε1 hx1 hxa2 hLx (le_of_eq hη) hy1 hy2 honex hgapx hD₀ hD₁ hD₂ i
  have hrec := sum_blocks (fun g : Fin 1 → ℕ => (1 : ℝ) / (g 0)) (a := a) (b := b) hx1
  rw [← hn] at hrec
  have hbig := sum_inv_big_le (a := a) (b := b) hx1
  have hSp' : ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊), (1 : ℝ) / (g 0) ≤
      Sp := by
    rw [hSp]; linarith
  refine le_trans (abs_sum_le_sum_abs _ _) (le_trans (sum_le_sum hblk) ?_)
  rw [sum_add_distrib, sum_ite_eq' (range (n + 1)) 0, ite_eq_left (mem_range.2 (Nat.succ_pos n)), ← mul_sum,
    ← hrec]
  have hk : (D₀ + D₁ * Sp) / Real.log x ^ 2 ≤ ε / Real.log x := by
    rw [div_le_div_iff₀ (by positivity) hlx, pow_two]
    have := (div_le_iff₀ hε).1 hlogx
    nlinarith
  have hm : 0 ≤ y * (D₁ / Real.log x ^ 2 + ε * D₂ / Real.log x) := by positivity
  calc y * D₀ / Real.log x ^ 2 + y * (D₁ / Real.log x ^ 2 + ε * D₂ / Real.log x) *
        ∑ g ∈ ShortSieveTypeII.tuples (fun _ : Fin 1 => ⌊x ^ a⌋₊) (fun _ => ⌊x ^ b⌋₊), (1 : ℝ) / (g 0) ≤
      y * D₀ / Real.log x ^ 2 + y * (D₁ / Real.log x ^ 2 + ε * D₂ / Real.log x) * Sp :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hSp' hm)
    _ = y * ((D₀ + D₁ * Sp) / Real.log x ^ 2) + ε * D₂ * Sp * y / Real.log x := by ring
    _ ≤ y * (ε / Real.log x) + ε * D₂ * Sp * y / Real.log x := add_le_add (mul_le_mul_of_nonneg_left hk hy0) le_rfl
    _ = ε * (D₂ * Sp + 1) * y / Real.log x := by ring

/-! ### Li's level, piece by piece -/

/-- Li's level on the piece `h`: `min(2(θ − α)/(2h − 1), γ)`. -/
noncomputable def nuPiece (θ γ : ℝ) (h : ℕ) (α : ℝ) : ℝ := min (2 * (θ - α) / (2 * h - 1)) γ

/-- On `(1/2 − h(2θ − 1), 1/2 − (h − 1)(2θ − 1)]`, `h ≥ 1`, Li's level is `nuPiece θ γ h`. -/
theorem liNu_eq_nuPiece {θ γ α : ℝ} {h : ℕ} (hθ : 1 / 2 < θ) (hh : 1 ≤ h)
    (h1 : 1 / 2 - h * (2 * θ - 1) < α) (h2 : α ≤ 1 / 2 - (h - 1) * (2 * θ - 1)) :
    liNu θ γ α = nuPiece θ γ h α := by
  have hd : 0 < 2 * θ - 1 := by linarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hfl : ⌊(1 / 2 - α) / (2 * θ - 1)⌋₊ = h - 1 := by
    rw [Nat.floor_eq_iff (div_nonneg (by nlinarith) hd.le)]
    push_cast [Nat.cast_sub hh]
    constructor
    · rw [le_div_iff₀ hd]; linarith
    · rw [div_lt_iff₀ hd]; linarith
  unfold liNu nuPiece
  rw [hfl]
  push_cast [Nat.cast_sub hh]
  ring_nf

theorem nuPiece_anti (θ γ : ℝ) {h : ℕ} (hh : 1 ≤ h) {α α' : ℝ} (hαα : α ≤ α') :
    nuPiece θ γ h α' ≤ nuPiece θ γ h α := by
  have hh1 : (0 : ℝ) < 2 * h - 1 := by have : (1 : ℝ) ≤ h := (by exact_mod_cast hh); linarith
  unfold nuPiece
  exact min_le_min_right _ (div_le_div_of_nonneg_right (by linarith) hh1.le)

theorem nuPiece_lip (θ γ : ℝ) {h : ℕ} (hh : 1 ≤ h) {α α' : ℝ} (hαα : α ≤ α') :
    nuPiece θ γ h α - nuPiece θ γ h α' ≤ 2 * (α' - α) := by
  have hh1 : (1 : ℝ) ≤ 2 * h - 1 := by have : (1 : ℝ) ≤ h := (by exact_mod_cast hh); linarith
  have hu : 2 * (θ - α') / (2 * h - 1) ≤ 2 * (θ - α) / (2 * h - 1) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hd : 2 * (θ - α) / (2 * h - 1) - 2 * (θ - α') / (2 * h - 1) ≤ 2 * (α' - α) := by
    rw [← sub_div, div_le_iff₀ (by linarith)]
    nlinarith
  unfold nuPiece
  rcases le_total (2 * (θ - α) / (2 * h - 1)) γ with h1 | h1 <;>
    rcases le_total (2 * (θ - α') / (2 * h - 1)) γ with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]; exact hd
  · rw [min_eq_left h1, min_eq_right h2]; linarith
  · rw [min_eq_right h1, min_eq_left h2]; linarith
  · rw [min_eq_right h1, min_eq_right h2]; linarith

/-- At the right end of the piece `h` the level is `min(2θ − 1, γ)`, its least value on the piece. -/
theorem le_nuPiece {θ γ α : ℝ} {h : ℕ} (hh : 1 ≤ h) (hγ : 2 * θ - 1 ≤ γ)
    (h2 : α ≤ 1 / 2 - (h - 1) * (2 * θ - 1)) : 2 * θ - 1 ≤ nuPiece θ γ h α := by
  have hh1 : (0 : ℝ) < 2 * h - 1 := by have : (1 : ℝ) ≤ h := (by exact_mod_cast hh); linarith
  unfold nuPiece
  refine le_min ?_ hγ
  rw [le_div_iff₀ hh1]
  nlinarith

/-- Splitting the range of `sTwo`. -/
theorem sTwo_split (ν : ℝ → ℝ) {a b c x y : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) (hbc : b ≤ c) :
    sTwo ν a c x y = sTwo ν a b x y + sTwo ν b c x y := by
  have h1 : ⌊x ^ a⌋₊ ≤ ⌊x ^ b⌋₊ := Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx hab)
  have h2 : ⌊x ^ b⌋₊ ≤ ⌊x ^ c⌋₊ := Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx hbc)
  unfold sTwo
  rw [← sum_union]
  · refine sum_congr ?_ fun _ _ => rfl
    ext g
    rw [mem_union, mem_tuples_one, mem_tuples_one, mem_tuples_one]
    constructor
    · rintro ⟨h3, h4, hp⟩
      by_cases h5 : g 0 ≤ ⌊x ^ b⌋₊
      · exact Or.inl ⟨h3, h5, hp⟩
      · exact Or.inr ⟨not_le.1 h5, h4, hp⟩
    · rintro (⟨h3, h4, hp⟩ | ⟨h3, h4, hp⟩)
      · exact ⟨h3, le_trans h4 h2, hp⟩
      · exact ⟨lt_of_le_of_lt h1 h3, h4, hp⟩
  · rw [Finset.disjoint_left]
    intro g hg hg'
    rw [mem_tuples_one] at hg hg'
    omega

/-- `sTwo` only sees the level on `(a, b]`. -/
theorem sTwo_congr {ν ν' : ℝ → ℝ} {a b x y : ℝ} (hx : 1 < x)
    (h : ∀ α, a < α → α ≤ b → ν α = ν' α) : sTwo ν a b x y = sTwo ν' a b x y := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  unfold sTwo
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
  have h1' : x ^ a < g 0 := Nat.lt_of_floor_lt h1
  have h2' : (g 0 : ℝ) ≤ x ^ b := le_trans (Nat.cast_le.2 h2) (Nat.floor_le (Real.rpow_nonneg hx0.le _))
  have hg0 : (0 : ℝ) < g 0 := lt_trans (Real.rpow_pos_of_pos hx0 _) h1'
  rw [h]
  · rw [lt_div_iff₀ hlx, ← Real.log_rpow hx0]; exact Real.log_lt_log (Real.rpow_pos_of_pos hx0 _) h1'
  · rw [div_le_iff₀ hlx, ← Real.log_rpow hx0]; exact Real.log_le_log hg0 h2'

/-- **The second root term with Li's level.** With Li's Lemma 3.1 (`1/2 < θ ≤ 1`, `2θ − 1 ≤ γ < 1/2`) and
`12ρ < 2θ − 1`, for `0 < a₀ ≤ 1/2` there is `C` with: for every `ε ∈ (0, 1]`, for large `x` and
`y ∈ [x^θ, x^{1−ρ}]`, the sums `Σ_{x^{a₀} < p ≤ x^{1/2}} S(·_p, x^{ν(log p/log x)})` with `ν = liNu θ γ` satisfy
`|Σ₂(A) − (y/x^{1−ρ}) Σ₂(B)| ≤ εC y/log x`: `abs_S2_sub_le` on each piece of `liNu`. -/
theorem abs_S2_liNu_sub_le {θ γ ρ a₀ : ℝ} (hLi : LiLemma31 θ γ ρ) (hθ : 1 / 2 < θ) (hθ1 : θ ≤ 1)
    (hγ : 2 * θ - 1 ≤ γ) (hγ2 : γ < 1 / 2) (hρ : 0 < ρ) (hρθ : 12 * ρ < 2 * θ - 1) (ha₀ : 0 < a₀)
    (ha₀2 : a₀ ≤ 1 / 2) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |sTwo (liNu θ γ) a₀ (1 / 2) x y - y / x ^ (1 - ρ) * sTwo (liNu θ γ) a₀ (1 / 2) x (x ^ (1 - ρ))| ≤
        ε * C * y / Real.log x := by
  set d := 2 * θ - 1 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  -- the claim for the ranges `(max(a₀, 1/2 − hd), 1/2]`
  have key : ∀ h : ℕ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ θ ≤ y →
      y ≤ x ^ (1 - ρ) → |sTwo (liNu θ γ) (max a₀ (1 / 2 - h * d)) (1 / 2) x y -
        y / x ^ (1 - ρ) * sTwo (liNu θ γ) (max a₀ (1 / 2 - h * d)) (1 / 2) x (x ^ (1 - ρ))| ≤
          ε * C * y / Real.log x := by
    intro h
    induction h with
    | zero =>
      refine ⟨0, fun ε _ _ => Filter.Eventually.of_forall fun x y _ _ => ?_⟩
      have hm : max a₀ (1 / 2 - ((0 : ℕ) : ℝ) * d) = 1 / 2 := by
        rw [Nat.cast_zero, zero_mul, sub_zero]; exact max_eq_right ha₀2
      rw [hm]
      have he : ∀ y', sTwo (liNu θ γ) (1 / 2) (1 / 2) x y' = 0 := fun y' => by
        unfold sTwo
        refine sum_eq_zero fun g hg => ?_
        obtain ⟨h1, h2, -⟩ := mem_tuples_one.1 hg
        omega
      rw [he, he]
      simp
    | succ h ih =>
      obtain ⟨C₁, hC₁⟩ := ih
      set a' := max a₀ (1 / 2 - ((h + 1 : ℕ) : ℝ) * d) with ha'
      set b' := max a₀ (1 / 2 - (h : ℝ) * d) with hb'
      have hab' : a' ≤ b' := max_le_max le_rfl (by push_cast; nlinarith)
      have hb'2 : b' ≤ 1 / 2 := max_le ha₀2 (by nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)])
      by_cases hlt : a' < b'
      · -- the piece `h + 1`
        have hb'eq : b' = 1 / 2 - (h : ℝ) * d := by
          rcases le_total a₀ (1 / 2 - (h : ℝ) * d) with h1 | h1
          · rw [hb', max_eq_right h1]
          · exfalso; rw [hb', max_eq_left h1] at hlt; exact absurd hlt (not_lt.2 (le_max_left _ _))
        have ha'lo : 1 / 2 - ((h + 1 : ℕ) : ℝ) * d ≤ a' := le_max_right _ _
        have hh1 : 1 ≤ h + 1 := Nat.succ_pos h
        have hpiece : ∀ α, a' < α → α ≤ b' → liNu θ γ α = nuPiece θ γ (h + 1) α := fun α h1 h2 =>
          liNu_eq_nuPiece hθ hh1 (lt_of_le_of_lt ha'lo h1) (by rw [hb'eq] at h2; push_cast; linarith)
        have hS := abs_S2_sub_le (νmin := d) (νmax := γ) (K := 2) hLi hθ hθ1 hγ hρ
          (lt_of_lt_of_le ha₀ (le_max_left _ _))
          hlt hb'2 (nuPiece θ γ (h + 1)) (fun α _ α' _ hαα => nuPiece_anti θ γ hh1 hαα)
          (fun α hα => le_of_eq (hpiece α hα.1 hα.2).symm)
          (fun α hα => le_nuPiece hh1 hγ (by rw [hb'eq] at hα; push_cast; linarith [hα.2]))
          (fun α _ => min_le_right _ _) hd0 (by rw [min_self]; exact hρθ) (by linarith) (by norm_num)
          (fun α _ α' _ hαα => nuPiece_lip θ γ hh1 hαα)
        obtain ⟨C₂, hC₂⟩ := hS
        refine ⟨C₂ + C₁, fun ε hε hε1 => ?_⟩
        filter_upwards [hC₁ ε hε hε1, hC₂ ε hε hε1, eventually_gt_atTop 1] with x h1 h2 hx1 y hy1 hy2
        have hsplit : ∀ y', sTwo (liNu θ γ) a' (1 / 2) x y' =
            sTwo (nuPiece θ γ (h + 1)) a' b' x y' + sTwo (liNu θ γ) b' (1 / 2) x y' := fun y' => by
          rw [sTwo_split _ hx1.le hab' hb'2, sTwo_congr hx1 hpiece]
        rw [hsplit, hsplit]
        have e1 := h1 y hy1 hy2
        have e2 := h2 y hy1 hy2
        calc |sTwo (nuPiece θ γ (h + 1)) a' b' x y + sTwo (liNu θ γ) b' (1 / 2) x y -
            y / x ^ (1 - ρ) * (sTwo (nuPiece θ γ (h + 1)) a' b' x (x ^ (1 - ρ)) +
              sTwo (liNu θ γ) b' (1 / 2) x (x ^ (1 - ρ)))| ≤
            |sTwo (nuPiece θ γ (h + 1)) a' b' x y -
              y / x ^ (1 - ρ) * sTwo (nuPiece θ γ (h + 1)) a' b' x (x ^ (1 - ρ))| +
            |sTwo (liNu θ γ) b' (1 / 2) x y - y / x ^ (1 - ρ) * sTwo (liNu θ γ) b' (1 / 2) x (x ^ (1 - ρ))| := by
              rw [mul_add]
              refine le_trans (le_of_eq (by ring_nf)) (abs_add_le _ _)
          _ ≤ ε * C₂ * y / Real.log x + ε * C₁ * y / Real.log x := add_le_add e2 e1
          _ = ε * (C₂ + C₁) * y / Real.log x := by ring
      · -- an empty piece
        have heq : a' = b' := le_antisymm hab' (not_lt.1 hlt)
        refine ⟨C₁, fun ε hε hε1 => ?_⟩
        rw [heq]
        exact hC₁ ε hε hε1
  -- enough pieces
  obtain ⟨C, hC⟩ := key ⌈(1 / 2 - a₀) / d⌉₊
  have hm : max a₀ (1 / 2 - (⌈(1 / 2 - a₀) / d⌉₊ : ℝ) * d) = a₀ := by
    refine max_eq_left ?_
    have := Nat.le_ceil ((1 / 2 - a₀) / d)
    rw [div_le_iff₀ hd0] at this
    linarith
  rw [hm] at hC
  exact ⟨C, hC⟩

end ShortSieveRoot

#print axioms ShortSieveRoot.abs_S1_sub_le
#print axioms ShortSieveRoot.sA_sub_le
#print axioms ShortSieveRoot.abs_S2_sub_le
#print axioms ShortSieveRoot.abs_S2_liNu_sub_le
