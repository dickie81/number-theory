import ShortSieveCount
import ShortSieveDreq

/-!
# Harman's moment lemma with real exponents

For `L(t) = Σ_{j∈S} c_j j^{−it}` with `S ⊆ (N, 2N]` and `|c_j| ≤ 1`, on heights `[a, b]` with `b − a ≤ N^D`
(`D` is `Dx` in Lean), this module counts the large values of `L` as powers of `N`, with constants independent of
`N`, `S`, `c`, `a`, `b` and the level, and turns the counts into a moment `∫_a^b |L|^δ` with a power saving when
`|L| ≤ N^{1−η₁}` on `[a, b]`:

* `card_le_mv_exp`: the `1`-separated points of `[a, b]` at which `|L| ≥ V ≥ N^σ` number at most
  `C·N^{e_MV(m, σ) + ε}` (`ShortSieveCount.card_le_mv` on `[a − 1/2, b + 1/2]`, the divisor bound at `ε/(8m²)`, and
  `log N ≤ N^κ/κ`);
* `card_le_hm_exp`: for `3/4 ≤ σ ≤ 1`, at most `C·N^{e_HM(m, σ) + ε}` for `N ≥ N₀`, uniformly in `σ`
  (`ShortSieveCount.card_le_hux` with the kernel bound `ZetaKernel.norm_kz_le` and windows of height
  `T₀ = N^{(24mσ − 13m)/5 − ε/4}`, which the kernel allows once `N` is large);
* `integral_rpow_le_of_counts`: `ShortSieveLevel.lintegral_rpow_le_of_counts` for a continuous real function, as an
  interval integral;
* `integral_le_of_level_counts`, `moment_le_of_counts`: if at every level `V ≥ N^σ`, `σ ≤ 1`, the count is at most
  `C·N^{δ₀(1−σ)+ε}` with `δ₀ < δ`, then `∫_a^b |L|^δ ≤ C·N^{δ−η₂}` for some `η₂ > 0`, with `M = N^{1−η₁}` and
  `⌊log₂ N⌋ + 1` dyadic levels: a level `N^σ ≤ M/2` has `σ ≤ 1 − η₁`, so its term `N^{δσ}·N^{δ₀(1−σ)+ε}` is at
  most `N^{δ−(δ−δ₀)η₁+ε}`; below the last level `|L| < 1`, and the bottom term is at most `b − a ≤ N^D`;
* `moment_le_hux`: for `m < D ≤ m + 1/2` and `δ > 4D − 2m`, the mean value count on `L^m` below `3/4` and the
  Halász–Montgomery count above (`ShortSieveDreq`);
* `moment_le_mv`: for `D ≤ k` and `δ > 2k`, the mean value count on `L^k` alone.
-/

open Finset Real MeasureTheory DirMean LinnikPower LinnikHuxley ShortSieveLevel ShortSieveDreq ShortSieveCount

noncomputable section

namespace ShortSieveMoment

/-! ### The counts as powers of `N` -/

/-- `G_m` on the line: `G_m(0) = C^{4m}Λ^{4mε}Λ`, `Λ = (2P)^m`. -/
lemma Gm_zero (εd : ℝ) (P m : ℕ) :
    Gm εd P m 0 = Cdiv εd ^ (4 * m) * (((2 * P : ℕ) : ℝ) ^ m) ^ (4 * m * εd) * ((2 * P : ℕ) : ℝ) ^ m := by
  rw [Gm, neg_zero, Real.rpow_zero, one_pow, mul_one]

/-- The mass of the `m`-th power as a power of `N`: `C^{4m}Λ^{4mε_d}Λ ≤ C^{4m}2^κ2^m N^{m+κ}` for
`4m²ε_d ≤ κ`. -/
lemma mass_arith {m : ℕ} {κ εd : ℝ} (hεd : 4 * (m : ℝ) ^ 2 * εd ≤ κ) {Cd : ℝ} (hCd : 0 ≤ Cd) {N : ℕ}
    (hN : 1 ≤ N) :
    Cd ^ (4 * m) * (((2 * N : ℕ) : ℝ) ^ m) ^ (4 * m * εd) * ((2 * N : ℕ) : ℝ) ^ m ≤
      Cd ^ (4 * m) * 2 ^ κ * 2 ^ m * (N : ℝ) ^ (m + κ) := by
  set x : ℝ := (N : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hy : ((2 * N : ℕ) : ℝ) = 2 * x := by rw [hx]; push_cast; ring
  rw [hy]
  have hG : ((2 * x) ^ m) ^ (4 * (m : ℝ) * εd) ≤ 2 ^ κ * x ^ κ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    calc (2 * x) ^ ((m : ℝ) * (4 * m * εd)) ≤ (2 * x) ^ κ :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ = 2 ^ κ * x ^ κ := Real.mul_rpow (by norm_num) hx0.le
  calc Cd ^ (4 * m) * ((2 * x) ^ m) ^ (4 * (m : ℝ) * εd) * (2 * x) ^ m
      ≤ Cd ^ (4 * m) * (2 ^ κ * x ^ κ) * (2 * x) ^ m := by gcongr
    _ = Cd ^ (4 * m) * 2 ^ κ * 2 ^ m * (x ^ κ * x ^ (m : ℝ)) := by rw [mul_pow, Real.rpow_natCast]; ring
    _ = Cd ^ (4 * m) * 2 ^ κ * 2 ^ m * x ^ (m + κ) := by rw [← Real.rpow_add hx0, add_comm κ]

/-- The arithmetic of the mean value count: the bound of `ShortSieveCount.card_le_mv` with `Λ = (2N)^m`, an
interval of length `w ≤ N^D + 1` and `V ≥ N^σ` is at most `C·N^{e_MV(m, σ)+ε}` when `4m²ε_d ≤ ε/2`. -/
lemma mv_arith {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) {εd : ℝ} (hεd : 4 * (m : ℝ) ^ 2 * εd ≤ ε / 2)
    {Cd : ℝ} (hCd : 0 ≤ Cd) {N : ℕ} (hN : 1 ≤ N) {Dx w σ V : ℝ}
    (hw : w ≤ (N : ℝ) ^ Dx + 1) (hV : (N : ℝ) ^ σ ≤ V) :
    (2 * m) ^ 3 * ((w + 8 * ((2 * N : ℕ) : ℝ) ^ m * (1 + Real.log (((2 * N : ℕ) : ℝ) ^ m))) *
      (2 + Real.log (2 * ((2 * N : ℕ) : ℝ) ^ m) ^ 2) *
      (Cd ^ (4 * m) * (((2 * N : ℕ) : ℝ) ^ m) ^ (4 * m * εd) * ((2 * N : ℕ) : ℝ) ^ m)) / V ^ (2 * m) ≤
    (2 * m) ^ 3 * (2 + 16 * m * 2 ^ m) * (6 * m ^ 2) * (Cd ^ (4 * m) * 2 ^ (ε / 2) * 2 ^ m) *
      (1 + 6 / ε) ^ 3 * (N : ℝ) ^ (eMV Dx m σ + ε) := by
  have hG := mass_arith hεd hCd hN
  set x : ℝ := (N : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hy : ((2 * N : ℕ) : ℝ) = 2 * x := by rw [hx]; push_cast; ring
  rw [hy] at hG ⊢
  set Λ : ℝ := (2 * x) ^ m with hΛ
  have hΛe : Λ = 2 ^ m * x ^ (m : ℝ) := by rw [hΛ, mul_pow, Real.rpow_natCast]
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by linarith)
  -- the logarithms, through `ℓ = 1 + log N`
  set ℓ : ℝ := 1 + Real.log x with hℓ
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogΛ : Real.log Λ = m * (Real.log 2 + Real.log x) := by
    rw [hΛ, Real.log_pow, Real.log_mul (by norm_num) hx0.ne']
  have hmℓ : 1 ≤ (m : ℝ) * ℓ := by nlinarith
  have hA1 : 1 + Real.log Λ ≤ 2 * m * ℓ := by rw [hlogΛ]; nlinarith
  have hA1' : 0 ≤ 1 + Real.log Λ := by have := Real.log_nonneg hΛ1; linarith
  have hlog2Λ : Real.log (2 * Λ) = Real.log 2 + Real.log Λ := Real.log_mul (by norm_num) (by positivity)
  have hB0 : 0 ≤ Real.log (2 * Λ) := Real.log_nonneg (by linarith)
  have hB1 : Real.log (2 * Λ) ≤ 2 * m * ℓ := by rw [hlog2Λ, hlogΛ]; nlinarith
  have hB : 2 + Real.log (2 * Λ) ^ 2 ≤ 6 * m ^ 2 * ℓ ^ 2 := by
    have := pow_le_pow_left₀ hB0 hB1 2
    nlinarith
  have hℓε : ℓ ≤ (1 + 6 / ε) * x ^ (ε / 6) := by
    have h1 := Real.log_le_rpow_div hx0.le (by positivity : 0 < ε / 6)
    have h2 : (1 : ℝ) ≤ x ^ (ε / 6) := Real.one_le_rpow hx1 (by positivity)
    calc ℓ ≤ x ^ (ε / 6) + x ^ (ε / 6) / (ε / 6) := by rw [hℓ]; linarith
      _ = (1 + 6 / ε) * x ^ (ε / 6) := by field_simp
  have hℓ3 : ℓ ^ 3 ≤ (1 + 6 / ε) ^ 3 * x ^ (ε / 2) := by
    calc ℓ ^ 3 ≤ ((1 + 6 / ε) * x ^ (ε / 6)) ^ 3 := pow_le_pow_left₀ (by linarith) hℓε 3
      _ = (1 + 6 / ε) ^ 3 * x ^ (ε / 2) := by
          have h3 : ε / 6 * ((3 : ℕ) : ℝ) = ε / 2 := by push_cast; ring
          rw [mul_pow, ← Real.rpow_natCast (x ^ (ε / 6)), ← Real.rpow_mul hx0.le, h3]
  -- the length of the interval and the main term of the mean value theorem
  set e₁ : ℝ := max Dx m with he₁
  have hxe₁ : 1 ≤ x ^ e₁ := Real.one_le_rpow hx1 (le_trans (by positivity) (le_max_right _ _))
  have hxD : x ^ Dx ≤ x ^ e₁ := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have hxm : x ^ (m : ℝ) ≤ x ^ e₁ := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_right _ _)
  have hA : w + 8 * Λ * (1 + Real.log Λ) ≤ (2 + 16 * m * 2 ^ m) * x ^ e₁ * ℓ := by
    have hΛx : Λ ≤ 2 ^ m * x ^ e₁ := by rw [hΛe]; gcongr
    have h1 : 8 * Λ * (1 + Real.log Λ) ≤ 8 * (2 ^ m * x ^ e₁) * (2 * m * ℓ) := by gcongr
    have h2 : w ≤ 2 * x ^ e₁ * ℓ := by
      calc w ≤ x ^ Dx + 1 := hw
        _ ≤ x ^ e₁ + x ^ e₁ := add_le_add hxD hxe₁
        _ = 2 * x ^ e₁ * 1 := by ring
        _ ≤ 2 * x ^ e₁ * ℓ := by gcongr
    calc w + 8 * Λ * (1 + Real.log Λ) ≤ 2 * x ^ e₁ * ℓ + 8 * (2 ^ m * x ^ e₁) * (2 * m * ℓ) := add_le_add h2 h1
      _ = (2 + 16 * m * 2 ^ m) * x ^ e₁ * ℓ := by ring
  -- the level
  have hV0 : 0 < V := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 σ) hV
  have hV2 : x ^ (2 * m * σ) ≤ V ^ (2 * m) := by
    calc x ^ (2 * m * σ) = (x ^ σ) ^ (2 * m) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring_nf
      _ ≤ V ^ (2 * m) := pow_le_pow_left₀ (by positivity) hV _
  have hcomb : x ^ e₁ * x ^ (m + ε / 2) * x ^ (ε / 2) / x ^ (2 * m * σ) = x ^ (eMV Dx m σ + ε) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_sub hx0]
    unfold eMV
    congr 1
    ring
  have hB' : 0 ≤ 2 + Real.log (2 * Λ) ^ 2 := by positivity
  have hG0 : 0 ≤ Cd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ := by positivity
  calc (2 * m) ^ 3 * ((w + 8 * Λ * (1 + Real.log Λ)) * (2 + Real.log (2 * Λ) ^ 2) *
        (Cd ^ (4 * m) * Λ ^ (4 * m * εd) * Λ)) / V ^ (2 * m)
      ≤ (2 * m) ^ 3 * (((2 + 16 * m * 2 ^ m) * x ^ e₁ * ℓ) * (6 * m ^ 2 * ℓ ^ 2) *
        (Cd ^ (4 * m) * 2 ^ (ε / 2) * 2 ^ m * x ^ (m + ε / 2))) / x ^ (2 * m * σ) := by
        gcongr
    _ = (2 * m) ^ 3 * (2 + 16 * m * 2 ^ m) * (6 * m ^ 2) * (Cd ^ (4 * m) * 2 ^ (ε / 2) * 2 ^ m) *
        ℓ ^ 3 * (x ^ e₁ * x ^ (m + ε / 2) / x ^ (2 * m * σ)) := by ring
    _ ≤ (2 * m) ^ 3 * (2 + 16 * m * 2 ^ m) * (6 * m ^ 2) * (Cd ^ (4 * m) * 2 ^ (ε / 2) * 2 ^ m) *
        ((1 + 6 / ε) ^ 3 * x ^ (ε / 2)) * (x ^ e₁ * x ^ (m + ε / 2) / x ^ (2 * m * σ)) := by
        gcongr
    _ = (2 * m) ^ 3 * (2 + 16 * m * 2 ^ m) * (6 * m ^ 2) * (Cd ^ (4 * m) * 2 ^ (ε / 2) * 2 ^ m) *
        (1 + 6 / ε) ^ 3 * (x ^ e₁ * x ^ (m + ε / 2) * x ^ (ε / 2) / x ^ (2 * m * σ)) := by ring
    _ = (2 * m) ^ 3 * (2 + 16 * m * 2 ^ m) * (6 * m ^ 2) * (Cd ^ (4 * m) * 2 ^ (ε / 2) * 2 ^ m) *
        (1 + 6 / ε) ^ 3 * x ^ (eMV Dx m σ + ε) := by rw [hcomb]

/-- **The mean value count as a power of `N`.** For `m ≥ 1` and `ε > 0` there is `C` such that, for `N ≥ 3`,
`S ⊆ (N, 2N]`, `|c_j| ≤ 1` and `b − a ≤ N^D`, the `1`-separated points of `[a, b]` at which
`|Σ_{j∈S} c_j j^{−it}| ≥ V ≥ N^σ` number at most `C·N^{e_MV(m, σ) + ε}`, `e_MV(m, σ) = max(D, m) + m(1 − 2σ)`. -/
theorem card_le_mv_exp {m : ℕ} (hm : 1 ≤ m) (Dx : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) → ∀ c : ℕ → ℂ,
      (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx → ∀ σ V : ℝ, (N : ℝ) ^ σ ≤ V →
      ∀ R : Finset ℝ, Sep R → (∀ x ∈ R, a ≤ x ∧ x ≤ b) → (∀ x ∈ R, V ≤ ‖dp S c x‖) →
      (R.card : ℝ) ≤ C * (N : ℝ) ^ (eMV Dx m σ + ε) := by
  set εd : ℝ := min (ε / (8 * m ^ 2)) 1 with hεd
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hεd0 : 0 < εd := lt_min (by positivity) one_pos
  have hεd1 : εd ≤ 1 := min_le_right _ _
  have hεd' : 4 * (m : ℝ) ^ 2 * εd ≤ ε / 2 := by
    calc 4 * (m : ℝ) ^ 2 * εd ≤ 4 * m ^ 2 * (ε / (8 * m ^ 2)) := by gcongr; exact min_le_left _ _
      _ = ε / 2 := by field_simp; ring
  have hCd : 0 ≤ Cdiv εd := zero_le_one.trans (one_le_Cdiv hεd0 hεd1)
  refine ⟨(2 * m) ^ 3 * (2 + 16 * m * 2 ^ m) * (6 * m ^ 2) * (Cdiv εd ^ (4 * m) * 2 ^ (ε / 2) * 2 ^ m) *
      (1 + 6 / ε) ^ 3, by positivity, fun N hN S hS c hc a b hab hba σ V hV R hsep hR hbig => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hV0 : 0 < V := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 σ) hV
  have hN3 : 3 ≤ N ^ m := hN.trans (Nat.le_self_pow (by omega) N)
  have h := card_le_mv (P := N) (by omega) hS hc hm hN3 (a := a - 1 / 2) (b := b + 1 / 2) (by linarith) hV0
    hεd0 hεd1 R hsep (fun x hx => ⟨by linarith [(hR x hx).1], by linarith [(hR x hx).2]⟩) hbig
  rw [Gm_zero] at h
  exact h.trans (mv_arith hm hε hεd' hCd (by omega) (by linarith) hV)

/-- The feasibility of the Halász–Montgomery count at the window `T₀ = N^{(24mσ − 13m)/5 − ε/4}`, for
`3/4 ≤ σ ≤ 1` and `N^{ε/16}` at least the constant. -/
lemma hm_feas_arith {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {εd εK : ℝ}
    (hεd : 4 * (m : ℝ) ^ 2 * εd ≤ ε / 48) (hεK0 : 0 ≤ εK) (hεK : 11 * (m : ℝ) / 5 * εK ≤ ε / 48)
    (hεK1 : εK ≤ 7 / 12) {Cd KE CK : ℝ} (hCd : 0 ≤ Cd) (hKE : 0 ≤ KE) (hCK : 0 ≤ CK) {N : ℕ} (hN : 1 ≤ N)
    (hNbig : 2 * Real.exp 1 * (Cd ^ (4 * m) * 2 ^ (ε / 48) * 2 ^ m) * ((KE + CK) * (3 * 2 ^ ((m : ℝ) / 12))) ≤
      (N : ℝ) ^ (ε / 16))
    {σ V : ℝ} (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hV : (N : ℝ) ^ σ ≤ V) :
    2 * Real.exp 1 * (Cd ^ (4 * m) * (((2 * N : ℕ) : ℝ) ^ m) ^ (4 * m * εd) * ((2 * N : ℕ) : ℝ) ^ m) *
      (KE + CK * (((2 * N : ℕ) : ℝ) ^ m) ^ (1 / 12 : ℝ) *
        ((N : ℝ) ^ ((24 * m * σ - 13 * m) / 5 - ε / 4) + 2) ^ (5 / 12 + εK)) ≤ V ^ (2 * m) := by
  have hG := mass_arith hεd hCd hN
  set x : ℝ := (N : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hy : ((2 * N : ℕ) : ℝ) = 2 * x := by rw [hx]; push_cast; ring
  rw [hy] at hG ⊢
  set Λ : ℝ := (2 * x) ^ m with hΛ
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by linarith)
  set τ : ℝ := (24 * m * σ - 13 * m) / 5 - ε / 4 with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; nlinarith
  have hτ1 : τ ≤ 11 * m / 5 := by rw [hτ]; nlinarith
  set p : ℝ := 5 / 12 + εK with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have hT1 : (1 : ℝ) ≤ x ^ τ := Real.one_le_rpow hx1 hτ0
  -- the factors of the kernel bound
  have hΛ12 : Λ ^ (1 / 12 : ℝ) = 2 ^ ((m : ℝ) / 12) * x ^ ((m : ℝ) / 12) := by
    rw [hΛ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx0.le]
    ring_nf
  have hΛ12' : 1 ≤ Λ ^ (1 / 12 : ℝ) := Real.one_le_rpow hΛ1 (by norm_num)
  have hTp : (x ^ τ + 2) ^ p ≤ 3 * x ^ (τ * p) := by
    calc (x ^ τ + 2) ^ p ≤ (3 * x ^ τ) ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp0
      _ = 3 ^ p * x ^ (τ * p) := by rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]
      _ ≤ 3 * x ^ (τ * p) := by
          gcongr
          calc (3 : ℝ) ^ p ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
            _ = 3 := Real.rpow_one 3
  have hTp' : 1 ≤ (x ^ τ + 2) ^ p := Real.one_le_rpow (by linarith) hp0
  have hτp : (m : ℝ) / 12 + τ * p ≤ 2 * m * σ - m - ε / 12 := by
    have := mul_le_mul_of_nonneg_right hτ1 hεK0
    rw [hτ, hp] at *
    nlinarith
  have hK : KE + CK * Λ ^ (1 / 12 : ℝ) * (x ^ τ + 2) ^ p ≤
      (KE + CK) * (3 * 2 ^ ((m : ℝ) / 12)) * x ^ (2 * m * σ - m - ε / 12) := by
    have h1 : 1 ≤ Λ ^ (1 / 12 : ℝ) * (x ^ τ + 2) ^ p := one_le_mul_of_one_le_of_one_le hΛ12' hTp'
    calc KE + CK * Λ ^ (1 / 12 : ℝ) * (x ^ τ + 2) ^ p
        ≤ (KE + CK) * (Λ ^ (1 / 12 : ℝ) * (x ^ τ + 2) ^ p) := by nlinarith
      _ ≤ (KE + CK) * ((2 ^ ((m : ℝ) / 12) * x ^ ((m : ℝ) / 12)) * (3 * x ^ (τ * p))) := by
          rw [hΛ12]; gcongr
      _ = (KE + CK) * (3 * 2 ^ ((m : ℝ) / 12)) * x ^ ((m : ℝ) / 12 + τ * p) := by
          rw [Real.rpow_add hx0]; ring
      _ ≤ (KE + CK) * (3 * 2 ^ ((m : ℝ) / 12)) * x ^ (2 * m * σ - m - ε / 12) := by
          gcongr
  have hV2 : x ^ (2 * m * σ) ≤ V ^ (2 * m) := by
    calc x ^ (2 * m * σ) = (x ^ σ) ^ (2 * m) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring_nf
      _ ≤ V ^ (2 * m) := pow_le_pow_left₀ (by positivity) hV _
  set A : ℝ := 2 * Real.exp 1 * (Cd ^ (4 * m) * 2 ^ (ε / 48) * 2 ^ m) * ((KE + CK) * (3 * 2 ^ ((m : ℝ) / 12)))
    with hA
  have hG0 : 0 ≤ Cd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ := by positivity
  calc 2 * Real.exp 1 * (Cd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ) *
        (KE + CK * Λ ^ (1 / 12 : ℝ) * (x ^ τ + 2) ^ p)
      ≤ 2 * Real.exp 1 * (Cd ^ (4 * m) * 2 ^ (ε / 48) * 2 ^ m * x ^ (m + ε / 48)) *
        ((KE + CK) * (3 * 2 ^ ((m : ℝ) / 12)) * x ^ (2 * m * σ - m - ε / 12)) := by gcongr
    _ = A * (x ^ (m + ε / 48) * x ^ (2 * m * σ - m - ε / 12)) := by rw [hA]; ring
    _ = A * x ^ (2 * m * σ - ε / 16) := by rw [← Real.rpow_add hx0]; congr 2; ring
    _ ≤ x ^ (ε / 16) * x ^ (2 * m * σ - ε / 16) := by gcongr
    _ = x ^ (2 * m * σ) := by rw [← Real.rpow_add hx0]; congr 1; ring
    _ ≤ V ^ (2 * m) := hV2

/-- The arithmetic of the Halász–Montgomery count: the bound of `ShortSieveCount.card_le_hux` at the window
`T₀ = N^{(24mσ − 13m)/5 − ε/4}`, with `b − a = w ≤ N^D` and `V ≥ N^σ`, is at most `C·N^{e_HM(m, σ)+ε}`. -/
lemma hm_count_arith {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) {εd : ℝ}
    (hεd : 4 * (m : ℝ) ^ 2 * εd ≤ ε / 48) {Cd KE : ℝ} (hCd : 0 ≤ Cd) (hKE : 0 ≤ KE) {N : ℕ} (hN : 1 ≤ N)
    {Dx w σ V : ℝ} (hw : w ≤ (N : ℝ) ^ Dx) (hV : (N : ℝ) ^ σ ≤ V) :
    (w / (N : ℝ) ^ ((24 * m * σ - 13 * m) / 5 - ε / 4) + 1) *
      (2 * Real.exp 1 * (Cd ^ (4 * m) * (((2 * N : ℕ) : ℝ) ^ m) ^ (4 * m * εd) * ((2 * N : ℕ) : ℝ) ^ m) *
        ((2 * N : ℕ) : ℝ) ^ m * (1 + KE * (2 * Real.log (((2 * N : ℕ) : ℝ) ^ m) + 1)) / V ^ (2 * m)) ≤
    2 * (2 * Real.exp 1 * (Cd ^ (4 * m) * 2 ^ (ε / 48) * 2 ^ m) * 2 ^ m * (1 + 3 * m * KE) * (1 + 4 / ε)) *
      (N : ℝ) ^ (eHM Dx m σ + ε) := by
  have hG := mass_arith hεd hCd hN
  set x : ℝ := (N : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hy : ((2 * N : ℕ) : ℝ) = 2 * x := by rw [hx]; push_cast; ring
  rw [hy] at hG ⊢
  set Λ : ℝ := (2 * x) ^ m with hΛ
  have hΛe : Λ = 2 ^ m * x ^ (m : ℝ) := by rw [hΛ, mul_pow, Real.rpow_natCast]
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by linarith)
  set τ : ℝ := (24 * m * σ - 13 * m) / 5 - ε / 4 with hτ
  -- the windows
  have hW : w / x ^ τ + 1 ≤ x ^ (Dx - τ) + 1 := by
    rw [Real.rpow_sub hx0 Dx τ]; gcongr
  -- the logarithm
  set ℓ : ℝ := 1 + Real.log x with hℓ
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlogΛ : Real.log Λ = m * (Real.log 2 + Real.log x) := by
    rw [hΛ, Real.log_pow, Real.log_mul (by norm_num) hx0.ne']
  have hmℓ : 1 ≤ (m : ℝ) * ℓ := by nlinarith
  have hL : 1 + KE * (2 * Real.log Λ + 1) ≤ (1 + 3 * m * KE) * ℓ := by
    have h1 : 2 * Real.log Λ + 1 ≤ 3 * m * ℓ := by rw [hlogΛ]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hKE]
  have hℓε : ℓ ≤ (1 + 4 / ε) * x ^ (ε / 4) := by
    have h1 := Real.log_le_rpow_div hx0.le (by positivity : 0 < ε / 4)
    have h2 : (1 : ℝ) ≤ x ^ (ε / 4) := Real.one_le_rpow hx1 (by positivity)
    calc ℓ ≤ x ^ (ε / 4) + x ^ (ε / 4) / (ε / 4) := by rw [hℓ]; linarith
      _ = (1 + 4 / ε) * x ^ (ε / 4) := by field_simp
  have hV0 : 0 < V := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 σ) hV
  have hV2 : x ^ (2 * m * σ) ≤ V ^ (2 * m) := by
    calc x ^ (2 * m * σ) = (x ^ σ) ^ (2 * m) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring_nf
      _ ≤ V ^ (2 * m) := pow_le_pow_left₀ (by positivity) hV _
  set A : ℝ := 2 * Real.exp 1 * (Cd ^ (4 * m) * 2 ^ (ε / 48) * 2 ^ m) * 2 ^ m * (1 + 3 * m * KE) * (1 + 4 / ε)
    with hA
  have hA0 : 0 ≤ A := by positivity
  set E₀ : ℝ := 2 * m * (1 - σ) + 13 * ε / 48 with hE₀
  -- one window
  have hcount : 2 * Real.exp 1 * (Cd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ) * Λ *
      (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m) ≤ A * x ^ E₀ := by
    have hL0 : 0 ≤ 1 + KE * (2 * Real.log Λ + 1) := by
      have := Real.log_nonneg hΛ1; positivity
    calc 2 * Real.exp 1 * (Cd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ) * Λ *
          (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m)
        ≤ 2 * Real.exp 1 * (Cd ^ (4 * m) * 2 ^ (ε / 48) * 2 ^ m * x ^ (m + ε / 48)) * (2 ^ m * x ^ (m : ℝ)) *
          ((1 + 3 * m * KE) * ((1 + 4 / ε) * x ^ (ε / 4))) / x ^ (2 * m * σ) := by
          rw [← hΛe]
          gcongr
          exact hL.trans (by gcongr)
      _ = A * (x ^ (m + ε / 48) * x ^ (m : ℝ) * x ^ (ε / 4) / x ^ (2 * m * σ)) := by rw [hA]; ring
      _ = A * x ^ E₀ := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_sub hx0, hE₀]
          congr 2
          ring
  have hc0 : 0 ≤ 2 * Real.exp 1 * (Cd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ) * Λ *
      (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m) := by
    have := Real.log_nonneg hΛ1; positivity
  have he1 : Dx - τ + E₀ ≤ eHM Dx m σ + ε := by
    unfold eHM
    have := le_max_right (2 * (m : ℝ) * (1 - σ)) (Dx + m * (23 / 5 - 34 / 5 * σ))
    rw [hτ, hE₀]
    linarith
  have he2 : E₀ ≤ eHM Dx m σ + ε := by
    unfold eHM
    have := le_max_left (2 * (m : ℝ) * (1 - σ)) (Dx + m * (23 / 5 - 34 / 5 * σ))
    rw [hE₀]
    linarith
  calc (w / x ^ τ + 1) * (2 * Real.exp 1 * (Cd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ) * Λ *
          (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m))
      ≤ (x ^ (Dx - τ) + 1) * (A * x ^ E₀) := by gcongr
    _ = A * (x ^ (Dx - τ + E₀) + x ^ E₀) := by rw [Real.rpow_add hx0 (Dx - τ) E₀]; ring
    _ ≤ A * (x ^ (eHM Dx m σ + ε) + x ^ (eHM Dx m σ + ε)) := by gcongr
    _ = 2 * A * x ^ (eHM Dx m σ + ε) := by ring

/-- **The Halász–Montgomery count as a power of `N`.** For `m ≥ 1` and `ε > 0` there are `C` and `N₀` such that,
for `N ≥ N₀`, `S ⊆ (N, 2N]`, `|c_j| ≤ 1`, `b − a ≤ N^D` and every `3/4 ≤ σ ≤ 1`, the `1`-separated points of
`[a, b]` at which `|Σ_{j∈S} c_j j^{−it}| ≥ V ≥ N^σ` number at most `C·N^{e_HM(m, σ) + ε}`,
`e_HM(m, σ) = max(2m(1 − σ), D + m(23/5 − 34σ/5))`: `ShortSieveCount.card_le_hux` with the kernel bound of
`ZetaKernel.norm_kz_le` and the window `T₀ = N^{(24mσ − 13m)/5 − ε/4}`. -/
theorem card_le_hm_exp {m : ℕ} (hm : 1 ≤ m) (Dx : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) → ∀ c : ℕ → ℂ,
      (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx → ∀ σ V : ℝ, 3 / 4 ≤ σ → σ ≤ 1 →
      (N : ℝ) ^ σ ≤ V → ∀ R : Finset ℝ, Sep R → (∀ x ∈ R, a ≤ x ∧ x ≤ b) → (∀ x ∈ R, V ≤ ‖dp S c x‖) →
      (R.card : ℝ) ≤ C * (N : ℝ) ^ (eHM Dx m σ + ε) := by
  -- it suffices to take `ε ≤ 1`
  set ε' : ℝ := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set εd : ℝ := min (ε' / (192 * m ^ 2)) 1 with hεd
  have hεd0 : 0 < εd := lt_min (by positivity) one_pos
  have hεd1 : εd ≤ 1 := min_le_right _ _
  have hεd' : 4 * (m : ℝ) ^ 2 * εd ≤ ε' / 48 := by
    calc 4 * (m : ℝ) ^ 2 * εd ≤ 4 * m ^ 2 * (ε' / (192 * m ^ 2)) := by gcongr; exact min_le_left _ _
      _ = ε' / 48 := by field_simp; ring
  set εK : ℝ := ε' / (200 * m) with hεK
  have hεK0 : 0 < εK := by positivity
  have hεK' : 11 * (m : ℝ) / 5 * εK ≤ ε' / 48 := by
    have : 11 * (m : ℝ) / 5 * εK = 11 * ε' / 1000 := by rw [hεK]; field_simp; ring
    rw [this]; linarith
  have hεK1 : εK ≤ 7 / 12 := by
    rw [hεK, div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨CK, hCK0, hCK⟩ := ZetaKernel.norm_kz_le hεK0 (by linarith)
  have hCd : 0 ≤ Cdiv εd := zero_le_one.trans (one_le_Cdiv hεd0 hεd1)
  have hKE := InghamDensity.KE_pos
  set A : ℝ := 2 * Real.exp 1 * (Cdiv εd ^ (4 * m) * 2 ^ (ε' / 48) * 2 ^ m) *
    ((InghamDensity.KE + CK) * (3 * 2 ^ ((m : ℝ) / 12))) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨2 * (2 * Real.exp 1 * (Cdiv εd ^ (4 * m) * 2 ^ (ε' / 48) * 2 ^ m) * 2 ^ m *
      (1 + 3 * m * InghamDensity.KE) * (1 + 4 / ε')), by positivity, max 3 ⌈A ^ (16 / ε')⌉₊,
      fun N hN S hS c hc a b hab hba σ V hσ hσ1 hV R hsep hR hbig => ?_⟩
  have hN3 : 3 ≤ N := le_of_max_le_left hN
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hx0 : (0 : ℝ) < N := by linarith
  have hNA : A ^ (16 / ε') ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  have hNbig : A ≤ (N : ℝ) ^ (ε' / 16) := by
    calc A = (A ^ (16 / ε')) ^ (ε' / 16) := by
          rw [← Real.rpow_mul hA0, show 16 / ε' * (ε' / 16) = 1 by field_simp, Real.rpow_one]
      _ ≤ (N : ℝ) ^ (ε' / 16) := Real.rpow_le_rpow (by positivity) hNA (by positivity)
  have hV0 : 0 < V := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 σ) hV
  have hfeas := hm_feas_arith hm hε'0 hε'1 hεd' hεK0.le hεK' hεK1 hCd hKE.le hCK0 (by omega) hNbig hσ hσ1 hV
  rw [← Gm_zero] at hfeas
  have h := card_le_hux (P := N) (by omega) hS hc hm hab hV0 hεd0 hεd1 hεK0.le hCK0 hCK
    (Real.rpow_pos_of_pos hx0 ((24 * m * σ - 13 * m) / 5 - ε' / 4)) hfeas R hsep hR hbig
  rw [Gm_zero] at h
  calc (R.card : ℝ) ≤ _ := h
    _ ≤ _ := hm_count_arith hm hε'0 hεd' hCd hKE.le (by omega) hba hV
    _ ≤ _ := by gcongr

/-! ### Moments from counts -/

/-- **Moments from counts of large values, for a real function.** For a continuous `f ≥ 0` with `f ≤ M` on
`[a, b]`, if at most `K j` points `1`-separated in `[a, b]` have `f ≥ M/2^{j+1}`, then
`∫_a^b f^δ ≤ (M/2^J)^δ (b − a) + Σ_{j<J} (M/2^j)^δ · 2K j` (`ShortSieveLevel.lintegral_rpow_le_of_counts`). -/
theorem integral_rpow_le_of_counts {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {M : ℝ} (hfM : ∀ t ∈ Set.Icc a b, f t ≤ M) {δ : ℝ} (hδ : 0 ≤ δ)
    (J : ℕ) (K : ℕ → ℝ)
    (hK : ∀ j < J, ∀ R : Finset ℝ, (R : Set ℝ) ⊆ Set.Icc a b → Sep R → (∀ x ∈ R, M / 2 ^ (j + 1) ≤ f x) →
      (R.card : ℝ) ≤ K j) :
    ∫ t in a..b, f t ^ δ ≤ (M / 2 ^ J) ^ δ * (b - a) + ∑ j ∈ range J, (M / 2 ^ j) ^ δ * (2 * K j) := by
  have hM : 0 ≤ M := (hf0 a).trans (hfM a ⟨le_rfl, hab⟩)
  have hK0 : ∀ j < J, 0 ≤ K j := fun j hj => by
    have := hK j hj ∅ (by simp) (fun x hx => by simp at hx) (fun x hx => by simp at hx)
    simpa using this
  set F : ℝ → ENNReal := fun t => ENNReal.ofReal (f t) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hf.measurable
  have hFM : ∀ t ∈ Set.Icc a b, F t ≤ ENNReal.ofReal M := fun t ht => ENNReal.ofReal_le_ofReal (hfM t ht)
  have h2 : ∀ j : ℕ, ENNReal.ofReal M / 2 ^ j = ENNReal.ofReal (M / 2 ^ j) := fun j => by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hK' : ∀ j < J, ∀ R : Finset ℝ, (R : Set ℝ) ⊆ Set.Icc a b → Sep R →
      (∀ x ∈ R, ENNReal.ofReal M / 2 ^ (j + 1) ≤ F x) → R.card ≤ ⌊K j⌋₊ := by
    intro j hj R hR hsep hbig
    refine Nat.le_floor (hK j hj R hR hsep fun x hx => ?_)
    have := hbig x hx
    rw [h2] at this
    exact (ENNReal.ofReal_le_ofReal_iff (hf0 x)).1 this
  have hmain := lintegral_rpow_le_of_counts hFm hFM hδ J (fun j => ⌊K j⌋₊) hK'
  -- the real integral
  have hint : ∫ t in a..b, f t ^ δ = (∫⁻ t in Set.Icc a b, F t ^ δ).toReal := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      refine lintegral_congr fun t => ?_
      rw [hF]
      dsimp only
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 t) hδ]
    · exact Filter.Eventually.of_forall fun t => Real.rpow_nonneg (hf0 t) δ
    · exact (hf.rpow_const fun t => Or.inr hδ).aestronglyMeasurable
  rw [hint]
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have hterm0 : ∀ j ∈ range J, 0 ≤ (M / 2 ^ j) ^ δ * (2 * K j) := fun j hj => by
    have := hK0 j (mem_range.1 hj)
    positivity
  refine ENNReal.toReal_le_of_le_ofReal (add_nonneg (by positivity) (sum_nonneg hterm0)) (hmain.trans ?_)
  rw [ENNReal.ofReal_add (by positivity) (sum_nonneg hterm0), ENNReal.ofReal_sum_of_nonneg hterm0]
  gcongr with j hj
  · rw [h2, ENNReal.ofReal_rpow_of_nonneg (by positivity) hδ, ENNReal.ofReal_mul (by positivity)]
  · rw [h2, ENNReal.ofReal_rpow_of_nonneg (by positivity) hδ, ENNReal.ofReal_mul (by positivity)]
    gcongr
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Nat.floor_le (hK0 j (mem_range.1 hj)))

/-- **Moments from counts at every level.** For `N ≥ 2`, a continuous `f ≥ 0` with `f ≤ N^{1−η₁}` on `[a, b]`,
`b − a ≤ N^D`, and counts `C·N^{δ₀(1−σ)+ε}` of the `1`-separated points of `[a, b]` at which `f ≥ V ≥ N^σ`, for
every `σ ≤ 1 − η₁`: `∫_a^b f^δ ≤ N^D + (⌊log₂ N⌋ + 1)·2^{δ+1}C·N^{δ−(δ−δ₀)η₁+ε}` (the levels `V_j = N^{σ_j}`,
`σ_j = log_N(M/2^{j+1})`, of `integral_rpow_le_of_counts`, with `M/2^J < 1` at `J = ⌊log₂ N⌋ + 1`). -/
theorem integral_le_of_level_counts {N : ℕ} (hN : 2 ≤ N) {a b : ℝ} (hab : a ≤ b) {Dx : ℝ}
    (hba : b - a ≤ (N : ℝ) ^ Dx) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) {η₁ : ℝ}
    (hη₁ : 0 ≤ η₁) (hfM : ∀ t ∈ Set.Icc a b, f t ≤ (N : ℝ) ^ (1 - η₁)) {δ δ₀ C ε : ℝ} (hδ : 0 ≤ δ)
    (hδ₀ : δ₀ ≤ δ) (hC : 0 ≤ C)
    (hcount : ∀ σ V : ℝ, σ ≤ 1 - η₁ → (N : ℝ) ^ σ ≤ V → ∀ R : Finset ℝ, (R : Set ℝ) ⊆ Set.Icc a b →
      Sep R → (∀ x ∈ R, V ≤ f x) → (R.card : ℝ) ≤ C * (N : ℝ) ^ (δ₀ * (1 - σ) + ε)) :
    ∫ t in a..b, f t ^ δ ≤ (N : ℝ) ^ Dx +
      (Nat.log 2 N + 1) * (2 ^ (δ + 1) * C * (N : ℝ) ^ (δ - (δ - δ₀) * η₁ + ε)) := by
  set x : ℝ := (N : ℝ) with hx
  have hx1 : (1 : ℝ) < x := by rw [hx]; exact_mod_cast (by omega : 1 < N)
  have hx0 : 0 < x := by linarith
  set M : ℝ := x ^ (1 - η₁) with hMdef
  have hM0 : 0 < M := Real.rpow_pos_of_pos hx0 _
  set J := Nat.log 2 N + 1 with hJ
  set σ : ℕ → ℝ := fun j => Real.logb x (M / 2 ^ (j + 1)) with hσ
  have hσx : ∀ j, x ^ σ j = M / 2 ^ (j + 1) := fun j => Real.rpow_logb hx0 hx1.ne' (by positivity)
  have hσ1 : ∀ j, σ j ≤ 1 - η₁ := fun j => by
    have h : σ j ≤ Real.logb x M :=
      Real.logb_le_logb_of_le hx1 (by positivity) (div_le_self hM0.le (one_le_pow₀ (by norm_num)))
    rwa [hMdef, Real.logb_rpow hx0 hx1.ne'] at h
  have hmain := integral_rpow_le_of_counts hab hf hf0 hfM hδ J (fun j => C * x ^ (δ₀ * (1 - σ j) + ε))
    (fun j _ R hR hsep hbig => hcount (σ j) _ (hσ1 j) (hσx j).le R hR hsep hbig)
  refine hmain.trans (add_le_add ?_ ?_)
  · -- below the last level `f < 1`
    have hMJ : M / 2 ^ J ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc M ≤ x := by
            calc M = x ^ (1 - η₁) := rfl
              _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
              _ = x := Real.rpow_one x
        _ ≤ 2 ^ J := by
            have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
            rw [hx]; exact_mod_cast this.le
    calc (M / 2 ^ J) ^ δ * (b - a) ≤ 1 * x ^ Dx := by
          gcongr
          · exact Real.rpow_le_one (by positivity) hMJ hδ
      _ = x ^ Dx := one_mul _
  · -- the levels
    rw [show ((Nat.log 2 N : ℝ) + 1) = (J : ℝ) by rw [hJ]; push_cast; ring]
    calc ∑ j ∈ range J, (M / 2 ^ j) ^ δ * (2 * (C * x ^ (δ₀ * (1 - σ j) + ε)))
        ≤ ∑ _j ∈ range J, 2 ^ (δ + 1) * C * x ^ (δ - (δ - δ₀) * η₁ + ε) := by
          refine sum_le_sum fun j _ => ?_
          have hMj : M / 2 ^ j = 2 * x ^ σ j := by rw [hσx, pow_succ]; field_simp
          rw [hMj, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]
          have hexp : σ j * δ + (δ₀ * (1 - σ j) + ε) ≤ δ - (δ - δ₀) * η₁ + ε := by
            nlinarith [mul_nonneg (sub_nonneg.2 hδ₀) (sub_nonneg.2 (hσ1 j))]
          calc 2 ^ δ * x ^ (σ j * δ) * (2 * (C * x ^ (δ₀ * (1 - σ j) + ε)))
              = 2 ^ (δ + 1) * C * x ^ (σ j * δ + (δ₀ * (1 - σ j) + ε)) := by
                rw [Real.rpow_add hx0 (σ j * δ), Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
                ring
            _ ≤ 2 ^ (δ + 1) * C * x ^ (δ - (δ - δ₀) * η₁ + ε) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1.le hexp) (by positivity)
      _ = J * (2 ^ (δ + 1) * C * x ^ (δ - (δ - δ₀) * η₁ + ε)) := by
          rw [sum_const, card_range, nsmul_eq_mul]

/-- The number of levels: `⌊log₂ N⌋ + 1 ≤ (1 + 2/κ)N^κ` for `N ≥ 1` and `κ > 0`. -/
lemma log_two_add_one_le {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    (Nat.log 2 N : ℝ) + 1 ≤ (1 + 2 / κ) * (N : ℝ) ^ κ := by
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ κ := Real.one_le_rpow hx1 hκ.le
  have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogN : Real.log N ≤ (N : ℝ) ^ κ / κ := Real.log_le_rpow_div hx0.le hκ
  have hn : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
    have h0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
    nlinarith
  calc (Nat.log 2 N : ℝ) + 1 ≤ 2 * ((N : ℝ) ^ κ / κ) + (N : ℝ) ^ κ := by linarith
    _ = (1 + 2 / κ) * (N : ℝ) ^ κ := by field_simp; ring

/-- **The moment lemma from counts of large values.** Let `δ₀ < δ`, `D < δ`, `δ ≥ 0` and `η₁ > 0`, and suppose
that for every `ε > 0` there are `C` and `N₀` such that, for `N ≥ N₀`, `S ⊆ (N, 2N]`, `|c_j| ≤ 1`, `b − a ≤ N^D`
and every `σ ≤ 1`, at most `C·N^{δ₀(1−σ)+ε}` points `1`-separated in `[a, b]` have `|Σ_{j∈S} c_j j^{−it}| ≥ V ≥ N^σ`.
Then there are `η₂ > 0`, `C` and `N₀` with `∫_a^b |Σ_{j∈S} c_j j^{−it}|^δ dt ≤ C·N^{δ−η₂}` whenever moreover
`|Σ_{j∈S} c_j j^{−it}| ≤ N^{1−η₁}` on `[a, b]` (`integral_le_of_level_counts` at `ε = (δ − δ₀)η₁/4`). -/
theorem moment_le_of_counts {Dx δ δ₀ η₁ : ℝ} (hδ₀ : δ₀ < δ) (hDx : Dx < δ) (hδ0 : 0 ≤ δ) (hη₁ : 0 < η₁)
    (hcount : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) →
      ∀ c : ℕ → ℂ, (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx →
      ∀ σ V : ℝ, σ ≤ 1 → (N : ℝ) ^ σ ≤ V → ∀ R : Finset ℝ, Sep R → (∀ x ∈ R, a ≤ x ∧ x ≤ b) →
      (∀ x ∈ R, V ≤ ‖dp S c x‖) → (R.card : ℝ) ≤ C * (N : ℝ) ^ (δ₀ * (1 - σ) + ε)) :
    ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) →
      ∀ c : ℕ → ℂ, (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx →
      (∀ t ∈ Set.Icc a b, ‖dp S c t‖ ≤ (N : ℝ) ^ (1 - η₁)) →
      ∫ t in a..b, ‖dp S c t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η₂) := by
  set ε : ℝ := (δ - δ₀) * η₁ / 4 with hε
  have hε0 : 0 < ε := by have := sub_pos.2 hδ₀; positivity
  obtain ⟨C₁, N₁, hC₁⟩ := hcount ε hε0
  set C₂ : ℝ := max C₁ 0 with hC₂
  have hC₂0 : 0 ≤ C₂ := le_max_right _ _
  refine ⟨min (2 * ε) (δ - Dx), lt_min (by linarith) (sub_pos.2 hDx),
    1 + (1 + 2 / ε) * (2 ^ (δ + 1) * C₂), max N₁ 2, fun N hN S hS c hc a b hab hba hM => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hN1 : N₁ ≤ N := le_of_max_le_left hN
  set x : ℝ := (N : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast (by omega : 1 ≤ N)
  have hx0 : 0 < x := by linarith
  have hlev := integral_le_of_level_counts hN2 hab hba (continuous_dp S c).norm (fun t => norm_nonneg _)
    hη₁.le hM hδ0 hδ₀.le hC₂0 (ε := ε) fun σ V hσ hV R hR hsep hbig =>
      (hC₁ N hN1 S hS c hc a b hab hba σ V (by linarith) hV R hsep (fun x hx => hR (mem_coe.2 hx)) hbig).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  refine hlev.trans ?_
  set η₂ := min (2 * ε) (δ - Dx) with hη₂
  have hη₂1 : η₂ ≤ 2 * ε := min_le_left _ _
  have hη₂2 : η₂ ≤ δ - Dx := min_le_right _ _
  have hlogJ := log_two_add_one_le (by omega : 1 ≤ N) hε0
  have h1 : x ^ Dx ≤ x ^ (δ - η₂) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : ((Nat.log 2 N : ℝ) + 1) * (2 ^ (δ + 1) * C₂ * x ^ (δ - (δ - δ₀) * η₁ + ε)) ≤
      (1 + 2 / ε) * (2 ^ (δ + 1) * C₂) * x ^ (δ - η₂) := by
    calc ((Nat.log 2 N : ℝ) + 1) * (2 ^ (δ + 1) * C₂ * x ^ (δ - (δ - δ₀) * η₁ + ε))
        ≤ (1 + 2 / ε) * x ^ ε * (2 ^ (δ + 1) * C₂ * x ^ (δ - (δ - δ₀) * η₁ + ε)) := by gcongr
      _ = (1 + 2 / ε) * (2 ^ (δ + 1) * C₂) * x ^ (ε + (δ - (δ - δ₀) * η₁ + ε)) := by
          rw [Real.rpow_add hx0 ε]; ring
      _ ≤ (1 + 2 / ε) * (2 ^ (δ + 1) * C₂) * x ^ (δ - η₂) := by
          gcongr
          linarith
  calc x ^ Dx + ((Nat.log 2 N : ℝ) + 1) * (2 ^ (δ + 1) * C₂ * x ^ (δ - (δ - δ₀) * η₁ + ε))
      ≤ x ^ (δ - η₂) + (1 + 2 / ε) * (2 ^ (δ + 1) * C₂) * x ^ (δ - η₂) := add_le_add h1 h2
    _ = (1 + (1 + 2 / ε) * (2 ^ (δ + 1) * C₂)) * x ^ (δ - η₂) := by ring

/-! ### Harman's moment lemma -/

/-- **Harman's moment lemma from the mean value theorem and the Halász–Montgomery count.** For `m ≥ 1`,
`m < D ≤ m + 1/2`, `δ > 4D − 2m` and `η₁ > 0` there are `η₂ > 0`, `C` and `N₀` such that, for `N ≥ N₀`,
`S ⊆ (N, 2N]`, `|c_j| ≤ 1` and `b − a ≤ N^D`, if `|Σ_{j∈S} c_j j^{−it}| ≤ N^{1−η₁}` on `[a, b]` then
`∫_a^b |Σ_{j∈S} c_j j^{−it}|^δ dt ≤ C·N^{δ−η₂}`: the counts of `card_le_mv_exp` (`σ ≤ 3/4`) and `card_le_hm_exp`
(`σ ≥ 3/4`) on the `m`-th power have exponent at most `(4D − 2m)(1 − σ)` (`ShortSieveDreq`). -/
theorem moment_le_hux {m : ℕ} (hm : 1 ≤ m) {Dx δ η₁ : ℝ} (hD : (m : ℝ) < Dx) (hD' : Dx ≤ m + 1 / 2)
    (hδ : 4 * Dx - 2 * m < δ) (hη₁ : 0 < η₁) :
    ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) →
      ∀ c : ℕ → ℂ, (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx →
      (∀ t ∈ Set.Icc a b, ‖dp S c t‖ ≤ (N : ℝ) ^ (1 - η₁)) →
      ∫ t in a..b, ‖dp S c t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η₂) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine moment_le_of_counts (δ₀ := 4 * Dx - 2 * m) hδ (by linarith) (by linarith) hη₁ fun ε hε => ?_
  obtain ⟨C₁, hC₁, hmv⟩ := card_le_mv_exp hm Dx hε
  obtain ⟨C₂, hC₂, N₂, hhm⟩ := card_le_hm_exp hm Dx hε
  refine ⟨max C₁ C₂, max 3 N₂, fun N hN S hS c hc a b hab hba σ V hσ hV R hsep hR hbig => ?_⟩
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  rcases le_total σ (3 / 4) with h34 | h34
  · calc (R.card : ℝ) ≤ C₁ * (N : ℝ) ^ (eMV Dx m σ + ε) :=
          hmv N (le_of_max_le_left hN) S hS c hc a b hab hba σ V hV R hsep hR hbig
      _ ≤ max C₁ C₂ * (N : ℝ) ^ ((4 * Dx - 2 * m) * (1 - σ) + ε) := by
          gcongr
          · exact le_max_left _ _
          · exact mv_exp_le_of_le_three_quarters hD le_rfl h34
  · calc (R.card : ℝ) ≤ C₂ * (N : ℝ) ^ (eHM Dx m σ + ε) :=
          hhm N (le_of_max_le_right hN) S hS c hc a b hab hba σ V h34 hσ hV R hsep hR hbig
      _ ≤ max C₁ C₂ * (N : ℝ) ^ ((4 * Dx - 2 * m) * (1 - σ) + ε) := by
          gcongr
          · exact le_max_right _ _
          · exact hm_exp_le_of_three_quarters_le hm hD.le hD' le_rfl h34 hσ

/-- **Harman's moment lemma from the mean value theorem.** For `k ≥ 1`, `D ≤ k`, `δ > 2k` and `η₁ > 0` there are
`η₂ > 0`, `C` and `N₀` such that, for `N ≥ N₀`, `S ⊆ (N, 2N]`, `|c_j| ≤ 1` and `b − a ≤ N^D`, if
`|Σ_{j∈S} c_j j^{−it}| ≤ N^{1−η₁}` on `[a, b]` then `∫_a^b |Σ_{j∈S} c_j j^{−it}|^δ dt ≤ C·N^{δ−η₂}`: the count of
`card_le_mv_exp` on the `k`-th power has exponent at most `2k(1 − σ)` (`ShortSieveDreq.mv_exp_le`). -/
theorem moment_le_mv {k : ℕ} (hk : 1 ≤ k) {Dx δ η₁ : ℝ} (hD : Dx ≤ k) (hδ : 2 * k < δ) (hη₁ : 0 < η₁) :
    ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) →
      ∀ c : ℕ → ℂ, (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx →
      (∀ t ∈ Set.Icc a b, ‖dp S c t‖ ≤ (N : ℝ) ^ (1 - η₁)) →
      ∫ t in a..b, ‖dp S c t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η₂) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine moment_le_of_counts (δ₀ := 2 * k) hδ (by linarith) (by linarith) hη₁ fun ε hε => ?_
  obtain ⟨C, hC, hmv⟩ := card_le_mv_exp hk Dx hε
  refine ⟨C, 3, fun N hN S hS c hc a b hab hba σ V hσ hV R hsep hR hbig => ?_⟩
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  calc (R.card : ℝ) ≤ C * (N : ℝ) ^ (eMV Dx k σ + ε) := hmv N hN S hS c hc a b hab hba σ V hV R hsep hR hbig
    _ ≤ C * (N : ℝ) ^ (2 * k * (1 - σ) + ε) := by
        gcongr
        exact mv_exp_le hD le_rfl hσ

end ShortSieveMoment
