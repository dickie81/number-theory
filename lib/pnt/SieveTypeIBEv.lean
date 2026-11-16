/-
# The leaves by the bilinear estimate: blocks, splines, and a block pair

Plain statements. For `ρ > 1` the block of `d ≥ 1` is `blk ρ d = ⌊log d/log ρ⌋`. At a scale `D > 0`, with `ρ ≥ 1`,
`0 ≤ η ≤ 1` and `r ≥ 1`, the splines (`SieveSpline.spl`) of step `ℓ = ⌊ηN₁/(rDρ²)⌋ + 1` (`stp`) are the majorant
`TPs`, equal to `1` on `(⌊N₁/(Dρ²)⌋, ⌊N₂/D⌋]`, and the minorant `TMs`, supported in `(⌊N₁/D⌋, ⌊N₂/(Dρ²)⌋]`; so
`r(ℓ − 1) ≤ ηN₁/(Dρ²)` (`stp_sub_le`) and `ℓ ≥ ηN₁/(rDρ²)` (`le_stp`).

* `blk_spec`, `blk_pair`: `ρ^{blk d} ≤ d < ρ^{blk d + 1}`, so a block pair `(β₁, β₂)` puts `d₁d₂` in
  `[ρ^{β₁+β₂}, ρ^{β₁+β₂}ρ²)`.
* `sandwich`: for `D ≤ d < Dρ²`, `TMs ≤ rng(d, ·) ≤ TPs`.
* `mass_diff_le`: the majorant's mass exceeds the minorant's by at most `(N₁ + N₂)(1 − ρ⁻²)/D + 2ηN₁/(Dρ²) + 2`;
  `len_TPs_le`, `len_TMs_le`: both supports have length at most `N₂/D + ηN₁/(Dρ²)`.
* `pair_le`: for a family with comparisons `c = ∏_j I_j` as in `SieveTypeIBFam.typeIB_sharp0`, values `π₁`, `π₂`, `f`
  at least `1` and fibres `Σ_{π₁(y₁)f_σ = d} |λ_σ| ≤ M_f`, `#{π₂(y₂) = d} ≤ M₂`, and `d(n) ≤ F` for `0 < n < q`: a block
  pair's bilinear sum (`SieveTypeIBLeaf.blockSum`) with a spline `t` is at most
  `(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)M_fM₂·bdP + Σ_j 2φ(q)⁻¹(B − A)Σ |λ_σ|M_j(ℓ_j)`, the last sum over the block pair, with
  `bdP = √(P₁P₂(P₁/q + 1)F(n/q + 1)n) + (B − A)(P₂/ℓ)^r P₁P₂ + P₁P₂d(q)/φ(q)`, `P_i = ρ^{β_i+1}` and `n` the spline's
  length.

The proof of `pair_le`: `SieveTypeIBFam.typeIB_sharp0` on the block pair, with `D_m = ⌊P₂⌋` (`π₂ ≤ D_m` on the block),
`H = ⌊(q − 1)/(2D_m)⌋` (so `2HD_m < q` and `q/(2ℓ(H + 1)) ≤ D_m/ℓ`), and `m = ⌊P₁⌋/q + 1`: the block's values `d₁`
with a given inverse mod `q` lie in one residue class of `[1, P₁]` (`eq_of_inv_eq`,
`SieveSpline.card_Ioc_filter_cong_le`). The block's values number at most `P_i`, so its fibres give
`Σ_d A₁(d)² ≤ M_f²P₁` and `Σ|a₁| ≤ M_fP₁` (`fibre_le`), and the same with `M₂`, `P₂`.

The file imports `SieveTypeIBLeaf.lean`.
-/
import SieveTypeIBLeaf

open Finset

namespace SieveTypeIBEv

open SieveTypeIB SieveSpline SieveTypeIBLeaf

/-! ### Blocks -/

/-- The block of `d`: `⌊log d/log ρ⌋`. -/
noncomputable def blk (ρ : ℝ) (d : ℕ) : ℕ := ⌊Real.log d / Real.log ρ⌋₊

/-- `ρ^{blk d} ≤ d < ρ^{blk d + 1}` for `ρ > 1` and `d ≥ 1`. -/
theorem blk_spec {ρ : ℝ} (hρ : 1 < ρ) {d : ℕ} (hd : 1 ≤ d) :
    ρ ^ blk ρ d ≤ d ∧ (d : ℝ) < ρ ^ (blk ρ d + 1) := by
  have hρ0 : 0 < ρ := by linarith
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hld : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hq : 0 ≤ Real.log d / Real.log ρ := div_nonneg hld hlρ.le
  constructor
  · have h1 := Nat.floor_le hq
    rw [← Real.log_le_log_iff (by positivity) hd0, Real.log_pow]
    rw [blk]
    calc (⌊Real.log d / Real.log ρ⌋₊ : ℝ) * Real.log ρ ≤ Real.log d / Real.log ρ * Real.log ρ :=
          mul_le_mul_of_nonneg_right h1 hlρ.le
      _ = Real.log d := div_mul_cancel₀ _ hlρ.ne'
  · have h1 := Nat.lt_floor_add_one (Real.log d / Real.log ρ)
    rw [← Real.log_lt_log_iff hd0 (by positivity), Real.log_pow, blk]
    push_cast
    calc Real.log d = Real.log d / Real.log ρ * Real.log ρ := (div_mul_cancel₀ _ hlρ.ne').symm
      _ < (⌊Real.log d / Real.log ρ⌋₊ + 1) * Real.log ρ := mul_lt_mul_of_pos_right h1 hlρ

/-- A block pair's values: `blk d₁ = β₁` and `blk d₂ = β₂` put `d₁d₂` in `[ρ^{β₁+β₂}, ρ^{β₁+β₂}ρ²)`. -/
theorem blk_pair {ρ : ℝ} (hρ : 1 < ρ) {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    ρ ^ (blk ρ d₁ + blk ρ d₂) ≤ ((d₁ * d₂ : ℕ) : ℝ) ∧
      ((d₁ * d₂ : ℕ) : ℝ) < ρ ^ (blk ρ d₁ + blk ρ d₂) * ρ ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨h1, h2⟩ := blk_spec hρ hd₁
  obtain ⟨h3, h4⟩ := blk_spec hρ hd₂
  push_cast
  rw [pow_add]
  constructor
  · exact mul_le_mul h1 h3 (by positivity) (by positivity)
  · calc (d₁ : ℝ) * d₂ < ρ ^ (blk ρ d₁ + 1) * ρ ^ (blk ρ d₂ + 1) :=
          mul_lt_mul'' h2 h4 (by positivity) (by positivity)
      _ = ρ ^ blk ρ d₁ * ρ ^ blk ρ d₂ * ρ ^ 2 := by ring

/-! ### Splines at a scale -/

/-- The splines' step at the scale `D`: `ℓ = ⌊ηN₁/(rDρ²)⌋ + 1`. -/
noncomputable def stp (η ρ D : ℝ) (N₁ r : ℕ) : ℕ := ⌊η * N₁ / (r * D * ρ ^ 2)⌋₊ + 1

/-- The majorant at the scale `D`: the spline equal to `1` on `(⌊N₁/(Dρ²)⌋, ⌊N₂/D⌋]`. -/
noncomputable def TPs (η ρ D : ℝ) (N₁ N₂ r : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (⌊N₁ / (D * ρ ^ 2)⌋₊ - r * (stp η ρ D N₁ r - 1), ⌊N₂ / D⌋₊, stp η ρ D N₁ r, r)

/-- The minorant at the scale `D`: the spline supported in `(⌊N₁/D⌋, ⌊N₂/(Dρ²)⌋]`. -/
noncomputable def TMs (η ρ D : ℝ) (N₁ N₂ r : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (⌊N₁ / D⌋₊, ⌊N₂ / (D * ρ ^ 2)⌋₊ - r * (stp η ρ D N₁ r - 1), stp η ρ D N₁ r, r)

theorem one_le_stp (η ρ D : ℝ) (N₁ r : ℕ) : 1 ≤ stp η ρ D N₁ r := by unfold stp; omega

/-- `r(ℓ − 1) ≤ ηN₁/(Dρ²)`. -/
theorem stp_sub_le {η ρ D : ℝ} (hη : 0 ≤ η) (hρ : 0 < ρ) (hD : 0 < D) (N₁ : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ((r * (stp η ρ D N₁ r - 1) : ℕ) : ℝ) ≤ η * N₁ / (D * ρ ^ 2) := by
  unfold stp
  rw [Nat.add_sub_cancel]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have h := Nat.floor_le (show 0 ≤ η * N₁ / (r * D * ρ ^ 2) by positivity)
  push_cast
  calc (r : ℝ) * ⌊η * N₁ / (r * D * ρ ^ 2)⌋₊ ≤ r * (η * N₁ / (r * D * ρ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hr0.le
    _ = η * N₁ / (D * ρ ^ 2) := by field_simp

/-- `ηN₁/(rDρ²) ≤ ℓ`. -/
theorem le_stp (η ρ D : ℝ) (N₁ r : ℕ) : η * N₁ / (r * D * ρ ^ 2) ≤ stp η ρ D N₁ r := by
  unfold stp
  push_cast
  exact (Nat.lt_floor_add_one _).le

/-- For `η ≤ 1`: `r(ℓ − 1) ≤ ⌊N₁/(Dρ²)⌋`. -/
theorem stp_sub_le_floor {η ρ D : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hρ : 0 < ρ) (hD : 0 < D) (N₁ : ℕ) {r : ℕ}
    (hr : 1 ≤ r) : r * (stp η ρ D N₁ r - 1) ≤ ⌊(N₁ : ℝ) / (D * ρ ^ 2)⌋₊ := by
  apply Nat.le_floor
  refine (stp_sub_le hη hρ hD N₁ hr).trans ?_
  rw [mul_div_assoc]
  exact mul_le_of_le_one_left (by positivity) hη1

/-- Where a spline is positive: `A < B` and `A < k ≤ B + r(ℓ − 1)`. -/
theorem spl_ne_zero {A B ℓ r k : ℕ} (h : spl A B ℓ r k ≠ 0) : A < B ∧ A < k ∧ k ≤ B + r * (ℓ - 1) := by
  rw [spl, div_ne_zero_iff] at h
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.1 (Nat.cast_ne_zero.1 h.1)
  rw [Finset.mem_filter] at hx
  have hm := tsum_mem_supp hx.1
  rw [hx.2, supp, Finset.mem_Ioc] at hm
  rw [tup, Finset.mem_product, Finset.mem_Ioc] at hx
  exact ⟨by omega, hm.1, hm.2⟩

/-- **The sandwich at a scale.** For `0 < D ≤ d < Dρ²`, `ρ ≥ 1`, `0 ≤ η ≤ 1` and `r ≥ 1`: the minorant and the
majorant at the scale `D` lie below and above `rng(d, ·)`. -/
theorem sandwich {η ρ D : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hρ : 1 ≤ ρ) (hD : 0 < D) (N₁ N₂ : ℕ) {r : ℕ} (hr : 1 ≤ r)
    {d : ℕ} (hd1 : D ≤ d) (hd2 : (d : ℝ) < D * ρ ^ 2) (k : ℕ) :
    splv (TMs η ρ D N₁ N₂ r) k ≤ rng N₁ N₂ d k ∧ rng N₁ N₂ d k ≤ splv (TPs η ρ D N₁ N₂ r) k := by
  have hρ0 : 0 < ρ := by linarith
  have hDρ : 0 < D * ρ ^ 2 := by positivity
  have hℓ1 := one_le_stp η ρ D N₁ r
  have hsP := stp_sub_le_floor hη hη1 hρ0 hD N₁ hr
  constructor
  · -- the minorant: where it is positive, `N₁/D < k ≤ N₂/(Dρ²)`
    by_cases hpos : splv (TMs η ρ D N₁ N₂ r) k = 0
    · rw [hpos]; exact rng_nonneg _ _ _ _
    · have h := spl_ne_zero hpos
      simp only [TMs] at h
      obtain ⟨hAB, hAk, hkB⟩ := h
      have hk : k ≤ ⌊(N₂ : ℝ) / (D * ρ ^ 2)⌋₊ := by omega
      have hk0 : 1 ≤ k := by omega
      have hk1 : (N₁ : ℝ) / D < k := (Nat.floor_lt (by positivity)).1 hAk
      have hk2 : (k : ℝ) ≤ N₂ / (D * ρ ^ 2) := (Nat.le_floor_iff (by positivity)).1 hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have hlo : N₁ < d * k := by
        have : (N₁ : ℝ) < D * k := by rwa [div_lt_iff₀ hD, mul_comm] at hk1
        have h2 : D * k ≤ d * k := mul_le_mul_of_nonneg_right hd1 (by positivity)
        exact_mod_cast (show ((N₁ : ℕ) : ℝ) < ((d * k : ℕ) : ℝ) by push_cast; linarith)
      have hhi : d * k ≤ N₂ := by
        have : D * ρ ^ 2 * k ≤ N₂ := by rwa [le_div_iff₀ hDρ, mul_comm] at hk2
        have h2 : (d : ℝ) * k ≤ D * ρ ^ 2 * k := mul_le_mul_of_nonneg_right hd2.le (by positivity)
        exact_mod_cast (show ((d * k : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) by push_cast; linarith)
      have hrng : rng N₁ N₂ d k = 1 := by
        unfold rng
        rw [ite_eq_left ⟨hlo, hhi⟩]
      rw [hrng]
      exact spl_le_one _ _ _ _ _ hℓ1
  · -- the majorant: where `rng = 1`, `N₁/(Dρ²) < k ≤ N₂/D`
    unfold rng
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      have hk0 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · rw [hk, mul_zero] at h1; omega
        · exact hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have h1R : (N₁ : ℝ) < d * k := by exact_mod_cast h1
      have h2R : (d : ℝ) * k ≤ N₂ := by exact_mod_cast h2
      have hlo : (N₁ : ℝ) / (D * ρ ^ 2) < k := by
        rw [div_lt_iff₀ hDρ]
        have : (d : ℝ) * k ≤ D * ρ ^ 2 * k := mul_le_mul_of_nonneg_right hd2.le (by positivity)
        linarith
      have hhi : (k : ℝ) ≤ N₂ / D := by
        rw [le_div_iff₀ hD]
        have : D * k ≤ d * k := mul_le_mul_of_nonneg_right hd1 (by positivity)
        linarith
      unfold splv TPs
      dsimp only
      refine (spl_eq_one _ _ _ _ _ hℓ1 ?_ ?_).symm.le
      · have := (Nat.floor_lt (by positivity)).2 hlo
        omega
      · exact Nat.le_floor hhi
    · exact spl_nonneg _ _ _ _ _

/-- **The transition's mass.** For `N₁ ≤ N₂`, `0 < D`, `ρ ≥ 1`, `0 ≤ η ≤ 1` and `r ≥ 1`, the majorant's mass exceeds
the minorant's by at most `(N₁ + N₂)(1 − ρ⁻²)/D + 2ηN₁/(Dρ²) + 2`. -/
theorem mass_diff_le {η ρ D : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hρ : 1 ≤ ρ) (hD : 0 < D) {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂)
    {r : ℕ} (hr : 1 ≤ r) :
    massv (TPs η ρ D N₁ N₂ r) - massv (TMs η ρ D N₁ N₂ r) ≤
      (N₁ + N₂) * (1 - 1 / ρ ^ 2) / D + 2 * (η * N₁ / (D * ρ ^ 2)) + 2 := by
  have hρ0 : 0 < ρ := by linarith
  have hDρ : 0 < D * ρ ^ 2 := by positivity
  have hsP := stp_sub_le_floor hη hη1 hρ0 hD N₁ hr
  have hs := stp_sub_le hη hρ0 hD N₁ hr
  set s := r * (stp η ρ D N₁ r - 1) with hsdef
  set a := ⌊(N₂ : ℝ) / D⌋₊ with ha
  set b := ⌊(N₁ : ℝ) / (D * ρ ^ 2)⌋₊ with hb
  set c := ⌊(N₂ : ℝ) / (D * ρ ^ 2)⌋₊ with hc
  set e := ⌊(N₁ : ℝ) / D⌋₊ with he
  have hmP : massv (TPs η ρ D N₁ N₂ r) = ((a - (b - s) : ℕ) : ℝ) := rfl
  have hmM : massv (TMs η ρ D N₁ N₂ r) = ((c - s - e : ℕ) : ℝ) := rfl
  have haR : (a : ℝ) ≤ N₂ / D := Nat.floor_le (by positivity)
  have hbR : (N₁ : ℝ) / (D * ρ ^ 2) - 1 < b := Nat.sub_one_lt_floor _
  have hcR : (N₂ : ℝ) / (D * ρ ^ 2) - 1 < c := Nat.sub_one_lt_floor _
  have heR : (e : ℝ) ≤ N₁ / D := Nat.floor_le (by positivity)
  have hTM : (c : ℝ) - s - e ≤ ((c - s - e : ℕ) : ℝ) := by
    have h1 : c ≤ (c - s - e) + s + e := by omega
    have : (c : ℝ) ≤ ((c - s - e : ℕ) : ℝ) + s + e := by exact_mod_cast h1
    linarith
  have hN : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ
  have hu : (N₁ : ℝ) / (D * ρ ^ 2) ≤ N₂ / D := by
    calc (N₁ : ℝ) / (D * ρ ^ 2) ≤ N₁ / D :=
          div_le_div_of_nonneg_left (by positivity) hD (le_mul_of_one_le_right hD.le hρ2)
      _ ≤ N₂ / D := div_le_div_of_nonneg_right hN hD.le
  have hid : ((N₁ : ℝ) + N₂) * (1 - 1 / ρ ^ 2) / D =
      (N₂ / D - N₁ / (D * ρ ^ 2)) + (N₁ / D - N₂ / (D * ρ ^ 2)) := by
    field_simp
    ring
  rw [hmP, hmM, hid]
  have hsR : ((s : ℕ) : ℝ) ≤ η * N₁ / (D * ρ ^ 2) := hs
  by_cases hab : b - s ≤ a
  · have hTP : ((a - (b - s) : ℕ) : ℝ) = a - b + s := by
      rw [Nat.cast_sub hab, Nat.cast_sub hsP]; ring
    rw [hTP]
    linarith
  · have hTP : ((a - (b - s) : ℕ) : ℝ) = 0 := by
      rw [Nat.sub_eq_zero_of_le (by omega)]; simp
    rw [hTP]
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    linarith

/-- The splines' lengths: `B + r(ℓ − 1) − A ≤ N₂/D + ηN₁/(Dρ²)` for the majorant and the minorant. -/
theorem len_TPs_le {η ρ D : ℝ} (hη : 0 ≤ η) (hρ : 1 ≤ ρ) (hD : 0 < D) (N₁ N₂ : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (((TPs η ρ D N₁ N₂ r).2.1 + (TPs η ρ D N₁ N₂ r).2.2.2 * ((TPs η ρ D N₁ N₂ r).2.2.1 - 1) -
      (TPs η ρ D N₁ N₂ r).1 : ℕ) : ℝ) ≤ N₂ / D + η * N₁ / (D * ρ ^ 2) := by
  have hρ0 : 0 < ρ := by linarith
  have hs := stp_sub_le hη hρ0 hD N₁ hr
  simp only [TPs]
  set s := r * (stp η ρ D N₁ r - 1) with hsdef
  have h1 : ⌊(N₂ : ℝ) / D⌋₊ + s - (⌊(N₁ : ℝ) / (D * ρ ^ 2)⌋₊ - s) ≤ ⌊(N₂ : ℝ) / D⌋₊ + s := Nat.sub_le _ _
  have h2 : ((⌊(N₂ : ℝ) / D⌋₊ : ℕ) : ℝ) ≤ N₂ / D := Nat.floor_le (by positivity)
  have h3 : ((⌊(N₂ : ℝ) / D⌋₊ + s - (⌊(N₁ : ℝ) / (D * ρ ^ 2)⌋₊ - s) : ℕ) : ℝ) ≤ ⌊(N₂ : ℝ) / D⌋₊ + (s : ℝ) := by
    exact_mod_cast h1
  have hsR : ((s : ℕ) : ℝ) ≤ η * N₁ / (D * ρ ^ 2) := hs
  linarith

theorem len_TMs_le {η ρ D : ℝ} (hη : 0 ≤ η) (hρ : 1 ≤ ρ) (hD : 0 < D) (N₁ N₂ : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (((TMs η ρ D N₁ N₂ r).2.1 + (TMs η ρ D N₁ N₂ r).2.2.2 * ((TMs η ρ D N₁ N₂ r).2.2.1 - 1) -
      (TMs η ρ D N₁ N₂ r).1 : ℕ) : ℝ) ≤ N₂ / D + η * N₁ / (D * ρ ^ 2) := by
  have hρ0 : 0 < ρ := by linarith
  have hDρ : 0 < D * ρ ^ 2 := by positivity
  have hs := stp_sub_le hη hρ0 hD N₁ hr
  simp only [TMs]
  set s := r * (stp η ρ D N₁ r - 1) with hsdef
  set c := ⌊(N₂ : ℝ) / (D * ρ ^ 2)⌋₊ with hc
  have h1 : c - s + s - ⌊(N₁ : ℝ) / D⌋₊ ≤ c + s := by omega
  have h2 : (c : ℝ) ≤ N₂ / (D * ρ ^ 2) := Nat.floor_le (by positivity)
  have h4 : (N₂ : ℝ) / (D * ρ ^ 2) ≤ N₂ / D :=
    div_le_div_of_nonneg_left (by positivity) hD (le_mul_of_one_le_right hD.le (one_le_pow₀ hρ))
  have h3 : (((c - s + s - ⌊(N₁ : ℝ) / D⌋₊ : ℕ)) : ℝ) ≤ c + (s : ℝ) := by exact_mod_cast h1
  have hsR : ((s : ℕ) : ℝ) ≤ η * N₁ / (D * ρ ^ 2) := hs
  linarith

/-! ### A block pair -/

/-- A block's fibres: if the values `π y` (`y ∈ Y`) lie in `[1, P]` and every fibre has `Σ‖c‖ ≤ M`, then
`Σ_d (Σ_{π y = d} ‖c y‖)² ≤ M²P` and `Σ_y ‖c y‖ ≤ MP`. -/
theorem fibre_le {ι : Type*} (Y : Finset ι) (π : ι → ℕ) (c : ι → ℂ) {P M : ℝ} (hP0 : 0 ≤ P) (hM0 : 0 ≤ M)
    (hP : ∀ y ∈ Y, 1 ≤ π y ∧ (π y : ℝ) ≤ P) (hM : ∀ d, ∑ y ∈ Y.filter (fun y => π y = d), ‖c y‖ ≤ M) :
    ∑ d ∈ Y.image π, (∑ y ∈ Y.filter (fun y => π y = d), ‖c y‖) ^ 2 ≤ M ^ 2 * P ∧ ∑ y ∈ Y, ‖c y‖ ≤ M * P := by
  classical
  have hcard : ((Y.image π).card : ℝ) ≤ P := by
    have hsub : Y.image π ⊆ Finset.Icc 1 ⌊P⌋₊ := by
      intro d hd
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hd
      exact Finset.mem_Icc.2 ⟨(hP y hy).1, Nat.le_floor (hP y hy).2⟩
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact le_trans (by exact_mod_cast h) (Nat.floor_le hP0)
  have h0 : ∀ d, 0 ≤ ∑ y ∈ Y.filter (fun y => π y = d), ‖c y‖ := fun d => Finset.sum_nonneg fun y _ => norm_nonneg _
  constructor
  · calc ∑ d ∈ Y.image π, (∑ y ∈ Y.filter (fun y => π y = d), ‖c y‖) ^ 2 ≤ ∑ _d ∈ Y.image π, M ^ 2 :=
          Finset.sum_le_sum fun d _ => pow_le_pow_left₀ (h0 d) (hM d) 2
      _ = M ^ 2 * (Y.image π).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ M ^ 2 * P := mul_le_mul_of_nonneg_left hcard (by positivity)
  · rw [← SieveTypeIBFam.sum_fiber_norm Y π c]
    calc ∑ d ∈ Y.image π, ∑ y ∈ Y.filter (fun y => π y = d), ‖c y‖ ≤ ∑ _d ∈ Y.image π, M :=
          Finset.sum_le_sum fun d _ => hM d
      _ = M * (Y.image π).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ M * P := mul_le_mul_of_nonneg_left hcard hM0

/-- The length `B + r(ℓ − 1) − A` of a spline's support. -/
noncomputable def lenv (t : ℕ × ℕ × ℕ × ℕ) : ℝ := ((t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1 : ℕ) : ℝ)

/-- Units with the same inverse are equal. -/
theorem eq_of_inv_eq {q : ℕ} {d d₀ : ZMod q} (hd : IsUnit d) (hd₀ : IsUnit d₀) (h : d⁻¹ = d₀⁻¹) : d = d₀ := by
  have h1 : d * d⁻¹ = 1 := ZMod.mul_inv_of_unit d hd
  have h2 : d₀ * d₀⁻¹ = 1 := ZMod.mul_inv_of_unit d₀ hd₀
  calc d = d * (d₀ * d₀⁻¹) := by rw [h2, mul_one]
    _ = d₀ * (d * d⁻¹) := by rw [h]; ring
    _ = d₀ := by rw [h1, mul_one]

open scoped FourierTransform
open MeasureTheory

variable {q : ℕ} [NeZero q]

end SieveTypeIBEv
