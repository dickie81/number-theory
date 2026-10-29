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

/-- A block pair's bound. With `P_i = ρ^{β_i+1}` and the spline's length `n`:
`√(P₁P₂(P₁/q + 1)F(n/q + 1)n) + (B − A)(P₂/ℓ)^r P₁P₂ + P₁P₂d(q)/φ(q)`. -/
noncomputable def bdP (q : ℕ) (ρ : ℝ) (β₁ β₂ : ℕ) (t : ℕ × ℕ × ℕ × ℕ) (F : ℕ) : ℝ :=
  √(ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * (ρ ^ (β₁ + 1) / q + 1) * F * (lenv t / q + 1) * lenv t) +
    massv t * (ρ ^ (β₂ + 1) / t.2.2.1) ^ t.2.2.2 * (ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1)) +
    ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * ((q.divisors.card : ℝ) / q.totient)

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

/-- **A block pair.** Let the comparisons `c = ∏_j I_j` of `SieveTypeIBFam.typeIB_sharp0` be given, every value
`π₁(y₁)`, `π₂(y₂)`, `f_σ` at least `1`, and the fibres bounded: `Σ_{π₁(y₁)f_σ = d} |λ_σ| ≤ M_f` and
`#{y₂ : π₂(y₂) = d} ≤ M₂`; let `d(n) ≤ F` for `0 < n < q`. The bilinear sum of the block pair `(β₁, β₂)` of `blk ρ`
with the spline `t` is at most `(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)·M_fM₂·bdP` plus the near-boundary masses
`Σ_j 2φ(q)⁻¹(B − A)Σ_{(y₁,σ),y₂} |λ_σ|M_j(ℓ_j)` over the block pair. -/
theorem pair_le (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (c : ι₁ → ι₂ → ℝ)
    {J : ℕ} (I : Fin J → ι₁ → ι₂ → ℝ) (hc : ∀ y₁ y₂, c y₁ y₂ = ∏ j, I j y₁ y₂)
    (Gs Ms : Fin J → ℝ → ℝ) (hGc : ∀ j, Continuous (fun u => ((Gs j u : ℝ) : ℂ)))
    (hGi : ∀ j, Integrable (fun u => ((Gs j u : ℝ) : ℂ))) (hGf : ∀ j, Integrable (𝓕 (fun u => ((Gs j u : ℝ) : ℂ))))
    (hMc : ∀ j, Continuous (fun u => ((Ms j u : ℝ) : ℂ))) (hMi : ∀ j, Integrable (fun u => ((Ms j u : ℝ) : ℂ)))
    (hMf : ∀ j, Integrable (𝓕 (fun u => ((Ms j u : ℝ) : ℂ))))
    (φ : Fin J → ι₁ → ℝ) (ψ : Fin J → ι₂ → ℝ)
    (hI : ∀ j y₁ y₂, 0 ≤ I j y₁ y₂ ∧ I j y₁ y₂ ≤ 1) (hG : ∀ j u, 0 ≤ Gs j u ∧ Gs j u ≤ 1)
    (hIG : ∀ j y₁ y₂, |I j y₁ y₂ - Gs j (φ j y₁ + ψ j y₂)| ≤ Ms j (φ j y₁ + ψ j y₂))
    {ρ : ℝ} (hρ : 1 < ρ) (β₁ β₂ : ℕ) (t : ℕ × ℕ × ℕ × ℕ) (hℓ : 1 ≤ t.2.2.1)
    (hπ₁ : ∀ y ∈ Y₁, 1 ≤ π₁ y) (hπ₂ : ∀ y ∈ Y₂, 1 ≤ π₂ y) (hf : ∀ σ ∈ S, 1 ≤ f σ)
    {Mf M₂ : ℝ} (hMf0 : 0 ≤ Mf) (hMfib : ∀ d, ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => π₁ x.1 * f x.2 = d), |lam x.2| ≤ Mf)
    (hM₂ : ∀ d, (#(Y₂.filter (fun y => π₂ y = d)) : ℝ) ≤ M₂)
    {F : ℕ} (hF : ∀ n, 0 < n → n < q → n.divisors.card ≤ F) :
    ‖blockSum q a Y₁ Y₂ π₁ π₂ S f lam c (blk ρ) (blk ρ) β₁ β₂ t‖ ≤
      ((∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) + ∑ j, ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) *
          (Mf * M₂ * bdP q ρ β₁ β₂ t F) +
        ∑ j, 2 * (q.totient : ℝ)⁻¹ * (massv t *
          ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
            ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  have hq0 : 0 < q := NeZero.pos q
  set Y₁' := (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁) with hY₁'
  set Y₂' := Y₂.filter (fun y => blk ρ (π₂ y) = β₂) with hY₂'
  set P₁ : ℝ := ρ ^ (β₁ + 1) with hP₁
  set P₂ : ℝ := ρ ^ (β₂ + 1) with hP₂
  have hP₁0 : 0 ≤ P₁ := by positivity
  have hP₂0 : 0 ≤ P₂ := by positivity
  set Dm : ℕ := ⌊P₂⌋₊ with hDm
  have hDm1 : 1 ≤ Dm := Nat.le_floor (by rw [hP₂]; push_cast; exact one_le_pow₀ hρ.le)
  set H : ℕ := (q - 1) / (2 * Dm) with hH
  set m : ℕ := ⌊P₁⌋₊ / q + 1 with hm
  -- the values of the block pair
  have hv₁ : ∀ x ∈ Y₁', 1 ≤ π₁ x.1 * f x.2 ∧ ((π₁ x.1 * f x.2 : ℕ) : ℝ) ≤ P₁ := by
    intro x hx
    obtain ⟨hx1, hxb⟩ := Finset.mem_filter.1 hx
    obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hx1
    have h1 : 1 ≤ π₁ x.1 * f x.2 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := hπ₁ _ hy; omega)
      (by have := hf _ hσ; omega))
    refine ⟨h1, ?_⟩
    have := (blk_spec hρ h1).2
    rw [hxb] at this
    exact this.le
  have hv₂ : ∀ y ∈ Y₂', 1 ≤ π₂ y ∧ (π₂ y : ℝ) ≤ P₂ := by
    intro y hy
    obtain ⟨hy2, hyb⟩ := Finset.mem_filter.1 hy
    refine ⟨hπ₂ y hy2, ?_⟩
    have := (blk_spec hρ (hπ₂ y hy2)).2
    rw [hyb] at this
    exact this.le
  -- the block sum in the form of `typeIB_sharp0`
  have hform : blockSum q a Y₁ Y₂ π₁ π₂ S f lam c (blk ρ) (blk ρ) β₁ β₂ t =
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', (fun x : ι₁ × κ => ((lam x.2 : ℝ) : ℂ)) x * (fun _ : ι₂ => (1 : ℂ)) y₂ *
        (∏ j, ((fun j (x : ι₁ × κ) y₂ => I j x.1 y₂) j x y₂ : ℂ)) *
        ∑ k ∈ supp t.1 t.2.1 t.2.2.1 t.2.2.2, ((spl t.1 t.2.1 t.2.2.1 t.2.2.2 k : ℝ) : ℂ) *
          SieveFamily.dw q a ((fun x : ι₁ × κ => π₁ x.1 * f x.2) x * π₂ y₂ * k) := by
    rw [blockSum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y₂ _ => ?_
    rw [hc, Complex.ofReal_prod]
    rfl
  rw [hform]
  have hb := SieveTypeIBFam.typeIB_sharp0 a ha Y₁' Y₂' (fun x : ι₁ × κ => π₁ x.1 * f x.2) π₂
    (fun x : ι₁ × κ => ((lam x.2 : ℝ) : ℂ)) (fun _ : ι₂ => (1 : ℂ)) (fun j (x : ι₁ × κ) y₂ => I j x.1 y₂)
    Gs Ms hGc hGi hGf hMc hMi hMf (fun j (x : ι₁ × κ) => φ j x.1) ψ (fun j x y₂ => hI j x.1 y₂) hG
    (fun j x y₂ => hIG j x.1 y₂) t.1 t.2.1 t.2.2.1 t.2.2.2 hℓ (H := H) (Dm := Dm) (F := F) (m := m)
    (fun y hy => (hv₂ y hy).1)
    (fun y hy => Nat.le_floor (hv₂ y hy).2) hDm1
    (by
      have h1 : 2 * H * Dm ≤ q - 1 := by
        rw [hH, mul_comm 2, mul_assoc]
        exact Nat.div_mul_le_self _ _
      omega)
    (by
      -- a residue class of the block's values
      intro r
      set T := (Y₁'.image (fun x : ι₁ × κ => π₁ x.1 * f x.2)).filter
        (fun d : ℕ => IsUnit (d : ZMod q) ∧ ((d : ZMod q))⁻¹ = r) with hT
      rcases T.eq_empty_or_nonempty with hT0 | ⟨d₀, hd₀⟩
      · rw [hT0, Finset.card_empty]; exact Nat.zero_le _
      · have hsub : T ⊆ (Finset.Ioc 0 ⌊P₁⌋₊).filter (fun k' : ℕ => (k' : ZMod q) = (d₀ : ZMod q)) := by
          intro d hd
          obtain ⟨hdi, hdu, hdr⟩ := Finset.mem_filter.1 hd
          obtain ⟨hd0i, hd0u, hd0r⟩ := Finset.mem_filter.1 hd₀
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hdi
          refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(hv₁ x hx).1, Nat.le_floor (hv₁ x hx).2⟩, ?_⟩
          exact eq_of_inv_eq hdu hd0u (hdr.trans hd0r.symm)
        refine (Finset.card_le_card hsub).trans ?_
        have := SieveSpline.card_Ioc_filter_cong_le (q := q) 0 ⌊P₁⌋₊ d₀
        rw [Nat.sub_zero] at this
        exact this)
    (by
      intro τ hτ hτH y hy
      apply hF
      · exact Nat.mul_pos (Int.natAbs_pos.2 hτ) (hv₂ y hy).1
      · have h1 : τ.natAbs * π₂ y ≤ H * Dm := Nat.mul_le_mul hτH (Nat.le_floor (hv₂ y hy).2)
        have h2 : 2 * H * Dm ≤ q - 1 := by
          rw [hH, mul_comm 2, mul_assoc]
          exact Nat.div_mul_le_self _ _
        have h3 : H * Dm ≤ 2 * H * Dm := by rw [mul_assoc]; omega
        omega)
  refine hb.trans ?_
  -- the bound `bdIB` of the block pair
  set bd := SieveTypeIBFam.bdIB q Y₁' Y₂' (fun x : ι₁ × κ => π₁ x.1 * f x.2) π₂ (fun x : ι₁ × κ => ((lam x.2 : ℝ) : ℂ))
    (fun _ : ι₂ => (1 : ℂ)) t.1 t.2.1 t.2.2.1 t.2.2.2 H F m with hbd
  have hM₂0 : 0 ≤ M₂ := le_trans (Nat.cast_nonneg _) (hM₂ 0)
  obtain ⟨hsq₁, hl₁⟩ := fibre_le Y₁' (fun x : ι₁ × κ => π₁ x.1 * f x.2) (fun x => ((lam x.2 : ℝ) : ℂ)) hP₁0 hMf0
    hv₁ (fun d => by
      refine le_trans ?_ (hMfib d)
      simp only [Complex.norm_real, Real.norm_eq_abs]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => abs_nonneg _
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx1).1, hx2⟩)
  obtain ⟨hsq₂, hl₂⟩ := fibre_le Y₂' π₂ (fun _ => (1 : ℂ)) hP₂0 hM₂0 hv₂ (fun d => by
      refine le_trans ?_ (hM₂ d)
      simp only [norm_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast Finset.card_le_card fun y hy => by
        obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
        exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy1).1, hy2⟩)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hdq : (0 : ℝ) ≤ (q.divisors.card : ℝ) / q.totient := by positivity
  have hm' : (m : ℝ) ≤ P₁ / q + 1 := by
    rw [hm]; push_cast
    have h1 : ((⌊P₁⌋₊ / q : ℕ) : ℝ) ≤ (⌊P₁⌋₊ : ℝ) / q := Nat.cast_div_le
    have h2 : (⌊P₁⌋₊ : ℝ) / q ≤ P₁ / q := div_le_div_of_nonneg_right (Nat.floor_le hP₁0) (by positivity)
    linarith
  have hn' : ((((t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) / q + 1 : ℕ) : ℝ)) ≤ lenv t / q + 1 := by
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) (n := q)
    rw [lenv]
    linarith
  have hlen0 : 0 ≤ lenv t := Nat.cast_nonneg _
  -- `q/(2ℓ(H + 1)) ≤ D_m/ℓ`
  have htail : (q : ℝ) / (2 * t.2.2.1 * (H + 1)) ≤ P₂ / t.2.2.1 := by
    have hℓ0 : (0 : ℝ) < t.2.2.1 := by exact_mod_cast hℓ
    have hqH : q ≤ 2 * Dm * (H + 1) := by
      have e1 := Nat.div_add_mod (q - 1) (2 * Dm)
      have e2 := Nat.mod_lt (q - 1) (show 0 < 2 * Dm by omega)
      rw [← hH] at e1
      rw [mul_add, mul_one]
      generalize 2 * Dm * H = X at e1 ⊢
      omega
    have hqH' : (q : ℝ) ≤ 2 * Dm * (H + 1) := by exact_mod_cast hqH
    have hDmP : (Dm : ℝ) ≤ P₂ := Nat.floor_le hP₂0
    rw [div_le_div_iff₀ (by positivity) hℓ0]
    calc (q : ℝ) * t.2.2.1 ≤ 2 * Dm * (H + 1) * t.2.2.1 := mul_le_mul_of_nonneg_right hqH' hℓ0.le
      _ ≤ 2 * P₂ * (H + 1) * t.2.2.1 := by gcongr
      _ = P₂ * (2 * t.2.2.1 * (H + 1)) := by ring
  have hbdle : bd ≤ Mf * M₂ * bdP q ρ β₁ β₂ t F := by
    rw [hbd, SieveTypeIBFam.bdIB, bdP]
    simp only [norm_one]
    -- the three terms
    have hA : √(∑ d ∈ Y₁'.image (fun x : ι₁ × κ => π₁ x.1 * f x.2),
          (∑ y ∈ Y₁'.filter (fun y => π₁ y.1 * f y.2 = d), ‖((lam y.2 : ℝ) : ℂ)‖) ^ 2) *
        √(m * F * (∑ d ∈ Y₂'.image π₂, (∑ y ∈ Y₂'.filter (fun y => π₂ y = d), (1 : ℝ)) ^ 2) *
          ((((t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) / q + 1 : ℕ) : ℝ) *
            (t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1 : ℕ))) ≤
        Mf * M₂ * √(P₁ * P₂ * (P₁ / q + 1) * F * (lenv t / q + 1) * lenv t) := by
      have hsq₂' : ∑ d ∈ Y₂'.image π₂, (∑ y ∈ Y₂'.filter (fun y => π₂ y = d), (1 : ℝ)) ^ 2 ≤ M₂ ^ 2 * P₂ := by
        simpa using hsq₂
      have e : Mf * M₂ * √(P₁ * P₂ * (P₁ / q + 1) * F * (lenv t / q + 1) * lenv t) =
          √(Mf ^ 2 * P₁) * √((P₁ / q + 1) * F * (M₂ ^ 2 * P₂) * ((lenv t / q + 1) * lenv t)) := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show Mf ^ 2 * P₁ * ((P₁ / q + 1) * F * (M₂ ^ 2 * P₂) * ((lenv t / q + 1) * lenv t)) =
          (Mf * M₂) ^ 2 * (P₁ * P₂ * (P₁ / q + 1) * F * (lenv t / q + 1) * lenv t) by ring]
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ (Mf * M₂) ^ 2 by positivity), Real.sqrt_sq (by positivity)]
      rw [e]
      refine mul_le_mul (Real.sqrt_le_sqrt hsq₁) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
      have hn0 : (0 : ℝ) ≤ ((((t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) / q + 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hm' hF0) hsq₂' (Finset.sum_nonneg
        fun d _ => sq_nonneg _) (by positivity)) (mul_le_mul hn' le_rfl hlen0 (by positivity))
        (mul_nonneg hn0 hlen0) (by positivity)
    have hB : ((t.2.1 - t.1 : ℕ) : ℝ) * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 *
          ((∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * ∑ y ∈ Y₂', (1 : ℝ)) ≤
        Mf * M₂ * (massv t * (P₂ / t.2.2.1) ^ t.2.2.2 * (P₁ * P₂)) := by
      have hl₂' : ∑ y ∈ Y₂', (1 : ℝ) ≤ M₂ * P₂ := by simpa using hl₂
      have hpow : ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 ≤ (P₂ / t.2.2.1) ^ t.2.2.2 :=
        pow_le_pow_left₀ (by positivity) htail _
      have hm0 : 0 ≤ massv t := Nat.cast_nonneg _
      calc ((t.2.1 - t.1 : ℕ) : ℝ) * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 *
            ((∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * ∑ y ∈ Y₂', (1 : ℝ))
          ≤ massv t * (P₂ / t.2.2.1) ^ t.2.2.2 * ((Mf * P₁) * (M₂ * P₂)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hm0) (mul_le_mul hl₁ hl₂'
              (Finset.sum_nonneg fun _ _ => zero_le_one) (by positivity)) (by positivity) (by positivity)
        _ = Mf * M₂ * (massv t * (P₂ / t.2.2.1) ^ t.2.2.2 * (P₁ * P₂)) := by ring
    have hC : (∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * (∑ y ∈ Y₂', (1 : ℝ)) * ((q.divisors.card : ℝ) / q.totient) ≤
        Mf * M₂ * (P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) := by
      have hl₂' : ∑ y ∈ Y₂', (1 : ℝ) ≤ M₂ * P₂ := by simpa using hl₂
      calc (∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * (∑ y ∈ Y₂', (1 : ℝ)) * ((q.divisors.card : ℝ) / q.totient)
          ≤ (Mf * P₁) * (M₂ * P₂) * ((q.divisors.card : ℝ) / q.totient) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hl₁ hl₂' (Finset.sum_nonneg fun _ _ => zero_le_one)
              (by positivity)) hdq
        _ = Mf * M₂ * (P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) := by ring
    have e : Mf * M₂ * (√(P₁ * P₂ * (P₁ / q + 1) * F * (lenv t / q + 1) * lenv t) +
        massv t * (P₂ / t.2.2.1) ^ t.2.2.2 * (P₁ * P₂) + P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) =
        Mf * M₂ * √(P₁ * P₂ * (P₁ / q + 1) * F * (lenv t / q + 1) * lenv t) +
          Mf * M₂ * (massv t * (P₂ / t.2.2.1) ^ t.2.2.2 * (P₁ * P₂)) +
          Mf * M₂ * (P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) := by ring
    rw [e]
    exact add_le_add (add_le_add hA hB) hC
  -- the near-boundary masses
  have hnb : ∀ j, ∑ y₁ ∈ Y₁', ∑ y₂ ∈ Y₂', ‖((lam y₁.2 : ℝ) : ℂ)‖ * ‖(1 : ℂ)‖ * Ms j (φ j y₁.1 + ψ j y₂) =
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', |lam x.2| * Ms j (φ j x.1 + ψ j y₂) := by
    intro j
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y₂ _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]
  simp only [hnb]
  have hFour : 0 ≤ (∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) :=
    Finset.prod_nonneg fun j _ => integral_nonneg fun u => norm_nonneg _
  have hFourM : ∀ j, 0 ≤ ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖ := fun j => integral_nonneg fun u => norm_nonneg _
  have hbd0 : 0 ≤ bd := by
    rw [hbd, SieveTypeIBFam.bdIB]
    positivity
  rw [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
  have h1 := mul_le_mul_of_nonneg_left hbdle hFour
  have h2 : ∑ j, (∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) * bd ≤
      ∑ j, (∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) * (Mf * M₂ * bdP q ρ β₁ β₂ t F) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left hbdle (hFourM j)
  have h3 : ∑ j, 2 * (q.totient : ℝ)⁻¹ * (((t.2.1 - t.1 : ℕ) : ℝ) *
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) =
      ∑ j, 2 * (q.totient : ℝ)⁻¹ * (massv t *
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) := rfl
  linarith

end SieveTypeIBEv
