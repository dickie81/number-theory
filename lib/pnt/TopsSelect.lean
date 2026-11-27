import TileProb
import GainSums
import DesignTops

/-!
# The random tops: coset counts, the density window and G1 at once

A step of the proof of the sharp frontier (`SharpInputs`, the design's Stage 2, M-G4): the tops of the design are
drawn at random, each `a ∈ A` independently with probability `δ₁` on `A₀` and `3δ₁/4` off it (`topWt`; the model of
`ProdWeights`), and one selection (`ProdWeights.exists_le_two_mul`) gives tops `TT` with coset counts within
`x⁻¹|TT|`, the density window `δ₁|A|/2 ≤ |TT| ≤ 2δ₁|A|`, and the clause G1 (`Setting.DesignAdm.exists_tops_G1`).

**The growth of the tops** (`TopsBig ε x`, eventually true at fixed `ε`: `topsBig_eventually`): `3G′ ≤ x^{ε/4}`,
`L₂ ≤ G′` and `16C_b ≤ x^{ε/4}`, with `C_b = 2(L₂ + 1)^{K+1} + 6` (`scCb`) and the tile parameters `tilePar` at
`k = designK x ε`. `G′ ≤ C₁·log x·x^{ε/8}` (as in `gainBig_eventually`), `L₂ ≤ 2(10(130 + 40ε)/ε + 1)` for `x ≥ e`
(`k ≤ 3x^{9/2+10ε}`), and `G′ ≥ u ≥ x^{ε/8}`.

**The bad mean per top** (`Setting.DesignAdm.pexp_bad_le`). At `p ∈ PR` (inert, so the step is `h_p`, of order
`n′ ≥ x^{ε/4} ≥ 3G′`) the orbit of `t` is `e(i) = t₀σ^i` (`t₀ = basePoint σ t`, injective on `[0, ord σ)`), `t` sits
at `i₀ = orbitPos σ t`, and `topPositions T σ t₀` is `orbPos n′ e T`. So `ProdWeights.pexp_forced_bad_le` applies,
and with `n′ ≤ |A| ≤ 2x^{2+8ε+ε/100}`, `δ₁^K ≤ x^{−(4+8ε)}` (`K ≥ 8(4 + 8ε)/ε`), `(1 − μ)^{M₀} ≤ e^{−μM₀} ≤
x^{−(5+8ε)}` and `C(G′, N)δ₁^N ≤ (eG′δ₁/N)^N ≤ 2^{−N} ≤ x^{−(5+8ε)}` for `N ∈ {N₁, N₁ + 1}` (`N₁ ≥ 6eG′δ₁` and
`N₁ ≥ (5 + 8ε)log₂ x`): `P(t ∈ T, t bad at p) ≤ δ₁·C_b·x^{−2+ε/100}`.

**The selection** (`Setting.DesignAdm.exists_tops_G1`). With `Y_ζ(T) = Σ_{κ(a) = ζ}(1_{a ∈ T} − q_a)`,
`F₁ = Σ_γ Y_{κ(γ)}²` has mean `Σ_γ Σ_{κ(a) = κ(γ)} q_a(1 − q_a) ≤ |A|·|A₀|·δ₁` (`ProdWeights.pexp_var`), and the bad
sum `F₂ = Σ_{p ∈ PR}(log p/p)·#{t ∈ T bad at p}` has mean at most `Σ_p (log p/p)·|A|·δ₁C_b x^{−2+ε/100}`. At a `TT`
with `F₁ ≤ 2c₁`, `F₂ ≤ 2c₂`: `Y` is constant on cosets, so `|A₀|·Y_ζ² ≤ F₁` and `|Y_ζ| ≤ √(2|A|δ₁)`; the excess
`Z = |TT| − Σ_a q_a` is `Σ_γ Y_{κ(γ)}/|A₀|`, at most `o√(2|A|δ₁)`; `Σ_a q_a = δ₁|A₀|(3o + 1)/4` and the count of the
coset of `γ` is `λ_γΣ_a q_a + Y_{κ(γ)}`, so `|count − λ_γ|TT|| ≤ |Y| + λ_γ|Z| ≤ (7/3)√(2|A|δ₁) ≤ x⁻¹|TT|` and
`δ₁|A|/2 ≤ |TT| ≤ 2δ₁|A|`, as `32o² ≤ |A|δ₁` and `44x² ≤ |A|δ₁`. Finally `Σ_{PR} log p/p ≤ x^{ε/3}(1 + x^{ε/3})`
(`sum_log_div_le_of_mem` up to `X′`), so `F₂ ≤ 12C_b x^{−2+2ε/3+ε/100}|TT| ≤ x^{−2+ε}|TT|` by `16C_b ≤ x^{ε/4}`: G1.
-/

open Finset Filter

namespace ZetaBalance

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε : ℝ}

/-! ## The weights, the constant and the growth -/

/-- **The selection weights**: `δ₁` on `A₀`, `3δ₁/4` off it. -/
noncomputable def topWt (κ : S.A →* ℂˣ) (x ε : ℝ) (a : S.A) : ℝ :=
  if a ∈ A₀ κ then scδ₁ x ε else 3 * scδ₁ x ε / 4

/-- **The constant of the bad-top mean**, `C_b = 2(L₂ + 1)^{K+1} + 6`. -/
noncomputable def scCb (x ε : ℝ) (k : ℕ) : ℝ :=
  2 * (((tilePar x ε k).L₂ : ℝ) + 1) ^ ((tilePar x ε k).K + 1) + 6

/-- **The growth conditions of the tops** (eventually true at fixed `ε`, `topsBig_eventually`). -/
structure TopsBig (ε x : ℝ) : Prop where
  /-- `3G′ ≤ x^{ε/4}`: an orbit at a prime of `PR` holds three windows of `G′` (G1's runs; L5/L6's `J ≥ 4`). -/
  G'_le : 3 * ((tilePar x ε (designK x ε)).G' : ℝ) ≤ x ^ (ε / 4)
  /-- `L₂ ≤ G′`. -/
  L₂_le : (tilePar x ε (designK x ε)).L₂ ≤ (tilePar x ε (designK x ε)).G'
  /-- `16·C_b ≤ x^{ε/4}`. -/
  Cb_le : 16 * scCb x ε (designK x ε) ≤ x ^ (ε / 4)

/-- **`δ₁` at an admissible size**: `0 < δ₁ = x^{−ε/8} ≤ 1/4096`, `δ₁⁻¹ = x^{ε/8}`. -/
theorem DesignBig.scδ₁_mem (h : DesignBig ε x) :
    0 < scδ₁ x ε ∧ scδ₁ x ε ≤ 1 / 100 ∧ (scδ₁ x ε)⁻¹ = x ^ (ε / 8) := by
  have hx0 := h.pos
  have h1 : (scδ₁ x ε)⁻¹ = x ^ (ε / 8) := by rw [scδ₁, Real.rpow_neg hx0.le, inv_inv]
  have h2 : 4096 ≤ x ^ (ε / 8) := h.le_rpow (by linarith [h.ε_pos])
  have h0 : 0 < scδ₁ x ε := Real.rpow_pos_of_pos hx0 _
  refine ⟨h0, ?_, h1⟩
  rw [← inv_inv (scδ₁ x ε), h1, one_div]
  exact inv_anti₀ (by norm_num) (by linarith)

/-- **The weights are in `[3δ₁/4, δ₁]`.** -/
theorem topWt_mem (κ : S.A →* ℂˣ) {x ε : ℝ} (h0 : 0 < scδ₁ x ε) (a : S.A) :
    3 * scδ₁ x ε / 4 ≤ topWt κ x ε a ∧ topWt κ x ε a ≤ scδ₁ x ε := by
  unfold topWt
  split_ifs <;> constructor <;> linarith

/-- **The cell length**: `1/δ₁ ≤ u ≤ 1/δ₁ + 1`. -/
theorem tilePar_u_mem (x ε : ℝ) (k : ℕ) (h0 : 0 < scδ₁ x ε) :
    1 / scδ₁ x ε ≤ (tilePar x ε k).u ∧ ((tilePar x ε k).u : ℝ) ≤ 1 / scδ₁ x ε + 1 := by
  rw [one_div]
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (inv_pos.2 h0).le).le⟩

/-- **The block length** `(M₀ + 1)(6r + 1)u ≤ G′`. -/
theorem tilePar_blockLen_le (x ε : ℝ) (k : ℕ) :
    ((tilePar x ε k).M₀ + 1) * (tilePar x ε k).blockLen ≤ (tilePar x ε k).G' :=
  Nat.mul_le_mul_right _ (by simp [tilePar])

/-- **The orbit at a prime of `PR`**: the step is `h_p` (`p` is inert), of order at least `x^{ε/4}`. -/
theorem Setting.orderOf_orbitStep_ge {p : ℕ} (hp : p ∈ S.PR κ x ε) :
    x ^ (ε / 4) ≤ orderOf (S.orbitStep (S.twA κ) p) := by
  obtain ⟨-, -, hcls, hord⟩ := mem_filter.1 hp
  have : S.orbitStep (S.twA κ) p = S.hPtw (S.twA κ) p := by simp [Setting.orbitStep, hcls]
  rw [this]
  exact hord

/-! ## The bad mean per top -/

/-- **The numbers of the bad mean**: for `n′ ≤ |A|`,
`n′·(C(L₂ + 1, K + 1)δ₁^K + (1 − μ)^{M₀} + C(G′, N₁)δ₁^{N₁} + C(G′, N₁ + 1)δ₁^{N₁+1}) ≤ C_b·x^{−2+ε/100}`:
`δ₁^K ≤ x^{−(4+8ε)}`, the other three terms are at most `x^{−(5+8ε)}` each, and `n′ ≤ 2x^{2+8ε+ε/100}`. -/
theorem Setting.DesignAdm.bad_numbers (hS : S.DesignAdm κ x ε) {n' : ℕ} (hn : n' ≤ Fintype.card S.A) (k : ℕ) :
    (n' : ℝ) * ((((tilePar x ε k).L₂ + 1).choose ((tilePar x ε k).K + 1) : ℝ) * scδ₁ x ε ^ (tilePar x ε k).K +
      (1 - (10 : ℝ)⁻¹ ^ (6 * (tilePar x ε k).r + 1)) ^ (tilePar x ε k).M₀ +
      (((tilePar x ε k).G'.choose (tilePar x ε k).N₁ : ℝ) * scδ₁ x ε ^ (tilePar x ε k).N₁ +
        ((tilePar x ε k).G'.choose ((tilePar x ε k).N₁ + 1) : ℝ) * scδ₁ x ε ^ ((tilePar x ε k).N₁ + 1))) ≤
      scCb x ε k * x ^ (-2 + ε / 100) := by
  have hx0 := hS.big.pos
  have hx1 := hS.big.one_lt
  have hε := hS.big.ε_pos
  obtain ⟨hδ0, -, -⟩ := hS.big.scδ₁_mem
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1.le
  -- the facts about the parameters, before abbreviating them
  have hn' : (n' : ℝ) ≤ 2 * x ^ (2 + 8 * ε + ε / 100) :=
    (by exact_mod_cast hn : (n' : ℝ) ≤ Fintype.card S.A).trans hS.card_le
  have hK : 8 * (4 + 8 * ε) / ε ≤ (tilePar x ε k).K := by
    have h : 8 * ((2 + 8 * ε) + 2) / ε ≤ (tilePar x ε k).K := Nat.le_ceil _
    rwa [show (2 + 8 * ε) + 2 = 4 + 8 * ε by ring] at h
  have hM : ((2 + 8 * ε) + 3) * 10 ^ (6 * (tilePar x ε k).r + 1) * Real.log x ≤ (tilePar x ε k).M₀ :=
    Nat.le_ceil _
  have hN : (tilePar x ε k).N₁ = ⌈max (6 * Real.exp 1 * (tilePar x ε k).G' * scδ₁ x ε)
      (((2 + 8 * ε) + 3) * Real.logb 2 x)⌉₊ + 1 := tilePar_N₁ x ε k
  set L₂ := (tilePar x ε k).L₂
  set K := (tilePar x ε k).K
  set r := (tilePar x ε k).r
  set M₀ := (tilePar x ε k).M₀
  set G' := (tilePar x ε k).G'
  set N₁ := (tilePar x ε k).N₁
  set δ := scδ₁ x ε
  have hmax := Nat.le_ceil (max (6 * Real.exp 1 * G' * δ) (((2 + 8 * ε) + 3) * Real.logb 2 x))
  have hN₁ : 6 * Real.exp 1 * G' * δ ≤ N₁ ∧ (5 + 8 * ε) * Real.logb 2 x ≤ N₁ := by
    have e : (N₁ : ℝ) = ⌈max (6 * Real.exp 1 * G' * δ) (((2 + 8 * ε) + 3) * Real.logb 2 x)⌉₊ + 1 := by
      rw [hN]
      push_cast
      ring
    have h1 := le_max_left (6 * Real.exp 1 * G' * δ) (((2 + 8 * ε) + 3) * Real.logb 2 x)
    have h2 := le_max_right (6 * Real.exp 1 * G' * δ) (((2 + 8 * ε) + 3) * Real.logb 2 x)
    constructor <;> linarith
  -- `δ₁^K ≤ x^{−(4+8ε)}`
  have hδK : δ ^ K ≤ x ^ (-(4 + 8 * ε)) := by
    rw [show δ = x ^ (-(ε / 8)) from rfl, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    have : 8 * (4 + 8 * ε) ≤ K * ε := (div_le_iff₀ hε).1 hK
    linarith
  -- `C(L₂ + 1, K + 1) ≤ (L₂ + 1)^{K+1}`
  have hC : ((L₂ + 1).choose (K + 1) : ℝ) ≤ ((L₂ : ℝ) + 1) ^ (K + 1) := by
    have := Nat.choose_le_pow (L₂ + 1) (K + 1)
    exact_mod_cast this
  -- `(1 − μ)^{M₀} ≤ x^{−(5+8ε)}`
  have hμ1 : (10 : ℝ)⁻¹ ^ (6 * r + 1) * 10 ^ (6 * r + 1) = 1 := by rw [← mul_pow]; norm_num
  have h0μ : 0 ≤ 1 - (10 : ℝ)⁻¹ ^ (6 * r + 1) := sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
  have hTM : (1 - (10 : ℝ)⁻¹ ^ (6 * r + 1)) ^ M₀ ≤ x ^ (-(5 + 8 * ε)) := by
    have h1 : 1 - (10 : ℝ)⁻¹ ^ (6 * r + 1) ≤ Real.exp (-((10 : ℝ)⁻¹ ^ (6 * r + 1))) := by
      linarith [Real.add_one_le_exp (-((10 : ℝ)⁻¹ ^ (6 * r + 1)))]
    have h2 : (5 + 8 * ε) * Real.log x ≤ (10 : ℝ)⁻¹ ^ (6 * r + 1) * M₀ := by
      calc (5 + 8 * ε) * Real.log x =
          (10 : ℝ)⁻¹ ^ (6 * r + 1) * (((2 + 8 * ε) + 3) * 10 ^ (6 * r + 1) * Real.log x) := by
            rw [show (10 : ℝ)⁻¹ ^ (6 * r + 1) * (((2 + 8 * ε) + 3) * 10 ^ (6 * r + 1) * Real.log x) =
              ((10 : ℝ)⁻¹ ^ (6 * r + 1) * 10 ^ (6 * r + 1)) * (((2 + 8 * ε) + 3) * Real.log x) by ring, hμ1]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)
    calc (1 - (10 : ℝ)⁻¹ ^ (6 * r + 1)) ^ M₀ ≤ Real.exp (-((10 : ℝ)⁻¹ ^ (6 * r + 1))) ^ M₀ :=
          pow_le_pow_left₀ h0μ h1 _
      _ = Real.exp (-((10 : ℝ)⁻¹ ^ (6 * r + 1) * M₀)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-((5 + 8 * ε) * Real.log x)) := Real.exp_le_exp.2 (by linarith)
      _ = x ^ (-(5 + 8 * ε)) := by rw [Real.rpow_def_of_pos hx0]; congr 1; ring
  -- the binomial terms
  have hbin : ∀ N : ℕ, 1 ≤ N → 6 * Real.exp 1 * G' * δ ≤ N → (5 + 8 * ε) * Real.logb 2 x ≤ N →
      (G'.choose N : ℝ) * δ ^ N ≤ x ^ (-(5 + 8 * ε)) := by
    intro N hN1 hN2 hN3
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hb0 : 0 ≤ Real.exp 1 * G' * δ / N :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 1).le (Nat.cast_nonneg _)) hδ0.le) hN0.le
    have h2 : x ^ (5 + 8 * ε) ≤ (2 : ℝ) ^ N := by
      calc x ^ (5 + 8 * ε) = ((2 : ℝ) ^ Real.logb 2 x) ^ (5 + 8 * ε) := by
            rw [Real.rpow_logb (by norm_num) (by norm_num) hx0]
        _ = (2 : ℝ) ^ ((5 + 8 * ε) * Real.logb 2 x) := by
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
        _ ≤ (2 : ℝ) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hN3
        _ = 2 ^ N := Real.rpow_natCast 2 N
    calc (G'.choose N : ℝ) * δ ^ N ≤ (Real.exp 1 * G' * δ / N) ^ N := choose_mul_pow_le G' N hN1 hδ0.le
      _ ≤ (1 / 2) ^ N := by
          refine pow_le_pow_left₀ hb0 ?_ N
          rw [div_le_iff₀ hN0]
          linarith
      _ ≤ x ^ (-(5 + 8 * ε)) := by
          rw [Real.rpow_neg hx0.le, one_div, inv_pow]
          exact inv_anti₀ (Real.rpow_pos_of_pos hx0 _) h2
  have hB1 := hbin N₁ (by omega) hN₁.1 hN₁.2
  have hB2 := hbin (N₁ + 1) (by omega) (by push_cast; linarith [hN₁.1]) (by push_cast; linarith [hN₁.2])
  -- assembly
  have hX0 : 0 ≤ ((L₂ + 1).choose (K + 1) : ℝ) * δ ^ K + (1 - (10 : ℝ)⁻¹ ^ (6 * r + 1)) ^ M₀ +
      ((G'.choose N₁ : ℝ) * δ ^ N₁ + (G'.choose (N₁ + 1) : ℝ) * δ ^ (N₁ + 1)) := by
    have := pow_nonneg h0μ M₀
    have := pow_nonneg hδ0.le K
    have := pow_nonneg hδ0.le N₁
    have := pow_nonneg hδ0.le (N₁ + 1)
    positivity
  have hX : ((L₂ + 1).choose (K + 1) : ℝ) * δ ^ K + (1 - (10 : ℝ)⁻¹ ^ (6 * r + 1)) ^ M₀ +
      ((G'.choose N₁ : ℝ) * δ ^ N₁ + (G'.choose (N₁ + 1) : ℝ) * δ ^ (N₁ + 1)) ≤
      ((L₂ : ℝ) + 1) ^ (K + 1) * x ^ (-(4 + 8 * ε)) + 3 * x ^ (-(5 + 8 * ε)) := by
    have := mul_le_mul hC hδK (pow_nonneg hδ0.le _) (by positivity)
    linarith
  have e1 : x ^ (2 + 8 * ε + ε / 100) * x ^ (-(4 + 8 * ε)) = x ^ (-2 + ε / 100) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have e2 : x ^ (2 + 8 * ε + ε / 100) * x ^ (-(5 + 8 * ε)) ≤ x ^ (-2 + ε / 100) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hL0 : 0 ≤ ((L₂ : ℝ) + 1) ^ (K + 1) := by positivity
  calc _ ≤ (2 * x ^ (2 + 8 * ε + ε / 100)) *
        (((L₂ : ℝ) + 1) ^ (K + 1) * x ^ (-(4 + 8 * ε)) + 3 * x ^ (-(5 + 8 * ε))) :=
        mul_le_mul hn' hX hX0 (by positivity)
    _ = 2 * ((L₂ : ℝ) + 1) ^ (K + 1) * (x ^ (2 + 8 * ε + ε / 100) * x ^ (-(4 + 8 * ε))) +
        6 * (x ^ (2 + 8 * ε + ε / 100) * x ^ (-(5 + 8 * ε))) := by ring
    _ ≤ 2 * ((L₂ : ℝ) + 1) ^ (K + 1) * x ^ (-2 + ε / 100) + 6 * x ^ (-2 + ε / 100) := by
        rw [e1]
        linarith
    _ = scCb x ε k * x ^ (-2 + ε / 100) := by unfold scCb; ring

open scoped Classical in
/-- **The bad mean per top** at a prime of `PR`: `P(t ∈ T, t bad at p) ≤ δ₁·C_b·x^{−2+ε/100}`
(`ProdWeights.pexp_forced_bad_le` on the orbit `i ↦ t₀σ^i` of `t`, and `bad_numbers`). -/
theorem Setting.DesignAdm.pexp_bad_le (hS : S.DesignAdm κ x ε) (hT : TopsBig ε x) {p : ℕ}
    (hp : p ∈ S.PR κ x ε) (t : S.A) :
    ProdWeights.pexp (topWt κ x ε) (fun T => if t ∈ T ∧ ¬ (tilePar x ε (designK x ε)).IsGood
      (orderOf (S.orbitStep (S.twA κ) p)) (topPositions T (S.orbitStep (S.twA κ) p)
        (basePoint (S.orbitStep (S.twA κ) p) t)) then 1 else 0) ≤
      scδ₁ x ε * (scCb x ε (designK x ε) * x ^ (-2 + ε / 100)) := by
  obtain ⟨hδ0, hδ1, -⟩ := hS.big.scδ₁_mem
  have hord := S.orderOf_orbitStep_ge hp
  have hG3 := hT.G'_le
  have hG : (tilePar x ε (designK x ε)).G' ≤ orderOf (S.orbitStep (S.twA κ) p) := by
    have : ((tilePar x ε (designK x ε)).G' : ℝ) ≤ orderOf (S.orbitStep (S.twA κ) p) := by
      have := Nat.cast_nonneg (α := ℝ) (tilePar x ε (designK x ε)).G'
      linarith
    exact_mod_cast this
  have hL := hT.L₂_le.trans hG
  have hB := (tilePar_blockLen_le x ε (designK x ε)).trans hG
  have he : Set.InjOn (fun i => basePoint (S.orbitStep (S.twA κ) p) t * S.orbitStep (S.twA κ) p ^ i)
      (Set.Iio (orderOf (S.orbitStep (S.twA κ) p))) := fun i hi j hj h =>
    pow_injOn_Iio_orderOf hi hj (mul_left_cancel h)
  obtain ⟨hu1, hu2⟩ := tilePar_u_mem x ε (designK x ε) hδ0
  have key := ProdWeights.pexp_forced_bad_le (topWt_mem κ hδ0) hδ0 hδ1 (tilePar x ε (designK x ε)) hu1 hu2 he
    (orbitPos_lt _ t) hL hG hB
  simp only [basePoint_mul_orbitPos] at key
  refine key.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hS.bad_numbers orderOf_le_card_univ _) hδ0.le

/-! ## The selection -/

open scoped Classical in
/-- **The bad sum** of a set of tops, `Σ_{p ∈ PR}(log p/p)·#{t ∈ T bad at p}`: the left side of
`Setting.FewBadTopsAt`. -/
noncomputable def Setting.badSum (S : Setting) (κ : S.A →* ℂˣ) (x ε : ℝ) (k : ℕ) (T : Finset S.A) : ℝ :=
  ∑ p ∈ S.PR κ x ε, (Real.log p / p) * ((T.filter fun t => ¬ (tilePar x ε k).IsGood
    (orderOf (S.orbitStep (S.twA κ) p)) (topPositions T (S.orbitStep (S.twA κ) p)
      (basePoint (S.orbitStep (S.twA κ) p) t))).card : ℝ)

/-- **G1 bounds the bad sum.** -/
theorem Setting.fewBadTopsAt_iff (k : ℕ) (T : Finset S.A) :
    S.FewBadTopsAt κ x ε k T ↔ S.badSum κ x ε k T ≤ T.card * x ^ (-2 + ε) := Iff.rfl

/-- `log p/p ≥ 0`. -/
theorem log_div_natCast_nonneg (p : ℕ) : 0 ≤ Real.log p / p :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- The bad sum is nonnegative. -/
theorem Setting.badSum_nonneg (k : ℕ) (T : Finset S.A) : 0 ≤ S.badSum κ x ε k T :=
  sum_nonneg fun p _ => mul_nonneg (log_div_natCast_nonneg p) (Nat.cast_nonneg _)

/-- `#(T.filter P) = Σ_t [t ∈ T ∧ P t]`. -/
theorem card_filter_eq_sum {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) (P : α → Prop)
    [DecidablePred P] : ((T.filter P).card : ℝ) = ∑ t, if t ∈ T ∧ P t then 1 else 0 := by
  rw [sum_boole]
  congr 2
  ext t
  simp

open scoped Classical in
/-- **The mean of the bad sum**: `≤ Σ_{PR} (log p/p)·|A|·δ₁C_b x^{−2+ε/100}` (`pexp_bad_le` at each `p` and `t`). -/
theorem Setting.DesignAdm.pexp_badSum_le (hS : S.DesignAdm κ x ε) (hT : TopsBig ε x) :
    ProdWeights.pexp (topWt κ x ε) (S.badSum κ x ε (designK x ε)) ≤ (∑ p ∈ S.PR κ x ε, Real.log p / p) *
      (Fintype.card S.A * (scδ₁ x ε * (scCb x ε (designK x ε) * x ^ (-2 + ε / 100)))) := by
  have e : S.badSum κ x ε (designK x ε) = fun T => ∑ p ∈ S.PR κ x ε, (Real.log p / p) *
      ∑ t, (if t ∈ T ∧ ¬ (tilePar x ε (designK x ε)).IsGood (orderOf (S.orbitStep (S.twA κ) p))
        (topPositions T (S.orbitStep (S.twA κ) p) (basePoint (S.orbitStep (S.twA κ) p) t)) then 1 else 0) := by
    funext T
    unfold Setting.badSum
    refine sum_congr rfl fun p _ => ?_
    rw [card_filter_eq_sum]
  rw [e, ProdWeights.pexp_sum, sum_mul]
  refine sum_le_sum fun p hp => ?_
  rw [ProdWeights.pexp_const_mul, ProdWeights.pexp_sum]
  refine mul_le_mul_of_nonneg_left ?_ (log_div_natCast_nonneg p)
  calc _ ≤ ∑ _t : S.A, scδ₁ x ε * (scCb x ε (designK x ε) * x ^ (-2 + ε / 100)) :=
        sum_le_sum fun t _ => hS.pexp_bad_le hT hp t
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- **The excess of the tops over a value of `κ`**: `Y_ζ(T) = Σ_{κ(a) = ζ} (1_{a ∈ T} − q_a)`. -/
noncomputable def topExcess (κ : S.A →* ℂˣ) (x ε : ℝ) (ζ : ℂˣ) (T : Finset S.A) : ℝ :=
  ∑ a ∈ univ.filter (κ · = ζ), ((if a ∈ T then 1 else 0) - topWt κ x ε a)

/-- `a ≤ b` from `a² ≤ b²` for `a, b ≥ 0`. -/
theorem le_of_sq_le_sq_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt h

/-- **The sizes of the selection**: with `N = |A|δ₁`, `32o² ≤ N` and `44x² ≤ N`. -/
theorem Setting.DesignAdm.selection_sizes (hS : S.DesignAdm κ x ε) :
    32 * (orderOf κ : ℝ) ^ 2 ≤ Fintype.card S.A * scδ₁ x ε ∧ 44 * x ^ 2 ≤ Fintype.card S.A * scδ₁ x ε := by
  have hx0 := hS.big.pos
  have hx1 := hS.big.one_lt
  have hε := hS.big.ε_pos
  have hε' := hS.big.ε_lt
  have hδ0 := hS.big.scδ₁_mem.1
  have hN : x ^ (2 + 8 * ε - ε / 8) ≤ Fintype.card S.A * scδ₁ x ε := by
    have e : x ^ (2 + 8 * ε - ε / 8) = x ^ (2 + 8 * ε) * scδ₁ x ε := by
      rw [scδ₁, ← Real.rpow_add hx0]
      ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right hS.card_ge hδ0.le
  have hx2 : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_natCast x 2
  constructor
  · have ho : (orderOf κ : ℝ) ^ 2 ≤ x ^ (ε / 50) := by
      calc (orderOf κ : ℝ) ^ 2 ≤ (x ^ (ε / 100)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hS.orderOf_le 2
        _ = x ^ (ε / 50) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; ring
    have e : x ^ (2 + 8 * ε - ε / 8) = x ^ (ε / 50) * x ^ (2 + 8 * ε - ε / 8 - ε / 50) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have h1 : 32 ≤ x ^ (2 + 8 * ε - ε / 8 - ε / 50) := by
      have : x ^ (1 : ℝ) ≤ x ^ (2 + 8 * ε - ε / 8 - ε / 50) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      rw [Real.rpow_one] at this
      linarith [hS.big.x_ge]
    have h2 : 0 ≤ x ^ (ε / 50) := Real.rpow_nonneg hx0.le _
    nlinarith
  · have e : x ^ (2 + 8 * ε - ε / 8) = x ^ (2 : ℝ) * x ^ (8 * ε - ε / 8) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have h1 : 4096 ≤ x ^ (8 * ε - ε / 8) := hS.big.le_rpow (by linarith)
    rw [e, hx2] at hN
    nlinarith [sq_nonneg x]

open scoped Classical in
/-- **The tops** (Stage 2): coset counts within `x⁻¹|TT|`, the density window, and G1, from one selection
(`ProdWeights.exists_le_two_mul`) of the variance `F₁ = Σ_γ Y_{κ(γ)}²` and the bad sum. -/
theorem Setting.DesignAdm.exists_tops_G1 (hS : S.DesignAdm κ x ε) (hT : TopsBig ε x) : ∃ TT : Finset S.A,
    (∀ γ : S.A, |((TT.filter fun t => γ⁻¹ * t ∈ A₀ κ).card : ℝ) -
      (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) * TT.card| ≤ x⁻¹ * TT.card) ∧
    scδ₁ x ε * Fintype.card S.A / 2 ≤ TT.card ∧ (TT.card : ℝ) ≤ 2 * scδ₁ x ε * Fintype.card S.A ∧
    S.FewBadTopsAt κ x ε (designK x ε) TT := by
  have hx0 := hS.big.pos
  have hx1 := hS.big.one_lt
  have hε := hS.big.ε_pos
  obtain ⟨hδ0, hδ1, -⟩ := hS.big.scδ₁_mem
  have hq := topWt_mem κ hδ0
  have hqp : ProdWeights.IsProb (topWt κ x ε) := fun a => ⟨by linarith [(hq a).1], by linarith [(hq a).2]⟩
  have hfib : ∀ γ : S.A, ((univ.filter (κ · = κ γ)).card : ℝ) = (A₀ κ).card := fun γ => by
    exact_mod_cast card_fibre κ ⟨γ, rfl⟩
  have ha0 : (0 : ℝ) < (A₀ κ).card := by exact_mod_cast card_pos.2 ⟨1, mem_A₀.2 (map_one κ)⟩
  have ho1 : (1 : ℝ) ≤ orderOf κ := by exact_mod_cast orderOf_pos κ
  have hn : (0 : ℝ) < Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hno : (Fintype.card S.A : ℝ) = orderOf κ * (A₀ κ).card := by exact_mod_cast card_A_eq κ
  have hCb : 0 < scCb x ε (designK x ε) := by unfold scCb; positivity
  have hW0 : 0 ≤ ∑ p ∈ S.PR κ x ε, Real.log p / p := sum_nonneg fun p _ => log_div_natCast_nonneg p
  have hxr : 0 < x ^ (-2 + ε / 100) := Real.rpow_pos_of_pos hx0 _
  -- the selection
  have hqq : ∀ a, topWt κ x ε a * (1 - topWt κ x ε a) ≤ scδ₁ x ε := fun a => by
    have e : topWt κ x ε a * (1 - topWt κ x ε a) = topWt κ x ε a - topWt κ x ε a ^ 2 := by ring
    linarith [(hq a).2, sq_nonneg (topWt κ x ε a)]
  have hE₁ : ProdWeights.pexp (topWt κ x ε) (fun T => ∑ γ, topExcess κ x ε (κ γ) T ^ 2) ≤
      Fintype.card S.A * (A₀ κ).card * scδ₁ x ε := by
    rw [ProdWeights.pexp_sum]
    calc ∑ γ, ProdWeights.pexp (topWt κ x ε) (fun T => topExcess κ x ε (κ γ) T ^ 2) ≤
        ∑ _γ : S.A, ((A₀ κ).card : ℝ) * scδ₁ x ε := by
          refine sum_le_sum fun γ _ => ?_
          rw [show (fun T => topExcess κ x ε (κ γ) T ^ 2) = fun T => (∑ a ∈ univ.filter (κ · = κ γ),
            ((if a ∈ T then 1 else 0) - topWt κ x ε a)) ^ 2 from rfl, ProdWeights.pexp_var]
          calc ∑ a ∈ univ.filter (κ · = κ γ), topWt κ x ε a * (1 - topWt κ x ε a) ≤
              ∑ _a ∈ univ.filter (κ · = κ γ), scδ₁ x ε :=
                sum_le_sum fun a _ => hqq a
            _ = (A₀ κ).card * scδ₁ x ε := by rw [sum_const, nsmul_eq_mul, hfib]
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  have hE₂ : ProdWeights.pexp (topWt κ x ε) (S.badSum κ x ε (designK x ε)) ≤
      ((∑ p ∈ S.PR κ x ε, Real.log p / p) + 1) *
        (Fintype.card S.A * (scδ₁ x ε * (scCb x ε (designK x ε) * x ^ (-2 + ε / 100)))) :=
    (hS.pexp_badSum_le hT).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  obtain ⟨TT, h1, h2⟩ := ProdWeights.exists_le_two_mul hqp
    (F₁ := fun T => ∑ γ, topExcess κ x ε (κ γ) T ^ 2) (fun T => sum_nonneg fun γ _ => sq_nonneg _)
    (S.badSum_nonneg _) (by positivity) (by positivity) hE₁ hE₂
  -- the excesses are small
  have hN : 0 < (Fintype.card S.A : ℝ) * scδ₁ x ε := by positivity
  have hs0 : 0 ≤ √(2 * (Fintype.card S.A * scδ₁ x ε)) := Real.sqrt_nonneg _
  have hs2 : √(2 * (Fintype.card S.A * scδ₁ x ε)) ^ 2 = 2 * (Fintype.card S.A * scδ₁ x ε) :=
    Real.sq_sqrt (by positivity)
  have hY : ∀ γ : S.A, |topExcess κ x ε (κ γ) TT| ≤ √(2 * (Fintype.card S.A * scδ₁ x ε)) := by
    intro γ₀
    apply Real.abs_le_sqrt
    have hsub : ∑ γ ∈ univ.filter (κ · = κ γ₀), topExcess κ x ε (κ γ) TT ^ 2 ≤
        ∑ γ, topExcess κ x ε (κ γ) TT ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun γ _ _ => sq_nonneg _
    have heq : ∑ γ ∈ univ.filter (κ · = κ γ₀), topExcess κ x ε (κ γ) TT ^ 2 =
        (A₀ κ).card * topExcess κ x ε (κ γ₀) TT ^ 2 := by
      rw [sum_congr rfl fun γ hγ => by rw [(mem_filter.1 hγ).2], sum_const, nsmul_eq_mul, hfib]
    have h3 : (A₀ κ).card * topExcess κ x ε (κ γ₀) TT ^ 2 ≤ (A₀ κ).card * (2 * (Fintype.card S.A * scδ₁ x ε)) := by
      rw [← heq]
      calc _ ≤ _ := hsub
        _ ≤ _ := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_left h3 ha0
  -- the excess of `|TT|`
  have hZsum : ∑ γ, topExcess κ x ε (κ γ) TT =
      (A₀ κ).card * ∑ a, ((if a ∈ TT then (1 : ℝ) else 0) - topWt κ x ε a) := by
    simp only [topExcess, sum_filter]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    congr 1
    rw [← hfib a]
    congr 2
    ext γ
    simp [eq_comm]
  have hZ : |∑ a, ((if a ∈ TT then (1 : ℝ) else 0) - topWt κ x ε a)| ≤
      orderOf κ * √(2 * (Fintype.card S.A * scδ₁ x ε)) := by
    have h3 : (A₀ κ).card * |∑ a, ((if a ∈ TT then (1 : ℝ) else 0) - topWt κ x ε a)| ≤
        (A₀ κ).card * (orderOf κ * √(2 * (Fintype.card S.A * scδ₁ x ε))) := by
      rw [← abs_of_pos ha0, ← abs_mul, ← hZsum, abs_of_pos ha0]
      calc |∑ γ, topExcess κ x ε (κ γ) TT| ≤ ∑ γ, |topExcess κ x ε (κ γ) TT| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _γ : S.A, √(2 * (Fintype.card S.A * scδ₁ x ε)) := sum_le_sum fun γ _ => hY γ
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, hno]; ring
    exact le_of_mul_le_mul_left h3 ha0
  -- the mean `Σ_a q_a = δ₁|A₀|(3o + 1)/4`
  have hEval : ∑ a, topWt κ x ε a = scδ₁ x ε * (A₀ κ).card * (3 * orderOf κ + 1) / 4 := by
    simp only [topWt]
    rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc1 : (univ.filter (· ∈ A₀ κ)).card = (A₀ κ).card := by rw [filter_mem_eq_inter, univ_inter]
    have hc := card_filter_add_card_filter_not (s := (univ : Finset S.A)) (fun a => a ∈ A₀ κ)
    rw [hc1, card_univ] at hc
    have hc2 : ((univ.filter (fun a => ¬ a ∈ A₀ κ)).card : ℝ) = Fintype.card S.A - (A₀ κ).card := by
      rw [← hc]
      push_cast
      ring
    rw [hc1, hc2, hno]
    ring
  have hcard : (TT.card : ℝ) = ∑ a, topWt κ x ε a + ∑ a, ((if a ∈ TT then (1 : ℝ) else 0) - topWt κ x ε a) := by
    rw [sum_sub_distrib, sum_boole, filter_mem_eq_inter, univ_inter]
    ring
  -- the sizes
  obtain ⟨h32, h44⟩ := hS.selection_sizes
  have hos : orderOf κ * √(2 * (Fintype.card S.A * scδ₁ x ε)) ≤ Fintype.card S.A * scδ₁ x ε / 4 := by
    refine le_of_sq_le_sq_nonneg (by positivity) (by positivity) ?_
    rw [mul_pow, hs2]
    have := mul_le_mul_of_nonneg_right h32 (by positivity : (0 : ℝ) ≤ Fintype.card S.A * scδ₁ x ε / 16)
    linarith
  have hE1 : 3 * (Fintype.card S.A * scδ₁ x ε) / 4 ≤ ∑ a, topWt κ x ε a := by
    rw [hEval, hno]
    have : 0 ≤ scδ₁ x ε * (A₀ κ).card := by positivity
    linarith
  have hE2 : ∑ a, topWt κ x ε a ≤ Fintype.card S.A * scδ₁ x ε := by
    rw [hEval, hno]
    have := mul_le_mul_of_nonneg_right ho1 (by positivity : (0 : ℝ) ≤ (A₀ κ).card * scδ₁ x ε)
    linarith
  have hZ' := abs_le.1 (hZ.trans hos)
  have hlow : scδ₁ x ε * Fintype.card S.A / 2 ≤ TT.card := by rw [hcard]; linarith
  have hhigh : (TT.card : ℝ) ≤ 2 * scδ₁ x ε * Fintype.card S.A := by rw [hcard]; linarith
  refine ⟨TT, fun γ => ?_, hlow, hhigh, ?_⟩
  · -- the coset counts
    have hfil : TT.filter (fun t => γ⁻¹ * t ∈ A₀ κ) = (univ.filter (κ · = κ γ)).filter (· ∈ TT) := by
      ext t
      simp only [mem_filter, mem_univ, true_and, mem_A₀, map_mul, map_inv, inv_mul_eq_one]
      constructor
      · rintro ⟨h, h'⟩
        exact ⟨h'.symm, h⟩
      · rintro ⟨h, h'⟩
        exact ⟨h', h.symm⟩
    have hμ : ∑ a ∈ univ.filter (κ · = κ γ), topWt κ x ε a =
        (if γ ∈ A₀ κ then scδ₁ x ε else 3 * scδ₁ x ε / 4) * (A₀ κ).card := by
      have e : ∀ a ∈ univ.filter (κ · = κ γ),
          topWt κ x ε a = if γ ∈ A₀ κ then scδ₁ x ε else 3 * scδ₁ x ε / 4 := by
        intro a ha
        have h' : κ a = κ γ := (mem_filter.1 ha).2
        simp only [topWt, mem_A₀, h']
      rw [sum_congr rfl e, sum_const, nsmul_eq_mul, hfib, mul_comm]
    have hcount : ((TT.filter fun t => γ⁻¹ * t ∈ A₀ κ).card : ℝ) =
        (if γ ∈ A₀ κ then scδ₁ x ε else 3 * scδ₁ x ε / 4) * (A₀ κ).card + topExcess κ x ε (κ γ) TT := by
      rw [topExcess, sum_sub_distrib, hμ, hfil, ← sum_boole]
      ring
    have hlam : (if γ ∈ A₀ κ then (4 : ℝ) else 3) / (3 * orderOf κ + 1) * ∑ a, topWt κ x ε a =
        (if γ ∈ A₀ κ then scδ₁ x ε else 3 * scδ₁ x ε / 4) * (A₀ κ).card := by
      rw [hEval]
      have h3 : (3 * (orderOf κ : ℝ) + 1) ≠ 0 := by positivity
      split_ifs <;> field_simp
    have hlam0 : 0 ≤ (if γ ∈ A₀ κ then (4 : ℝ) else 3) / (3 * orderOf κ + 1) := by
      split_ifs <;> positivity
    have hlamo : (if γ ∈ A₀ κ then (4 : ℝ) else 3) / (3 * orderOf κ + 1) * orderOf κ ≤ 4 / 3 := by
      have h4 : (if γ ∈ A₀ κ then (4 : ℝ) else 3) ≤ 4 := by split_ifs <;> norm_num
      have h5 : (if γ ∈ A₀ κ then (4 : ℝ) else 3) * orderOf κ ≤ 4 * orderOf κ :=
        mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    have hkey : ((TT.filter fun t => γ⁻¹ * t ∈ A₀ κ).card : ℝ) -
        (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) * TT.card =
        topExcess κ x ε (κ γ) TT - (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) *
          ∑ a, ((if a ∈ TT then (1 : ℝ) else 0) - topWt κ x ε a) := by
      rw [hcount, hcard, mul_add, hlam]
      ring
    rw [hkey]
    have hb1 : |topExcess κ x ε (κ γ) TT - (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) *
        ∑ a, ((if a ∈ TT then (1 : ℝ) else 0) - topWt κ x ε a)| ≤
        7 / 3 * √(2 * (Fintype.card S.A * scδ₁ x ε)) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hlam0]
      have := mul_le_mul_of_nonneg_left hZ hlam0
      have h5 := mul_le_mul_of_nonneg_right hlamo hs0
      linarith [hY γ]
    have hb2 : 14 * x * √(2 * (Fintype.card S.A * scδ₁ x ε)) ≤ 3 * (Fintype.card S.A * scδ₁ x ε) := by
      refine le_of_sq_le_sq_nonneg (by positivity) (by positivity) ?_
      rw [mul_pow, hs2]
      have h6 := mul_le_mul_of_nonneg_right h44 (by positivity : (0 : ℝ) ≤ 9 * (Fintype.card S.A * scδ₁ x ε))
      have h7 : 0 ≤ x ^ 2 * (Fintype.card S.A * scδ₁ x ε) := by positivity
      linarith
    have hb3 : 7 / 3 * √(2 * (Fintype.card S.A * scδ₁ x ε)) ≤ x⁻¹ * (Fintype.card S.A * scδ₁ x ε / 2) := by
      rw [inv_mul_eq_div, le_div_iff₀ hx0]
      linarith
    have hb4 : x⁻¹ * (Fintype.card S.A * scδ₁ x ε / 2) ≤ x⁻¹ * TT.card :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_pos.2 hx0).le
    linarith
  · -- G1
    rw [Setting.fewBadTopsAt_iff]
    have hW : ∑ p ∈ S.PR κ x ε, Real.log p / p ≤ x ^ (ε / 3) * (1 + x ^ (ε / 3)) := by
      have hX' : 1 ≤ scX' x ε := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
      have h := sum_log_div_le_of_mem (P := S.PR κ x ε) hX' fun p hp => by
        obtain ⟨hpr, hpp, -⟩ := mem_filter.1 hp
        exact ⟨hpp.one_lt.le, (Nat.lt_ceil.1 (mem_range.1 hpr)).le⟩
      rwa [scX', Real.log_exp] at h
    have hx3 : 1 ≤ x ^ (ε / 3) := Real.one_le_rpow hx1.le (by positivity)
    have hx23 : x ^ (ε / 3) * x ^ (ε / 3) = x ^ (2 * ε / 3) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hW1 : ∑ p ∈ S.PR κ x ε, Real.log p / p + 1 ≤ 3 * x ^ (2 * ε / 3) := by
      have : x ^ (ε / 3) ≤ x ^ (2 * ε / 3) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      rw [mul_add, mul_one, hx23] at hW
      linarith
    have hP : x ^ (ε / 4) * x ^ (2 * ε / 3) * x ^ (-2 + ε / 100) ≤ x ^ (-2 + ε) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have hNT : (Fintype.card S.A : ℝ) * scδ₁ x ε ≤ 2 * TT.card := by linarith
    have hCb16 := hT.Cb_le
    have hx23' : 0 < x ^ (2 * ε / 3) := Real.rpow_pos_of_pos hx0 _
    calc S.badSum κ x ε (designK x ε) TT ≤ 2 * (((∑ p ∈ S.PR κ x ε, Real.log p / p) + 1) *
          (Fintype.card S.A * (scδ₁ x ε * (scCb x ε (designK x ε) * x ^ (-2 + ε / 100))))) := h2
      _ = 2 * ((∑ p ∈ S.PR κ x ε, Real.log p / p) + 1) * (Fintype.card S.A * scδ₁ x ε) *
          (scCb x ε (designK x ε) * x ^ (-2 + ε / 100)) := by ring
      _ ≤ 2 * (3 * x ^ (2 * ε / 3)) * (2 * TT.card) * (scCb x ε (designK x ε) * x ^ (-2 + ε / 100)) := by
          gcongr
      _ = 12 * scCb x ε (designK x ε) * (x ^ (2 * ε / 3) * x ^ (-2 + ε / 100)) * TT.card := by ring
      _ ≤ x ^ (ε / 4) * (x ^ (2 * ε / 3) * x ^ (-2 + ε / 100)) * TT.card := by
          gcongr
          linarith
      _ ≤ x ^ (-2 + ε) * TT.card := by
          gcongr
          rw [← mul_assoc]
          exact hP
      _ = TT.card * x ^ (-2 + ε) := mul_comm _ _

/-! ## The growth of the tops -/

/-- **The window `L₂` is bounded** at fixed `ε`: `L₂ ≤ 2(10(130 + 40ε)/ε + 1)` for `x ≥ e`, as
`k = designK x ε ≤ 3x^{9/2+10ε}` and `log((kx^{26})⁴) ≤ (130 + 40ε)log x`. -/
theorem tilePar_L₂_le {x ε : ℝ} (hε : 0 < ε) (hx : Real.exp 1 ≤ x) :
    ((tilePar x ε (designK x ε)).L₂ : ℝ) ≤ 2 * (10 * (130 + 40 * ε) / ε + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp zero_le_one) hx
  have hlog : 1 ≤ Real.log x := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hk : (1 : ℝ) ≤ designK x ε ∧ (designK x ε : ℝ) ≤ 3 * x ^ (9 / 2 + 10 * ε) := by
    have hp : 0 < x ^ (9 / 2 + 10 * ε) / 2 := by positivity
    have hc1 := Nat.ceil_lt_add_one hp.le
    have hc0 : (1 : ℝ) ≤ ⌈x ^ (9 / 2 + 10 * ε) / 2⌉₊ := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hp).ne'
    have hx' : 1 ≤ x ^ (9 / 2 + 10 * ε) := Real.one_le_rpow hx1 (by positivity)
    unfold designK
    push_cast
    constructor <;> linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlogk : Real.log (designK x ε) ≤ (2 + (9 / 2 + 10 * ε)) * Real.log x := by
    calc Real.log (designK x ε) ≤ Real.log (3 * x ^ (9 / 2 + 10 * ε)) := Real.log_le_log (by linarith) hk.2
      _ = Real.log 3 + (9 / 2 + 10 * ε) * Real.log x := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
      _ ≤ _ := by linarith
  have hlogy : Real.log (((designK x ε : ℝ) * x ^ 26) ^ 4) ≤ (130 + 40 * ε) * Real.log x := by
    rw [Real.log_pow, Real.log_mul (by linarith [hk.1]) (by positivity), Real.log_pow]
    push_cast
    linarith
  have hb1 : 1 < x ^ (ε / 10) := Real.one_lt_rpow (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by positivity)
  have hy1 : 1 ≤ ((designK x ε : ℝ) * x ^ 26) ^ 4 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hk.1 (one_le_pow₀ hx1))
  have hlogb : Real.logb (x ^ (ε / 10)) (((designK x ε : ℝ) * x ^ 26) ^ 4) ≤ 10 * (130 + 40 * ε) / ε := by
    rw [Real.logb, Real.log_rpow hx0, div_le_iff₀ (by positivity)]
    calc _ ≤ (130 + 40 * ε) * Real.log x := hlogy
      _ = 10 * (130 + 40 * ε) / ε * (ε / 10 * Real.log x) := by field_simp
  have hlogb0 : 0 ≤ Real.logb (x ^ (ε / 10)) (((designK x ε : ℝ) * x ^ 26) ^ 4) := Real.logb_nonneg hb1 hy1
  show ((2 * ⌈Real.logb (x ^ (ε / 10)) (((designK x ε : ℝ) * x ^ 26) ^ 4)⌉₊ : ℕ) : ℝ) ≤ _
  push_cast
  have := Nat.ceil_lt_add_one hlogb0
  linarith

/-- **The growth of the tops holds eventually**: for `ε > 0`, `TopsBig ε x` at every large `x`. With
`C₁ = 2B₀(A₀ + 6)` as in `gainBig_eventually`, `G′ ≤ C₁·log x·x^{ε/8}`, so `3G′ ≤ x^{ε/4}` once
`log x ≤ x^{ε/8}/(3C₁)`; `L₂ ≤ L₀ = 2(10(130 + 40ε)/ε + 1) ≤ x^{ε/8} ≤ u ≤ G′` once `x^{ε/8} ≥ L₀`; and
`16C_b ≤ 16(2(L₀ + 1)^{K+1} + 6) ≤ x^{ε/4}` eventually, as `K` does not read `x`. -/
theorem topsBig_eventually {ε : ℝ} (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → TopsBig ε x := by
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, r₀ = ⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨A₀', hA₀'⟩ : ∃ A : ℝ, A = ((2 + 8 * ε) + 3) * 10 ^ (6 * r₀ + 1) := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B : ℝ, B = 6 * r₀ + 1 := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = 2 * B₀ * (A₀' + 6) := ⟨_, rfl⟩
  obtain ⟨L₀, hL₀⟩ : ∃ L : ℝ, L = 2 * (10 * (130 + 40 * ε) / ε + 1) := ⟨_, rfl⟩
  have hA₀ : 0 < A₀' := by rw [hA₀']; positivity
  have hB0 : 0 < B₀ := by rw [hB₀]; positivity
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hL₀0 : 0 ≤ L₀ := by rw [hL₀]; positivity
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ((eventually_ge_atTop (Real.exp 1)).and
    ((eventually_log_le_rpow (c := 1 / (3 * C₁)) (s := ε / 8) (by positivity) (by positivity)).and
    (((tendsto_rpow_atTop (by positivity : 0 < ε / 8)).eventually_ge_atTop L₀).and
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 4)).eventually_ge_atTop
      (16 * (2 * (L₀ + 1) ^ (⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊ + 1) + 6))))))
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx₀ x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp zero_le_one) h1
  have hlog : 1 ≤ Real.log x := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) h1
  have hxe : 1 ≤ x ^ (ε / 8) := Real.one_le_rpow hx1 (by positivity)
  have hr : (tilePar x ε (designK x ε)).r = r₀ := by rw [hr₀]; rfl
  have hu := tilePar_u_le (ε := ε) (designK x ε) hx0
  have hM := tilePar_M₀_le (designK x ε) hx1 hε.le
  rw [hr] at hM
  have hM' : ((tilePar x ε (designK x ε)).M₀ : ℝ) ≤ A₀' * Real.log x + 1 := by rw [hA₀']; exact hM
  have hG : ((tilePar x ε (designK x ε)).G' : ℝ) =
      ((tilePar x ε (designK x ε)).M₀ + 5) * (B₀ * (tilePar x ε (designK x ε)).u) := by
    rw [tilePar_G', hr, hB₀]
    push_cast
    rfl
  have hM0 : (0 : ℝ) ≤ (tilePar x ε (designK x ε)).M₀ := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ (tilePar x ε (designK x ε)).u := Nat.cast_nonneg _
  -- `G′ ≤ C₁·log x·x^{ε/8}`
  have hG1 : ((tilePar x ε (designK x ε)).G' : ℝ) ≤ C₁ * Real.log x * x ^ (ε / 8) := by
    rw [hG]
    calc ((tilePar x ε (designK x ε)).M₀ + 5) * (B₀ * (tilePar x ε (designK x ε)).u : ℝ) ≤
        (A₀' * Real.log x + 6) * (B₀ * (2 * x ^ (ε / 8))) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hB0.le) (by positivity)
            (by positivity)
      _ ≤ ((A₀' + 6) * Real.log x) * (B₀ * (2 * x ^ (ε / 8))) := by gcongr; nlinarith
      _ = C₁ * Real.log x * x ^ (ε / 8) := by rw [hC₁]; ring
  -- `x^{ε/8} ≤ u ≤ G′`
  have hGu : x ^ (ε / 8) ≤ (tilePar x ε (designK x ε)).G' := by
    have h5 : x ^ (ε / 8) ≤ (tilePar x ε (designK x ε)).u := by
      have e : (scδ₁ x ε)⁻¹ = x ^ (ε / 8) := by rw [scδ₁, Real.rpow_neg hx0.le, inv_inv]
      rw [← e]
      exact Nat.le_ceil _
    have h6 : (tilePar x ε (designK x ε)).u ≤ (tilePar x ε (designK x ε)).G' := by
      show (tilePar x ε (designK x ε)).u ≤ ((tilePar x ε (designK x ε)).M₀ + 5) *
        ((6 * (tilePar x ε (designK x ε)).r + 1) * (tilePar x ε (designK x ε)).u)
      calc (tilePar x ε (designK x ε)).u ≤ (6 * (tilePar x ε (designK x ε)).r + 1) *
            (tilePar x ε (designK x ε)).u := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
    exact h5.trans (by exact_mod_cast h6)
  have hL := tilePar_L₂_le hε h1
  rw [← hL₀] at hL
  refine ⟨?_, ?_, ?_⟩
  · have h7 : 3 * C₁ * Real.log x ≤ x ^ (ε / 8) := by
      rw [show 1 / (3 * C₁) * x ^ (ε / 8) = x ^ (ε / 8) / (3 * C₁) by ring, le_div_iff₀ (by positivity)] at h2
      linarith
    have hx44 : x ^ (ε / 8) * x ^ (ε / 8) = x ^ (ε / 4) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    calc 3 * ((tilePar x ε (designK x ε)).G' : ℝ) ≤ 3 * (C₁ * Real.log x * x ^ (ε / 8)) := by linarith
      _ = (3 * C₁ * Real.log x) * x ^ (ε / 8) := by ring
      _ ≤ x ^ (ε / 8) * x ^ (ε / 8) := mul_le_mul_of_nonneg_right h7 (by positivity)
      _ = x ^ (ε / 4) := hx44
  · have : ((tilePar x ε (designK x ε)).L₂ : ℝ) ≤ (tilePar x ε (designK x ε)).G' := by linarith
    exact_mod_cast this
  · have hK : (tilePar x ε (designK x ε)).K = ⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊ := rfl
    have hC : scCb x ε (designK x ε) ≤ 2 * (L₀ + 1) ^ (⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊ + 1) + 6 := by
      unfold scCb
      rw [hK]
      have : ((tilePar x ε (designK x ε)).L₂ : ℝ) + 1 ≤ L₀ + 1 := by linarith
      have := pow_le_pow_left₀ (by positivity) this (⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊ + 1)
      linarith
    linarith
