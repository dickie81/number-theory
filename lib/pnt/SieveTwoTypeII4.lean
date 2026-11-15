/-
# Proposition 3′ in two variables with the fourth moment

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoTypeII.typeII_two_gen` is the Type II estimate in two variables `W₁`, `W₂` and a rest of prime sums, on a
region of a zone where each mean square over a bin of characters has an exponent by orthogonality or by the
Halász–Montgomery inequality. This file is the same estimate with the third bound of `SieveTwoFourth`, the fourth
moment, for which a polynomial of length `q^m` has the exponent `g/2 + max(m, 1/2) + 2e` over a bin of about `q^g`
characters (`SieveTwoZone4.SqExp4`). It is what a variable shorter than `√q` needs: orthogonality loses `q^{1−m}`
whatever the bin, the fourth moment `q^{(g−1)/2 + 1/2 − m}`, and the bins with few characters gain the difference.

* `ZoneOK4 g L d e R`: `SieveTwoTypeII.ZoneOK` with `twoBound4`.
* `typeII_two_gen4`, **Proposition 3′ in two variables with the fourth moment**: `typeII_two_gen` under `ZoneOK4`. The
  divisor bound for the pairs of each variable (`SieveTwoFourth.card_fiber_le_pow` at `ε = 1/(1000(|L| + 2))`, with
  `P_i ≤ q^{1 + L}`) gives `F_i ≤ 4C_ε q^{2/1000}`, which the third bound's slack `2e` absorbs.

The file imports `SieveTwoTypeII.lean` and `SieveTwoZone4.lean`.
-/
import SieveTwoTypeII
import SieveTwoZone4

namespace SieveTypeIIHM

open Finset SieveTypeII SieveTypeIIGen SieveCurveGlue

/-- **The zone's exponents on a region, with the fourth moment**: `ZoneOK` with `twoBound4`. -/
def ZoneOK4 (g : ℝ → ℝ) (L d e : ℝ) (R : ℝ → ℝ → Prop) : Prop :=
  ∀ β m₁ m₂ w : ℝ, 1 / 2 ≤ β → β ≤ 11 / 12 → R m₁ m₂ → 0 ≤ w → w ≤ 4 / 10 ^ 6 →
    twoBound4 L d e (g β) β m₁ m₂ w

set_option maxHeartbeats 1000000 in
open scoped ContDiff in
/-- **Proposition 3′ in two variables with the fourth moment, for a curve on a region of a zone, pointwise in the
heights.** `typeII_two_gen` with the zone's exponents by the three bounds (`ZoneOK4`). Hypotheses: `g ≤ 1` (`hg1`),
`g(1/2) = 1` (`hg0`), the counts `CurveCounts g` (`hcnt`), the zone's exponents on the region `R` (`hzone`), `f0`
smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀ ≥ 0`, `e₁ > 0` (`he₁`) and `0 < η ≤ 10⁻⁵`
(`hη`, `hη1`). There is `q₀` such that for `q ≥ q₀`, `S_i ⊆ (P_i, 2P_i]` with `P_i ≥ 1` and the exponents
`(log_q P₁, log_q P₂)` in `R`, and `K ≤ K₀` prime sums at scales `Q_j ≥ q^{e₁}` and heights `|h_j| ≤ q^η` with
`∏ Q_j ≤ 2^{K₀}q^L/(P₁P₂)`: the sum over `χ ≠ 1` of
`|dp S₁ (aχ) h₁||dp S₂ (bχ) h₂||∏_j Sp χ f0 (Q_j) (h_j)|` is at most
`q^{L − 1/50000}(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}`. -/
theorem typeII_two_gen4 {g : ℝ → ℝ} {L : ℝ} {R : ℝ → ℝ → Prop} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1)
    (hcnt : CurveCounts g) (hzone : ZoneOK4 g L (1 / 1000) (1 / 1000) R) {f0 : ℝ → ℝ}
    (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁)
    (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P₁ P₂ : ℕ) (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ (2 * P₁) → S₂ ⊆ Finset.Ioc P₂ (2 * P₂) →
      0 < P₁ → 0 < P₂ → R (Real.logb q P₁) (Real.logb q P₂) →
      ∀ (a b : ℕ → ℂ) (h₁ h₂ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / ((P₁ : ℝ) * P₂) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S₁ (fun m => a m * χ m) h₁‖ * ‖DirMean.dp S₂ (fun m => b m * χ m) h₂‖ *
            ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (L - 1 / 50000) *
          (Real.sqrt ((∑ m ∈ S₁, ‖a m‖ ^ 2) / P₁) * Real.sqrt ((∑ m ∈ S₂, ‖b m‖ ^ 2) / P₂)) := by
  -- the parameters
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 10 ^ 6 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 1 + L := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ : ∃ Kd : ℕ, Kd = ⌈5 * U / 12 / η⌉₊ := ⟨_, rfl⟩
  have hKdη : 5 * U / 12 ≤ η * Kd := by
    have h : 5 * U / 12 / η ≤ (Kd : ℝ) := hKd ▸ Nat.le_ceil (5 * U / 12 / η)
    rw [div_le_iff₀ hη] at h
    calc 5 * U / 12 ≤ (Kd : ℝ) * η := h
      _ = η * Kd := mul_comm _ _
  obtain ⟨Bc, Cc, hBc, hCc, hL1⟩ := SieveWeight.norm_Sp_le hf0 hsupp Kd
  obtain ⟨KLmax, hKLmax⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range 500001, Linnik.KL (βg i) (βg i + δ) := ⟨_, rfl⟩
  have hKLnn : ∀ i ≤ 500000, 0 ≤ Linnik.KL (βg i) (βg i + δ) := fun i hi =>
    (Linnik.KL_pos (by rw [hδ]; linarith) (by have := (βg_range hi).2; rw [hδ]; linarith)).le
  have hKLle : ∀ i ≤ 500000, Linnik.KL (βg i) (βg i + δ) ≤ KLmax := fun i hi => hKLmax ▸
    Finset.single_le_sum (f := fun i => Linnik.KL (βg i) (βg i + δ))
      (fun j hj => hKLnn j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (Finset.mem_range.2 (by omega))
  have hKLmax0 : 0 ≤ KLmax := (hKLnn 0 (by norm_num)).trans (hKLle 0 (by norm_num))
  -- `positivity` scans the hypotheses; the sum over `range 500001` would be unfolded there
  clear hKLmax
  obtain ⟨q₁, hMB⟩ := MB_le hBc hCc hKLmax0 (δ := δ) (by rw [hδ]; norm_num) (by rw [hδ]; norm_num) he₁ hη
    (by linarith) hKdη
  obtain ⟨Cd, hCd0, hCd⟩ := hcnt
  obtain ⟨CK, hCK0, hCK⟩ := offK_bound
  -- the divisor bound for the pairs of each variable, at `ε = 1/(1000(|L| + 2))`
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (1000 * (|L| + 2)) := ⟨_, rfl⟩
  have hLa : 0 < |L| + 2 := by positivity
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    nlinarith [abs_nonneg L]
  have hεL : (|L| + 2) * ε = 1 / 1000 := by rw [hε]; field_simp
  obtain ⟨CF, hCF⟩ : ∃ C : ℝ, C = LinnikPower.Cdiv ε * 4 := ⟨_, rfl⟩
  have hCF0 : 0 ≤ CF := by rw [hCF]; have := LinnikPower.one_le_Cdiv hε0 hε1; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = 2 ^ K₀ * 2 ^ K₀ *
      (Real.exp 1 * (2 + 12 * max Cd 1 * CK) + Real.sqrt (12 * max Cd 1 * CF)) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    have : 0 ≤ max Cd 1 := le_trans zero_le_one (le_max_right Cd 1)
    rw [hC₁]; positivity
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.1
    (LinnikTwelve.ev_log_pow (500000 * C₁ * 3 ^ 10) (1 / 100000) 10 (by norm_num))
  have hev : ∀ᶠ q : ℕ in Filter.atTop, q₁ ≤ q ∧ (2 : ℝ) ^ K₀ ≤ q ∧ 4 ≤ (q : ℝ) ^ e₁ ∧ Q₂ ≤ (q : ℝ) ∧ 2 ≤ q :=
    (Filter.eventually_ge_atTop q₁).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop ((2 : ℝ) ^ K₀)).and
        ((((tendsto_rpow_atTop he₁).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4).and
          ((tendsto_natCast_atTop_atTop.eventually_ge_atTop Q₂).and (Filter.eventually_ge_atTop 2))))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨q₀, fun q _ hq P₁ P₂ S₁ S₂ hS₁ hS₂ hP₁pos hP₂pos hR a b h₁ h₂ K hK Q h hQh hprod => ?_⟩
  obtain ⟨hq₁, hq2K, hqe, hqQ₂, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  -- `P_i = q^{m_i}` with `(m₁, m₂)` in the region
  have hP₁0 : (0 : ℝ) < P₁ := by exact_mod_cast hP₁pos
  have hP₂0 : (0 : ℝ) < P₂ := by exact_mod_cast hP₂pos
  have hP₁ge1 : (1 : ℝ) ≤ P₁ := by exact_mod_cast hP₁pos
  have hP₂ge1 : (1 : ℝ) ≤ P₂ := by exact_mod_cast hP₂pos
  have hPP0 : (0 : ℝ) < (P₁ : ℝ) * P₂ := mul_pos hP₁0 hP₂0
  have hPPge1 : (1 : ℝ) ≤ (P₁ : ℝ) * P₂ := by nlinarith
  obtain ⟨m₁, hm₁⟩ : ∃ m : ℝ, m = Real.logb q P₁ := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m : ℝ, m = Real.logb q P₂ := ⟨_, rfl⟩
  have hPm₁ : (P₁ : ℝ) = (q : ℝ) ^ m₁ := by rw [hm₁]; exact (Real.rpow_logb hq0 hq1.ne' hP₁0).symm
  have hPm₂ : (P₂ : ℝ) = (q : ℝ) ^ m₂ := by rw [hm₂]; exact (Real.rpow_logb hq0 hq1.ne' hP₂0).symm
  have hRm : R m₁ m₂ := by rw [hm₁, hm₂]; exact hR
  -- each `P_i` is at most `2^{K₀}q^L ≤ q^{1 + L}`, so `m_i ≤ 1 + L`
  have hprod1 : 1 ≤ ∏ j ∈ Finset.range K, Q j := Finset.one_le_prod₀ fun j hj => by
    have := (hQh j (Finset.mem_range.1 hj)).1
    linarith
  have hPPq : (P₁ : ℝ) * P₂ ≤ (q : ℝ) ^ (1 + L) := by
    have h1 : 1 ≤ 2 ^ K₀ * (q : ℝ) ^ L / ((P₁ : ℝ) * P₂) := hprod1.trans hprod
    rw [le_div_iff₀ hPP0, one_mul] at h1
    calc (P₁ : ℝ) * P₂ ≤ 2 ^ K₀ * (q : ℝ) ^ L := h1
      _ ≤ (q : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right hq2K (by positivity)
      _ = (q : ℝ) ^ (1 + L) := by rw [Real.rpow_add hq0, Real.rpow_one]
  have hm₁U : m₁ ≤ 1 + L := by
    have h : (q : ℝ) ^ m₁ ≤ (q : ℝ) ^ (1 + L) := by
      rw [← hPm₁]; exact le_trans (le_mul_of_one_le_right hP₁0.le hP₂ge1) hPPq
    exact (Real.rpow_le_rpow_left_iff hq1).1 h
  have hm₂U : m₂ ≤ 1 + L := by
    have h : (q : ℝ) ^ m₂ ≤ (q : ℝ) ^ (1 + L) := by
      rw [← hPm₂]; exact le_trans (le_mul_of_one_le_left hP₂0.le hP₁ge1) hPPq
    exact (Real.rpow_le_rpow_left_iff hq1).1 h
  have hFq : ∀ (P : ℕ) (m : ℝ), (P : ℝ) = (q : ℝ) ^ m → m ≤ 1 + L →
      LinnikPower.Cdiv ε * (4 * (P : ℝ) ^ 2) ^ ε ≤ CF * (q : ℝ) ^ (2 * (1 / 1000 : ℝ)) := by
    intro P m hPm hmU
    have hC1 := LinnikPower.one_le_Cdiv hε0 hε1
    have h4 : (4 : ℝ) ^ ε ≤ 4 := by
      calc (4 : ℝ) ^ ε ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
        _ = 4 := Real.rpow_one 4
    have hmε : m * ε ≤ 1 / 1000 := by
      calc m * ε ≤ (|L| + 2) * ε := mul_le_mul_of_nonneg_right (by linarith [le_abs_self L]) hε0.le
        _ = 1 / 1000 := hεL
    have hP2 : ((P : ℝ) ^ 2) ^ ε ≤ (q : ℝ) ^ (2 * (1 / 1000 : ℝ)) := by
      rw [hPm, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le]
      apply Real.rpow_le_rpow_of_exponent_le hq1.le
      push_cast
      nlinarith
    calc LinnikPower.Cdiv ε * (4 * (P : ℝ) ^ 2) ^ ε
        = LinnikPower.Cdiv ε * ((4 : ℝ) ^ ε * ((P : ℝ) ^ 2) ^ ε) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ LinnikPower.Cdiv ε * (4 * (q : ℝ) ^ (2 * (1 / 1000 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul h4 hP2 (by positivity) (by norm_num)
      _ = CF * (q : ℝ) ^ (2 * (1 / 1000 : ℝ)) := by rw [hCF]; ring
  obtain ⟨F₁, hF₁def⟩ : ∃ F : ℝ, F = LinnikPower.Cdiv ε * (4 * (P₁ : ℝ) ^ 2) ^ ε := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂def⟩ : ∃ F : ℝ, F = LinnikPower.Cdiv ε * (4 * (P₂ : ℝ) ^ 2) ^ ε := ⟨_, rfl⟩
  have hF₁ : ∀ n, (((S₁ ×ˢ S₁).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F₁ := fun n => by
    rw [hF₁def]; exact card_fiber_le_pow hS₁ hε0 hε1 n
  have hF₂ : ∀ n, (((S₂ ×ˢ S₂).filter fun p => p.1 * p.2 = n).card : ℝ) ≤ F₂ := fun n => by
    rw [hF₂def]; exact card_fiber_le_pow hS₂ hε0 hε1 n
  have hF₁0 : 0 ≤ F₁ := le_trans (Nat.cast_nonneg _) (hF₁ 0)
  have hF₂0 : 0 ≤ F₂ := le_trans (Nat.cast_nonneg _) (hF₂ 0)
  have hF₁q : F₁ ≤ CF * (q : ℝ) ^ (2 * (1 / 1000 : ℝ)) := by rw [hF₁def]; exact hFq P₁ m₁ hPm₁ hm₁U
  have hF₂q : F₂ ≤ CF * (q : ℝ) ^ (2 * (1 / 1000 : ℝ)) := by rw [hF₂def]; exact hFq P₂ m₂ hPm₂ hm₂U
  -- the heights
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = (q : ℝ) ^ η := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := hH ▸ Real.one_le_rpow hq1.le hη.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * H + 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have hT3 : T ≤ 3 * (q : ℝ) ^ η := by rw [hT, ← hH]; linarith
  have hQh' : ∀ j < K, 4 ≤ Q j ∧ |h j| + H + 1 ≤ T := fun j hj =>
    ⟨hqe.trans (hQh j hj).1, by have := (hQh j hj).2; rw [hT, hH]; rw [hH] at hH1; linarith⟩
  -- each scale is at most `q^U`
  have hQ1 : ∀ j < K, 1 ≤ Q j := fun j hj => by linarith [(hQh' j hj).1]
  have hQU : ∀ j < K, Q j ≤ (q : ℝ) ^ U := by
    intro j hj
    have hjK : j ∈ Finset.range K := Finset.mem_range.2 hj
    have hrest : 1 ≤ ∏ k ∈ (Finset.range K).erase j, Q k := Finset.one_le_prod₀ fun k hk =>
      hQ1 k (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
    have hQj := Finset.mul_prod_erase (Finset.range K) Q hjK
    have hQj0 : 0 ≤ Q j := by linarith [hQ1 j hj]
    have hqL : 0 ≤ (q : ℝ) ^ L := Real.rpow_nonneg hq0.le _
    calc Q j ≤ Q j * ∏ k ∈ (Finset.range K).erase j, Q k := le_mul_of_one_le_right hQj0 hrest
      _ = ∏ k ∈ Finset.range K, Q k := hQj
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ L / ((P₁ : ℝ) * P₂) := hprod
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ L := div_le_self (mul_nonneg (by norm_num) hqL) hPPge1
      _ ≤ (q : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right hq2K hqL
      _ = (q : ℝ) ^ U := by rw [hU, Real.rpow_add hq0, Real.rpow_one]
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hδ1 : δ ≤ 1 / 24 := by rw [hδ]; norm_num
  -- the kernels' bounds at `Λ = 2P_i` (`offK_bound`)
  obtain ⟨Bk₁, hBk₁⟩ : ∃ B : ℝ, B = CK * (2 * (P₁ : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 3 / 1000 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Bk₂, hBk₂⟩ : ∃ B : ℝ, B = CK * (2 * (P₂ : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 3 / 1000 : ℝ) := ⟨_, rfl⟩
  have hBk₁0 : 0 ≤ Bk₁ := by rw [hBk₁]; positivity
  have hBk₂0 : 0 ≤ Bk₂ := by rw [hBk₂]; positivity
  have hKk₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖∑' n, LinnikPower.kTerm ψ (2 * (P₁ : ℝ)) 0 n‖ ≤ Bk₁ :=
    fun ψ hψ => by rw [hBk₁]; exact hCK q ψ hψ (2 * (P₁ : ℝ)) (by linarith)
  have hKk₂ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖∑' n, LinnikPower.kTerm ψ (2 * (P₂ : ℝ)) 0 n‖ ≤ Bk₂ :=
    fun ψ hψ => by rw [hBk₂]; exact hCK q ψ hψ (2 * (P₂ : ℝ)) (by linarith)
  have e3 : (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) = 5 / 12 + 3 / 1000 := by norm_num
  have hBk₁' : Bk₁ ≤ CK * (2 * (P₁ : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) := by rw [hBk₁, e3]
  have hBk₂' : Bk₂ ≤ CK * (2 * (P₂ : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) := by rw [hBk₂, e3]
  -- Lemma 1 in each bin, with the bound's larger of it and `0`
  have hBχ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        max (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (bin βg 500000 T χ + 1)) δ H (Q j) (h j)) 0 := by
    intro χ hχ
    have hb := bin_lt (β := βg) (by norm_num : 0 < 500000) T χ
    have hθ := βg_range (i := bin βg 500000 T χ + 1) (by omega)
    refine le_trans ?_ (le_max_left _ _)
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j hj => ?_
    have hj' := hQh' j (Finset.mem_range.1 hj)
    exact hL1 q χ hχ (βg (bin βg 500000 T χ + 1)) δ H (Q j) (h j) hθ.1 hθ.2 hδ0 hδ1 (by linarith) hj'.1
      (bin_rect βg_top hχ (by norm_num) hj'.2)
  -- the pointwise bound by bins
  have hpt := sum_typeII_two_bins4 (q := q) (β := βg) (N := 500000) (by norm_num) T hP₁pos hP₂pos hS₁ hS₂ a b
    h₁ h₂ (fun χ => ∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j))
    (fun i => max (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) 0)
    (fun i => le_max_right _ _) hBχ hBk₁0 hBk₂0 hKk₁ hKk₂ hF₁ hF₂
  refine hpt.trans ?_
  obtain ⟨V₁, hV₁⟩ : ∃ V : ℝ, V = ∑ m ∈ S₁, ‖a m‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨V₂, hV₂⟩ : ∃ V : ℝ, V = ∑ m ∈ S₂, ‖b m‖ ^ 2 := ⟨_, rfl⟩
  have hV₁0 : 0 ≤ V₁ := by rw [hV₁]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV₂0 : 0 ≤ V₂ := by rw [hV₂]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← hV₁, ← hV₂]
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (V₁ / P₁) * Real.sqrt (V₂ / P₂) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← hR]
  have hbin : ∀ i ∈ Finset.range 500000,
      max (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) 0 *
        (Real.sqrt (sqTerm4 ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
            χ ≠ 1 ∧ bin βg 500000 T χ = i).card) P₁ q V₁ Bk₁ F₁) *
          Real.sqrt (sqTerm4 ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
            χ ≠ 1 ∧ bin βg 500000 T χ = i).card) P₂ q V₂ Bk₂ F₂)) ≤
        C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) * R := by
    intro i hi
    have hi' : i < 500000 := Finset.mem_range.1 hi
    have hβi := βg_range hi'.le
    have hβi1 := βg_range (Nat.succ_le_of_lt hi')
    have hθ0 : 0 ≤ βg (i + 1) + 2 * δ := by linarith [hβi1.1]
    have hθ1 : βg (i + 1) + 2 * δ ≤ 1 := by rw [hδ]; linarith [hβi1.2]
    have hMp := prod_MB_le_gen (L := L) (M := fun j => MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) (Q := Q)
      (θ' := βg (i + 1) + 2 * δ) hK hq0 hPP0 hθ0 hθ1
      (fun j hj => MB_nonneg hBc hCc hβi1.2 hδ0 hδ1 (by linarith) (by linarith [(hQh' j hj).1]))
      (fun j hj => by
        rw [hH]
        exact hMB q hq₁ _ _ _ hβi1.1 hβi1.2 (hKLle (i + 1) (by omega)) (hQh j hj).1 (hQU j hj) (hQh j hj).2)
      hQ1 hprod
    have he : βg (i + 1) + 2 * δ = βg i + (1 / 1200000 + 2 * δ) := by rw [βg_succ]; ring
    rw [he] at hMp
    have hcnt := card_bin_gen hg0 (q := q) (β := βg) (N := 500000) (by norm_num) βg_zero
      (fun k hk => ⟨(βg_range hk.le).1, by linarith [(βg_range hk.le).2]⟩) hT2
      (fun σ h1 h2 => hCd q σ T h1 h2 hT2) hi'
    have hw0 : (0 : ℝ) ≤ 1 / 1200000 + 2 * δ := by linarith
    have hw1 : 1 / 1200000 + 2 * δ ≤ 4 / 10 ^ 6 := by rw [hδ]; norm_num
    have hb := bin_bound_two4 (L := L) (V₁ := V₁) (V₂ := V₂) (by norm_num : (1 / 1000 : ℝ) ≤ 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 1 / 1000) hq1 hPm₁ hPm₂
      hT1 hT3 hη.le (hg1 (βg i)) (hzone (βg i) m₁ m₂ (1 / 1200000 + 2 * δ) hβi.1 hβi.2 hRm hw0 hw1)
      (by positivity : (0 : ℝ) ≤ 2 ^ K₀ * 2 ^ K₀) (le_trans zero_le_one (le_max_right Cd 1)) hCK0.le hCF0
      (max_le hMp (by positivity)) hcnt hBk₁' hBk₁0 hBk₂' hBk₂0 hV₁0 hV₂0 hF₁0 hF₁q hF₂0 hF₂q
    rw [hC₁, hR]
    exact hb
  refine (Finset.sum_le_sum hbin).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- absorbing the constants
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1.le
  have hlogT : 1 + Real.log ((q : ℝ) * T) ≤ 3 * (1 + Real.log q) := by
    have hT0 : 0 < T := by linarith
    have h1 : Real.log ((q : ℝ) * T) = Real.log q + Real.log T := Real.log_mul hq0.ne' hT0.ne'
    have h2 : Real.log T ≤ Real.log 3 + η * Real.log q := by
      rw [← Real.log_rpow hq0, ← Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hq0 η).ne']
      exact Real.log_le_log hT0 hT3
    have h3 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h4 : η * Real.log q ≤ Real.log q := by
      have : η ≤ 1 := by linarith
      exact mul_le_of_le_one_left hlq this
    linarith
  have hqT1 : 1 ≤ (q : ℝ) * T := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (q : ℝ) * T := mul_le_mul hq1.le hT1 zero_le_one hq0.le
  have hlq0 : 0 ≤ 1 + Real.log ((q : ℝ) * T) := by linarith [Real.log_nonneg hqT1]
  have habs : 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := by
    have h := hQ₂ (q : ℝ) hqQ₂
    calc 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 ≤ 500000 * C₁ * (3 * (1 + Real.log q)) ^ 10 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlq0 hlogT 10) (by linarith)
      _ = 500000 * C₁ * 3 ^ 10 * (1 + Real.log q) ^ 10 := by ring
      _ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := h
  have hE : 0 ≤ (q : ℝ) ^ (L - 1 / 25000 + η) := Real.rpow_nonneg hq0.le _
  have hfin : (q : ℝ) ^ (1 / 100000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η) ≤ (q : ℝ) ^ (L - 1 / 50000) := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  calc (500000 : ℝ) * (C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) * R)
      = 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) * R := by ring
    _ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η) * R := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs hE) hR0
    _ ≤ (q : ℝ) ^ (L - 1 / 50000) * R := mul_le_mul_of_nonneg_right hfin hR0

end SieveTypeIIHM

#print axioms SieveTypeIIHM.typeII_two_gen4
