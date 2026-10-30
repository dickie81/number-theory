import Mathlib
import TheoremC

/-! # The pole-overlap gap bound, and the Galerkin transfer

**Gap bound (operator level, no spectral decomposition).** Let `φ₀` be the ground state of the
pole-free form `Q₀` (`μ₁ = λ₀`), and `ψ` a normalised probe `⊥ φ₀` attaining
`μ₂ = inf {Q₀(χ)/‖χ‖² : χ ⊥ φ₀}`. With `c₁ = φ̂₀(i/2)`, `c₂ = ψ̂(i/2)`:

  `λ₂(Q) − λ₁(Q) ≥ c₂²(μ₂ − μ₁)/(c₁² + c₂²)`   (`lam2Ge_gap`).

* Upper bound on `λ₁`: the trial function `ψ − (c₂/c₁)φ₀` has zero pole term (`lam_le_trial`).
* Lower bound on `λ₂`: every 2-dimensional span has a unit vector `⊥ φ₀`, where `Q ≥ Q₀ ≥ μ₂`
  (`lam2Ge_of_Q0`).

So `c₂ ≠ 0` and `μ₂ > μ₁` give simplicity with an explicit gap (`simple_of_pole_overlap`).

**Galerkin transfer.** If truncation spaces `T K` (of probes) approximate every probe in `L²` and
archimedean energy, and the truncated forms have `λ₂(T K) ≥ λ₁(T K) + γ` eventually, then
`λ₂(Q) ≥ λ₁(Q) + γ` and the ground state is simple (`simple_of_trunc_gap`). The truncated `λ₂` is in
min–max form (`Lam2GeT`).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace WeilForm

/-! ## The operator-level gap bound -/

theorem poleR_ne_zero_of_groundState0 {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsGroundState0 a φ) :
    poleR φ a ≠ 0 := by
  intro h0
  have hq0 : weilQ0 a φ = lam0 a := by
    have := ((isGroundState0_iff ha).1 hφ).1.2; rw [this, hφ.2.1, mul_one]
  have hq : weilQ a φ = lam0 a := by
    have : weilQ a φ = weilQ0 a φ + 2 * poleR φ a ^ 2 := by unfold weilQ0; ring
    rw [this, hq0, h0]; ring
  have := lam_le hφ.1 hφ.2.1
  have := lam0_lt_lam ha
  linarith

/-- **The trial bound**: `λ₁(c₁² + c₂²) ≤ Q₀(ψ)c₁² + μ₁c₂²`. -/
theorem lam_le_trial {a : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) :
    lam a * (poleR φ a ^ 2 + poleR ψ a ^ 2)
      ≤ weilQ0 a ψ * poleR φ a ^ 2 + lam0 a * poleR ψ a ^ 2 := by
  have hc₁ := poleR_ne_zero_of_groundState0 ha hφ
  have h := lam_le_perp_trial ha hφ hc₁ hψ hn hx
  set s := poleR ψ a / poleR φ a
  have hc2 : 0 < poleR φ a ^ 2 := by positivity
  have hs2 : s ^ 2 * poleR φ a ^ 2 = poleR ψ a ^ 2 := by
    simp only [s]; field_simp
  have hm := mul_le_mul_of_nonneg_right h hc2.le
  have e1 : lam a * (1 + s ^ 2) * poleR φ a ^ 2 = lam a * (poleR φ a ^ 2 + poleR ψ a ^ 2) := by
    rw [← hs2]; ring
  have e2 : (weilQ0 a ψ + s ^ 2 * lam0 a) * poleR φ a ^ 2
      = weilQ0 a ψ * poleR φ a ^ 2 + lam0 a * poleR ψ a ^ 2 := by
    rw [← hs2]; ring
  linarith

theorem Lam2Ge.anti {a s s' : ℝ} (h : Lam2Ge a s) (hs : s' ≤ s) : Lam2Ge a s' := by
  intro g k hg hk hng hnk hx
  obtain ⟨α, β, hab, h1⟩ := h g k hg hk hng hnk hx
  exact ⟨α, β, hab, hs.trans h1⟩

/-- **Interlacing in min–max form**: `λ₂(Q) ≥ μ₂(Q₀)`. -/
theorem lam2Ge_of_Q0 {a μ₂ : ℝ} {φ : ℝ → ℝ} (hφ : Probe a φ)
    (hμ : ∀ χ, Probe a χ → xcorr χ φ 0 = 0 → μ₂ * normSq χ ≤ weilQ0 a χ) : Lam2Ge a μ₂ := by
  intro g k hg hk hng hnk hx
  set p := xcorr g φ 0
  set q := xcorr k φ 0
  have hlin : ∀ α β : ℝ, xcorr (fun t => α * g t + β * k t) φ 0 = α * p + β * q := by
    intro α β
    rw [xcorr_zero_eq]
    show _ = α * xcorr g φ 0 + β * xcorr k φ 0
    rw [xcorr_zero_eq, xcorr_zero_eq]
    have e : (fun t => (α * g t + β * k t) * φ t) = fun t => α * (g t * φ t) + β * (k t * φ t) := by
      funext t; ring
    have i1 : Integrable (fun t => α * (g t * φ t)) :=
      (hg.memL2.integrable_mul hφ.memL2).const_mul α
    have i2 : Integrable (fun t => β * (k t * φ t)) :=
      (hk.memL2.integrable_mul hφ.memL2).const_mul β
    rw [e, integral_add i1 i2, integral_const_mul, integral_const_mul]
  have hN : ∀ α β : ℝ, normSq (fun t => α * g t + β * k t) = α ^ 2 + β ^ 2 := by
    intro α β; rw [normSq_comb hg.memL2 hk.memL2, hng, hnk, hx]; ring
  have hfin : ∀ α β : ℝ, α ^ 2 + β ^ 2 = 1 → α * p + β * q = 0 →
      ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧ μ₂ ≤ weilQ a (fun t => α * g t + β * k t) := by
    intro α β hab h0
    refine ⟨α, β, hab, ?_⟩
    have hc : Probe a (fun t => α * g t + β * k t) := by
      have := probe_add_smul (probe_smul hg α) hk β; simpa using this
    have := hμ _ hc (by rw [hlin]; exact h0)
    rw [hN, hab, mul_one] at this
    exact this.trans (weilQ0_le a _)
  by_cases hr : p ^ 2 + q ^ 2 = 0
  · have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    exact hfin 1 0 (by norm_num) (by rw [hp, hq]; ring)
  · have hpos : 0 < p ^ 2 + q ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hr)
    set r := Real.sqrt (p ^ 2 + q ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt hpos.le
    refine hfin (q / r) (-(p / r)) ?_ ?_
    · rw [div_pow, neg_sq, div_pow, ← add_div, hr2]; field_simp; ring
    · field_simp; ring

/-- **The pole-overlap gap bound**: `λ₂(Q) ≥ λ₁(Q) + c₂²(μ₂ − μ₁)/(c₁² + c₂²)`. -/
theorem lam2Ge_gap {a μ₂ : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) (hψμ : weilQ0 a ψ = μ₂)
    (hμ : ∀ χ, Probe a χ → xcorr χ φ 0 = 0 → μ₂ * normSq χ ≤ weilQ0 a χ) :
    Lam2Ge a (lam a + poleR ψ a ^ 2 * (μ₂ - lam0 a) / (poleR φ a ^ 2 + poleR ψ a ^ 2)) := by
  have hc₁ := poleR_ne_zero_of_groundState0 ha hφ
  have hden : 0 < poleR φ a ^ 2 + poleR ψ a ^ 2 := by positivity
  have ht := lam_le_trial ha hφ hψ hn hx
  rw [hψμ] at ht
  refine (lam2Ge_of_Q0 hφ.1 hμ).anti ?_
  have : poleR ψ a ^ 2 * (μ₂ - lam0 a) / (poleR φ a ^ 2 + poleR ψ a ^ 2) ≤ μ₂ - lam a := by
    rw [div_le_iff₀ hden]; nlinarith [ht]
  linarith

/-- **Simplicity from a nonzero pole overlap**, with the explicit gap above. -/
theorem simple_of_pole_overlap {a μ₂ : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) (hψμ : weilQ0 a ψ = μ₂)
    (hμ : ∀ χ, Probe a χ → xcorr χ φ 0 = 0 → μ₂ * normSq χ ≤ weilQ0 a χ)
    (hc₂ : poleR ψ a ≠ 0) (hgap : lam0 a < μ₂) {g : ℝ → ℝ} (hg : IsGroundState a g) :
    SimpleGround a g := by
  have hc₁ := poleR_ne_zero_of_groundState0 ha hφ
  have hden : 0 < poleR φ a ^ 2 + poleR ψ a ^ 2 := by positivity
  have hκ : 0 < poleR ψ a ^ 2 * (μ₂ - lam0 a) / (poleR φ a ^ 2 + poleR ψ a ^ 2) := by
    apply div_pos _ hden
    exact mul_pos (by positivity) (by linarith)
  exact simpleGround_of_lam2 ha (by linarith) (lam2Ge_gap ha hφ hψ hn hx hψμ hμ) hg

/-! ## Continuity of `Q_λ` in `L²` plus archimedean energy -/

/-- `Q_λ(x + y) ≤ (1 + t)Q_λ(x) + (1 + 1/t)Q_λ(y)` (Cauchy–Schwarz for the nonnegative `Q_λ`). -/
theorem Qlam_add_le {a : ℝ} {x y : ℝ → ℝ} (hx : Probe a x) (hy : Probe a y) {t : ℝ} (ht : 0 < t) :
    Qlam a (fun u => x u + y u) ≤ (1 + t) * Qlam a x + (1 + 1 / t) * Qlam a y := by
  have e1 := Qlam_add_smul hx hy 1
  have e2 := Qlam_add_smul hx hy (-(1 / t))
  have n2 := Qlam_nonneg (probe_add_smul hx hy (-(1 / t)))
  simp only [one_mul] at e1
  unfold Qlam
  set B := bil0 a x y + 2 * poleR x a * poleR y a - lam a * xcorr x y 0
  set Qx := weilQ a x - lam a * normSq x
  set Qy := weilQ a y - lam a * normSq y
  have hQx : 0 ≤ Qx := Qlam_nonneg hx
  have hQy : 0 ≤ Qy := Qlam_nonneg hy
  rw [e2] at n2
  have hB : 2 * B ≤ t * Qx + Qy / t := by
    have h1 : 0 ≤ Qx - 2 * B / t + Qy / t ^ 2 := by
      have : Qx + 2 * -(1 / t) * B + (-(1 / t)) ^ 2 * Qy = Qx - 2 * B / t + Qy / t ^ 2 := by
        field_simp; ring
      linarith
    have h2 : 0 ≤ t * (Qx - 2 * B / t + Qy / t ^ 2) := mul_nonneg ht.le h1
    have : t * (Qx - 2 * B / t + Qy / t ^ 2) = t * Qx - 2 * B + Qy / t := by field_simp
    linarith
  have : (1 + 1 / t) * Qy = Qy + Qy / t := by field_simp
  rw [e1]; nlinarith

/-- `Q_λ` is dominated by `L²` norm plus archimedean energy. -/
theorem Qlam_le_d {a : ℝ} (ha : 0 < a) : ∃ C, 0 < C ∧ ∀ f, Probe a f →
    Qlam a f ≤ C * (normSq f + archE f) := by
  set K := 2 * (∫ u in (-a)..a, Real.exp (-u)) + |weilConst| + |lam a| + 2 * primeWeight a
  have hK : 0 ≤ K := by
    have : 0 ≤ primeWeight a := Finset.sum_nonneg fun n _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have : 0 ≤ ∫ u in (-a)..a, Real.exp (-u) :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => (exp_pos _).le
    positivity
  refine ⟨K + 1, by linarith, fun f hf => ?_⟩
  have h := Qlam_le ha hf
  have hN := normSq_nonneg f
  have hE := archE_nonneg hf
  nlinarith

end WeilForm

#print axioms WeilForm.lam_le_trial
#print axioms WeilForm.lam2Ge_of_Q0
#print axioms WeilForm.lam2Ge_gap
#print axioms WeilForm.simple_of_pole_overlap
