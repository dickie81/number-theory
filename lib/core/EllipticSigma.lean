import EllipticLegendre
import CMFormalGroup

/-!
# The Taylor series of the normalised sigma is the formal `σ*`

The link of the analytic `σ* = σ_W·e^{−s₂z²/2}` (`ThetaNorm.sgStar`) with the formal `σ*` of `CMFormalGroup`
(`CMFormalInert.sigF = z·exp(logSig)`, on which `ph` and `be` are built): `∂ⁿσ*(0) = n!·[zⁿ]sigF(g₂, g₃, s₂)` for the
lattice's `g₂`, `g₃`, `s₂` (`sgStar_taylor`). So identities of `σ*` near `0`, such as the addition formula of
`EllipticAdd`, are identities of `sigF`.

**Proof.** `σ*(z) = z·sigE(z)`, with `sigE = sigP·e^{−s₂z²/2}` entire, `sigE(0) = 1` and `sigE′ = sigE·Lp` near `0`,
where `Lp = zetaE − s₂z` (`deriv_sigE_eventually`, from `σ_W′ = σ_W·ζ_W` and `ζ_W = 1/z + zetaE`). Since
`zetaE′ = −℘[Λ − 0]` (`deriv_zetaE_eventually`), the derivatives of `Lp` at `0` are `−n!·lc(n)` and `−s₂`
(`iteratedDeriv_Lp_succ`), which `wpC_eq_lc` turns into the coefficients of `logSig` (`hurwitz_logSig`). Leibniz's rule
on `sigE′ = sigE·Lp` and the derivative of the formal `exp(logSig)` give the same recursion (`sigE_taylor`), as in
`CMThetaOne.th0_taylor`.

**Main declarations:** `sgStar_taylor`, `sigE_taylor`.
-/

namespace EllipticSigma

noncomputable section

open PeriodPair ThetaNorm CMThetaOne EllipticAdd EllipticLegendre Complex Filter Topology

variable (Λ : PeriodPair)

/-! ## `ζ_W − 1/z` and `σ_W/z` near `0` -/

/-- **`ζ_W(0) = 0`** (`ζ_W` is odd). -/
theorem zetaW_zero : zetaW Λ 0 = 0 := by
  have h := zetaW_neg Λ 0
  rw [neg_zero] at h
  linear_combination h / 2

/-- **`zetaE(0) = 0`.** -/
theorem zetaE_zero : zetaE Λ 0 = 0 := by
  have h := zetaW_eq_add Λ 0
  rw [zetaW_zero, div_zero, zero_add] at h
  exact h.symm

/-- **`zetaE′ = −℘[Λ − 0]`** off the lattice (`zetaE = ζ_W − 1/z` and `ζ_W′ = −℘`). -/
theorem hasDerivAt_zetaE {z : ℂ} (hz : z ∉ Λ.lattice) :
    HasDerivAt (zetaE Λ) (-Λ.weierstrassPExcept 0 z) z := by
  have hz0 : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
  have hfun : zetaE Λ = fun y => zetaW Λ y - 1 / y := funext fun y => by rw [zetaW_eq_add]; ring
  have h1 : HasDerivAt (fun y : ℂ => 1 / y) (-1 / z ^ 2) z := by
    have h := (hasDerivAt_const z (1 : ℂ)).fun_div (hasDerivAt_id z) hz0
    convert h using 1 <;> simp
  rw [hfun]
  convert (hasDerivAt_zetaW Λ hz).fun_sub h1 using 1
  rw [weierstrassP_eq]
  ring

/-- **`zetaE′ = −℘[Λ − 0]` near `0`** (at `0` itself by continuity of both sides). -/
theorem deriv_zetaE_eventually :
    deriv (zetaE Λ) =ᶠ[𝓝 0] fun z => -Λ.weierstrassPExcept 0 z := by
  have hs : (Λ.lattice \ {0} : Set ℂ)ᶜ ∈ 𝓝 (0 : ℂ) := Λ.isOpen_compl_lattice_sdiff.mem_nhds (by simp)
  have hEa : AnalyticAt ℂ (zetaE Λ) 0 := (differentiableOn_zetaE Λ).analyticAt hs
  have hpa := Λ.analyticAt_weierstrassPExcept 0
  have hpun : ∀ᶠ z in 𝓝[≠] 0, deriv (zetaE Λ) z = -Λ.weierstrassPExcept 0 z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hs] with z hz0 hzs
    exact (hasDerivAt_zetaE Λ fun h => hzs ⟨h, hz0⟩).deriv
  have h0 : deriv (zetaE Λ) 0 = -Λ.weierstrassPExcept 0 0 := by
    refine tendsto_nhds_unique (f := deriv (zetaE Λ)) (l := 𝓝[≠] (0 : ℂ))
      (hEa.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    exact (hpa.neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hpun.mono fun z hz => hz.symm)
  filter_upwards [hs] with z hzs
  by_cases hz0 : z = 0
  · rw [hz0, h0]
  · exact (hasDerivAt_zetaE Λ fun h => hzs ⟨h, hz0⟩).deriv

/-- **`σ*(z)/z`**: `sigE(z) = sigP(z)·exp(−s₂z²/2)`, entire with `sigE(0) = 1`. -/
def sigE (z : ℂ) : ℂ := sigP Λ z * cexp (-(s2 Λ) * z ^ 2 / 2)

/-- **`σ*(z) = z·sigE(z)`.** -/
theorem sgStar_eq : sgStar Λ = fun z => z ^ 1 * sigE Λ z := by
  funext z
  simp only [sgStar, sigE, sigmaW_eq, pow_one]
  ring

/-- **`sigE` is entire.** -/
theorem differentiable_sigE : Differentiable ℂ (sigE Λ) :=
  (differentiable_sigP Λ).mul (by fun_prop)

/-- **`sigP′ = sigP·zetaE` near `0`** (from `σ_W′ = σ_W·ζ_W` off the lattice; at `0` both sides vanish, `sigP` being
even). -/
theorem deriv_sigP_eventually : deriv (sigP Λ) =ᶠ[𝓝 0] fun z => sigP Λ z * zetaE Λ z := by
  filter_upwards [Λ.isOpen_compl_lattice_sdiff.mem_nhds (show (0 : ℂ) ∈ (Λ.lattice \ {0} : Set ℂ)ᶜ by simp)]
    with z hzs
  by_cases hz0 : z = 0
  · subst hz0
    have h := deriv_comp_neg (sigP Λ) 0
    simp only [sigP_neg, neg_zero] at h
    rw [zetaE_zero, mul_zero]
    linear_combination h / 2
  · have hz : z ∉ Λ.lattice := fun h => hzs ⟨h, hz0⟩
    have h1 := hasDerivAt_sigmaW Λ hz
    have h2 := (hasDerivAt_id' z).fun_mul ((differentiable_sigP Λ) z).hasDerivAt
    have hσ : sigmaW Λ = fun y => y * sigP Λ y := funext (sigmaW_eq Λ)
    rw [hσ] at h1
    have h3 := h1.unique h2
    rw [zetaW_eq_add] at h3
    refine mul_left_cancel₀ hz0 ?_
    field_simp at h3
    linear_combination -h3

/-- **The logarithmic derivative of `sigE`**: `Lp(z) = zetaE(z) − s₂z`. -/
def Lp (z : ℂ) : ℂ := zetaE Λ z - s2 Λ * z

/-- **`sigE′ = sigE·Lp` near `0`.** -/
theorem deriv_sigE_eventually : deriv (sigE Λ) =ᶠ[𝓝 0] fun z => sigE Λ z * Lp Λ z := by
  filter_upwards [deriv_sigP_eventually Λ] with z hz
  have h2 : HasDerivAt (fun z => cexp (-(s2 Λ) * z ^ 2 / 2)) (cexp (-(s2 Λ) * z ^ 2 / 2) * (-(s2 Λ) * z)) z := by
    have := (((hasDerivAt_pow 2 z).const_mul (-(s2 Λ))).div_const 2).cexp
    convert this using 1
    push_cast
    ring
  have h := ((differentiable_sigP Λ) z).hasDerivAt.fun_mul h2
  rw [hz] at h
  rw [show sigE Λ = fun z => sigP Λ z * cexp (-(s2 Λ) * z ^ 2 / 2) from rfl, h.deriv]
  simp only [Lp]
  ring

/-! ## The jets of `sigE` -/

/-- **The derivatives of `Lp` at `0`**: `∂^{n+1}Lp(0) = −n!·lc(n) − [n = 0]·s₂`. -/
theorem iteratedDeriv_Lp_succ (n : ℕ) :
    iteratedDeriv (n + 1) (Lp Λ) 0 = -(n.factorial * lc Λ n) - if n = 0 then s2 Λ else 0 := by
  have hev : deriv (Lp Λ) =ᶠ[𝓝 0] fun z => -(s2 Λ + Λ.weierstrassPExcept 0 z) := by
    have hs : (Λ.lattice \ {0} : Set ℂ)ᶜ ∈ 𝓝 (0 : ℂ) := Λ.isOpen_compl_lattice_sdiff.mem_nhds (by simp)
    filter_upwards [deriv_zetaE_eventually Λ, hs] with z hz hzs
    have hd : HasDerivAt (zetaE Λ) (deriv (zetaE Λ) z) z :=
      (((differentiableOn_zetaE Λ) z hzs).differentiableAt (Λ.isOpen_compl_lattice_sdiff.mem_nhds hzs)).hasDerivAt
    rw [show Lp Λ = fun z => zetaE Λ z - s2 Λ * z from rfl,
      (hd.fun_sub ((hasDerivAt_id' z).const_mul (s2 Λ))).deriv, hz]
    ring
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, iteratedDeriv_fun_neg]
  rcases n with _ | n
  · simp [lc]
  · rw [iteratedDeriv_const_add (Nat.succ_pos n), lc, mul_div_cancel₀ _ hfac]
    simp

/-- **The jet recursion of `sigE`** (Leibniz on `sigE′ = sigE·Lp`):
`∂^{n+1}sigE(0) = Σ_i C(n, i)·∂^i sigE(0)·∂^{n−i}Lp(0)`. -/
theorem iteratedDeriv_sigE_succ (n : ℕ) :
    iteratedDeriv (n + 1) (sigE Λ) 0 = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i (sigE Λ) 0 * iteratedDeriv (n - i) (Lp Λ) 0 := by
  have hs : (Λ.lattice \ {0} : Set ℂ)ᶜ ∈ 𝓝 (0 : ℂ) := Λ.isOpen_compl_lattice_sdiff.mem_nhds (by simp)
  have hEa : AnalyticAt ℂ (sigE Λ) 0 := (differentiable_sigE Λ).differentiableOn.analyticAt Filter.univ_mem
  have hLa : AnalyticAt ℂ (Lp Λ) 0 := by
    have := (differentiableOn_zetaE Λ).analyticAt hs
    unfold Lp; fun_prop
  rw [iteratedDeriv_succ', (deriv_sigE_eventually Λ).iteratedDeriv_eq,
    iteratedDeriv_fun_mul hEa.contDiffAt hLa.contDiffAt]

/-- **The Hurwitz coefficients of `logSig` are the derivatives of `Lp`**: `(j + 1)!·[z^{j+1}]logSig = ∂^j Lp(0)`, by
`wpC_eq_lc` (the Laurent coefficients of `℘` are `wpC`). -/
theorem hurwitz_logSig (j : ℕ) :
    ((j + 1).factorial : ℂ) * PowerSeries.coeff (j + 1) (CMFormalInert.logSig Λ.g₂ Λ.g₃ (s2 Λ)) =
      iteratedDeriv j (Lp Λ) 0 := by
  rcases j with _ | m
  · simp [CMFormalInert.logSig, Lp, zetaE_zero]
  rw [iteratedDeriv_Lp_succ, CMFormalInert.logSig, PowerSeries.coeff_mk]
  rcases m with _ | m
  · simp [lc_eq]
    ring
  have h2 : m + 1 + 1 + 1 ≠ 2 := by omega
  simp only [h2, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, sub_zero]
  rcases Nat.even_or_odd (m + 1 + 1 + 1) with he | ho
  · have hlc : CMFormalInert.wpC Λ.g₂ Λ.g₃ ((m + 1 + 1 + 1) / 2) = lc Λ (m + 1) := by
      obtain ⟨k, hk⟩ := he
      rw [wpC_eq_lc]
      congr 1
      omega
    simp only [he, ↓reduceIte, hlc]
    have hf : ((m + 1 + 1 + 1).factorial : ℂ) = (m + 3) * (m + 2) * (m + 1).factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have hD : ((m + 1 + 1 + 1 : ℕ) : ℂ) * (((m + 1 + 1 + 1 : ℕ) : ℂ) - 1) = (m + 3) * (m + 2) := by
      push_cast; ring
    have h3 : (m : ℂ) + 3 ≠ 0 := by norm_cast
    have h4 : (m : ℂ) + 2 ≠ 0 := by norm_cast
    rw [hf, hD]
    field_simp
  · have hno : ¬Even (m + 1 + 1 + 1) := Nat.not_even_iff_odd.mpr ho
    have hodd : Odd (m + 1) := by
      obtain ⟨k, hk⟩ := ho
      exact ⟨k - 1, by omega⟩
    simp [hno, lc_odd Λ hodd]

/-- **The Taylor series of `sigE` is `exp(logSig)`**: `∂^n sigE(0) = n!·[zⁿ]exp(logSig)` (the same recursion holds for
the formal exponential, from `d(exp ∘ L)/dz = exp(L)·L′`). -/
theorem sigE_taylor (n : ℕ) :
    iteratedDeriv n (sigE Λ) 0 = (n.factorial : ℂ) *
      PowerSeries.coeff n ((PowerSeries.exp ℂ).subst (CMFormalInert.logSig Λ.g₂ Λ.g₃ (s2 Λ))) := by
  set L := CMFormalInert.logSig Λ.g₂ Λ.g₃ (s2 Λ) with hL
  set E := (PowerSeries.exp ℂ).subst L with hE
  have h0 : PowerSeries.constantCoeff L = 0 := CMFormalInert.constantCoeff_logSig _ _ _
  have hsub : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero h0
  have hder : PowerSeries.derivative E = E * PowerSeries.derivative L := by
    rw [hE, PowerSeries.derivative_subst hsub, PowerSeries.derivative_exp]
  have hE0 : PowerSeries.coeff 0 E = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hE]
    exact (PowerSeries.constantCoeff_subst_of_constantCoeff_zero h0 (PowerSeries.exp ℂ)).trans (by simp)
  have hrec : ∀ n : ℕ, PowerSeries.coeff (n + 1) E * ((n : ℂ) + 1) = ∑ i ∈ Finset.range (n + 1),
      PowerSeries.coeff i E * (PowerSeries.coeff (n - i + 1) L * ((n - i : ℕ) + 1 : ℂ)) := by
    intro n
    have := congrArg (PowerSeries.coeff n) hder
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_derivative]
  have hσ0 : sigE Λ 0 = 1 := by simp [sigE, sigP_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [hσ0, hE0]
    · rw [iteratedDeriv_sigE_succ Λ n, show ((n + 1).factorial : ℂ) * PowerSeries.coeff (n + 1) E =
          n.factorial * (PowerSeries.coeff (n + 1) E * ((n : ℂ) + 1)) by push_cast [Nat.factorial_succ]; ring,
        hrec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi : i ≤ n := by simp at hi; omega
      rw [ih i (by omega), ← hurwitz_logSig Λ, show n - i + 1 = (n - i) + 1 from rfl]
      rw [← Nat.choose_mul_factorial_mul_factorial hi, Nat.factorial_succ (n - i)]
      push_cast
      ring

/-- **The Taylor series of `σ*` at `0` is the formal `σ*`** (the link of the analytic `σ* = σ_W·e^{−s₂z²/2}` with
`CMFormalInert.sigF` for the lattice's `g₂`, `g₃`, `s₂`): `∂^n σ*(0) = n!·[zⁿ]sigF(g₂, g₃, s₂)`. -/
theorem sgStar_taylor (n : ℕ) :
    iteratedDeriv n (sgStar Λ) 0 = (n.factorial : ℂ) * PowerSeries.coeff n (CMFormalInert.sigF Λ.g₂ Λ.g₃ (s2 Λ)) := by
  have hEa : AnalyticAt ℂ (sigE Λ) 0 := (differentiable_sigE Λ).differentiableOn.analyticAt Filter.univ_mem
  rw [sgStar_eq, CMFormalInert.sigF]
  rcases n with _ | n
  · simp
  rw [iteratedDeriv_fun_mul (f := fun z : ℂ => z ^ 1) (contDiffAt_id.pow 1) hEa.contDiffAt, Finset.sum_eq_single 1,
    PowerSeries.coeff_succ_X_mul, show n + 1 - 1 = n by omega, sigE_taylor, iteratedDeriv_fun_pow_zero]
  · simp only [↓reduceIte, Nat.choose_one_right, Nat.factorial_succ]
    push_cast
    ring
  · intro i _ hi
    rw [iteratedDeriv_fun_pow_zero, ite_eq_right_iff.mpr fun h => absurd h hi]
    simp
  · intro h
    simp at h

end

end EllipticSigma
