import UnramFrobLift
import TorsTransl

/-!
# CM equivariance and the classification `be ≃ c·serAB` without the torsion input

The theorems of `CMEquiv` and `UnramFrobLift` that take the input `CMEquiv.TorsionTransl`, with that input
discharged by `TorsTransl.isInt_translate'`: every translate `U_q = εT·G_q(ε·log_LT(T))` by a torsion point of order
prime to `ℓ` is an integral unit, for `ι`-integral `g₂`, `g₃`, with no further arithmetic.

**Either orientation** (`isInt_translate_any`). `isInt_translate'` is stated for `Im(ω₂/ω₁) > 0`; swapping the periods
(`CMEquiv.swapPair`) keeps the lattice, `g₂`, `g₃` (`g₂_swapPair`, `g₃_swapPair`) and the translates
(`CMEquiv.GqRes_swapPair`).

**CM equivariance** (`cm_equiv'`): `ph([ω]T) ≃ N(ω)·ph(T)` for the `Δ = 1` CM lattice at an inert `ℓ ≥ 5`, from CM-c
and a Frobenius lift on `K^ur` alone; the proof is that of `CMEquiv.cm_equiv`, with the translates of the kernel of
`[ω]` (`N(ω)q ∈ Λ`, `ℓ ∤ N(ω)`) integral units by `isInt_translate_any`.

**The classification** (`be_simeq_serAB_cm'`, the proof of `CMEquiv.be_simeq_serAB_cm` on `cm_equiv'`): `be ≃ c·serAB`
with `φ(c) = −c`, `‖c‖ ≤ 1`, for every unit `ε ∈ K^ur` making `t(ε·log_LT(T))` integral. With the Frobenius lift
`UnramFrobLift.frobUnram`, the hermitian property of `be` (`isHerm_be_cm_classical`) and the classification
(`be_classification_cm_classical`) hold for the CM curve under the classical CM inputs alone: CM-a′
(`CMUnramified`), CM-c (`CMThetaOne.CMjIntegral`), the strengthened CM-d (`CMs2Unram`), and CM-b
(`CMInertLubinTate`) for the existence of `ε`.

**Main results:** `isInt_translate_any`, `cm_equiv'`, `be_simeq_serAB_cm'`, `isHerm_be_cm_classical`,
`be_classification_cm_classical`.
-/

namespace CMTorsion

open PowerSeries CMFormalInert CMFormalBiadd CMFormalGauss CMEquiv

noncomputable section

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-! ## Either orientation -/

section Orientation

open PeriodPair ThetaNorm EllipticDivisor

/-- **Swapping the periods keeps `g₂`.** -/
theorem g₂_swapPair (Λ : PeriodPair) : (swapPair Λ).g₂ = Λ.g₂ := by
  simp only [PeriodPair.g₂, PeriodPair.G]
  rw [lattice_swapPair]

/-- **Swapping the periods keeps `g₃`.** -/
theorem g₃_swapPair (Λ : PeriodPair) : (swapPair Λ).g₃ = Λ.g₃ := by
  simp only [PeriodPair.g₃, PeriodPair.G]
  rw [lattice_swapPair]

/-- **Every prime-to-`ℓ` torsion translate is an integral unit, in either orientation** (`isInt_translate'` for `Λ`
or for `swapPair Λ`). -/
theorem isInt_translate_any (hℓ2 : ℓ ≠ 2) (Λ : PeriodPair) (ι : ℂ →+* ℂ_[ℓ]) (h2 : ‖ι Λ.g₂‖ ≤ 1)
    (h3 : ‖ι Λ.g₃‖ ≤ 1) {ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1) (ht : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)))
    {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} (hNℓ : ¬ ℓ ∣ N) (hNq : (N : ℂ) * q ∈ Λ.lattice) :
    IsInt ((logLTDivX ℂ_[ℓ] ℓ)⁻¹ * (map ι (tay (GqRes Λ q))).subst (zLT ℓ ε)) ∧
      constantCoeff ((logLTDivX ℂ_[ℓ] ℓ)⁻¹ * (map ι (tay (GqRes Λ q))).subst (zLT ℓ ε)) = 1 := by
  rcases lt_or_gt_of_ne (im_div_ne_zero Λ) with h | h
  · have hor' : 0 < ((swapPair Λ).ω₂ / (swapPair Λ).ω₁).im := by
      have h1 : Λ.ω₁ ≠ 0 := Λ.indep.ne_zero 0
      have h2 : Λ.ω₂ ≠ 0 := Λ.indep.ne_zero 1
      change 0 < (Λ.ω₁ / Λ.ω₂).im
      rw [show Λ.ω₁ / Λ.ω₂ = (Λ.ω₂ / Λ.ω₁)⁻¹ by rw [inv_div], Complex.inv_im, neg_div]
      exact neg_pos.mpr (div_neg_of_neg_of_pos h (Complex.normSq_pos.mpr (div_ne_zero h2 h1)))
    have := TorsTransl.isInt_translate' hℓ2 (swapPair Λ) hor' ι (by rwa [g₂_swapPair]) (by rwa [g₃_swapPair]) hε
      (by rwa [g₂_swapPair, g₃_swapPair]) (q := q) (by rwa [lattice_swapPair]) hNℓ (by rwa [lattice_swapPair])
    simpa only [GqRes_swapPair] using this
  · exact TorsTransl.isInt_translate' hℓ2 Λ h ι h2 h3 hε ht hq hNℓ hNq

end Orientation

/-! ## CM equivariance -/

section Equiv

open PeriodPair ThetaNorm EllipticSigma EllipticDivisor Topology

/-- **CM equivariance without the torsion input** `ph([ω]T) ≃ N(ω)·ph(T)` for the `Δ = 1` CM lattice at an inert
`ℓ ≥ 5`, for every `ε` with `‖ε‖ = 1` making `t(ε·log_LT(T))` integral (`CMEquiv.cm_equiv` without
`TorsionTransl`): the product formula near `0` (`sigE_omK0_mul`) becomes
`exp(N·ph(T) − ph([ω]T)) = (ωT/[ω]T)·∏_{q ∈ Q} U_q(T)`, with the translates `U_q = εT·G_q(z(T))` integral units
(`isInt_translate_any`: `N(ω)q ∈ Λ`, `ℓ ∤ N(ω)`) and `[ω]T/(ωT)` an integral unit (`isInt_mulLT`). -/
theorem cm_equiv' (hj : CMThetaOne.CMjIntegral) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : HasCM d Λ) (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d)
    (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι : ℂ ≃+* ℂ_[ℓ]) {φ : unramC ℓ →+* unramC ℓ}
    (hφ : ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖) {ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε))) :
    Simeq (PowerSeries.subst (mulLT (ι (omK0 d))) (ph ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε))
      (PowerSeries.C (((1 + d) / 4 : ℕ) : ℂ_[ℓ]) * ph ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε) := by
  classical
  have hℓ := hℓp.out.one_lt
  have hℓ2 : ℓ ≠ 2 := by omega
  have hd0 : d ≠ 0 := hd.ne_zero
  obtain ⟨h2, h3⟩ := norm_g_le_one hj hd hd4 hcm hΔ h5 ι
  obtain ⟨Q, hQ⟩ := exists_kerReps hd0 hd4 hcm
  have hcard := card_kerReps hd0 hd4 hcm hQ
  have hN1 : 1 ≤ (1 + d) / 4 := normOm_pos hd4
  have hNℓ : ¬ ℓ ∣ (1 + d) / 4 := not_dvd_normOm hd4 hin
  have hα1 : ‖ι (omK0 d)‖ = 1 := norm_iota_omK0 hℓ2 hdℓ hd4 hin ι
  -- the product formula as Taylor series over `ℂ`, carried to `ℂ_ℓ`
  have hT : rescale (omK0 d) (expSig Λ.g₂ Λ.g₃ (s2 Λ)) =
      expSig Λ.g₂ Λ.g₃ (s2 Λ) ^ ((1 + d) / 4) * ∏ q ∈ Q, tay (GqRes Λ q) := by
    have h := tay_congr (sigE_omK0_mul hd0 hd4 hcm hQ)
    rw [tay_comp_mul isOpen_univ (Set.mem_univ 0) (fun x _ => analyticAt_sigE Λ x) _ (fun _ _ => Set.mem_univ _),
      tay_sigE, tay_mul (f := fun z => sigE Λ z ^ ((1 + d) / 4)) ((analyticAt_sigE Λ 0).pow _)
        (Finset.analyticAt_fun_prod _ fun q hq => (analyticAt_GqRes Λ (hQ.1 q hq).1).1),
      tay_pow (analyticAt_sigE Λ 0), tay_sigE, tay_prod _ fun q hq => (analyticAt_GqRes Λ (hQ.1 q hq).1).1] at h
    exact h
  have hT' : rescale (ι (omK0 d)) (expSig (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ))) =
      expSig (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ^ ((1 + d) / 4) *
        ∏ q ∈ Q, PowerSeries.map (ι : ℂ →+* ℂ_[ℓ]) (tay (GqRes Λ q)) := by
    have h := congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[ℓ])) hT
    rw [← rescale_map, map_mul, map_pow, map_prod, map_expSig] at h
    exact h
  -- the translates in Lubin–Tate coordinates
  set lam := logLTDivX ℂ_[ℓ] ℓ with hlam
  set z := zLT ℓ ε with hzdef
  have hz0 : constantCoeff z = 0 := constantCoeff_zLT hℓ ε
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  have hU : ∀ q ∈ Q, IsInt (lam⁻¹ * (PowerSeries.map (ι : ℂ →+* ℂ_[ℓ]) (tay (GqRes Λ q))).subst z) ∧
      constantCoeff (lam⁻¹ * (PowerSeries.map (ι : ℂ →+* ℂ_[ℓ]) (tay (GqRes Λ q))).subst z) = 1 := by
    intro q hq
    exact isInt_translate_any hℓ2 Λ (ι : ℂ →+* ℂ_[ℓ]) h2 h3 hε ht (hQ.1 q hq).1 hNℓ
      (natCast_normOm_mul_mem hd4 hcm (hQ.1 q hq).2)
  set U : ℂ → ℂ_[ℓ]⟦X⟧ := fun q => lam⁻¹ * (PowerSeries.map (ι : ℂ →+* ℂ_[ℓ]) (tay (GqRes Λ q))).subst z
    with hUdef
  set p := ph ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε with hp
  set E := expSig (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) with hE
  set α := ι (omK0 d) with hα
  set N := (1 + d) / 4 with hN
  set m := mulLT α with hm
  have hms : HasSubst m := hasSubst_mulLT α
  have hm0 : constantCoeff m = 0 := constantCoeff_mulLT α
  have hlam0 : constantCoeff lam = 1 := constantCoeff_logLTDivX ℓ
  have hlaml : lam * lam⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hlam0]; exact one_ne_zero)
  have hp0 : constantCoeff p = 0 := constantCoeff_ph hℓ _ _ _ _
  have hpn0 : constantCoeff (-p) = 0 := by rw [map_neg, hp0, neg_zero]
  -- `exp(−ph) = lam·E(z)`
  have hexp : (exp ℂ_[ℓ]).subst (-p) = lam * E.subst z := by
    have hzs' : HasSubst (C ε * logLT ℂ_[ℓ] ℓ) := HasSubst.of_constantCoeff_zero' (constantCoeff_C_mul_logLT hℓ ε)
    have h : C ε * X * (exp ℂ_[ℓ]).subst (-p) = z * E.subst z := by
      have h0 := C_mul_X_mul_exp_neg_ph hℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε
      rw [sigF, subst_mul hzs', subst_X hzs'] at h0
      exact h0
    have hz' : z = C ε * X * lam := by rw [hzdef, zLT, ← X_mul_logLTDivX hℓ, mul_assoc]
    have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
    refine mul_left_cancel₀ (mul_ne_zero (by rwa [Ne, map_eq_zero_iff C C_injective]) X_ne_zero) ?_
    linear_combination h + E.subst z * hz'
  -- substituting `z` into the product formula
  have hsub : PowerSeries.subst m (E.subst z) = (E.subst z) ^ N * (lam ^ (N - 1) * ∏ q ∈ Q, U q) := by
    have h := congrArg (PowerSeries.subst z) hT'
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' _) hzs, subst_smul hzs, subst_X hzs,
      ← coe_substAlgHom hzs, map_mul, map_pow, map_prod, coe_substAlgHom hzs] at h
    have hzm : z.subst m = α • z := by
      rw [hzdef, zLT, ← smul_eq_C_mul, subst_smul hms, logLT_subst_mulLT, smul_eq_C_mul, smul_eq_C_mul,
        smul_eq_C_mul]
      ring
    have hG : ∀ q ∈ Q, (PowerSeries.map (ι : ℂ →+* ℂ_[ℓ]) (tay (GqRes Λ q))).subst z = lam * U q := fun q _ => by
      simp only [hUdef]
      rw [← mul_assoc, hlaml, one_mul]
    rw [subst_comp_subst_apply hzs hms, hzm, h, Finset.prod_congr rfl hG, Finset.prod_mul_distrib,
      Finset.prod_const, hcard]
  -- the logarithm of `[α]`
  have hlm : lam.subst m * m = C α * X * lam := by
    have h := logLT_subst_mulLT α
    rw [← X_mul_logLTDivX hℓ, subst_mul hms, subst_X hms] at h
    linear_combination h
  -- exponentials
  have hpm0 : constantCoeff (p.subst m) = 0 := constantCoeff_subst_eq_zero hm0 _ hp0
  set W := (exp ℂ_[ℓ]).subst (C (N : ℂ_[ℓ]) * p - p.subst m) with hW
  set Ep := (exp ℂ_[ℓ]).subst (-p) with hEp
  set Em := (exp ℂ_[ℓ]).subst (-(p.subst m)) with hEm
  have hW0 : constantCoeff (C (N : ℂ_[ℓ]) * p - p.subst m) = 0 := by
    rw [map_sub, map_mul, hp0, hpm0, mul_zero, sub_zero]
  have hv : W * Ep ^ N = Em := by
    rw [hW, hEp, ← exp_subst_nsmul hpn0 N, ← exp_subst_add hW0
      (by rw [map_nsmul, show MvPowerSeries.constantCoeff (-p) = 0 from hpn0, smul_zero]), hEm]
    congr 1
    rw [nsmul_eq_mul, map_natCast]
    ring
  have hi : lam.subst m * PowerSeries.subst m (E.subst z) = Em := by
    rw [← subst_mul hms, ← hexp, subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hpn0) hms, hEm,
      ← coe_substAlgHom hms, map_neg, coe_substAlgHom hms]
  have hEp0 : Ep ^ N ≠ 0 := pow_ne_zero _ fun h0 => by
    have h1 := congrArg MvPowerSeries.constantCoeff h0
    rw [hEp, constantCoeff_subst_of_constantCoeff_zero hpn0] at h1
    simp at h1
  have key1 : W * lam * Ep ^ N = lam.subst m * (∏ q ∈ Q, U q) * Ep ^ N := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    calc W * lam * Ep ^ N = lam * (W * Ep ^ N) := by ring
      _ = lam * (lam.subst m * PowerSeries.subst m (E.subst z)) := by rw [hv, hi]
      _ = lam.subst m * (lam * E.subst z) ^ N * ∏ q ∈ Q, U q := by
        rw [hsub, hM, Nat.add_sub_cancel]
        ring
      _ = _ := by rw [← hexp]; ring
  have key2 : W * lam = lam.subst m * ∏ q ∈ Q, U q := mul_right_cancel₀ hEp0 key1
  -- `[α]T = T·m'`, `m'(0) = α`
  set m' : ℂ_[ℓ]⟦X⟧ := PowerSeries.mk fun n => coeff (n + 1) m with hm'def
  have hm' : m = X * m' := by
    ext n
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, hm0, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X,
        zero_mul]
    · rw [coeff_succ_X_mul, coeff_mk]
  have key3 : W * m' = C α * ∏ q ∈ Q, U q := by
    have h : (W * m' - C α * ∏ q ∈ Q, U q) * (X * lam) = 0 := by
      linear_combination m * key2 + (∏ q ∈ Q, U q) * hlm - W * lam * hm'
    have hXl : X * lam ≠ 0 := mul_ne_zero X_ne_zero fun h0 => by
      have := congrArg constantCoeff h0
      rw [hlam0, map_zero] at this
      exact one_ne_zero this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hXl)
  -- integrality
  have hαu : α ∈ unramC ℓ := iota_omK0_mem hℓ2 hdℓ ι
  have hφα : φ (φ ⟨α, hαu⟩) = ⟨α, hαu⟩ := phi_phi_iota_omK0 hℓ2 hd4 hdℓ ι φ
  have hmi : IsInt m := isInt_mulLT (unramC ℓ) hφ ⟨α, hαu⟩ hα1.le hφα
  have hm'i : IsInt m' := fun n => by rw [coeff_mk]; exact hmi (n + 1)
  have hm'0 : constantCoeff m' = α := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, hm, coeff_one_mulLT]
  have hα0 : α ≠ 0 := norm_ne_zero_iff.1 (by rw [hα1]; exact one_ne_zero)
  set m'' := C α⁻¹ * m' with hm''
  have hm''0 : MvPowerSeries.constantCoeff (m'' : MvPowerSeries Unit ℂ_[ℓ]) = 1 := by
    change constantCoeff (C α⁻¹ * m') = 1
    rw [map_mul, constantCoeff_C, hm'0, inv_mul_cancel₀ hα0]
  have hm''i : IsIntK (m''⁻¹ : MvPowerSeries Unit ℂ_[ℓ]) :=
    ((isInt_C (by rw [norm_inv, hα1, inv_one])).mul hm'i).isIntK.inv hm''0
  have hUi : IsInt (∏ q ∈ Q, U q) :=
    Finset.prod_induction _ (fun f => IsInt f) (fun _ _ ha hb => ha.mul hb) (by
      rw [← map_one (C (R := ℂ_[ℓ]))]; exact isInt_C (by simp)) fun q hq => (hU q hq).1
  have hWe : W = (∏ q ∈ Q, U q) * m''⁻¹ := by
    have h1 : m'' * m''⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by
      change MvPowerSeries.constantCoeff (m'' : MvPowerSeries Unit ℂ_[ℓ]) ≠ 0
      rw [hm''0]
      exact one_ne_zero)
    have h2 : W * m'' = ∏ q ∈ Q, U q := by
      rw [hm'', mul_left_comm, key3, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hα0, map_one, one_mul]
    rw [← h2, mul_assoc, h1, mul_one]
  have hWi : IsInt W := by
    rw [hWe]
    exact (hUi.isIntK.mul hm''i).isInt
  refine Simeq.symm ⟨hW0, ?_⟩
  rw [expMv_eq_subst hW0]
  exact hWi.isIntK

end Equiv

/-! ## The classification without the torsion input -/

section Classification

open PeriodPair ThetaNorm

/-- **The classification without `IsHerm` and without the torsion input** (`CMEquiv.be_simeq_serAB_cm` on
`cm_equiv'`): for the `Δ = 1` CM lattice at an inert `ℓ ≥ 5` and every unit `ε ∈ K^ur` making `t(ε·log_LT(T))`
integral, `be ≃ c·serAB` with `c ∈ K^ur`, `φ(c) = −c`, `‖c‖ ≤ 1`. The structure theorem gives
`be ≃ a·L(X)L(Y) + γ·serAB`; the polarised equivariance `be([ω]X, [ω]Y) ≃ N·be` against
`be([ω]X, [ω]Y) ≃ aω²·L(X)L(Y) + γ₂·serAB` gives `a(N − ω²) = 0`, so `a = 0`. -/
theorem be_simeq_serAB_cm' (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram) {d : ℕ}
    {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
    (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι : ℂ ≃+* ℂ_[ℓ]) {φ : unramC ℓ →+* unramC ℓ}
    (hφ : ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖) {ε : ℂ_[ℓ]} (hεu : ε ∈ unramC ℓ)
    (hε : ‖ε‖ = 1) (ht : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε))) :
    ∃ c : unramC ℓ, φ c = -c ∧ ‖c‖ ≤ 1 ∧
      Simeq (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε) (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) := by
  have hℓ := hℓp.out.one_lt
  have hℓ2 : ℓ ≠ 2 := by omega
  have hd0 : d ≠ 0 := hd.ne_zero
  obtain ⟨h2, h3⟩ := norm_g_le_one hj hd hd4 hcm hΔ h5 ι
  obtain ⟨h2u, h3u⟩ := hu d Λ hd hd4 hcm hΔ ℓ h5 hdℓ ι
  obtain ⟨hsu, -⟩ := hs d Λ hd hd4 hcm hΔ ℓ h5 hdℓ ι
  obtain ⟨hAdd, hODE⟩ := addLaw_weierODE_map Λ (ι : ℂ →+* ℂ_[ℓ])
  set B := be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε with hBdef
  have hk : ∀ n, MvPowerSeries.coeff n B ∈ unramC ℓ := fun n => by
    set be' := be ℓ (⟨ι Λ.g₂, h2u⟩ : unramC ℓ) ⟨ι Λ.g₃, h3u⟩ ⟨ι (s2 Λ), hsu⟩ ⟨ε, hεu⟩
    have h : MvPowerSeries.map (unramC ℓ).subtype be' = B := map_be (unramC ℓ).subtype hℓ _ _ _ _
    rw [← h, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n be').2
  have hBd : Simeq (deltaX B) 0 := (biadd_iff_deltaX _).1 (be_biadd hℓ2 h2 h3 hε hAdd hODE ht)
  obtain ⟨a₀, γ, hγ, hγ1, hS⟩ :=
    gauss_structure (unramC ℓ) isClosed_unramC hφ hk (constantCoeff_be hℓ _ _ _ _) (be_symm _ _ _ _) hBd
  -- `[ω]`
  set α := ι (omK0 d) with hα
  set N := (1 + d) / 4 with hN
  have hαu : α ∈ unramC ℓ := iota_omK0_mem hℓ2 hdℓ ι
  have hm : IsInt (mulLT α) := isInt_mulLT (unramC ℓ) hφ ⟨α, hαu⟩ (norm_iota_omK0 hℓ2 hdℓ hd4 hin ι).le
    (phi_phi_iota_omK0 hℓ2 hd4 hdℓ ι φ)
  have cP : ∀ i, MvPowerSeries.constantCoeff (mulPair α i) = 0 := fun i => constantCoeff_mulLT_X α i
  have iP : ∀ i, IntS (mulPair α i) := fun i => intS_mulLT_X hm i
  have hP : MvPowerSeries.HasSubst (mulPair α) := MvPowerSeries.hasSubst_of_constantCoeff_zero cP
  -- (1) `B(P_ω) ≃ N·B`, the polarised CM equivariance
  have hB1 : Simeq (B.subst (mulPair α)) (MvPowerSeries.C (N : ℂ_[ℓ]) * B) := by
    have hce := cm_equiv' hj hd hd4 hcm hΔ h5 hdℓ hin ι hφ hε ht
    set p := ph ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε
    have hsub : ∀ {A : MvPowerSeries (Fin 2) ℂ_[ℓ]}, IntS A → MvPowerSeries.constantCoeff A = 0 →
        Simeq (PowerSeries.subst A (p.subst (mulLT α))) ((C (N : ℂ_[ℓ]) * p).subst A) := fun hA hA0 =>
      hce.subst (fun _ => hA) fun _ => hA0
    have hCs : ∀ A : MvPowerSeries (Fin 2) ℂ_[ℓ], MvPowerSeries.constantCoeff A = 0 →
        (C (N : ℂ_[ℓ]) * p).subst A = MvPowerSeries.C (N : ℂ_[ℓ]) * p.subst A := fun A hA => by
      rw [subst_mul (HasSubst.of_constantCoeff_zero hA), subst_C]
    have e : MvPowerSeries.C (N : ℂ_[ℓ]) * B = (C (N : ℂ_[ℓ]) * p).subst (ltAdd ℂ_[ℓ] ℓ) -
        (C (N : ℂ_[ℓ]) * p).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) -
        (C (N : ℂ_[ℓ]) * p).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) := by
      rw [hCs _ (constantCoeff_ltAdd hℓ), hCs _ (MvPowerSeries.constantCoeff_X 0),
        hCs _ (MvPowerSeries.constantCoeff_X 1), hBdef, be]
      ring
    rw [be_subst_mulPair, e]
    exact ((hsub isIntK_ltAdd (constantCoeff_ltAdd hℓ)).sub (hsub (isIntK_X 0) (MvPowerSeries.constantCoeff_X 0))).sub
      (hsub (isIntK_X 1) (MvPowerSeries.constantCoeff_X 1))
  -- (2) `B(P_ω) ≃ a₀ω²·L(X)L(Y) + B₂`
  set B₂ := (MvPowerSeries.C (γ : ℂ_[ℓ]) * serAB ℓ).subst (mulPair α) with hB₂
  have hB2 : Simeq (B.subst (mulPair α))
      (MvPowerSeries.C ((a₀ : ℂ_[ℓ]) * α ^ 2) * (logX ℓ * logY ℓ) + B₂) := by
    have h := hS.subst iP cP
    rwa [MvPowerSeries.subst_add hP, mul_assoc, MvPowerSeries.subst_mul hP, MvPowerSeries.subst_C,
      logXY_subst_mulPair, ← mul_assoc, ← map_mul] at h
  -- (3) `B₂` is hermitian, so `B₂ ≃ γ₂·serAB`
  have hsym : MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (MvPowerSeries.C (γ : ℂ_[ℓ]) * serAB ℓ) =
      MvPowerSeries.C (γ : ℂ_[ℓ]) * serAB ℓ := by
    ext n
    rw [eq_ex2 n, coeff_subst_swap, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
    congr 1
    exact sAB_swap _ _
  have hk₂ : ∀ n, MvPowerSeries.coeff n B₂ ∈ unramC ℓ :=
    coeff_subst_mem _ (fun n => by
      rw [MvPowerSeries.coeff_C_mul, eq_ex2 n]
      exact (unramC ℓ).mul_mem γ.2 (sAB_mem _ _)) cP fun i n => coeff_mulLT_X_mem (unramC ℓ) ⟨α, hαu⟩ i n
  have hB20 : MvPowerSeries.constantCoeff B₂ = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hP cP (by rw [map_mul, constantCoeff_serAB, mul_zero])
  have hB2d : Simeq (deltaX B₂) 0 :=
    simeq_deltaX_subst_mulPair hm ((biadd_iff_deltaX _).1 (serAB_biadd (unramC ℓ) hφ hγ hγ1))
  have hB2H : IsHerm B₂ := (isHerm_C_mul_serAB _).subst_mulPair hm
  obtain ⟨a₂, γ₂, -, -, hS₂⟩ :=
    gauss_structure (unramC ℓ) isClosed_unramC hφ hk₂ hB20 (subst_swap_mulPair α hsym) hB2d
  obtain ⟨ζ, hζk, hζ, hζ1⟩ := exists_teich_unramC (ℓ := ℓ)
  have ha₂ : a₂ = 0 := (alpha_eq_zero_iff hφ hk₂ hS₂).2 ⟨1, bdd_of_isHerm hφ hζk hζ hζ1 hk₂ hB2H⟩
  rw [ha₂, ZeroMemClass.coe_zero, map_zero, zero_mul, zero_mul, zero_add] at hS₂
  -- (4) uniqueness of the pair: `a₀(N − ω²) = 0`
  have h1 : Simeq (MvPowerSeries.C (N : ℂ_[ℓ]) *
      (MvPowerSeries.C (a₀ : ℂ_[ℓ]) * logX ℓ * logY ℓ + MvPowerSeries.C (γ : ℂ_[ℓ]) * serAB ℓ))
      (MvPowerSeries.C ((a₀ : ℂ_[ℓ]) * α ^ 2) * (logX ℓ * logY ℓ) + MvPowerSeries.C (γ₂ : ℂ_[ℓ]) * serAB ℓ) :=
    (hS.natCast_mul N).symm.trans (hB1.symm.trans (hB2.trans ((Simeq.refl _).add hS₂)))
  set c₁ : unramC ℓ := (N : unramC ℓ) * a₀ - a₀ * ⟨α, hαu⟩ ^ 2 with hc₁def
  set c₂ : unramC ℓ := (N : unramC ℓ) * γ - γ₂ with hc₂def
  have h2' : Simeq 0 (MvPowerSeries.C (c₁ : ℂ_[ℓ]) * logX ℓ * logY ℓ + MvPowerSeries.C (c₂ : ℂ_[ℓ]) * serAB ℓ) := by
    have h := (simeq_iff_sub.1 h1).symm
    convert h using 1
    push_cast [hc₁def, hc₂def]
    simp only [map_sub, map_mul, map_natCast, map_pow]
    ring
  have hc₁ : c₁ = 0 :=
    (alpha_eq_zero_iff hφ (B := 0) (fun n => by rw [map_zero]; exact zero_mem _) h2').2 ⟨0, fun j => by simp⟩
  have hne : (N : ℂ_[ℓ]) - α ^ 2 ≠ 0 := by
    intro h
    have h' : ι ((N : ℂ) - omK0 d ^ 2) = 0 := by rw [map_sub, map_natCast, map_pow]; exact h
    rw [map_eq_zero_iff ι ι.injective] at h'
    have him := congrArg Complex.im h'
    rw [Complex.sub_im, Complex.natCast_im, sq, Complex.mul_im, omK0_re, Complex.zero_im] at him
    exact omK0_im_ne_zero hd0 (by linarith)
  have ha₀ : a₀ = 0 := by
    have h : (a₀ : ℂ_[ℓ]) * ((N : ℂ_[ℓ]) - α ^ 2) = 0 := by
      have := congrArg Subtype.val hc₁
      push_cast [hc₁def] at this
      linear_combination this
    exact Subtype.ext ((mul_eq_zero.1 h).resolve_right hne)
  rw [ha₀, ZeroMemClass.coe_zero, map_zero, zero_mul, zero_mul, zero_add] at hS
  exact ⟨γ, hγ, hγ1, hS⟩

/-- **The hermitian property of `be` for the CM curve from the classical CM inputs alone**: under CM-a′, CM-c and the
strengthened CM-d, `IsHerm (be …)` for every unit `ε ∈ K^ur` making `t(ε·log_LT(T))` integral
(`be_simeq_serAB_cm'` with the Frobenius lift `UnramFrobLift.frobUnram`). -/
theorem isHerm_be_cm_classical (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram) {d : ℕ}
    {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ) (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1)
    (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι : ℂ ≃+* ℂ_[ℓ]) :
    ∀ ε : ℂ_[ℓ], ε ∈ unramC ℓ → ‖ε‖ = 1 → IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) →
      IsHerm (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε) := by
  intro ε hεu hε ht
  obtain ⟨c, -, -, hc⟩ := be_simeq_serAB_cm' hj hu hs hd hd4 hcm hΔ h5 hdℓ hin ι
    UnramFrobLift.norm_frobUnram_sub_pow_le hεu hε ht
  exact (isHerm_C_mul_serAB _).of_simeq hc.symm

/-- **The classification for the CM curve from the classical CM inputs alone**: with CM-b, CM-c, CM-a′ and the
strengthened CM-d, the Lubin–Tate unit `ε` of CM-b has `be ≃ c·serAB` with `φ(c) = −c`, `‖c‖ ≤ 1`, for the Frobenius
lift `φ = UnramFrobLift.frobUnram ℓ` (`be_classification_cm'` with `isHerm_be_cm_classical`). -/
theorem be_classification_cm_classical (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified)
    (hs : CMs2Unram) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
    (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι : ℂ ≃+* ℂ_[ℓ]) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ c : unramC ℓ, UnramFrobLift.frobUnram ℓ c = -c ∧ ‖c‖ ≤ 1 ∧
      Simeq (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε) (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) :=
  be_classification_cm' hb hj hu hs hd hd4 hcm hΔ h5 hdℓ hin ι UnramFrobLift.norm_frobUnram_sub_pow_le
    (isHerm_be_cm_classical hj hu hs hd hd4 hcm hΔ h5 hdℓ hin ι)

end Classification

end

end CMTorsion
