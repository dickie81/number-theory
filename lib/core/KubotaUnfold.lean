import KubotaSiegel

/-! # Integrals over `Γ\H³`, and unfolding

`SL_2(ℤ[ω])` has a measurable partition of unity `ρ`. This file defines partitions of unity for every
subgroup `Γ`. It proves that `∫ρ·F dz dv/v³` does not depend on the choice, for `F` invariant under `Γ`.

* **Partitions of unity** (`IsPU`, a definition; `isPU_top` and `IsPU.tsum_inv`, with `lintegral_slAct`,
  `ae_UHS`, `slAct_inv_slAct` and `slAct_slAct_inv`): `IsPU Γ ρ` says that `ρ` is measurable and
  `Σ_{γ∈Γ} ρ(γ·p) = 1` for `v > 0`. `ρ` is one for the whole group.
* **Unfolding** (**`lintegral_unfold`**): `∫ρ·Σ_{γ∈Γ} Φ_γ dz dv/v³ = ∫Ψ dz dv/v³` when `Φ_γ(γ⁻¹·q) = Ψ(q)`
  for `v > 0`.
* **Independence** (**`lintegral_isPU_eq`**): `∫ρF = ∫ρ′F` for partitions of unity `ρ, ρ′` for `Γ` and `F`
  invariant under `Γ`.
* **Subgroups** (`outMul` and `puLe`, definitions, and the instance `countable_quot`; **`isPU_puLe`**, with
  `isPU_puLe_top`; **`lintegral_puLe`**): for `Γ′ ≤ Γ`, `Σ_{q∈Γ/Γ′} ρ(q·p)` is a partition of unity for `Γ′`,
  and with it `∫ρ′F = #(Γ/Γ′)·∫ρF`. For `Γ` of finite index in `SL_2(ℤ[ω])`, `∫ρ_Γ dz dv/v³ < ∞` is the case
  `F = 1` of `KubotaEisTrunc`'s `lintegral_puLe_top_mul_lt_top`.
* **Translates of `P`** (`tsum_fundP`): `Σ_{t∈ℤ[ω]} 1_P(w + σ(t)) = 1`.
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

theorem lintegral_slAct (γ : SL(2, 𝓞 K)) {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (slAct γ p) ∂uhsMeasure = ∫⁻ p, F p ∂uhsMeasure :=
  lintegral_actP (det_map_σO γ.2) hF

theorem ae_UHS : ∀ᵐ p ∂uhsMeasure, p ∈ UHS :=
  withDensity_absolutelyContinuous _ _ (ae_restrict_mem measurableSet_UHS)

theorem slAct_inv_slAct (γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    slAct γ⁻¹ (slAct γ p) = p := by
  rw [← slAct_mul _ _ hp, inv_mul_cancel, slAct_one]

theorem slAct_slAct_inv (γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    slAct γ (slAct γ⁻¹ p) = p := by
  rw [← slAct_mul _ _ hp, mul_inv_cancel, slAct_one]

/-- **A partition of unity for `Γ`**: measurable, with `Σ_{γ∈Γ} ρ(γ·p) = 1` on upper half-space. -/
def IsPU (Γ : Subgroup SL(2, 𝓞 K)) (ρ : ℂ × ℝ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ p ∈ UHS, ∑' γ : Γ, ρ (slAct γ p) = 1

/-- `ρ` is a partition of unity for the whole group. -/
theorem isPU_top : IsPU ⊤ rhoK := by
  refine ⟨measurable_rhoK, fun p hp => ?_⟩
  rw [← tsum_rhoK hp]
  exact (Equiv.subtypeUnivEquiv Subgroup.mem_top).tsum_eq (fun γ => rhoK (slAct γ p))

/-- `Σ_{γ∈Γ} ρ(γ⁻¹·p) = 1` as well. -/
theorem IsPU.tsum_inv {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ) {p : ℂ × ℝ}
    (hp : p ∈ UHS) : ∑' γ : Γ, ρ (slAct (γ⁻¹ : Γ) p) = 1 := by
  rw [← hρ.2 p hp]
  exact (Equiv.inv Γ).tsum_eq (fun γ => ρ (slAct γ p))

/-- **Unfolding**: `∫ρ·Σ_{γ∈Γ} Φ_γ = ∫Ψ` when `Φ_γ(γ⁻¹·q) = Ψ(q)`. -/
theorem lintegral_unfold {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    {Φ : Γ → ℂ × ℝ → ℝ≥0∞} {Ψ : ℂ × ℝ → ℝ≥0∞} (hΦ : ∀ γ, Measurable (Φ γ)) (hΨ : Measurable Ψ)
    (h : ∀ γ : Γ, ∀ q ∈ UHS, Φ γ (slAct (γ⁻¹ : Γ) q) = Ψ q) :
    ∫⁻ p, ρ p * ∑' γ, Φ γ p ∂uhsMeasure = ∫⁻ q, Ψ q ∂uhsMeasure := by
  have h1 : ∀ γ : Γ, ∫⁻ p, ρ p * Φ γ p ∂uhsMeasure =
      ∫⁻ q, ρ (slAct (γ⁻¹ : Γ) q) * Ψ q ∂uhsMeasure := by
    intro γ
    rw [← lintegral_slAct (γ⁻¹ : Γ) (F := fun p => ρ p * Φ γ p) (hρ.1.mul (hΦ γ))]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with q hq
    rw [h γ q hq]
  calc ∫⁻ p, ρ p * ∑' γ, Φ γ p ∂uhsMeasure = ∫⁻ p, ∑' γ, ρ p * Φ γ p ∂uhsMeasure := by
        simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' γ, ∫⁻ p, ρ p * Φ γ p ∂uhsMeasure :=
        lintegral_tsum fun γ => (hρ.1.mul (hΦ γ)).aemeasurable
    _ = ∑' γ : Γ, ∫⁻ q, ρ (slAct (γ⁻¹ : Γ) q) * Ψ q ∂uhsMeasure := tsum_congr h1
    _ = ∫⁻ q, ∑' γ : Γ, ρ (slAct (γ⁻¹ : Γ) q) * Ψ q ∂uhsMeasure :=
        (lintegral_tsum fun γ => ((hρ.1.comp (measurable_slAct _)).mul hΨ).aemeasurable).symm
    _ = ∫⁻ q, Ψ q ∂uhsMeasure := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_UHS] with q hq
        rw [ENNReal.tsum_mul_right, hρ.tsum_inv hq, one_mul]

/-- **The integral over `Γ\H³` does not depend on the partition of unity.** -/
theorem lintegral_isPU_eq {Γ : Subgroup SL(2, 𝓞 K)} {ρ ρ' : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    (hρ' : IsPU Γ ρ') {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ UHS, F (slAct γ p) = F p) :
    ∫⁻ p, ρ p * F p ∂uhsMeasure = ∫⁻ p, ρ' p * F p ∂uhsMeasure := by
  have e : ∫⁻ p, ρ p * F p ∂uhsMeasure =
      ∫⁻ p, ρ p * ∑' γ : Γ, ρ' (slAct γ p) * F p ∂uhsMeasure := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with p hp
    rw [ENNReal.tsum_mul_right, hρ'.2 p hp, one_mul]
  rw [e]
  refine lintegral_unfold hρ (fun γ => (hρ'.1.comp (measurable_slAct _)).mul hF) (hρ'.1.mul hF)
    fun γ q hq => ?_
  rw [Subgroup.coe_inv, slAct_slAct_inv _ hq, hinv _ (Γ.inv_mem γ.2) q hq]

/-- `(q, h) ↦ q.out·h`, a bijection `(α ⧸ s) × s ≃ α`. -/
def outMul {α : Type*} [Group α] (s : Subgroup α) : (α ⧸ s) × s ≃ α :=
  Equiv.ofBijective (fun x => x.1.out * x.2)
    ⟨fun x y hxy => by
      have h1 : x.1 = y.1 := by
        have := congrArg (QuotientGroup.mk (s := s)) hxy
        simp only [QuotientGroup.mk_mul_of_mem _ x.2.2, QuotientGroup.mk_mul_of_mem _ y.2.2,
          QuotientGroup.out_eq'] at this
        exact this
      have hxy' : y.1.out * (x.2 : α) = y.1.out * y.2 := by simpa only [h1] using hxy
      exact Prod.ext h1 (Subtype.ext (mul_left_cancel hxy')),
    fun g => by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul s g
      exact ⟨(QuotientGroup.mk g, h⁻¹), by simp [hh]⟩⟩

instance countable_quot (Γ : Subgroup SL(2, 𝓞 K)) (H : Subgroup Γ) : Countable (Γ ⧸ H) :=
  QuotientGroup.mk_surjective.countable

/-- **A partition of unity for a subgroup** `Γ′ ≤ Γ`: `Σ_{q∈Γ/Γ′} ρ(q·p)`. -/
def puLe (Γ Γ' : Subgroup SL(2, 𝓞 K)) (ρ : ℂ × ℝ → ℝ≥0∞) (p : ℂ × ℝ) : ℝ≥0∞ :=
  ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ρ (slAct (q.out : SL(2, 𝓞 K)) p)

theorem isPU_puLe {Γ Γ' : Subgroup SL(2, 𝓞 K)} (hle : Γ' ≤ Γ) {ρ : ℂ × ℝ → ℝ≥0∞}
    (hρ : IsPU Γ ρ) : IsPU Γ' (puLe Γ Γ' ρ) := by
  refine ⟨Measurable.tsum fun q => hρ.1.comp (measurable_slAct _), fun p hp => ?_⟩
  unfold puLe
  rw [← hρ.2 p hp]
  calc ∑' γ' : Γ', ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ρ (slAct (q.out : SL(2, 𝓞 K)) (slAct γ' p))
      = ∑' c : Γ'.subgroupOf Γ, ∑' q : Γ ⧸ Γ'.subgroupOf Γ,
          ρ (slAct ((q.out * c : Γ) : SL(2, 𝓞 K)) p) := by
        rw [← (Subgroup.subgroupOfEquivOfLe hle).toEquiv.tsum_eq]
        refine tsum_congr fun c => tsum_congr fun q => ?_
        rw [Subgroup.coe_mul, slAct_mul _ _ hp]
        rfl
    _ = ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ∑' c : Γ'.subgroupOf Γ,
          ρ (slAct ((q.out * c : Γ) : SL(2, 𝓞 K)) p) := ENNReal.tsum_comm
    _ = ∑' x : (Γ ⧸ Γ'.subgroupOf Γ) × Γ'.subgroupOf Γ,
          ρ (slAct ((x.1.out * x.2 : Γ) : SL(2, 𝓞 K)) p) := ENNReal.tsum_prod.symm
    _ = ∑' γ : Γ, ρ (slAct (γ : SL(2, 𝓞 K)) p) :=
        (outMul _).tsum_eq (fun γ : Γ => ρ (slAct (γ : SL(2, 𝓞 K)) p))

/-- Every subgroup has a partition of unity: `Σ_{q ∈ SL_2(ℤ[ω])/Γ} ρ(q·p)`, from `ρ`. -/
theorem isPU_puLe_top (Γ : Subgroup SL(2, 𝓞 K)) : IsPU Γ (puLe ⊤ Γ rhoK) :=
  isPU_puLe le_top isPU_top

/-- **The index**: `∫ρ′F = [Γ : Γ′]·∫ρF` for `ρ′ = Σ_{q∈Γ/Γ′} ρ(q·)` and `F` invariant under `Γ`. -/
theorem lintegral_puLe {Γ Γ' : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) (hinv : ∀ γ ∈ Γ, ∀ p ∈ UHS, F (slAct γ p) = F p) :
    ∫⁻ p, puLe Γ Γ' ρ p * F p ∂uhsMeasure =
      ENat.card (Γ ⧸ Γ'.subgroupOf Γ) * ∫⁻ p, ρ p * F p ∂uhsMeasure := by
  have h1 : ∀ q : Γ ⧸ Γ'.subgroupOf Γ, ∫⁻ p, ρ (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure =
      ∫⁻ p, ρ p * F p ∂uhsMeasure := by
    intro q
    rw [← lintegral_slAct (q.out : SL(2, 𝓞 K)) (F := fun p => ρ p * F p) (hρ.1.mul hF)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with p hp
    rw [hinv _ q.out.2 p hp]
  unfold puLe
  simp_rw [← ENNReal.tsum_mul_right]
  calc ∫⁻ p, ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ρ (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure
      = ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ∫⁻ p, ρ (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure :=
        lintegral_tsum fun q => ((hρ.1.comp (measurable_slAct _)).mul hF).aemeasurable
    _ = ∑' _q : Γ ⧸ Γ'.subgroupOf Γ, ∫⁻ p, ρ p * F p ∂uhsMeasure := tsum_congr h1
    _ = _ := ENNReal.tsum_const _

/-- **Translates of `P`**: `Σ_{t∈ℤ[ω]} 1_P(w + σ(t)) = 1`. -/
theorem tsum_fundP (w : ℂ) : ∑' t : 𝓞 K, fundP.indicator (1 : ℂ → ℝ≥0∞) (w + σO t) = 1 := by
  obtain ⟨t₀, ht₀⟩ := exists_transl_mem_fundP w
  rw [tsum_eq_single t₀ fun t ht => ?_]
  · rw [Set.indicator_of_mem ht₀, Pi.one_apply]
  · refine Set.indicator_of_notMem (fun h => ht ?_) _
    have e : w + σO t₀ + σO (t - t₀) = w + σO t := by rw [map_sub]; ring
    have := eq_zero_of_mem_fundP ht₀ (by rw [e]; exact h)
    exact sub_eq_zero.1 this

end Eis

end

#print axioms Eis.lintegral_slAct
#print axioms Eis.ae_UHS
#print axioms Eis.slAct_inv_slAct
#print axioms Eis.slAct_slAct_inv
#print axioms Eis.isPU_top
#print axioms Eis.IsPU.tsum_inv
#print axioms Eis.lintegral_unfold
#print axioms Eis.lintegral_isPU_eq
#print axioms Eis.isPU_puLe
#print axioms Eis.isPU_puLe_top
#print axioms Eis.lintegral_puLe
#print axioms Eis.tsum_fundP
