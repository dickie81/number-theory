import CMFormalGauss

/-!
# CM equivariance for `ω`, and the classification `be ≃ c·serAB` without the hermitian input

D1b-5 of the D1b plan: the hermitian input of the classification (`CMFormalBiadd.IsHerm (be …)`, the hypothesis
`hH` of `CMFormalGauss.be_classification_cm'`) is proved from the CM equivariance of the single global
`ω = (1 + √−d)/2`, a unit at the inert `ℓ`; no Teichmüller density argument. Notation: `N = N(ω) = (1 + d)/4`, `Λ`
the `Δ = 1` CM lattice, `σ*` Masser's normalised sigma (`sgStar`), `L = log_LT`, `[α]T = e(α·L(T))` (`mulLT`).

**The kernel of `[ω]`.** `ω² − ω + N = 0`, `ω̄ω = N`, `ωΛ ⊆ Λ` (`HasCM`), and `[ω⁻¹Λ : Λ] = N`: the matrix of `ω` in
a basis of `Λ` has `(ω₁, ω₂)` in the kernel of `M − ω`, so, as `ω ∉ ℝ`, its trace is `1` and its determinant `N`
(`relIndex_omInvLat`, by `AddSubgroup.relIndex_eq_natAbs_det`). Representatives `Q` of `(ω⁻¹Λ ∖ Λ)/Λ` exist
(`exists_kerReps`) and have `N − 1` elements (`card_kerReps`).

**The CM product formula** (`sgStar_omK0_mul`): `σ*(ωz) = ω·σ*(z)^N·∏_{q ∈ Q} G_q(z)` off `Λ`.
* `σ*(z + l) = κ·e^{(π/A)l̄z}·σ*(z)` with `κ² = e^{(π/A)l̄l}` (`sgStar_add_lattice`: put `z = −l/2` if `l/2 ∉ Λ`,
  otherwise split `l = (l + ω₁) − ω₁`; the area form `l̄₁l₂ − l̄₂l₁ ∈ 2iAℤ` kills the cross term).
* Division by an entire function with simple zeros (`exists_eq_mul_of_simple`), applied to the factors `σ_W(z + q)`,
  `q ∈ {0} ∪ Q`, whose zeros `−q + Λ` partition `ω⁻¹Λ` (`exists_sgStar_omK0_factor`).
* The quotient `R` of the two sides is entire, with the multiplier `κ(ωl)/(κ(l)^N·∏_q e^{η(l)q − η(q)l})` along a
  period: the Gaussian factors cancel as `ω̄ω = N`, and the multiplier is unimodular (`κ(ωl)² = (κ(l)^N)²`, and the
  factors of `G_q` are `N`-th roots of unity). So `|R|` is periodic, `R` is constant (Liouville), and `R(0) = 1` as
  `σ*(ωz) ∼ ωz`, `z·G_q(z) → 1`. Either orientation of the periods (`swapPair`); near `0`, `sigE_omK0_mul`.

**`ι(ω) ∈ K^ur`** (`iota_omK0_mem`): square roots of prime-to-`ℓ` integers lie in `K^ur` (`mem_unramC_of_sq`). A
Teichmüller `y₀` has `‖y₀² − c‖ < 1` (a factor of `c^m − 1 = ∏_{w^m = 1}(c − w)` is small, `m = (ℓ² − 1)/2`), and
Newton's iteration stays in the closed `K^ur`, with `±y_n → x`. `ι(ω)` is a unit at an inert `ℓ` (`norm_iota_omK0`),
and `φ²(ι ω) = ι ω` for every endomorphism `φ` of `K^ur` (`phi_phi_iota_omK0`).

**The endomorphism `[α]`** (`mulLT`): `L([α]A) = α·L(A)` (`lgP_subst_mulLT`), `[α](A ⊕ B) = [α]A ⊕ [α]B`
(`mulLT_subst_addP`), `[α](ζT) = ζ·[α]T` for Teichmüller `ζ` (`rescale_mulLT_teich`); `[α]` is integral for `α` in a
subfield with a Frobenius lift, `‖α‖ ≤ 1`, `φ²α = α` (Hazewinkel, `isInt_mulLT`).

**CM equivariance** (`cm_equiv`): `ph([ω]T) ≃ N·ph(T)`. In Lubin–Tate coordinates the product formula near `0` reads
`exp(N·ph(T) − ph([ω]T))·([ω]T/T) = ω·∏_{q ∈ Q} U_q(T)`, with the translates `U_q = εT·G_q(ε·L(T))` integral units
(`isInt_translate`, its hypotheses from the input `TorsionTransl`).

**The classification** (`be_simeq_serAB_cm`). The structure theorem gives `be ≃ a·L(X)L(Y) + γ·serAB`. The polarised
equivariance gives `be([ω]X, [ω]Y) ≃ N·be`, while `be([ω]X, [ω]Y) ≃ aω²·L(X)L(Y) + B₂`, where
`B₂ = (γ·serAB)([ω]X, [ω]Y)` is symmetric, biadditive (`deltaX_subst_mulPair`), has coefficients in `K^ur`
(`coeff_subst_mem`) and is hermitian (`IsHerm.subst_mulPair`), so `B₂ ≃ γ₂·serAB`. Uniqueness of the pair
(`alpha_eq_zero_iff` at `B = 0`) gives `a(N − ω²) = 0`, so `a = 0`. Hence `IsHerm (be …)` (`isHerm_be_cm`) and the
classification without the hermitian input (`be_classification_cm_omega`).

**Inputs.** Besides CM-a′/c/d (CM-b only for the existence of `ε`): the torsion arithmetic `TorsionTransl` and a
Frobenius lift on `K^ur` (`UnramFrob`, or `φ` with `hφ`).

**Main results:** `relIndex_omInvLat`, `card_kerReps`, `sgStar_add_lattice`, `sgStar_omK0_mul`, `sigE_omK0_mul`,
`iota_omK0_mem`, `isInt_mulLT`, `cm_equiv`, `be_simeq_serAB_cm`, `isHerm_be_cm`, `be_classification_cm_omega`; the
definitions `omK0`, `KerReps`, `mulLT`, `TorsionTransl`, `UnramFrob`.
-/

namespace CMEquiv

open PowerSeries CMFormalInert CMFormalBiadd CMFormalGauss

noncomputable section

/-! ## The CM unit `ω` and the kernel of `[ω]` -/

section Omega

open PeriodPair ThetaNorm

/-- **`ω = (1 + i√d)/2`** as a complex number (the generator in `HasCM`). -/
def omK0 (d : ℕ) : ℂ := (1 + Complex.I * (Real.sqrt d : ℂ)) / 2

/-- **`HasCM` says `ωΛ ⊆ Λ`.** -/
theorem omK0_mul_mem {d : ℕ} {Λ : PeriodPair} (hcm : HasCM d Λ) {z : ℂ} (hz : z ∈ Λ.lattice) :
    omK0 d * z ∈ Λ.lattice :=
  hcm z hz

/-- **`(1 + d)/4` as a complex number**, for `d ≡ 3 (mod 4)`. -/
theorem natCast_normOm {d : ℕ} (hd4 : d % 4 = 3) : (((1 + d) / 4 : ℕ) : ℂ) = (1 + d) / 4 := by
  rw [Nat.cast_div (by omega) (by norm_num)]
  push_cast
  ring

/-- **`√d² = d`** in `ℂ`. -/
theorem sqrt_sq_complex (d : ℕ) : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

/-- **`ω² − ω + N(ω) = 0`**, `N(ω) = (1 + d)/4`. -/
theorem omK0_sq {d : ℕ} (hd4 : d % 4 = 3) : omK0 d ^ 2 - omK0 d + (((1 + d) / 4 : ℕ) : ℂ) = 0 := by
  rw [natCast_normOm hd4, omK0]
  linear_combination (Complex.I ^ 2 / 4) * sqrt_sq_complex d + ((d : ℂ) / 4) * Complex.I_sq

/-- **The real part of `ω`.** -/
theorem omK0_re (d : ℕ) : (omK0 d).re = 1 / 2 := by
  simp [omK0]

/-- **The imaginary part of `ω`.** -/
theorem omK0_im (d : ℕ) : (omK0 d).im = Real.sqrt d / 2 := by
  simp [omK0]

/-- **`ω` is not real** for `d ≠ 0`. -/
theorem omK0_im_ne_zero {d : ℕ} (hd : d ≠ 0) : (omK0 d).im ≠ 0 := by
  rw [omK0_im]
  have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hd)
  positivity

/-- **`ω ≠ 0`.** -/
theorem omK0_ne_zero (d : ℕ) : omK0 d ≠ 0 := fun h => by
  have := congrArg Complex.re h
  rw [omK0_re, Complex.zero_re] at this
  norm_num at this

/-- **`ω̄ = 1 − ω`.** -/
theorem conj_omK0 (d : ℕ) : starRingEnd ℂ (omK0 d) = 1 - omK0 d := by
  apply Complex.ext <;> simp [omK0_re, omK0_im, Complex.conj_re, Complex.conj_im]; norm_num

/-- **`ω̄ω = N(ω)`.** -/
theorem conj_omK0_mul {d : ℕ} (hd4 : d % 4 = 3) :
    starRingEnd ℂ (omK0 d) * omK0 d = (((1 + d) / 4 : ℕ) : ℂ) := by
  rw [conj_omK0]
  linear_combination -omK0_sq hd4

/-- **`ω̄Λ ⊆ Λ`**, so `N(ω)·q ∈ Λ` whenever `ωq ∈ Λ`. -/
theorem natCast_normOm_mul_mem {d : ℕ} {Λ : PeriodPair} (hd4 : d % 4 = 3) (hcm : HasCM d Λ) {q : ℂ}
    (hq : omK0 d * q ∈ Λ.lattice) : (((1 + d) / 4 : ℕ) : ℂ) * q ∈ Λ.lattice := by
  rw [← conj_omK0_mul hd4, conj_omK0, mul_assoc, sub_mul, one_mul]
  exact sub_mem hq (omK0_mul_mem hcm hq)

/-- **`N(ω)` is prime to an inert `ℓ`**: if `ℓ ∣ (1 + d)/4`, then `−d ≡ 1` would be a square mod `ℓ`. -/
theorem not_dvd_normOm {ℓ d : ℕ} (hd4 : d % 4 = 3) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) :
    ¬ ℓ ∣ (1 + d) / 4 := by
  rintro ⟨k, hk⟩
  refine hin ⟨1, ?_⟩
  have h : (1 + d : ℕ) = ℓ * (4 * k) := by
    have h0 : 1 + d = 4 * (ℓ * k) := by omega
    rw [h0]
    ring
  have h' : ((1 + d : ℕ) : ZMod ℓ) = 0 := by rw [h, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  push_cast at h'
  linear_combination h'

/-- **The lattice `ω⁻¹Λ`** of points killed by `[ω]` modulo `Λ`: `{z : ωz ∈ Λ}`. -/
def omInvLat (d : ℕ) (Λ : PeriodPair) : AddSubgroup ℂ :=
  Λ.lattice.toAddSubgroup.comap (AddMonoidHom.mulLeft (omK0 d))

/-- **A lattice point in coordinates**: `x = a·ω₁ + b·ω₂` with the coordinates of `latticeBasis`. -/
theorem coe_eq_repr (Λ : PeriodPair) (x : Λ.lattice) :
    (x : ℂ) = (Λ.latticeBasis.repr x 0 : ℂ) * Λ.ω₁ + (Λ.latticeBasis.repr x 1 : ℂ) * Λ.ω₂ := by
  conv_lhs => rw [← Λ.latticeBasis.sum_repr x]
  rw [Submodule.coe_sum, Fin.sum_univ_two, Submodule.coe_smul, Submodule.coe_smul, latticeBasis_zero,
    latticeBasis_one, zsmul_eq_mul, zsmul_eq_mul]

/-- **The index `[ω⁻¹Λ : Λ] = N(ω)`**: in the basis `(ω₁, ω₂)`, `[ω]` has a matrix `M` with `(ω₁, ω₂)` in the kernel
of `M − ω`, so `ω` (and `ω̄`) is a root of `x² − tr(M)x + det(M)`; as `ω ∉ ℝ`, `tr M = ω + ω̄ = 1` and
`det M = ω − ω² = N(ω)` (`AddSubgroup.relIndex_eq_natAbs_det` with the bases `ω_i` and `ω⁻¹ω_i`). -/
theorem relIndex_omInvLat {d : ℕ} {Λ : PeriodPair} (hd : d ≠ 0) (hd4 : d % 4 = 3) (hcm : HasCM d Λ) :
    Λ.lattice.toAddSubgroup.relIndex (omInvLat d Λ) = (1 + d) / 4 := by
  have hω := omK0_ne_zero d
  set ω := omK0 d with hωdef
  let e : Λ.lattice ≃ₗ[ℤ] (omInvLat d Λ).toIntSubmodule :=
    { toFun := fun x => ⟨ω⁻¹ * x, by
        change ω * (ω⁻¹ * (x : ℂ)) ∈ Λ.lattice
        rw [mul_inv_cancel_left₀ hω]
        exact x.2⟩
      invFun := fun y => ⟨ω * y, y.2⟩
      left_inv := fun x => Subtype.ext (by simp [hω])
      right_inv := fun y => Subtype.ext (by simp [hω])
      map_add' := fun x y => Subtype.ext (by simp [mul_add])
      map_smul' := fun n x => Subtype.ext (by simp [zsmul_eq_mul]; ring) }
  let e' : Λ.lattice ≃ₗ[ℤ] Λ.lattice.toAddSubgroup.toIntSubmodule :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun y => ⟨y, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have H : Λ.lattice.toAddSubgroup ≤ omInvLat d Λ := fun z hz => omK0_mul_mem hcm hz
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ H (Λ.latticeBasis.map e') (Λ.latticeBasis.map e),
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]
  set x₁ : Λ.lattice := ⟨ω * Λ.ω₁, omK0_mul_mem hcm Λ.ω₁_mem_lattice⟩
  set x₂ : Λ.lattice := ⟨ω * Λ.ω₂, omK0_mul_mem hcm Λ.ω₂_mem_lattice⟩
  have e1 : e.symm ⟨(Λ.latticeBasis.map e' 0 : ℂ), H (Λ.latticeBasis.map e' 0).2⟩ = x₁ := Subtype.ext (by
    change ω * ((Λ.latticeBasis 0 : Λ.lattice) : ℂ) = ω * Λ.ω₁
    rw [latticeBasis_zero])
  have e2 : e.symm ⟨(Λ.latticeBasis.map e' 1 : ℂ), H (Λ.latticeBasis.map e' 1).2⟩ = x₂ := Subtype.ext (by
    change ω * ((Λ.latticeBasis 1 : Λ.lattice) : ℂ) = ω * Λ.ω₂
    rw [latticeBasis_one])
  rw [e1, e2]
  set a := Λ.latticeBasis.repr x₁ 0
  set b := Λ.latticeBasis.repr x₁ 1
  set c := Λ.latticeBasis.repr x₂ 0
  set d' := Λ.latticeBasis.repr x₂ 1
  have h1 : ω * Λ.ω₁ = a * Λ.ω₁ + b * Λ.ω₂ := coe_eq_repr Λ x₁
  have h2 : ω * Λ.ω₂ = c * Λ.ω₁ + d' * Λ.ω₂ := coe_eq_repr Λ x₂
  have hP : (((a : ℂ) - ω) * (d' - ω) - b * c) * Λ.ω₁ = 0 := by
    linear_combination -((d' : ℂ) - ω) * h1 + (b : ℂ) * h2
  have hP' : ((a : ℂ) - ω) * (d' - ω) - b * c = 0 :=
    (mul_eq_zero.1 hP).resolve_right (Λ.indep.ne_zero 0)
  have hω2 := omK0_sq hd4
  generalize (1 + d) / 4 = N at hω2 ⊢
  have h3 : (((1 - (a + d') : ℤ) : ℂ)) * ω + (((a * d' - c * b - N : ℤ) : ℂ)) = 0 := by
    push_cast
    linear_combination hP' - hω2
  have him := congrArg Complex.im h3
  have hre := congrArg Complex.re h3
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
    Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re, sub_zero] at him hre
  have htr : ((1 - (a + d') : ℤ) : ℝ) = 0 :=
    (mul_eq_zero.1 him).resolve_right (omK0_im_ne_zero hd)
  rw [htr, zero_mul, zero_add] at hre
  have hdet : a * d' - c * b - N = 0 := by exact_mod_cast hre
  rw [show a * d' - c * b = N by linarith]
  simp

/-- **Representatives of the nonzero kernel of `[ω]`**: a finite set `Q` of representatives of `(ω⁻¹Λ ∖ Λ)/Λ`. -/
def KerReps (ω : ℂ) (Λ : PeriodPair) (Q : Finset ℂ) : Prop :=
  (∀ q ∈ Q, q ∉ Λ.lattice ∧ ω * q ∈ Λ.lattice) ∧ (∀ q ∈ Q, ∀ q' ∈ Q, q - q' ∈ Λ.lattice → q = q') ∧
    ∀ z : ℂ, z ∉ Λ.lattice → ω * z ∈ Λ.lattice → ∃ q ∈ Q, z - q ∈ Λ.lattice

/-- **`N(ω) ≥ 1`.** -/
theorem normOm_pos {d : ℕ} (hd4 : d % 4 = 3) : 0 < (1 + d) / 4 := by omega

/-- **The kernel of `[ω]` has `N(ω)` elements**: any set of representatives of its nonzero classes has
`N(ω) − 1` elements (`relIndex_omInvLat`). -/
theorem card_kerReps {d : ℕ} {Λ : PeriodPair} (hd : d ≠ 0) (hd4 : d % 4 = 3) (hcm : HasCM d Λ) {Q : Finset ℂ}
    (hQ : KerReps (omK0 d) Λ Q) : Q.card = (1 + d) / 4 - 1 := by
  classical
  set H := Λ.lattice.toAddSubgroup.addSubgroupOf (omInvLat d Λ)
  have hcardq : Nat.card (omInvLat d Λ ⧸ H) = (1 + d) / 4 := relIndex_omInvLat hd hd4 hcm
  have : Finite (omInvLat d Λ ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcardq]; exact (normOm_pos hd4).ne')
  let _ := Fintype.ofFinite (omInvLat d Λ ⧸ H)
  rw [Nat.card_eq_fintype_card] at hcardq
  rw [← hcardq, ← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ (0 : omInvLat d Λ ⧸ H))]
  refine Finset.card_bij (fun q hq => (QuotientAddGroup.mk ⟨q, (hQ.1 q hq).2⟩ : omInvLat d Λ ⧸ H))
    (fun q hq => ?_) (fun q hq q' hq' h => ?_) (fun c hc => ?_)
  · rw [Finset.mem_erase, Ne, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨(hQ.1 q hq).1, Finset.mem_univ _⟩
  · rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    refine (hQ.2.1 q' hq' q hq ?_).symm
    simpa [sub_eq_neg_add] using h
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    have hy : (y : ℂ) ∉ Λ.lattice := fun h => (Finset.mem_erase.1 hc).1
      ((QuotientAddGroup.eq_zero_iff _).2 ((AddSubgroup.mem_addSubgroupOf).2 h))
    obtain ⟨q, hq, hyq⟩ := hQ.2.2 y hy y.2
    refine ⟨q, hq, (QuotientAddGroup.eq).2 ((AddSubgroup.mem_addSubgroupOf).2 ?_)⟩
    simpa [sub_eq_neg_add] using hyq

/-- **Representatives of the nonzero kernel exist**: the representatives `out c` of the nonzero classes of
`ω⁻¹Λ/Λ`, a finite group (`relIndex_omInvLat`). -/
theorem exists_kerReps {d : ℕ} {Λ : PeriodPair} (hd : d ≠ 0) (hd4 : d % 4 = 3) (hcm : HasCM d Λ) :
    ∃ Q : Finset ℂ, KerReps (omK0 d) Λ Q := by
  classical
  set H := Λ.lattice.toAddSubgroup.addSubgroupOf (omInvLat d Λ)
  have hcardq : Nat.card (omInvLat d Λ ⧸ H) = (1 + d) / 4 := relIndex_omInvLat hd hd4 hcm
  have : Finite (omInvLat d Λ ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcardq]; exact (normOm_pos hd4).ne')
  let _ := Fintype.ofFinite (omInvLat d Λ ⧸ H)
  have hmem : ∀ c : omInvLat d Λ ⧸ H, ((c.out : omInvLat d Λ) : ℂ) ∈ Λ.lattice ↔ c = 0 := fun c => by
    rw [← Submodule.mem_toAddSubgroup, ← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff,
      QuotientAddGroup.out_eq']
  unfold KerReps
  refine ⟨(Finset.univ.erase (0 : omInvLat d Λ ⧸ H)).image fun c => ((c.out : omInvLat d Λ) : ℂ), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨fun h => (Finset.mem_erase.1 hc).1 ((hmem c).1 h), (c.out : omInvLat d Λ).2⟩
  · intro q hq q' hq' h
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hq'
    have hcc : c = c' := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf]
      simpa [sub_eq_neg_add] using neg_mem h
    rw [hcc]
  · intro z hz hωz
    set c : omInvLat d Λ ⧸ H := QuotientAddGroup.mk ⟨z, hωz⟩
    have hc : c ≠ 0 := fun h => hz ((AddSubgroup.mem_addSubgroupOf).1 ((QuotientAddGroup.eq_zero_iff _).1 h))
    refine ⟨_, Finset.mem_image.2 ⟨c, Finset.mem_erase.2 ⟨hc, Finset.mem_univ _⟩, rfl⟩, ?_⟩
    have h := QuotientAddGroup.out_eq' c
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    simpa [sub_eq_neg_add] using h

end Omega

/-! ## The quasi-periodicity of `σ*` -/

section SgStar

open PeriodPair ThetaNorm EllipticAdd EllipticDivisor EllipticLegendre CMThetaOne

variable (Λ : PeriodPair)

/-- **`σ*` is odd.** -/
theorem sgStar_neg (z : ℂ) : sgStar Λ (-z) = -sgStar Λ z := by
  simp only [sgStar, sigmaW_neg, neg_sq, neg_mul]

/-- **`σ*` vanishes only on the lattice.** -/
theorem sgStar_ne_zero {z : ℂ} (hz : z ∉ Λ.lattice) : sgStar Λ z ≠ 0 :=
  mul_ne_zero (sigmaW_ne_zero Λ hz) (Complex.exp_ne_zero _)

/-- **The multiplier relation of `σ*`** along a period `l` with factor `κ`:
`σ*(z + l) = κ·e^{(π/A)l̄z}·σ*(z)`. -/
def SgMult (l κ : ℂ) : Prop :=
  ∀ z, sgStar Λ (z + l) = κ * Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ l * z) * sgStar Λ z

/-- **`σ*` has a multiplier along every period** (`sigmaW_add_lattice` with Masser's `η(l) = s₂l + (π/A)l̄`). -/
theorem exists_sgMult (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {l : ℂ} (hl : l ∈ Λ.lattice) : ∃ κ, SgMult Λ l κ := by
  obtain ⟨c, -, hσ⟩ := sigmaW_add_lattice Λ hl (η := etaR Λ l) fun z hz => zetaW_add_lattice Λ legendre hor hl hz
  refine ⟨c * Complex.exp (-(s2 Λ) * l ^ 2 / 2), fun z => ?_⟩
  simp only [sgStar]
  rw [hσ]
  have he : Complex.exp (etaR Λ l * z) * Complex.exp (-(s2 Λ) * (z + l) ^ 2 / 2) =
      Complex.exp (-(s2 Λ) * l ^ 2 / 2) *
        Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ l * z) * Complex.exp (-(s2 Λ) * z ^ 2 / 2) := by
    simp only [← Complex.exp_add, etaR]
    ring_nf
  linear_combination c * sigmaW Λ z * he

/-- **The multiplier of a period whose half is not a period**: `κ = −e^{(π/A)l̄l/2}` (put `z = −l/2`), so
`κ² = e^{(π/A)l̄l}`. -/
theorem SgMult.sq_of_half {l κ : ℂ} (h : SgMult Λ l κ) (hl2 : l / 2 ∉ Λ.lattice) :
    κ ^ 2 = Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ l * l) := by
  have e := h (-(l / 2))
  rw [show -(l / 2) + l = l / 2 by ring, sgStar_neg] at e
  set c := ((Real.pi / area Λ : ℝ) : ℂ)
  have hs := sgStar_ne_zero Λ hl2
  have hκ : κ * Complex.exp (c * starRingEnd ℂ l * -(l / 2)) = -1 := by
    refine mul_right_cancel₀ hs ?_
    linear_combination e
  have hE : Complex.exp (c * starRingEnd ℂ l * -(l / 2)) ^ 2 * Complex.exp (c * starRingEnd ℂ l * l) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    push_cast
    ring_nf
    exact Complex.exp_zero
  linear_combination (Complex.exp (c * starRingEnd ℂ l * l) * (κ * Complex.exp (c * starRingEnd ℂ l * -(l / 2)) - 1))
    * hκ - κ ^ 2 * hE

/-- **Multipliers compose**: `κ(l₁ + l₂) = κ(l₁)κ(l₂)e^{(π/A)l̄₁l₂}`. -/
theorem SgMult.add {l₁ l₂ κ₁ κ₂ : ℂ} (h₁ : SgMult Λ l₁ κ₁) (h₂ : SgMult Λ l₂ κ₂) :
    SgMult Λ (l₁ + l₂)
      (κ₁ * κ₂ * Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ l₁ * l₂)) := by
  intro z
  set c := ((Real.pi / area Λ : ℝ) : ℂ)
  rw [show z + (l₁ + l₂) = z + l₂ + l₁ by ring, h₁, h₂, map_add]
  have he : Complex.exp (c * starRingEnd ℂ l₁ * (z + l₂)) * Complex.exp (c * starRingEnd ℂ l₂ * z) =
      Complex.exp (c * starRingEnd ℂ l₁ * l₂) * Complex.exp (c * (starRingEnd ℂ l₁ + starRingEnd ℂ l₂) * z) := by
    simp only [← Complex.exp_add]
    ring_nf
  linear_combination κ₁ * κ₂ * sgStar Λ z * he

/-- **The quasi-periodicity of `σ*` with its multiplier squared**: `σ*(z + l) = κ·e^{(π/A)l̄z}·σ*(z)` with
`κ² = e^{(π/A)l̄l}` (so `κ = ±e^{(π/A)|l|²/2}`). If `l/2` is a period, write `l = (l + ω₁) + (−ω₁)`; the area form
`l̄₁l₂ − l̄₂l₁ ∈ 2iAℤ` makes the cross term a root of unity of order one. -/
theorem sgStar_add_lattice (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {l : ℂ} (hl : l ∈ Λ.lattice) :
    ∃ κ : ℂ, κ ^ 2 = Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ l * l) ∧ SgMult Λ l κ := by
  by_cases hl2 : l / 2 ∈ Λ.lattice
  · set l₁ := l + Λ.ω₁
    set l₂ := -Λ.ω₁
    have hl₁ : l₁ ∈ Λ.lattice := add_mem hl Λ.ω₁_mem_lattice
    have hl₂ : l₂ ∈ Λ.lattice := neg_mem Λ.ω₁_mem_lattice
    have h₁2 : l₁ / 2 ∉ Λ.lattice := fun h => Λ.ω₁_div_two_notMem_lattice (by
      rw [show Λ.ω₁ / 2 = l₁ / 2 - l / 2 by ring]; exact sub_mem h hl2)
    have h₂2 : l₂ / 2 ∉ Λ.lattice := fun h => Λ.ω₁_div_two_notMem_lattice (by
      rw [show Λ.ω₁ / 2 = -(l₂ / 2) by ring]; exact neg_mem h)
    obtain ⟨κ₁, hκ₁⟩ := exists_sgMult Λ hor hl₁
    obtain ⟨κ₂, hκ₂⟩ := exists_sgMult Λ hor hl₂
    have hs₁ := hκ₁.sq_of_half Λ h₁2
    have hs₂ := hκ₂.sq_of_half Λ h₂2
    have hsum : l₁ + l₂ = l := by ring
    refine ⟨_, ?_, hsum ▸ hκ₁.add Λ hκ₂⟩
    obtain ⟨k, hk⟩ := conj_mul_sub_lattice Λ hor hl₁ hl₂
    have hA : (area Λ : ℂ) ≠ 0 := by exact_mod_cast (ChainCanon.area_pos Λ).ne'
    have hcA : ((Real.pi / area Λ : ℝ) : ℂ) * (2 * Complex.I * (k * area Λ)) = k * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    have h1 : Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * (starRingEnd ℂ l₁ * l₂ - starRingEnd ℂ l₂ * l₁)) = 1 := by
      rw [hk, hcA, Complex.exp_int_mul_two_pi_mul_I]
    rw [← hsum, mul_pow, mul_pow, hs₁, hs₂, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    rw [← mul_one (Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * starRingEnd ℂ (l₁ + l₂) * (l₁ + l₂))), ← h1,
      ← Complex.exp_add]
    congr 1
    simp only [map_add]
    push_cast
    ring
  · obtain ⟨κ, hκ⟩ := exists_sgMult Λ hor hl
    exact ⟨κ, hκ.sq_of_half Λ hl2, hκ⟩

end SgStar

/-! ## Dividing by an entire function with simple zeros -/

section Divide

open Filter Topology

/-- **Division by an entire function with simple zeros**: if `g` has only simple zeros and `f` vanishes at them,
then `f = g·h` with `h` entire (`h = f/g` off the zeros and `f′/g′` at them; near a zero `z₀`,
`h = dslope f z₀ / dslope g z₀`). -/
theorem exists_eq_mul_of_simple {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ z, g z = 0 → f z = 0) (hg' : ∀ z, g z = 0 → deriv g z ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, f z = g z * h z := by
  classical
  refine ⟨fun z => if g z = 0 then deriv f z / deriv g z else f z / g z, fun z₀ => ?_, fun z => ?_⟩
  · by_cases h0 : g z₀ = 0
    · have hdf : Differentiable ℂ (dslope f z₀) := by
        rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
        exact hf.differentiableOn
      have hdg : Differentiable ℂ (dslope g z₀) := by
        rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
        exact hg.differentiableOn
      have hg0 : dslope g z₀ z₀ ≠ 0 := by rw [dslope_same]; exact hg' z₀ h0
      have hev : ∀ᶠ z in 𝓝 z₀, dslope g z₀ z ≠ 0 := hdg.continuous.continuousAt.eventually_ne hg0
      have heq : (fun z => if g z = 0 then deriv f z / deriv g z else f z / g z) =ᶠ[𝓝 z₀]
          fun z => dslope f z₀ z / dslope g z₀ z := by
        filter_upwards [hev] with z hz
        by_cases hzz : z = z₀
        · subst hzz
          simp [h0, dslope_same]
        · have eg := sub_smul_dslope g z₀ z
          have ef := sub_smul_dslope f z₀ z
          rw [h0, sub_zero, smul_eq_mul] at eg
          rw [hfg z₀ h0, sub_zero, smul_eq_mul] at ef
          have hgz : g z ≠ 0 := by rw [← eg]; exact mul_ne_zero (sub_ne_zero.2 hzz) hz
          rw [ite_eq_right hgz, ← eg, ← ef, mul_div_mul_left _ _ (sub_ne_zero.2 hzz)]
      exact heq.differentiableAt_iff.2 ((hdf z₀).div (hdg z₀) hg0)
    · have hev : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg.continuous.continuousAt.eventually_ne h0
      have heq : (fun z => if g z = 0 then deriv f z / deriv g z else f z / g z) =ᶠ[𝓝 z₀]
          fun z => f z / g z := by
        filter_upwards [hev] with z hz using ite_eq_right hz
      exact heq.differentiableAt_iff.2 ((hf z₀).div (hg z₀) h0)
  · by_cases h0 : g z = 0
    · simp [h0, hfg z h0]
    · simp only [ite_eq_right h0]
      field_simp

end Divide

/-! ## The CM product formula `σ*(ωz) = ω·σ*(z)^{N(ω)}·∏ G_q(z)` -/

section Product

open PeriodPair ThetaNorm EllipticAdd EllipticSigma EllipticDivisor EllipticLegendre CMThetaOne Filter Topology

variable {d : ℕ} {Λ : PeriodPair}

/-- **`σ*` is entire.** -/
theorem differentiable_sgStar (Λ : PeriodPair) : Differentiable ℂ (sgStar Λ) :=
  (differentiable_sigmaW Λ).mul (by fun_prop)

/-- **The zeros of `σ_W` are simple**: `σ_W′(l) = c ≠ 0` at a period, from `σ_W(z + l) = c·e^{ηz}·σ_W(z)`. -/
theorem hasDerivAt_sigmaW_lattice (Λ : PeriodPair) {l : ℂ} (hl : l ∈ Λ.lattice) :
    ∃ c ≠ 0, HasDerivAt (sigmaW Λ) c l := by
  obtain ⟨η, hη⟩ := exists_zetaW_add_sub Λ hl
  obtain ⟨c, hc, hσ⟩ := sigmaW_add_lattice Λ hl hη
  have h1 : HasDerivAt (fun z => c * Complex.exp (η * z) * sigmaW Λ z) c 0 := by
    have h := (((hasDerivAt_id' (0 : ℂ)).const_mul η).cexp.const_mul c).fun_mul (hasDerivAt_sigmaW_zero Λ)
    convert h using 1
    simp [sigmaW_zero]
  have h2 : HasDerivAt (fun z => sigmaW Λ (z + l)) c (l - l) := by
    rw [sub_self, show (fun z => sigmaW Λ (z + l)) = fun z => c * Complex.exp (η * z) * sigmaW Λ z from funext hσ]
    exact h1
  refine ⟨c, hc, ?_⟩
  simpa using h2.comp_sub_const l l

/-- **`σ*(ωz)` factors through the zeros `ω⁻¹Λ`**: `σ*(ωz) = (∏_{q ∈ {0} ∪ Q} σ_W(z + q))·h(z)` with `h` entire
(divide successively by the factors, whose zeros `−q + Λ` are simple and pairwise disjoint). -/
theorem exists_sgStar_omK0_factor (hcm : HasCM d Λ) {Q : Finset ℂ} (hQ : KerReps (omK0 d) Λ Q) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z, sgStar Λ (omK0 d * z) = (∏ q ∈ insert 0 Q, sigmaW Λ (z + q)) * h z := by
  classical
  have huniq : ∀ q ∈ insert 0 Q, ∀ q' ∈ insert 0 Q, q - q' ∈ Λ.lattice → q = q' := by
    intro q hq q' hq' h
    rcases Finset.mem_insert.1 hq with rfl | hq <;> rcases Finset.mem_insert.1 hq' with rfl | hq'
    · rfl
    · exact absurd (by simpa using neg_mem h) (hQ.1 q' hq').1
    · exact absurd (by simpa using h) (hQ.1 q hq).1
    · exact hQ.2.1 q hq q' hq' h
  have hker : ∀ q ∈ insert 0 Q, omK0 d * q ∈ Λ.lattice := fun q hq => by
    rcases Finset.mem_insert.1 hq with rfl | hq
    · rw [mul_zero]; exact zero_mem _
    · exact (hQ.1 q hq).2
  have hA : Differentiable ℂ fun z => sgStar Λ (omK0 d * z) :=
    (differentiable_sgStar Λ).comp (differentiable_id.const_mul _)
  suffices H : ∀ T ⊆ insert 0 Q, ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z, sgStar Λ (omK0 d * z) = (∏ q ∈ T, sigmaW Λ (z + q)) * h z from H _ subset_rfl
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun _ => ⟨_, hA, fun z => by simp⟩
  | insert a T ha ih =>
    intro hT
    obtain ⟨h, hdh, hh⟩ := ih ((Finset.subset_insert a T).trans hT)
    have haQ := hT (Finset.mem_insert_self a T)
    have hvan : ∀ z, sigmaW Λ (z + a) = 0 → h z = 0 := fun z hz => by
      have hza : z + a ∈ Λ.lattice := (sigmaW_eq_zero_iff Λ _).1 hz
      have hωz : omK0 d * z ∈ Λ.lattice := by
        have := sub_mem (omK0_mul_mem hcm hza) (hker a haQ)
        rwa [mul_add, add_sub_cancel_right] at this
      have hs : sgStar Λ (omK0 d * z) = 0 := by simp [sgStar, (sigmaW_eq_zero_iff Λ _).2 hωz]
      have hP : ∏ q ∈ T, sigmaW Λ (z + q) ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq => by
        rw [Ne, sigmaW_eq_zero_iff]
        intro hzq
        have hqa := huniq q (hT (Finset.mem_insert_of_mem hq)) a haQ (by
          have := sub_mem hzq hza
          rwa [add_sub_add_left_eq_sub] at this)
        exact ha (hqa ▸ hq)
      have := hh z
      rw [hs] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hP
    obtain ⟨h', hd', hh'⟩ : ∃ h' : ℂ → ℂ, Differentiable ℂ h' ∧ ∀ z, h z = sigmaW Λ (z + a) * h' z := by
      refine exists_eq_mul_of_simple hdh ((differentiable_sigmaW Λ).comp (differentiable_id.add_const a)) hvan
        fun z hz => ?_
      obtain ⟨c, hc, hdc⟩ := hasDerivAt_sigmaW_lattice Λ ((sigmaW_eq_zero_iff Λ _).1 hz)
      rw [(hdc.comp_add_const z a).deriv]
      exact hc
    exact ⟨h', hd', fun z => by rw [hh z, hh' z, Finset.prod_insert ha]; ring⟩

/-- **From `σ*` to `σ*/z`**: an identity `σ*(ωz) = ω·σ*(z)^N·∏ G_q(z)·r`, `|Q| = N − 1`, `z ≠ 0`, is
`E(ωz) = E(z)^N·∏ (z·G_q)(z)·r` for `E = σ*/z` (`sigE`) and `z·G_q = GqRes`. -/
theorem sigE_eq_of_sgStar {N : ℕ} (hN : 1 ≤ N) {Q : Finset ℂ} (hcard : Q.card = N - 1) {z : ℂ} (hz0 : z ≠ 0)
    {r : ℂ} (h : sgStar Λ (omK0 d * z) = omK0 d * sgStar Λ z ^ N * (∏ q ∈ Q, Gq Λ q z) * r) :
    sigE Λ (omK0 d * z) = sigE Λ z ^ N * (∏ q ∈ Q, GqRes Λ q z) * r := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hcard
  have hs : ∀ w, sgStar Λ w = w * sigE Λ w := fun w => by rw [sgStar_eq]; simp
  have hG : ∏ q ∈ Q, Gq Λ q z = (∏ q ∈ Q, GqRes Λ q z) / z ^ M := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [← mul_Gq Λ hz0]
    field_simp
  rw [hs, hs, hG] at h
  have hω := omK0_ne_zero d
  refine mul_left_cancel₀ (mul_ne_zero hω hz0) ?_
  rw [h, mul_pow, pow_succ]
  field_simp

/-- **The CM product formula, oriented case** (see `sgStar_omK0_mul`). -/
theorem sgStar_omK0_mul_of_or (hd : d ≠ 0) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
    (hor : 0 < (Λ.ω₂ / Λ.ω₁).im) {Q : Finset ℂ} (hQ : KerReps (omK0 d) Λ Q) {z : ℂ} (hz : z ∉ Λ.lattice) :
    sgStar Λ (omK0 d * z) = omK0 d * sgStar Λ z ^ ((1 + d) / 4) * ∏ q ∈ Q, Gq Λ q z := by
  classical
  have hN1 : 1 ≤ (1 + d) / 4 := normOm_pos hd4
  have hcard : Q.card = (1 + d) / 4 - 1 := card_kerReps hd hd4 hcm hQ
  have hω := omK0_ne_zero d
  have h0Q : (0 : ℂ) ∉ Q := fun h => (hQ.1 0 h).1 (zero_mem _)
  obtain ⟨h, hdh, hh⟩ := exists_sgStar_omK0_factor hcm hQ
  set ω := omK0 d with hωdef
  set N := (1 + d) / 4 with hNdef
  set K : ℂ → ℂ := fun z => ω * Complex.exp (-(s2 Λ) * z ^ 2 / 2) ^ N *
    ∏ q ∈ Q, (Complex.exp (-(etaR Λ q * z)) / sigmaW Λ q) with hKdef
  have hK0 : ∀ z, K z ≠ 0 := fun z => mul_ne_zero (mul_ne_zero hω (pow_ne_zero _ (Complex.exp_ne_zero _)))
    (Finset.prod_ne_zero_iff.2 fun q hq => div_ne_zero (Complex.exp_ne_zero _) (sigmaW_ne_zero Λ (hQ.1 q hq).1))
  have hKd : Differentiable ℂ K := by
    refine ((differentiable_const _).mul ((by fun_prop : Differentiable ℂ fun z : ℂ =>
      Complex.exp (-(s2 Λ) * z ^ 2 / 2)).pow N)).mul ?_
    exact Differentiable.fun_finsetProd fun q _ =>
      (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (-(etaR Λ q * z))).div_const _
  -- `K·∏_{{0} ∪ Q} σ_W(z + q) = ω·σ*(z)^N·∏ G_q(z)` off the lattice
  have hKP : ∀ z ∉ Λ.lattice, K z * ∏ q ∈ insert 0 Q, sigmaW Λ (z + q) =
      ω * sgStar Λ z ^ N * ∏ q ∈ Q, Gq Λ q z := by
    intro z hz
    have hsz := sigmaW_ne_zero Λ hz
    have hGq : ∀ q ∈ Q, Gq Λ q z =
        Complex.exp (-(etaR Λ q * z)) / sigmaW Λ q * sigmaW Λ (z + q) * (sigmaW Λ z)⁻¹ := fun q hq => by
      have := sigmaW_ne_zero Λ (hQ.1 q hq).1
      simp only [Gq]
      field_simp
    rw [Finset.prod_insert h0Q, add_zero, Finset.prod_congr rfl hGq, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_const, hcard]
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM, Nat.add_sub_cancel]
    simp only [K, sgStar, hM]
    rw [mul_pow, inv_pow, pow_succ (sigmaW Λ z)]
    field_simp
  set R : ℂ → ℂ := fun z => h z / K z with hRdef
  have hRd : Differentiable ℂ R := hdh.div hKd hK0
  have hDR : ∀ z ∉ Λ.lattice, sgStar Λ (ω * z) = ω * sgStar Λ z ^ N * (∏ q ∈ Q, Gq Λ q z) * R z := by
    intro z hz
    rw [hh z, ← hKP z hz]
    simp only [R]
    field_simp [hK0 z]
  -- the multiplier of `R` along a period is unimodular
  have hmult : ∀ l ∈ Λ.lattice, ∃ χ : ℂ, ‖χ‖ = 1 ∧ ∀ z, R (z + l) = χ * R z := by
    intro l hl
    have hωl : ω * l ∈ Λ.lattice := omK0_mul_mem hcm hl
    obtain ⟨κ₁, hκ₁2, hκ₁⟩ := sgStar_add_lattice Λ hor hωl
    obtain ⟨κ, hκ2, hκ⟩ := sgStar_add_lattice Λ hor hl
    set U := ∏ q ∈ Q, Complex.exp (etaR Λ l * q - etaR Λ q * l) with hUdef
    have hU : ‖U‖ = 1 := by
      rw [norm_prod]
      refine Finset.prod_eq_one fun q hq => ?_
      have h1 := congrArg norm (exp_factor_pow Λ hor (natCast_normOm_mul_mem hd4 hcm (hQ.1 q hq).2) hl)
      rw [norm_pow, norm_one] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
    have hκ0 : κ ≠ 0 := fun h0 => by
      rw [h0, zero_pow two_ne_zero] at hκ2
      exact Complex.exp_ne_zero _ hκ2.symm
    have hconj : starRingEnd ℂ (ω * l) * (ω * l) = N * (starRingEnd ℂ l * l) := by
      rw [map_mul, ← conj_omK0_mul hd4]
      ring
    have hκ₁n : ‖κ₁‖ = ‖κ‖ ^ N := by
      have e : κ₁ ^ 2 = (κ ^ N) ^ 2 := by
        rw [hκ₁2, ← pow_mul, mul_comm N 2, pow_mul, hκ2, ← Complex.exp_nat_mul, mul_assoc, hconj]
        ring_nf
      have := congrArg norm e
      rw [norm_pow, norm_pow, norm_pow] at this
      rw [← norm_pow]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by rw [norm_pow]; exact this)
    refine ⟨κ₁ / (κ ^ N * U), ?_, ?_⟩
    · rw [norm_div, norm_mul, norm_pow, hκ₁n, hU, mul_one, div_self (pow_ne_zero _ (norm_ne_zero_iff.2 hκ0))]
    have hdense : Dense {z : ℂ | ω * z ∉ Λ.lattice} := by
      have e : {z : ℂ | ω * z ∉ Λ.lattice} = ((fun w => ω⁻¹ * w) '' (Λ.lattice : Set ℂ))ᶜ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image]
        constructor
        · rintro h ⟨w, hw, rfl⟩
          exact h (by rwa [mul_inv_cancel_left₀ hω])
        · rintro h hz
          exact h ⟨ω * z, hz, by rw [inv_mul_cancel_left₀ hω]⟩
      rw [e]
      exact ((countable_lattice Λ).image _).dense_compl ℂ
    have hfun : (fun z => R (z + l)) = fun z => κ₁ / (κ ^ N * U) * R z := by
      refine Continuous.ext_on hdense (hRd.continuous.comp (continuous_id.add continuous_const))
        (continuous_const.mul hRd.continuous) fun z hz => ?_
      have hz' : z ∉ Λ.lattice := fun h => hz (omK0_mul_mem hcm h)
      have hzl : z + l ∉ Λ.lattice := add_mem_compl Λ hz' hl
      have hD0 : ω * sgStar Λ z ^ N * ∏ q ∈ Q, Gq Λ q z ≠ 0 := by
        intro h0
        have := hDR z hz'
        rw [h0, zero_mul] at this
        exact sgStar_ne_zero Λ hz this
      have e1 : sgStar Λ (ω * (z + l)) =
          κ₁ * Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * N * starRingEnd ℂ l * z) * sgStar Λ (ω * z) := by
        rw [mul_add, hκ₁ (ω * z)]
        congr 2
        rw [map_mul, mul_assoc ((Real.pi / area Λ : ℝ) : ℂ), mul_assoc ((Real.pi / area Λ : ℝ) : ℂ),
          mul_mul_mul_comm, conj_omK0_mul hd4, ← hNdef]
        ring_nf
      have e2 : ω * sgStar Λ (z + l) ^ N * ∏ q ∈ Q, Gq Λ q (z + l) =
          κ ^ N * U * Complex.exp (((Real.pi / area Λ : ℝ) : ℂ) * N * starRingEnd ℂ l * z) *
            (ω * sgStar Λ z ^ N * ∏ q ∈ Q, Gq Λ q z) := by
        rw [hκ z, Finset.prod_congr rfl fun q hq => Gq_add Λ hor (hQ.1 q hq).1 hl hz', Finset.prod_mul_distrib,
          ← hUdef, mul_pow, mul_pow, ← Complex.exp_nat_mul]
        ring_nf
      have h1 := hDR (z + l) hzl
      rw [e1, e2, hDR z hz'] at h1
      have hE := Complex.exp_ne_zero (((Real.pi / area Λ : ℝ) : ℂ) * N * starRingEnd ℂ l * z)
      have hkU : κ ^ N * U ≠ 0 := mul_ne_zero (pow_ne_zero _ hκ0) (norm_ne_zero_iff.1 (by rw [hU]; exact one_ne_zero))
      change R (z + l) = κ₁ / (κ ^ N * U) * R z
      clear_value R
      rw [div_mul_eq_mul_div, eq_div_iff hkU]
      refine mul_left_cancel₀ (mul_ne_zero hE hD0) ?_
      linear_combination -h1
    exact fun z => congrFun hfun z
  -- Liouville: `|R|` is periodic, hence bounded, hence `R` is constant
  have hper : ∀ z w, w ∈ Λ.lattice → ‖R (z + w)‖ = ‖R z‖ := fun z w hw => by
    obtain ⟨χ, hχ, hR⟩ := hmult w hw
    rw [hR, norm_mul, hχ, one_mul]
  have hcpt := IsZLattice.isCompact_range_of_periodic Λ.lattice (fun z => ‖R z‖)
    (continuous_norm.comp hRd.continuous) hper
  obtain ⟨C, hC⟩ := hcpt.bddAbove
  have hbd : Bornology.IsBounded (Set.range R) :=
    isBounded_iff_forall_norm_le.2 ⟨C, by rintro _ ⟨z, rfl⟩; exact hC ⟨z, rfl⟩⟩
  have hconst : ∀ z, R z = R 0 := fun z => hRd.apply_eq_apply_of_bounded hbd z 0
  -- the constant is `1`: compare `σ*(ωz)/z` and `σ*(z)^N∏G_q(z)/z` at `0`
  have hR0 : R 0 = 1 := by
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), sigE Λ (ω * z) = sigE Λ z ^ N * (∏ q ∈ Q, GqRes Λ q z) * R 0 := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Λ.compl_lattice_sdiff_singleton_mem_nhds 0)]
        with z hz0 hzΛ
      have hz : z ∉ Λ.lattice := fun h => hzΛ ⟨h, hz0⟩
      exact sigE_eq_of_sgStar hN1 hcard hz0 (by rw [hDR z hz, hconst z])
    have hc1 : ContinuousAt (fun z => sigE Λ (ω * z)) 0 :=
      ((differentiable_sigE Λ).comp (differentiable_id.const_mul ω)).continuous.continuousAt
    have hc2 : ContinuousAt (fun z => sigE Λ z ^ N * (∏ q ∈ Q, GqRes Λ q z) * R 0) 0 :=
      ((((differentiable_sigE Λ).pow N).continuous.continuousAt).mul
        (Finset.analyticAt_fun_prod _ fun q hq => (analyticAt_GqRes Λ (hQ.1 q hq).1).1).continuousAt).mul
        continuousAt_const
    have hs0 : sigE Λ 0 = 1 := by simp [sigE, sigP_zero]
    have hq0 : ∏ q ∈ Q, GqRes Λ q 0 = 1 := Finset.prod_eq_one fun q hq => (analyticAt_GqRes Λ (hQ.1 q hq).1).2
    have l1 := hc1.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    have l2 := (hc2.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).congr' (hev.mono fun z hz => hz.symm)
    have := tendsto_nhds_unique l1 l2
    simpa [hs0, hq0] using this.symm
  rw [hDR z hz, hconst z, hR0, mul_one]

/-! ## Removing the orientation: swapping the periods -/

/-- **The period pair with its periods swapped** (the same lattice, the opposite orientation). -/
def swapPair (Λ : PeriodPair) : PeriodPair :=
  ⟨Λ.ω₂, Λ.ω₁, LinearIndependent.pair_iff.mpr fun s t hst =>
    (LinearIndependent.pair_iff.mp Λ.indep t s (by rw [add_comm]; exact hst)).symm⟩

/-- **Swapping keeps the lattice.** -/
theorem lattice_swapPair (Λ : PeriodPair) : (swapPair Λ).lattice = Λ.lattice := by
  simp only [PeriodPair.lattice, swapPair, Set.pair_comm]

/-- **Swapping keeps `σ_W`.** -/
theorem sigP_swapPair (Λ : PeriodPair) : sigP (swapPair Λ) = sigP Λ := by
  funext z
  simp only [sigP]
  rw [lattice_swapPair]

/-- **Swapping keeps `ζ_W`.** -/
theorem zetaW_swapPair (Λ : PeriodPair) : zetaW (swapPair Λ) = zetaW Λ := by
  funext z
  simp only [zetaW]
  rw [lattice_swapPair]

/-- **Swapping keeps Masser's `s₂`.** -/
theorem s2_swapPair (Λ : PeriodPair) : s2 (swapPair Λ) = s2 Λ := by
  simp only [s2, zetaW_swapPair]
  rw [← neg_div_neg_eq]
  congr 1 <;> simp only [swapPair] <;> ring

/-- **Swapping keeps the area.** -/
theorem area_swapPair (Λ : PeriodPair) : area (swapPair Λ) = area Λ := by
  simp only [area, swapPair, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  rw [← abs_neg]
  congr 1
  ring

/-- **Swapping keeps `σ*`.** -/
theorem sgStar_swapPair (Λ : PeriodPair) : sgStar (swapPair Λ) = sgStar Λ := by
  funext z
  simp only [sgStar, sigmaW_eq, sigP_swapPair, s2_swapPair]

/-- **Swapping keeps the translates.** -/
theorem Gq_swapPair (Λ : PeriodPair) (q : ℂ) : Gq (swapPair Λ) q = Gq Λ q := by
  funext z
  simp only [Gq, etaR, sigmaW_eq, sigP_swapPair, s2_swapPair, area_swapPair]

/-- **Swapping keeps the translates near `0`.** -/
theorem GqRes_swapPair (Λ : PeriodPair) (q : ℂ) : GqRes (swapPair Λ) q = GqRes Λ q := by
  funext z
  simp only [GqRes, etaR, sigmaW_eq, sigP_swapPair, s2_swapPair, area_swapPair]

/-- **The CM product formula** `σ*(ωz) = ω·σ*(z)^{N(ω)}·∏_{q ∈ Q} G_q(z)` for `z ∉ Λ`, `Q` representatives of
`(ω⁻¹Λ ∖ Λ)/Λ` (`|Q| = N(ω) − 1`, `card_kerReps`). `σ*(ωz) = (∏_{q ∈ {0} ∪ Q} σ_W(z + q))·h(z)` with `h` entire
(`exists_sgStar_omK0_factor`); the quotient `R` of the two sides is entire, and along a period `l` it has the
multiplier `κ(ωl)/(κ(l)^N·∏_q e^{η(l)q − η(q)l})`: the Gaussian factors cancel as `ω̄ω = N`, and the multiplier is
unimodular (`κ(ωl)² = (κ(l)^N)²` by `sgStar_add_lattice`, `G_q`'s factors are `N`-th roots of unity). So `|R|` is
periodic, `R` is constant (Liouville), and `R = 1` at `0` (`σ*(ωz) ∼ ωz`, `z·G_q(z) → 1`). Either orientation of
the periods (`swapPair`). -/
theorem sgStar_omK0_mul (hd : d ≠ 0) (hd4 : d % 4 = 3) (hcm : HasCM d Λ) {Q : Finset ℂ}
    (hQ : KerReps (omK0 d) Λ Q) {z : ℂ} (hz : z ∉ Λ.lattice) :
    sgStar Λ (omK0 d * z) = omK0 d * sgStar Λ z ^ ((1 + d) / 4) * ∏ q ∈ Q, Gq Λ q z := by
  rcases lt_or_gt_of_ne (im_div_ne_zero Λ) with h | h
  · have hor' : 0 < ((swapPair Λ).ω₂ / (swapPair Λ).ω₁).im := by
      have h1 : Λ.ω₁ ≠ 0 := Λ.indep.ne_zero 0
      have h2 : Λ.ω₂ ≠ 0 := Λ.indep.ne_zero 1
      change 0 < (Λ.ω₁ / Λ.ω₂).im
      rw [show Λ.ω₁ / Λ.ω₂ = (Λ.ω₂ / Λ.ω₁)⁻¹ by rw [inv_div], Complex.inv_im, neg_div]
      exact neg_pos.mpr (div_neg_of_neg_of_pos h (Complex.normSq_pos.mpr (div_ne_zero h2 h1)))
    have hcm' : HasCM d (swapPair Λ) := by
      unfold HasCM
      rw [lattice_swapPair]
      exact hcm
    have hQ' : KerReps (omK0 d) (swapPair Λ) Q := by
      unfold KerReps
      rw [lattice_swapPair]
      exact hQ
    have := sgStar_omK0_mul_of_or hd hd4 hcm' hor' hQ' (z := z) (by rw [lattice_swapPair]; exact hz)
    simpa only [sgStar_swapPair, Gq_swapPair] using this
  · exact sgStar_omK0_mul_of_or hd hd4 hcm h hQ hz

/-- **The CM product formula near `0`**: `E(ωz) = E(z)^{N(ω)}·∏_{q ∈ Q} (z·G_q)(z)` for `E = σ*/z`, on a
neighbourhood of `0` (both sides are `1` at `0`). -/
theorem sigE_omK0_mul (hd : d ≠ 0) (hd4 : d % 4 = 3) (hcm : HasCM d Λ) {Q : Finset ℂ}
    (hQ : KerReps (omK0 d) Λ Q) :
    (fun z => sigE Λ (omK0 d * z)) =ᶠ[𝓝 0] fun z => sigE Λ z ^ ((1 + d) / 4) * ∏ q ∈ Q, GqRes Λ q z := by
  filter_upwards [Λ.compl_lattice_sdiff_singleton_mem_nhds 0] with z hzΛ
  by_cases hz0 : z = 0
  · subst hz0
    have hs0 : sigE Λ 0 = 1 := by simp [sigE, sigP_zero]
    rw [mul_zero, hs0, one_pow, one_mul, Finset.prod_eq_one fun q hq => (analyticAt_GqRes Λ (hQ.1 q hq).1).2]
  · have hz : z ∉ Λ.lattice := fun h => hzΛ ⟨h, hz0⟩
    have := sigE_eq_of_sgStar (normOm_pos hd4) (card_kerReps hd hd4 hcm hQ) hz0 (r := 1)
      (by rw [mul_one]; exact sgStar_omK0_mul hd hd4 hcm hQ hz)
    rwa [mul_one] at this

end Product

/-! ## `ι(ω)` lies in `K^ur` -/

section Unram

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`2` is a unit at an odd prime.** -/
theorem norm_two_padicC (hℓ2 : ℓ ≠ 2) : ‖(2 : ℂ_[ℓ])‖ = 1 := by
  have h := CMThetaOne.norm_natCast_padicComplex (ℓ := ℓ) (n := 2)
    ((Nat.Prime.coprime_iff_not_dvd hℓp.out).2 fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓp.out Nat.prime_two).1 h))
  exact_mod_cast h

/-- **Integers prime to `ℓ` are units.** -/
theorem norm_intCast_padicC {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c) : ‖(c : ℂ_[ℓ])‖ = 1 := by
  have h : ¬ ℓ ∣ c.natAbs := fun h => hc (Int.natCast_dvd.2 h)
  have := CMThetaOne.norm_natCast_padicComplex (ℓ := ℓ) ((Nat.Prime.coprime_iff_not_dvd hℓp.out).2 h)
  rcases Int.natAbs_eq c with hc' | hc'
  · rw [hc', Int.cast_natCast]
    exact this
  · rw [hc', Int.cast_neg, Int.cast_natCast, norm_neg]
    exact this

/-- **A Teichmüller approximation of a square root**: for an integer `c` prime to `ℓ ≠ 2`, some `y ∈ K^ur` with
`‖y‖ = 1` has `‖y² − c‖ < 1`. With `m = (ℓ² − 1)/2`, `c^m ≡ 1 (mod ℓ)` (Fermat, `ℓ + 1` even), so a factor of
`c^m − 1 = ∏_{w^m = 1} (c − w)` is small, and `w = y²` for an `(ℓ² − 1)`-th root of unity `y`. -/
theorem exists_sq_near (hℓ2 : ℓ ≠ 2) {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c) :
    ∃ y ∈ unramC ℓ, ‖y‖ = 1 ∧ ‖y ^ 2 - c‖ < 1 := by
  classical
  have hℓ := hℓp.out
  obtain ⟨k, hk⟩ := hℓ.odd_of_ne_two hℓ2
  have hk1 : 1 ≤ k := by have := hℓ.two_le; omega
  set m := 2 * k ^ 2 + 2 * k with hm
  set n := ℓ ^ 2 - 1 with hn
  have hnm : n = 2 * m := by rw [hn, hk]; ring_nf; omega
  have hm0 : 0 < m := by positivity
  have hnd : ¬ ℓ ∣ n := fun h => hℓ.not_dvd_one (by
    have h' : ℓ ∣ ℓ ^ 2 := dvd_pow_self ℓ two_ne_zero
    rw [show ℓ ^ 2 = n + 1 by have := Nat.one_le_pow 2 ℓ hℓ.pos; omega] at h'
    exact (Nat.dvd_add_right h).1 h')
  have : NeZero ((n : ℕ) : ℂ_[ℓ]) := ⟨Nat.cast_ne_zero.2 (by omega)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[ℓ] n
  have hζu : ζ ∈ unramC ℓ :=
    Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, by omega, hnd, hζ.pow_eq_one⟩)
  have hζ1 : ‖ζ‖ = 1 := by
    have h := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) (by omega)).1 h
  have hw : IsPrimitiveRoot (ζ ^ 2) m := hζ.pow (by omega) hnm
  -- `c^m ≡ 1 (mod ℓ)`
  have hcm : ‖(c : ℂ_[ℓ]) ^ m - 1‖ < 1 := by
    have hz : ((c ^ m - 1 : ℤ) : ZMod ℓ) = 0 := by
      have hc0 : (c : ZMod ℓ) ≠ 0 := fun h => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c ℓ).1 h)
      have hF := ZMod.pow_card_sub_one_eq_one hc0
      push_cast
      rw [show m = (ℓ - 1) * (k + 1) by rw [hm, hk]; simp; ring, pow_mul, hF, one_pow, sub_self]
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).1 hz
    have e : (c : ℂ_[ℓ]) ^ m - 1 = (ℓ : ℂ_[ℓ]) * t := by exact_mod_cast ht
    rw [e, norm_mul]
    calc ‖(ℓ : ℂ_[ℓ])‖ * ‖(t : ℂ_[ℓ])‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one _ t) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact norm_ell_lt_one
  -- a factor is small
  have hprod := congrArg (Polynomial.eval (c : ℂ_[ℓ])) (Polynomial.X_pow_sub_one_eq_prod hm0 hw)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at hprod
  obtain ⟨w, hwm, hwc⟩ : ∃ w ∈ Polynomial.nthRootsFinset m (1 : ℂ_[ℓ]), ‖(c : ℂ_[ℓ]) - w‖ < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : ∀ w ∈ Polynomial.nthRootsFinset m (1 : ℂ_[ℓ]), ‖(c : ℂ_[ℓ]) - w‖ = 1 := fun w hw' => by
      refine le_antisymm (norm_sub_le_one (IsUltrametricDist.norm_intCast_le_one _ c) ?_) (hcon w hw')
      have h := congrArg norm ((Polynomial.mem_nthRootsFinset hm0 _).1 hw')
      rw [norm_pow, norm_one] at h
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg w) (by omega)).1 h).le
    rw [hprod, norm_prod, Finset.prod_eq_one h1] at hcm
    exact lt_irrefl _ hcm
  have : NeZero m := ⟨by omega⟩
  obtain ⟨j, -, hj⟩ := hw.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hm0 _).1 hwm)
  refine ⟨ζ ^ j, (unramC ℓ).pow_mem hζu j, by rw [norm_pow, hζ1, one_pow], ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hj, norm_sub_rev]
  exact hwc

/-- **Square roots of prime-to-`ℓ` integers lie in `K^ur`**: Newton's iteration `y ↦ (y + c/y)/2` from
`exists_sq_near` stays in `K^ur` with `‖y_n² − c‖ ≤ r^{n+1}`; since `(x − y_n)(x + y_n) = c − y_n²` and
`‖(x + y_n) − (x − y_n)‖ = 1`, one of `±y_n` is within `r^{n+1}` of `x`, and `K^ur` is closed. -/
theorem mem_unramC_of_sq (hℓ2 : ℓ ≠ 2) {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c) {x : ℂ_[ℓ]} (hx : x ^ 2 = c) :
    x ∈ unramC ℓ := by
  obtain ⟨y₀, hy₀u, hy₀1, hy₀c⟩ := exists_sq_near hℓ2 hc
  have hc1 : ‖(c : ℂ_[ℓ])‖ = 1 := norm_intCast_padicC hc
  have h2 := norm_two_padicC (ℓ := ℓ) hℓ2
  set r := ‖y₀ ^ 2 - c‖ with hr
  let y : ℕ → ℂ_[ℓ] := fun n => Nat.rec y₀ (fun _ yn => (yn + c / yn) / 2) n
  have hy : ∀ n, y n ∈ unramC ℓ ∧ ‖y n‖ = 1 ∧ ‖y n ^ 2 - c‖ ≤ r ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨hy₀u, hy₀1, by simp [y, r]⟩
    | succ n ih =>
      obtain ⟨hu, h1, he⟩ := ih
      have hyn0 : y n ≠ 0 := norm_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
      have hsucc : y (n + 1) = (y n + c / y n) / 2 := rfl
      have he' : y (n + 1) ^ 2 - c = (y n ^ 2 - c) ^ 2 / (2 ^ 2 * y n ^ 2) := by
        rw [hsucc]
        field_simp
        ring
      have hnorm : ‖y (n + 1) ^ 2 - c‖ = ‖y n ^ 2 - c‖ ^ 2 := by
        rw [he', norm_div, norm_mul, norm_pow, norm_pow, norm_pow, h1, h2]
        simp
      have hrn : r ^ (n + 1) ≤ r := pow_le_of_le_one (norm_nonneg _) hy₀c.le (by omega)
      have hle : ‖y (n + 1) ^ 2 - c‖ ≤ r ^ (n + 1 + 1) := by
        rw [hnorm, sq]
        calc ‖y n ^ 2 - c‖ * ‖y n ^ 2 - c‖ ≤ r ^ (n + 1) * r ^ (n + 1) :=
              mul_le_mul he he (norm_nonneg _) (by positivity)
          _ ≤ r ^ (n + 1) * r := mul_le_mul_of_nonneg_left hrn (by positivity)
          _ = r ^ (n + 1 + 1) := by ring
      refine ⟨?_, ?_, hle⟩
      · rw [hsucc]
        exact (unramC ℓ).div_mem ((unramC ℓ).add_mem hu ((unramC ℓ).div_mem (intCast_mem _ c) hu))
          (ofNat_mem _ 2)
      · have hlt : ‖y (n + 1) ^ 2 - c‖ < ‖(c : ℂ_[ℓ])‖ := by
          rw [hc1]
          exact lt_of_le_of_lt hle (pow_lt_one₀ (norm_nonneg _) hy₀c (by omega))
        have h' : ‖y (n + 1) ^ 2‖ = 1 := by
          rw [show y (n + 1) ^ 2 = (y (n + 1) ^ 2 - c) + c by ring,
            IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le, hc1]
        rw [norm_pow] at h'
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'
  have happ : ∀ n, ∃ s ∈ unramC ℓ, ‖x - s‖ ≤ r ^ (n + 1) := by
    intro n
    obtain ⟨hu, h1, he⟩ := hy n
    have hprod : ‖x - y n‖ * ‖x + y n‖ ≤ r ^ (n + 1) := by
      rw [← norm_mul, show (x - y n) * (x + y n) = -(y n ^ 2 - c) by rw [← hx]; ring, norm_neg]
      exact he
    have hmax : 1 ≤ max ‖x + y n‖ ‖x - y n‖ := by
      have h' := norm_sub_le_max' (x + y n) (x - y n)
      rwa [show x + y n - (x - y n) = 2 * y n by ring, norm_mul, h2, h1, one_mul] at h'
    rcases le_max_iff.1 hmax with h | h
    · refine ⟨y n, hu, ?_⟩
      nlinarith [norm_nonneg (x - y n)]
    · refine ⟨-y n, neg_mem hu, ?_⟩
      rw [sub_neg_eq_add]
      nlinarith [norm_nonneg (x + y n)]
  choose s hs hxs using happ
  refine isClosed_unramC.mem_of_tendsto (b := Filter.atTop) ?_ (Filter.Eventually.of_forall hs)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun n : ℕ => r ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hy₀c).comp (Filter.tendsto_add_atTop_nat 1)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [norm_sub_rev]
  exact hxs n

/-- **`ι(ω) ∈ K^ur`**: `ι(ω) = (1 + x)/2` with `x² = −d` (`mem_unramC_of_sq`). -/
theorem iota_omK0_mem (hℓ2 : ℓ ≠ 2) {d : ℕ} (hdℓ : ¬ ℓ ∣ d) (ι : ℂ ≃+* ℂ_[ℓ]) : ι (omK0 d) ∈ unramC ℓ := by
  have hx : ι (Complex.I * (Real.sqrt d : ℂ)) ^ 2 = ((-(d : ℤ) : ℤ) : ℂ_[ℓ]) := by
    rw [← map_pow, mul_pow, Complex.I_sq, sqrt_sq_complex]
    simp
  have hc : ¬ (ℓ : ℤ) ∣ -(d : ℤ) := by rw [dvd_neg]; exact_mod_cast hdℓ
  have hmem := mem_unramC_of_sq hℓ2 hc hx
  rw [omK0, map_div₀, map_add, map_one, map_ofNat]
  exact (unramC ℓ).div_mem ((unramC ℓ).add_mem (one_mem _) hmem) (ofNat_mem _ 2)

/-- **`ι(ω)` is a root of `x² − x + N(ω)`.** -/
theorem iota_omK0_sq {d : ℕ} (hd4 : d % 4 = 3) (ι : ℂ ≃+* ℂ_[ℓ]) :
    ι (omK0 d) ^ 2 - ι (omK0 d) + (((1 + d) / 4 : ℕ) : ℂ_[ℓ]) = 0 := by
  have h := congrArg ι (omK0_sq hd4)
  rwa [map_add, map_sub, map_pow, map_natCast, map_zero] at h

/-- **`φ²(ι ω) = ι ω`** for every ring endomorphism `φ` of `K^ur`: `φ` permutes the roots `ι ω`, `1 − ι ω` of
`x² − x + N(ω)`. -/
theorem phi_phi_iota_omK0 (hℓ2 : ℓ ≠ 2) {d : ℕ} (hd4 : d % 4 = 3) (hdℓ : ¬ ℓ ∣ d) (ι : ℂ ≃+* ℂ_[ℓ])
    (φ : unramC ℓ →+* unramC ℓ) :
    φ (φ ⟨ι (omK0 d), iota_omK0_mem hℓ2 hdℓ ι⟩) = ⟨ι (omK0 d), iota_omK0_mem hℓ2 hdℓ ι⟩ := by
  set a : unramC ℓ := ⟨ι (omK0 d), iota_omK0_mem hℓ2 hdℓ ι⟩
  have ha : a ^ 2 - a + (((1 + d) / 4 : ℕ) : unramC ℓ) = 0 := Subtype.ext (by
    simpa using iota_omK0_sq hd4 ι)
  have hfa : (φ a - a) * (φ a - (1 - a)) = 0 := by
    have h := congrArg φ ha
    rw [map_add, map_sub, map_pow, map_natCast, map_zero] at h
    linear_combination h - ha
  rcases mul_eq_zero.1 hfa with h | h
  · rw [sub_eq_zero.1 h, sub_eq_zero.1 h]
  · rw [sub_eq_zero.1 h, map_sub, map_one, sub_eq_zero.1 h]
    ring

/-- **`ι(ω)` is a unit** at an inert `ℓ ≠ 2`: `ι(ω) = (1 ± x)/2`-integral, and `ι(ω)(1 − ι(ω)) = N(ω)` is a unit. -/
theorem norm_iota_omK0 (hℓ2 : ℓ ≠ 2) {d : ℕ} (hdℓ : ¬ ℓ ∣ d) (hd4 : d % 4 = 3)
    (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι : ℂ ≃+* ℂ_[ℓ]) : ‖ι (omK0 d)‖ = 1 := by
  set α := ι (omK0 d)
  set x := ι (Complex.I * (Real.sqrt d : ℂ))
  have hx2 : x ^ 2 = -(d : ℂ_[ℓ]) := by
    rw [← map_pow, mul_pow, Complex.I_sq, sqrt_sq_complex]
    simp
  have hd1 : ‖(d : ℂ_[ℓ])‖ = 1 := CMThetaOne.norm_natCast_padicComplex ((Nat.Prime.coprime_iff_not_dvd hℓp.out).2 hdℓ)
  have hx1 : ‖x‖ = 1 := by
    have h := congrArg norm hx2
    rw [norm_pow, norm_neg, hd1] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have hα : α = (1 + x) / 2 := by
    simp only [α, x, omK0, map_div₀, map_add, map_one, map_ofNat]
  have h2 := norm_two_padicC (ℓ := ℓ) hℓ2
  have hα1 : ‖α‖ ≤ 1 := by
    rw [hα, norm_div, h2, div_one]
    exact norm_add_le_one (by simp) hx1.le
  have hβ1 : ‖1 - α‖ ≤ 1 := by
    rw [hα, show (1 : ℂ_[ℓ]) - (1 + x) / 2 = (1 - x) / 2 by ring, norm_div, h2, div_one]
    exact norm_sub_le_one (by simp) hx1.le
  have hN : ‖(((1 + d) / 4 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    CMThetaOne.norm_natCast_padicComplex ((Nat.Prime.coprime_iff_not_dvd hℓp.out).2 (not_dvd_normOm hd4 hin))
  have hprod : α * (1 - α) = (((1 + d) / 4 : ℕ) : ℂ_[ℓ]) := by
    linear_combination -iota_omK0_sq hd4 ι
  have h := congrArg norm hprod
  rw [norm_mul, hN] at h
  refine le_antisymm hα1 ?_
  nlinarith [norm_nonneg α, norm_nonneg (1 - α)]

end Unram

/-! ## The formal endomorphism `[α]` -/

section MulLT

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`[α]T = e(α·L(T))`** on the Lubin–Tate group (`L = log_LT`, `e = expLT`). -/
def mulLT (α : ℂ_[ℓ]) : ℂ_[ℓ]⟦X⟧ := PowerSeries.subst (PowerSeries.C α * logLT ℂ_[ℓ] ℓ) (expLT ℂ_[ℓ] ℓ)

/-- **`[α]` has no constant term.** -/
theorem constantCoeff_mulLT (α : ℂ_[ℓ]) : constantCoeff (mulLT α) = 0 :=
  constantCoeff_subst_eq_zero (constantCoeff_C_mul_logLT hℓp.out.one_lt α) _ (constantCoeff_expLT _ _)

/-- **`[α]` substitutes.** -/
theorem hasSubst_mulLT (α : ℂ_[ℓ]) : HasSubst (mulLT α) := HasSubst.of_constantCoeff_zero' (constantCoeff_mulLT α)

/-- **`L([α]T) = α·L(T)`.** -/
theorem logLT_subst_mulLT (α : ℂ_[ℓ]) : (logLT ℂ_[ℓ] ℓ).subst (mulLT α) = C α * logLT ℂ_[ℓ] ℓ := by
  have hg := HasSubst.of_constantCoeff_zero' (constantCoeff_C_mul_logLT hℓp.out.one_lt α)
  rw [mulLT, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (constantCoeff_expLT _ _)) hg,
    logLT_subst_expLT _ hℓp.out.one_lt, subst_X hg]

/-- **`L([α]A) = α·L(A)`** for a point `A` (a series without constant term). -/
theorem lgP_subst_mulLT (α : ℂ_[ℓ]) {σ : Type} {A : MvPowerSeries σ ℂ_[ℓ]}
    (hA : MvPowerSeries.constantCoeff A = 0) : lgP ℓ ((mulLT α).subst A) = α • lgP ℓ A := by
  have hAs : HasSubst A := HasSubst.of_constantCoeff_zero hA
  rw [lgP, ← subst_comp_subst_apply (hasSubst_mulLT α) hAs, logLT_subst_mulLT, ← smul_eq_C_mul, subst_smul hAs,
    lgP]

/-- **`[α]A` has no constant term.** -/
theorem constantCoeff_mulLT_subst (α : ℂ_[ℓ]) {σ : Type} {A : MvPowerSeries σ ℂ_[ℓ]}
    (hA : MvPowerSeries.constantCoeff A = 0) : MvPowerSeries.constantCoeff ((mulLT α).subst A) = 0 :=
  constantCoeff_subst_eq_zero hA _ (constantCoeff_mulLT α)

/-- **`[α]` is an endomorphism of the group law**: `[α](A ⊕ B) = [α]A ⊕ [α]B` (compare logarithms). -/
theorem mulLT_subst_addP (α : ℂ_[ℓ]) {σ : Type} {A B : MvPowerSeries σ ℂ_[ℓ]}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    (mulLT α).subst (addP A B) = addP ((mulLT α).subst A) ((mulLT α).subst B) := by
  have hAB := constantCoeff_addP hA hB
  refine eq_of_lgP_eq hℓp.out.one_lt (constantCoeff_mulLT_subst α hAB)
    (constantCoeff_addP (constantCoeff_mulLT_subst α hA) (constantCoeff_mulLT_subst α hB)) ?_
  rw [lgP_subst_mulLT α hAB, lgP_addP hA hB, lgP_addP (constantCoeff_mulLT_subst α hA)
    (constantCoeff_mulLT_subst α hB), lgP_subst_mulLT α hA, lgP_subst_mulLT α hB, smul_add]

/-- **`e` is tangent to the identity.** -/
theorem coeff_one_expLT : coeff 1 (expLT ℂ_[ℓ] ℓ) = 1 := by
  have h := congrArg (coeff 1) (logLT_subst_expLT ℂ_[ℓ] hℓp.out.one_lt)
  rwa [coeff_one_subst (constantCoeff_expLT _ _), coeff_one_logLT, one_mul, coeff_one_X] at h

/-- **The linear term of `[α]` is `α`.** -/
theorem coeff_one_mulLT (α : ℂ_[ℓ]) : coeff 1 (mulLT α) = α := by
  rw [mulLT, coeff_one_subst (constantCoeff_C_mul_logLT hℓp.out.one_lt α), coeff_one_expLT, coeff_C_mul,
    coeff_one_logLT, one_mul, mul_one]

/-- **`L(ζT) = ζL(T)`** for a Teichmüller `ζ^{ℓ²} = ζ` (`L` has only the exponents `ℓ^{2j}`). -/
theorem rescale_logLT_teich {ζ : ℂ_[ℓ]} (hζ : ζ ^ (ℓ ^ 2) = ζ) :
    rescale ζ (logLT ℂ_[ℓ] ℓ) = C ζ * logLT ℂ_[ℓ] ℓ := by
  ext n
  rw [coeff_rescale, coeff_C_mul]
  by_cases h : ∃ j, n = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := h
    rw [pow_pow_two_mul hζ j]
  · push Not at h
    rw [coeff_logLT_of_ne _ h, mul_zero, mul_zero]

/-- **`[α]` commutes with the Teichmüller units**: `[α](ζT) = ζ·[α]T` for `ζ^{ℓ²} = ζ` (compare logarithms). -/
theorem rescale_mulLT_teich (α : ℂ_[ℓ]) {ζ : ℂ_[ℓ]} (hζ : ζ ^ (ℓ ^ 2) = ζ) :
    rescale ζ (mulLT α) = C ζ * mulLT α := by
  have hm := hasSubst_mulLT α
  have hζX : HasSubst (ζ • X : ℂ_[ℓ]⟦X⟧) := HasSubst.smul_X' ζ
  have h0 : constantCoeff (rescale ζ (mulLT α)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_mulLT]
  have h0' : constantCoeff (C ζ * mulLT α) = 0 := by rw [map_mul, constantCoeff_mulLT, mul_zero]
  refine eq_of_lgP_eq (σ := Unit) hℓp.out.one_lt h0 h0' ?_
  have e1 : lgP ℓ (rescale ζ (mulLT α) : MvPowerSeries Unit ℂ_[ℓ]) = α • (ζ • logLT ℂ_[ℓ] ℓ) := by
    rw [lgP, rescale_eq_subst, ← subst_comp_subst_apply hm hζX, logLT_subst_mulLT, ← smul_eq_C_mul,
      subst_smul hζX, ← rescale_eq_subst, rescale_logLT_teich hζ, ← smul_eq_C_mul]
  have e2 : lgP ℓ (C ζ * mulLT α : MvPowerSeries Unit ℂ_[ℓ]) = ζ • (α • logLT ℂ_[ℓ] ℓ) := by
    have e : C ζ * mulLT α = (ζ • X : ℂ_[ℓ]⟦X⟧).subst (mulLT α) := by
      rw [subst_smul hm, subst_X hm, smul_eq_C_mul]
    rw [lgP, e, ← subst_comp_subst_apply hζX hm, ← rescale_eq_subst, rescale_logLT_teich hζ, ← smul_eq_C_mul,
      subst_smul hm, logLT_subst_mulLT, ← smul_eq_C_mul]
  rw [e1, e2, smul_comm]

/-- **`[α]` over a subfield**: for `α ∈ k`, `[α]` is the image of `e(α·L)` computed over `k`. -/
theorem mulLT_eq_map (k : Subfield ℂ_[ℓ]) (α : k) :
    mulLT (α : ℂ_[ℓ]) = PowerSeries.map k.subtype ((expLT k ℓ).subst (C α * logLT k ℓ)) := by
  have hℓ := hℓp.out.one_lt
  rw [show PowerSeries.map k.subtype ((expLT k ℓ).subst (C α * logLT k ℓ)) =
      (PowerSeries.map k.subtype (expLT k ℓ)).subst (PowerSeries.map k.subtype (C α * logLT k ℓ)) from
    PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' (constantCoeff_C_mul_logLT hℓ α)) _,
    map_expLT _ hℓ, map_mul, map_C, map_logLT, mulLT]
  rfl

/-- **The coefficients of `[α]` lie in `k`** for `α ∈ k`. -/
theorem coeff_mulLT_mem (k : Subfield ℂ_[ℓ]) (α : k) (n : ℕ) : coeff n (mulLT (α : ℂ_[ℓ])) ∈ k := by
  rw [mulLT_eq_map k α, coeff_map]
  exact (coeff n ((expLT k ℓ).subst (C α * logLT k ℓ))).2

/-- **`[α]` is integral** for `α` in a subfield `k` with a Frobenius lift `φ`, `‖α‖ ≤ 1`, `φ²(α) = α`
(Hazewinkel, `isIntK_expLT_subst`: `g = α·L` has `g − ℓ⁻¹g^{φ²}(T^{ℓ²}) = αT` by `logLT_eq_X_add`). -/
theorem isInt_mulLT (k : Subfield ℂ_[ℓ]) {φ : k →+* k} (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    (α : k) (hα : ‖α‖ ≤ 1) (hφα : φ (φ α) = α) : IsInt (mulLT (α : ℂ_[ℓ])) := by
  have hℓ := hℓp.out.one_lt
  set L : MvPowerSeries Unit k := logLT k ℓ
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit k) = 0 :=
    MvPowerSeries.constantCoeff_X ()
  have hLX : (logLT k ℓ).subst (MvPowerSeries.X () : MvPowerSeries Unit k) = L := by
    have e : (fun _ : Unit => (MvPowerSeries.X () : MvPowerSeries Unit k)) = MvPowerSeries.X := by
      funext u
      rfl
    rw [PowerSeries.subst, e, MvPowerSeries.subst_self]
    rfl
  have hfX : frobS ℓ φ (MvPowerSeries.X () : MvPowerSeries Unit k) = MvPowerSeries.X () ^ ℓ := by
    simp [frobS, MvPowerSeries.expand_X]
  have hfL : frobS ℓ φ (frobS ℓ φ L) = (logLT k ℓ).subst (X ^ (ℓ ^ 2) : k⟦X⟧) := by
    rw [← hLX, frobS_logLT_subst φ hX0, frobS_logLT_subst φ (by rw [hfX, map_pow, hX0, zero_pow hℓp.out.ne_zero]),
      hfX, map_pow, hfX, ← pow_mul, ← sq]
    rfl
  have hfC : ∀ a : k, frobS ℓ φ (MvPowerSeries.C a : MvPowerSeries Unit k) = MvPowerSeries.C (φ a) := fun a => by
    simp [frobS, MvPowerSeries.expand_C]
  set g : MvPowerSeries Unit k := MvPowerSeries.C α * L
  have hg0 : MvPowerSeries.constantCoeff g = 0 := constantCoeff_C_mul_logLT hℓ α
  have hX : (MvPowerSeries.X () : MvPowerSeries Unit k) =
      L - (ℓ : k)⁻¹ • (logLT k ℓ).subst (X ^ (ℓ ^ 2) : k⟦X⟧) := by
    have h := logLT_eq_X_add k hℓ
    change L = (MvPowerSeries.X () : MvPowerSeries Unit k) + (ℓ : k)⁻¹ • (logLT k ℓ).subst (X ^ (ℓ ^ 2) : k⟦X⟧)
      at h
    rw [h, add_sub_cancel_right]
  have hg : g - (ℓ : k)⁻¹ • frobS ℓ φ (frobS ℓ φ g) = MvPowerSeries.C α * MvPowerSeries.X () := by
    rw [map_mul, map_mul, hfC, hfC, hφα, hfL, hX, mul_sub, mul_smul_comm]
  have hint : IsIntK ((expLT k ℓ).subst g) := isIntK_expLT_subst hφ hg0 (by
    rw [hg]
    exact (isIntK_C hα).mul (isIntK_X ()))
  refine IsIntK.isInt fun n => ?_
  rw [mulLT_eq_map k α]
  exact hint n

end MulLT

/-! ## The CM equivariance `ph([ω]T) ≃ N(ω)·ph(T)` -/

section Equiv

open PeriodPair ThetaNorm EllipticSigma EllipticDivisor Topology

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`tay` of a finite product.** -/
theorem tay_prod {ι : Type} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    tay (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, tay (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tay_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [tay_mul (hf a (Finset.mem_insert_self a s)) (Finset.analyticAt_fun_prod _ fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)), ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **Torsion arithmetic** (input; the uniform form of `isInt_translate`'s hypotheses, `CMFormalBiadd`'s open
item (3)): for the `Δ = 1` CM lattice, an inert-or-split `ℓ ≥ 5` with `ℓ ∤ d` and a torsion point `q ∉ Λ` with
`Nq ∈ Λ`, `ℓ ∤ N`, the elliptic function `G_qᴺ` is `P(℘) + ℘′Q(℘)` with `2 deg P ≤ N`, `2 deg Q + 3 ≤ N` and
`ι`-integral coefficients (good reduction at `ℓ`, and `q` does not reduce to the origin). -/
def TorsionTransl : Prop :=
  ∀ (d : ℕ) (Λ : PeriodPair), Squarefree d → d % 4 = 3 → HasCM d Λ → Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ¬ ℓ ∣ d → ∀ ι : ℂ ≃+* ℂ_[ℓ], ∀ q : ℂ, q ∉ Λ.lattice →
      ∀ N : ℕ, 0 < N → ¬ ℓ ∣ N → (N : ℂ) * q ∈ Λ.lattice → ∃ P Q : Polynomial ℂ,
        (∀ z ∉ Λ.lattice, Gq Λ q z ^ N = P.eval (Λ.weierstrassP z) + Λ.derivWeierstrassP z * Q.eval
          (Λ.weierstrassP z)) ∧
        2 * P.natDegree ≤ N ∧ 2 * Q.natDegree + 3 ≤ N ∧ (∀ i, ‖ι (P.coeff i)‖ ≤ 1) ∧ ∀ i, ‖ι (Q.coeff i)‖ ≤ 1

/-- **A Frobenius lift on `K^ur`** (input unless constructed; D1a′'s gap 2): a ring endomorphism `φ` of `unramC ℓ`
with `‖φ(x) − x^ℓ‖ ≤ ‖ℓ‖` on the unit ball. -/
def UnramFrob (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ φ : unramC ℓ →+* unramC ℓ, ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖

/-- **CM equivariance** `ph([ω]T) ≃ N(ω)·ph(T)` for the `Δ = 1` CM lattice at an inert `ℓ ≥ 5`, for every
`ε` with `‖ε‖ = 1` making `t(ε·log_LT(T))` integral. With `z(T) = ε·log_LT(T)`, `εT·exp(−ph(T)) = σ*(z(T))`, and
the product formula near `0` (`sigE_omK0_mul`) becomes `exp(N·ph(T) − ph([ω]T)) = (ωT/[ω]T)·∏_{q ∈ Q} U_q(T)` with
the translates `U_q = εT·G_q(z(T))` integral units (`isInt_translate`, hypotheses from `TorsionTransl`) and
`[ω]T/(ωT)` an integral unit (`isInt_mulLT`). -/
theorem cm_equiv (hj : CMThetaOne.CMjIntegral) (htor : TorsionTransl) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d)
    (hd4 : d % 4 = 3) (hcm : HasCM d Λ) (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d)
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
  have hNn : ‖(((1 + d) / 4 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    CMThetaOne.norm_natCast_padicComplex ((Nat.Prime.coprime_iff_not_dvd hℓp.out).2 hNℓ)
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
    obtain ⟨P, P', hPQ, hdP, hdQ, hPi, hQi⟩ := htor d Λ hd hd4 hcm hΔ ℓ h5 hdℓ ι q (hQ.1 q hq).1 ((1 + d) / 4)
      (by omega) hNℓ (natCast_normOm_mul_mem hd4 hcm (hQ.1 q hq).2)
    exact isInt_translate hℓ2 Λ (ι : ℂ →+* ℂ_[ℓ]) h2 h3 hε ht (hQ.1 q hq).1 hNn hPQ hdP hdQ hPi hQi
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

/-! ## `≃`, the hermitian property, and substituting `[α]` into two-variable series -/

section Pair

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`≃` is stable under differences.** -/
theorem _root_.CMFormalInert.Simeq.sub {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[ℓ]} (h₁ : Simeq f g)
    (h₂ : Simeq f' g') : Simeq (f - f') (g - g') := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- **`≃` is stable under multiplication by natural numbers.** -/
theorem _root_.CMFormalInert.Simeq.natCast_mul {σ : Type} {f g : MvPowerSeries σ ℂ_[ℓ]} (h : Simeq f g) (n : ℕ) :
    Simeq (MvPowerSeries.C (n : ℂ_[ℓ]) * f) (MvPowerSeries.C (n : ℂ_[ℓ]) * g) := by
  induction n with
  | zero => simpa using Simeq.refl (0 : MvPowerSeries σ ℂ_[ℓ])
  | succ n ih =>
    have e : ∀ u : MvPowerSeries σ ℂ_[ℓ],
        MvPowerSeries.C ((n + 1 : ℕ) : ℂ_[ℓ]) * u = MvPowerSeries.C (n : ℂ_[ℓ]) * u + u := fun u => by
      push_cast
      rw [map_add, map_one]
      ring
    rw [e, e]
    exact ih.add h

/-- **`≃` is stable under integral rescaling** of the variables. -/
theorem _root_.CMFormalInert.Simeq.rescale {σ : Type} [Finite σ] {f g : MvPowerSeries σ ℂ_[ℓ]} (h : Simeq f g)
    {c : σ → ℂ_[ℓ]} (hc : ∀ i, ‖c i‖ ≤ 1) : Simeq (MvPowerSeries.rescale c f) (MvPowerSeries.rescale c g) := by
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_eq_subst]
  refine h.subst (fun i n => ?_) (fun i => ?_)
  · rw [Pi.smul_apply', MvPowerSeries.coeff_smul, norm_mul]
    exact mul_le_one_of_le (hc i) (isIntK_X i n) (norm_nonneg _)
  · rw [Pi.smul_apply', MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

/-- **Teichmüller elements are integral.** -/
theorem norm_le_one_of_teich {ζ : ℂ_[ℓ]} (hζ : ζ ^ (ℓ ^ 2) = ζ) : ‖ζ‖ ≤ 1 := by
  by_contra h
  push Not at h
  have h1 : ‖ζ‖ < ‖ζ‖ ^ (ℓ ^ 2) := lt_self_pow₀ h (by have := hℓp.out.two_le; nlinarith)
  rw [← norm_pow, hζ] at h1
  exact lt_irrefl _ h1

/-- **The hermitian property passes along `≃`** (`≃` is stable under the integral rescalings). -/
theorem _root_.CMFormalBiadd.IsHerm.of_simeq {B B' : MvPowerSeries (Fin 2) ℂ_[ℓ]} (hB : IsHerm B)
    (h : Simeq B B') : IsHerm B' := by
  intro ζ hζ
  have hζ1 := norm_le_one_of_teich hζ
  have hζl : ‖ζ‖ ^ ℓ ≤ 1 := pow_le_one₀ (norm_nonneg _) hζ1
  have c1 : ∀ i, ‖(![ζ, 1] : Fin 2 → ℂ_[ℓ]) i‖ ≤ 1 := fun i => by fin_cases i <;> simp [hζ1]
  have c2 : ∀ i, ‖(![1, ζ ^ ℓ] : Fin 2 → ℂ_[ℓ]) i‖ ≤ 1 := fun i => by fin_cases i <;> simp [hζl]
  exact ((h.symm.rescale c1).trans (hB ζ hζ)).trans (h.rescale c2)

/-- **Substituting into a substitution of a pair.** -/
theorem subst_pair_subst {σ τ : Type} [Finite σ] (F : MvPowerSeries (Fin 2) ℂ_[ℓ])
    {ψ : Fin 2 → MvPowerSeries σ ℂ_[ℓ]} {χ : σ → MvPowerSeries τ ℂ_[ℓ]}
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) (hχ : ∀ i, MvPowerSeries.constantCoeff (χ i) = 0) :
    (F.subst ψ).subst χ = F.subst ![(ψ 0).subst χ, (ψ 1).subst χ] := by
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hψ)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hχ)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **`[α]` in the variables of a pair**: `P_α = ([α]X, [α]Y)`. -/
def mulPair (α : ℂ_[ℓ]) : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ] := fun i => (mulLT α).subst (MvPowerSeries.X i)

/-- **`[α]X_i` has no constant term.** -/
theorem constantCoeff_mulLT_X {σ : Type} (α : ℂ_[ℓ]) (i : σ) :
    MvPowerSeries.constantCoeff ((mulLT α).subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[ℓ])) = 0 :=
  constantCoeff_mulLT_subst α (MvPowerSeries.constantCoeff_X i)

/-- **`[α]X_i` is integral** when `[α]` is. -/
theorem intS_mulLT_X {σ : Type} {α : ℂ_[ℓ]} (hm : IsInt (mulLT α)) (i : σ) :
    IntS ((mulLT α).subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[ℓ])) :=
  hm.isIntK.subst (fun _ => isIntK_X i) fun _ => MvPowerSeries.constantCoeff_X i

/-- **Evaluating `[α]X_i`**: `([α]X_i)(χ) = [α](χ_i)`. -/
theorem subst_mulLT_X {σ τ : Type} [Finite σ] (α : ℂ_[ℓ]) (i : σ) {χ : σ → MvPowerSeries τ ℂ_[ℓ]}
    (hχ : ∀ i, MvPowerSeries.constantCoeff (χ i) = 0) :
    ((mulLT α).subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[ℓ])).subst χ = (mulLT α).subst (χ i) := by
  rw [subst_subst _ (MvPowerSeries.constantCoeff_X i) (MvPowerSeries.hasSubst_of_constantCoeff_zero hχ),
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hχ)]

/-- **`L` along `[α]`**: `L([α]X)L([α]Y) = α²·L(X)L(Y)`. -/
theorem logXY_subst_mulPair (α : ℂ_[ℓ]) :
    (logX ℓ * logY ℓ).subst (mulPair α) = MvPowerSeries.C (α ^ 2) * (logX ℓ * logY ℓ) := by
  have hP : MvPowerSeries.HasSubst (mulPair α) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => constantCoeff_mulLT_X α i
  have h : ∀ i : Fin 2, MvPowerSeries.subst (mulPair α) ((logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X i)) =
      α • (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[ℓ]) := fun i => by
    rw [subst_subst _ (MvPowerSeries.constantCoeff_X i) hP, MvPowerSeries.subst_X hP]
    exact lgP_subst_mulLT α (MvPowerSeries.constantCoeff_X i)
  rw [MvPowerSeries.subst_mul hP, logX, logY, h, h, smul_mul_smul_comm, MvPowerSeries.smul_eq_C_mul, sq]

/-- **`[ζα]`-twists**: `[α](ζA) = ζ·[α]A` for a Teichmüller `ζ` (`rescale_mulLT_teich`). -/
theorem mulLT_subst_smul (α : ℂ_[ℓ]) {ζ : ℂ_[ℓ]} (hζ : ζ ^ (ℓ ^ 2) = ζ) {σ : Type} {A : MvPowerSeries σ ℂ_[ℓ]}
    (hA : MvPowerSeries.constantCoeff A = 0) : (mulLT α).subst (ζ • A) = ζ • (mulLT α).subst A := by
  have hAs : HasSubst A := HasSubst.of_constantCoeff_zero hA
  have e : ζ • A = (ζ • X : ℂ_[ℓ]⟦X⟧).subst A := by rw [subst_smul hAs, subst_X hAs]
  rw [e, ← subst_comp_subst_apply (HasSubst.smul_X' ζ) hAs, ← rescale_eq_subst, rescale_mulLT_teich α hζ,
    ← smul_eq_C_mul, subst_smul hAs]

/-- **Rescaling commutes with `P_α`** for Teichmüller factors. -/
theorem rescale_subst_mulPair (α : ℂ_[ℓ]) {c : Fin 2 → ℂ_[ℓ]} (hc : ∀ i, c i ^ (ℓ ^ 2) = c i)
    (F : MvPowerSeries (Fin 2) ℂ_[ℓ]) :
    MvPowerSeries.rescale c (F.subst (mulPair α)) = (MvPowerSeries.rescale c F).subst (mulPair α) := by
  have hP : MvPowerSeries.HasSubst (mulPair α) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => constantCoeff_mulLT_X α i
  have hcX : MvPowerSeries.HasSubst (c • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) :=
    MvPowerSeries.HasSubst.smul_X c
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.subst_comp_subst_apply hP hcX, MvPowerSeries.subst_comp_subst_apply hcX hP]
  congr 1
  funext i
  simp only [mulPair]
  rw [subst_subst _ (MvPowerSeries.constantCoeff_X i) hcX, MvPowerSeries.subst_X hcX, Pi.smul_apply',
    mulLT_subst_smul α (hc i) (MvPowerSeries.constantCoeff_X i), MvPowerSeries.subst_smul hP,
    MvPowerSeries.subst_X hP]
  rfl

/-- **The hermitian property passes to `B(P_α)`** (`[α]` commutes with the Teichmüller units). -/
theorem _root_.CMFormalBiadd.IsHerm.subst_mulPair {F : MvPowerSeries (Fin 2) ℂ_[ℓ]} (hF : IsHerm F) {α : ℂ_[ℓ]}
    (hm : IsInt (mulLT α)) : IsHerm (F.subst (mulPair α)) := by
  intro ζ hζ
  have hζl : (ζ ^ ℓ) ^ (ℓ ^ 2) = ζ ^ ℓ := by rw [← pow_mul, mul_comm, pow_mul, hζ]
  have c1 : ∀ i, (![ζ, 1] : Fin 2 → ℂ_[ℓ]) i ^ (ℓ ^ 2) = (![ζ, 1] : Fin 2 → ℂ_[ℓ]) i := fun i => by
    fin_cases i <;> simp [hζ]
  have c2 : ∀ i, (![1, ζ ^ ℓ] : Fin 2 → ℂ_[ℓ]) i ^ (ℓ ^ 2) = (![1, ζ ^ ℓ] : Fin 2 → ℂ_[ℓ]) i := fun i => by
    fin_cases i <;> simp [hζl]
  rw [rescale_subst_mulPair α c1, rescale_subst_mulPair α c2]
  exact (hF ζ hζ).subst (fun i => intS_mulLT_X hm i) fun i => constantCoeff_mulLT_X α i

/-- **Symmetry passes to `B(P_α)`.** -/
theorem subst_swap_mulPair (α : ℂ_[ℓ]) {F : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hF : MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] F = F) :
    MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (F.subst (mulPair α)) = F.subst (mulPair α) := by
  have cP : ∀ i, MvPowerSeries.constantCoeff (mulPair α i) = 0 := fun i => constantCoeff_mulLT_X α i
  have hP : MvPowerSeries.HasSubst (mulPair α) := MvPowerSeries.hasSubst_of_constantCoeff_zero cP
  have cs : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) i) = 0 := fun i => by
    fin_cases i <;> exact MvPowerSeries.constantCoeff_X _
  conv_rhs => rw [← hF]
  rw [subst_pair_subst F cP cs, subst_pair_subst F cs cP]
  have e0 : MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (mulPair α 0) = mulPair α 1 :=
    subst_mulLT_X α 0 cs
  have e1 : MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (mulPair α 1) = mulPair α 0 :=
    subst_mulLT_X α 1 cs
  have f0 : MvPowerSeries.subst (mulPair α)
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) 0) = mulPair α 1 :=
    MvPowerSeries.subst_X hP 1
  have f1 : MvPowerSeries.subst (mulPair α)
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) 1) = mulPair α 0 :=
    MvPowerSeries.subst_X hP 0
  rw [e0, e1, f0, f1]

/-- **Biadditivity defects along `P_α`**: `deltaX(B(P_α)) = (deltaX B)([α]X, [α]X′, [α]Y)`, as `[α]` is an
endomorphism of the group law (`mulLT_subst_addP`). -/
theorem deltaX_subst_mulPair (α : ℂ_[ℓ]) (F : MvPowerSeries (Fin 2) ℂ_[ℓ]) :
    deltaX (F.subst (mulPair α)) =
      (deltaX F).subst (fun i : Fin 3 => (mulLT α).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ])) := by
  set ψ : Fin 3 → MvPowerSeries (Fin 3) ℂ_[ℓ] := fun i => (mulLT α).subst (MvPowerSeries.X i) with hψdef
  have cψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0 := fun i => constantCoeff_mulLT_X α i
  have hψ : MvPowerSeries.HasSubst ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero cψ
  have cP : ∀ i, MvPowerSeries.constantCoeff (mulPair α i) = 0 := fun i => constantCoeff_mulLT_X α i
  have cX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hX : ∀ i : Fin 3, MvPowerSeries.subst ψ (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) =
      (mulLT α).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) :=
    fun i => MvPowerSeries.subst_X hψ i
  have c2 : ∀ {A B : MvPowerSeries (Fin 3) ℂ_[ℓ]}, MvPowerSeries.constantCoeff A = 0 →
      MvPowerSeries.constantCoeff B = 0 →
        ∀ i, MvPowerSeries.constantCoeff ((![A, B] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[ℓ]) i) = 0 := fun hA hB i => by
    fin_cases i
    · exact hA
    · exact hB
  have t : ∀ A B : MvPowerSeries (Fin 3) ℂ_[ℓ], ∀ (hA : MvPowerSeries.constantCoeff A = 0)
      (hB : MvPowerSeries.constantCoeff B = 0), MvPowerSeries.subst ψ A = (mulLT α).subst A →
      MvPowerSeries.subst ψ B = (mulLT α).subst B →
      (F.subst (mulPair α)).subst ![A, B] = (F.subst ![A, B]).subst ψ := by
    intro A B hA hB eA eB
    rw [subst_pair_subst F cP (c2 hA hB), subst_pair_subst F (c2 hA hB) cψ]
    congr 1
    funext i
    fin_cases i
    · change ((mulLT α).subst (MvPowerSeries.X 0)).subst ![A, B] = MvPowerSeries.subst ψ A
      rw [subst_mulLT_X α 0 (c2 hA hB), eA]
      rfl
    · change ((mulLT α).subst (MvPowerSeries.X 1)).subst ![A, B] = MvPowerSeries.subst ψ B
      rw [subst_mulLT_X α 1 (c2 hA hB), eB]
      rfl
  have hadd : MvPowerSeries.subst ψ
      (addP (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ_[ℓ]) =
      (mulLT α).subst (addP (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ_[ℓ]) := by
    rw [mulLT_subst_addP α (cX 0) (cX 1), addP, subst_pair_subst _ (c2 (cX 0) (cX 1)) cψ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hX, hX]
    rfl
  simp only [deltaX]
  rw [MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_sub hψ,
    ← t _ _ (constantCoeff_addP (cX 0) (cX 1)) (cX 2) hadd (hX 2), ← t _ _ (cX 0) (cX 2) (hX 0) (hX 2),
    ← t _ _ (cX 1) (cX 2) (hX 1) (hX 2)]

/-- **Biadditivity passes to `B(P_α)`** for integral `[α]`. -/
theorem simeq_deltaX_subst_mulPair {α : ℂ_[ℓ]} (hm : IsInt (mulLT α)) {F : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hF : Simeq (deltaX F) 0) : Simeq (deltaX (F.subst (mulPair α))) 0 := by
  have cψ : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      ((mulLT α).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ])) = 0 := fun i => constantCoeff_mulLT_X α i
  have h := hF.subst (fun i => intS_mulLT_X hm i) cψ
  rwa [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero cψ), map_zero,
    MvPowerSeries.coe_substAlgHom, ← deltaX_subst_mulPair] at h

/-- **Substitutions keep coefficients in a subfield**: if `F` and the `ψ_s` (without constant terms) have their
coefficients in `k`, so has `F(ψ)`. -/
theorem coeff_subst_mem (k : Subfield ℂ_[ℓ]) {σ τ : Type} [Finite σ] {F : MvPowerSeries σ ℂ_[ℓ]}
    (hF : ∀ n, MvPowerSeries.coeff n F ∈ k) {ψ : σ → MvPowerSeries τ ℂ_[ℓ]}
    (hψ0 : ∀ s, MvPowerSeries.constantCoeff (ψ s) = 0) (hψ : ∀ s n, MvPowerSeries.coeff n (ψ s) ∈ k) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n (F.subst ψ) ∈ k := by
  set F' : MvPowerSeries σ k := fun n => ⟨MvPowerSeries.coeff n F, hF n⟩
  set ψ' : σ → MvPowerSeries τ k := fun s n => ⟨MvPowerSeries.coeff n (ψ s), hψ s n⟩
  have hF' : MvPowerSeries.map k.subtype F' = F := by ext n; rfl
  have hψ' : ∀ s, MvPowerSeries.map k.subtype (ψ' s) = ψ s := fun s => by ext n; rfl
  have hψ'0 : ∀ s, MvPowerSeries.constantCoeff (ψ' s) = 0 := fun s => Subtype.ext (by
    change MvPowerSeries.coeff 0 (ψ s) = 0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ0 s])
  have h := MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hψ'0) (h := k.subtype) F'
  rw [hF'] at h
  simp only [hψ'] at h
  rw [← h, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff n (F'.subst ψ')).2

/-- **`[α]X_i` has coefficients in `k`** for `α ∈ k`. -/
theorem coeff_mulLT_X_mem (k : Subfield ℂ_[ℓ]) (α : k) {σ : Type} (i : σ) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n ((mulLT (α : ℂ_[ℓ])).subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[ℓ])) ∈ k := by
  classical
  refine coeff_subst_mem k (σ := Unit) (fun e => ?_) (fun _ => MvPowerSeries.constantCoeff_X i) (fun _ e => ?_) n
  · have h := coeff_mulLT_mem k α (e ())
    have he : Finsupp.single () (e ()) = e := by
      ext
      simp
    rwa [PowerSeries.coeff, he] at h
  · rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact one_mem k
    · exact zero_mem k


end Pair

/-! ## The classification `be ≃ c·serAB` without the hermitian input -/

section Classification

open PeriodPair ThetaNorm

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`be` along `P_α`**: `be([α]X, [α]Y) = (ph∘[α])(X ⊕ Y) − (ph∘[α])(X) − (ph∘[α])(Y)` (`[α]` is an
endomorphism of the group law). -/
theorem be_subst_mulPair (a b s ε α : ℂ_[ℓ]) :
    (be ℓ a b s ε).subst (mulPair α) =
      PowerSeries.subst (ltAdd ℂ_[ℓ] ℓ) ((ph ℓ a b s ε).subst (mulLT α)) -
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) ((ph ℓ a b s ε).subst (mulLT α)) -
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) ((ph ℓ a b s ε).subst (mulLT α)) := by
  have hℓ := hℓp.out.one_lt
  have cP : ∀ i, MvPowerSeries.constantCoeff (mulPair α i) = 0 := fun i => constantCoeff_mulLT_X α i
  have hP : MvPowerSeries.HasSubst (mulPair α) := MvPowerSeries.hasSubst_of_constantCoeff_zero cP
  have hms := hasSubst_mulLT α
  have hl : MvPowerSeries.subst (mulPair α) (ltAdd ℂ_[ℓ] ℓ) = (mulLT α).subst (ltAdd ℂ_[ℓ] ℓ) := by
    have e : ltAdd ℂ_[ℓ] ℓ = addP (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by
      rw [addP, show (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) =
        MvPowerSeries.X from by funext i; fin_cases i <;> rfl, MvPowerSeries.subst_self]
      rfl
    conv_rhs => rw [e]
    rw [mulLT_subst_addP α (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1), addP]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [be, MvPowerSeries.subst_sub hP, MvPowerSeries.subst_sub hP, subst_subst _ (constantCoeff_ltAdd hℓ) hP,
    subst_subst _ (MvPowerSeries.constantCoeff_X 0) hP, subst_subst _ (MvPowerSeries.constantCoeff_X 1) hP,
    MvPowerSeries.subst_X hP, MvPowerSeries.subst_X hP, hl]
  simp only [mulPair]
  rw [← subst_comp_subst_apply hms (HasSubst.of_constantCoeff_zero (constantCoeff_ltAdd hℓ)),
    ← subst_comp_subst_apply hms (HasSubst.X 0), ← subst_comp_subst_apply hms (HasSubst.X 1)]

/-- **The classification without `IsHerm`**: for the `Δ = 1` CM lattice at an inert `ℓ ≥ 5` and every unit
`ε ∈ K^ur` making `t(ε·log_LT(T))` integral, `be ≃ c·serAB` with `c ∈ K^ur`, `φ(c) = −c`, `‖c‖ ≤ 1`. By the
structure theorem, `be ≃ a·L(X)L(Y) + γ·serAB`. Polarising the CM equivariance (`cm_equiv`) gives
`be([ω]X, [ω]Y) ≃ N·be(X, Y)`; on the other side `be([ω]X, [ω]Y) ≃ aω²·L(X)L(Y) + B₂` with `B₂ = (γ·serAB)([ω]X, [ω]Y)`,
which is exactly hermitian (`[ω]` commutes with the Teichmüller units), so `B₂ ≃ γ₂·serAB` (`bdd_of_isHerm`,
`alpha_eq_zero_iff`). Uniqueness of the pair gives `a(N − ω²) = 0`, and `ω² ≠ N(ω) = ωω̄`: `a = 0`. -/
theorem be_simeq_serAB_cm (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram)
    (htor : TorsionTransl) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
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
    have hce := cm_equiv hj htor hd hd4 hcm hΔ h5 hdℓ hin ι hφ hε ht
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

/-- **The hermitian property of `be` for the CM curve, proved** (the headline): under CM-a′/c/d, the torsion
arithmetic `TorsionTransl` and a Frobenius lift on `K^ur`, `IsHerm (be …)` holds for every unit `ε ∈ K^ur` making
`t(ε·log_LT(T))` integral, exactly the hypothesis `hH` of `be_classification_cm'` (`be_simeq_serAB_cm`,
`isHerm_C_mul_serAB`, `IsHerm.of_simeq`). -/
theorem isHerm_be_cm (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified) (hs : CMs2Unram) (htor : TorsionTransl)
    (hF : UnramFrob ℓ) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
    (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι : ℂ ≃+* ℂ_[ℓ]) :
    ∀ ε : ℂ_[ℓ], ε ∈ unramC ℓ → ‖ε‖ = 1 → IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) →
      IsHerm (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε) := by
  intro ε hεu hε ht
  obtain ⟨φ, hφ⟩ := hF
  obtain ⟨c, -, -, hc⟩ := be_simeq_serAB_cm hj hu hs htor hd hd4 hcm hΔ h5 hdℓ hin ι hφ hεu hε ht
  exact (isHerm_C_mul_serAB _).of_simeq hc.symm

/-- **The classification for the CM curve without the hermitian input** (`be_classification_cm'` with
`isHerm_be_cm`): with CM-b, CM-c, CM-a′, the strengthened CM-d, `TorsionTransl` and a Frobenius lift `φ` on `K^ur`,
the Lubin–Tate unit `ε` of CM-b has `be ≃ c·serAB` with `φ(c) = −c`, `‖c‖ ≤ 1`. -/
theorem be_classification_cm_omega (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified)
    (hs : CMs2Unram) (htor : TorsionTransl) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : HasCM d Λ) (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d)
    (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι : ℂ ≃+* ℂ_[ℓ]) {φ : unramC ℓ →+* unramC ℓ}
    (hφ : ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ c : unramC ℓ, φ c = -c ∧ ‖c‖ ≤ 1 ∧
      Simeq (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (s2 Λ)) ε) (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) :=
  be_classification_cm' hb hj hu hs hd hd4 hcm hΔ h5 hdℓ hin ι hφ
    (isHerm_be_cm hj hu hs htor ⟨φ, hφ⟩ hd hd4 hcm hΔ h5 hdℓ hin ι)

end Classification

end

end CMEquiv
