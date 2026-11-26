import ThetaNorm

/-!
# The canonical theta of the chain

The constants and the base theta of the explicit theta chain (chain spec §3.3), as closed definitions: no `Pin`, no
`ThetaStd`, no root of a theta taken. Everything here is a function of `sd = √d/2`, of the lattice `Λ_M` and the
isometry `g` of `θ₀` (choices of the construction), and, for the constants `TP`, of the embedding `σ₀`, the ideal `𝔟`
and the coordinate generators `g_τ`.

**The CM lattice.** `ω = (1 + i√d)/2 = 1/2 + i·sd` (`omegaD`) and the base lattice `ℤ + ℤω` (`baseLat`), the image of
`O_{K₀}` at the chosen embedding. Its discriminant `Δ = g₂³ − 27g₃²` (`discr`, with Mathlib's `g₂`, `g₃`) has the
principal 12th root `δ` (`deltaC`), and the canonical lattice is `Lc = δ·(ℤ + ℤω)` (`cmLat`), so that `Δ(Lc) = 1`
(`discr_cmLat`, from `G_n(cΛ) = c^{−n}G_n(Λ)`, `G_eq_of_lattice_eq`). The form is `s = 1/area(Lc)` (`sC`, positive
for every lattice, `sC_pos`) and the 2-torsion point is `t = δ/2` (`tC`): `2t ∈ Lc` and `(1 ± √−d)t/2 ∉ Lc`, as
`ω/2 ∉ ℤ + ℤω` (`tC_spec`, the clauses of `Pin.Canonical`). Period pairs are built by `perLat`, which falls back to
`(1, i)` when the two periods are dependent, so the definitions carry no proof: they hold the intended values when
`sd ≠ 0` and `Δ(ℤ + ℤω) ≠ 0`, and the lemmas take these facts as hypotheses.

**The base theta.** With `κ = 1`, `G = (Iop(Lc^{4Φ}, g(Λ_M⁴)) F0) ∘ g` (`bigG`) is the right side of `IsTheta0` for
the canonical pin (`canonPin`, `isTheta0_canonPin_iff`). The base theta of a step is
`θ_std(z) = ∏_{i<b, j<a} G(z_{·ij}, 0, 0, 0)·G(0)^{−3ab/4}` (`thetaStd`, with `slot0 v = (v, 0, 0, 0)`). For a `θ₀`
with `θ₀^{⊗4} = G` it is `tensPow θ₀` when `4 ∣ ab`: `θ₀(v)θ₀(0)³ = G(v, 0, 0, 0)` and `θ₀(0)⁴ = G(0)`
(`slice_slot0`). Every rank `N_j = k + j(t + 1)` of the chain is even, so `4 ∣ N_jN_{j+1}` at every step, and no fourth
root is taken: the `ζ⁴` freedom of `θ₀` is gone.

**The constants.** `chainTP` is the `TP` of the chain: `σ₀`, `δ = deltaC`, `s = sC`, `sd`, `𝔄 = 𝔟⁻¹` (`ideA`, the
`x` with `x𝔟 ⊆ O_E`, `mem_ideA`; the spec's `O_{K₀}·𝔟⁻¹` is the same `O_E`-module, as `1 ∈ O_{K₀} ⊆ O_E`) and
`cD(τ) = σ₀(g_τ)`. The lattice of `θ₀` is `Λ_M = ι(𝔄)` (`lamM`).

**Main declarations** (read by the Stage-U chain): `deltaC`, `cmLat`, `sC`, `tC`, `bigG`, `thetaStd`, `lamM`, `ideA`,
`chainTP`, `canonPin`.

**Sanity theorems:** `discr_cmLat`, `tC_spec`, `sC_pos`, `mem_ideA`, `isTheta0_canonPin_iff`, `slice_slot0`.
-/

namespace ChainCanon

open NumberField ThetaChain ThetaNorm Complex

noncomputable section

/-! ## The CM lattice -/

section Lattice

/-- **The generator `ω = (1 + i√d)/2`** of `O_{K₀}` at the chosen embedding, as `1/2 + i·sd` (`sd = √d/2`). -/
def omegaD (sd : ℝ) : ℂ := 1 / 2 + sd * I

/-- **The square lattice `(1, i)`**, the fallback of `perLat`. -/
def sqLat : PeriodPair := ⟨1, I, by simpa using Complex.basisOneI.linearIndependent⟩

open Classical in
/-- **The period pair of two periods**: `(ω₁, ω₂)` when they are `ℝ`-independent, the square lattice otherwise (so
the definitions below carry no proof). -/
def perLat (ω₁ ω₂ : ℂ) : PeriodPair := if h : LinearIndependent ℝ ![ω₁, ω₂] then ⟨ω₁, ω₂, h⟩ else sqLat

/-- **`perLat` returns its first period** when the periods are independent. -/
theorem perLat_ω₁ {ω₁ ω₂ : ℂ} (h : LinearIndependent ℝ ![ω₁, ω₂]) : (perLat ω₁ ω₂).ω₁ = ω₁ := by
  simp [perLat, h]

/-- **`perLat` returns its second period** when the periods are independent. -/
theorem perLat_ω₂ {ω₁ ω₂ : ℂ} (h : LinearIndependent ℝ ![ω₁, ω₂]) : (perLat ω₁ ω₂).ω₂ = ω₂ := by
  simp [perLat, h]

/-- **`c` and `cω` are `ℝ`-independent** for `c ≠ 0` and `sd ≠ 0` (`Im ω = sd`). -/
theorem indep_omegaD {c : ℂ} {sd : ℝ} (hc : c ≠ 0) (hsd : sd ≠ 0) :
    LinearIndependent ℝ ![c, c * omegaD sd] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  have h : (s : ℂ) + t * omegaD sd = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left hc
    rw [← hst, Complex.real_smul, Complex.real_smul]
    ring
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [omegaD] at him hre
  have ht : t = 0 := him.resolve_right hsd
  subst ht
  simpa using hre

/-- **The base lattice `ℤ + ℤω`** (`φ₀(O_{K₀})`). -/
def baseLat (sd : ℝ) : PeriodPair := perLat 1 (omegaD sd)

/-- **The periods of `ℤ + ℤω`** for `sd ≠ 0`. -/
theorem baseLat_ω (sd : ℝ) (hsd : sd ≠ 0) : (baseLat sd).ω₁ = 1 ∧ (baseLat sd).ω₂ = omegaD sd := by
  have h : LinearIndependent ℝ ![(1 : ℂ), omegaD sd] := by simpa using indep_omegaD one_ne_zero hsd
  exact ⟨perLat_ω₁ h, perLat_ω₂ h⟩

/-- **The discriminant** `Δ = g₂³ − 27g₃²` of a period pair (Mathlib's `g₂ = 60G₄`, `g₃ = 140G₆`). -/
def discr (Lp : PeriodPair) : ℂ := Lp.g₂ ^ 3 - 27 * Lp.g₃ ^ 2

/-- **`δ`, the principal 12th root of `Δ(ℤ + ℤω)`**: canonical, no choice. -/
def deltaC (sd : ℝ) : ℂ := discr (baseLat sd) ^ (12 : ℂ)⁻¹

/-- **The canonical CM lattice `Lc = δ·(ℤ + ℤω)`**, with `Δ(Lc) = 1` (`discr_cmLat`). -/
def cmLat (sd : ℝ) : PeriodPair := perLat (deltaC sd) (deltaC sd * omegaD sd)

/-- **The form `s = 1/area(Lc)`** of the theta functions. -/
def sC (sd : ℝ) : ℝ := (area (cmLat sd))⁻¹

/-- **The 2-torsion point `t = δ/2`** of `Lc` (`tC_spec`). -/
def tC (sd : ℝ) : ℂ := deltaC sd / 2

/-- **`δ¹² = Δ(ℤ + ℤω)`.** -/
theorem deltaC_pow (sd : ℝ) : deltaC sd ^ 12 = discr (baseLat sd) := cpow_ofNat_inv_pow _ 12

/-- **`δ ≠ 0`** when `Δ(ℤ + ℤω) ≠ 0`. -/
theorem deltaC_ne_zero {sd : ℝ} (hΔ : discr (baseLat sd) ≠ 0) : deltaC sd ≠ 0 := fun h =>
  hΔ (by rw [← deltaC_pow, h]; norm_num)

/-- **The periods of `Lc`** for `sd ≠ 0` and `Δ(ℤ + ℤω) ≠ 0`. -/
theorem cmLat_ω {sd : ℝ} (hsd : sd ≠ 0) (hΔ : discr (baseLat sd) ≠ 0) :
    (cmLat sd).ω₁ = deltaC sd ∧ (cmLat sd).ω₂ = deltaC sd * omegaD sd :=
  ⟨perLat_ω₁ (indep_omegaD (deltaC_ne_zero hΔ) hsd), perLat_ω₂ (indep_omegaD (deltaC_ne_zero hΔ) hsd)⟩

/-- **`Lc = δ·(ℤ + ℤω)`** as lattices. -/
theorem cmLat_lattice {sd : ℝ} (hsd : sd ≠ 0) (hΔ : discr (baseLat sd) ≠ 0) :
    (cmLat sd).lattice = (baseLat sd).lattice.map (LinearMap.mulLeft ℤ (deltaC sd)) := by
  rw [PeriodPair.lattice, PeriodPair.lattice, Submodule.map_span, Set.image_pair, (cmLat_ω hsd hΔ).1,
    (cmLat_ω hsd hΔ).2, (baseLat_ω sd hsd).1, (baseLat_ω sd hsd).2]
  simp

/-- **Scaling the lattice**: `G_n(cΛ) = c^{−n}·G_n(Λ)` (reindex the sum by `l ↦ cl`). -/
theorem G_eq_of_lattice_eq {Lp Lp' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : Lp'.lattice = Lp.lattice.map (LinearMap.mulLeft ℤ c)) (n : ℕ) : Lp'.G n = (c ^ n)⁻¹ * Lp.G n := by
  let e : Lp.lattice ≃ₗ[ℤ] Lp'.lattice :=
    (Submodule.equivMapOfInjective _ (mul_right_injective₀ hc) Lp.lattice).trans (LinearEquiv.ofEq _ _ h.symm)
  rw [PeriodPair.G, PeriodPair.G, ← tsum_mul_left, ← e.toEquiv.tsum_eq]
  congr 1
  ext l
  change ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]

/-- **Scaling the discriminant**: `Δ(cΛ) = c^{−12}·Δ(Λ)`. -/
theorem discr_eq_of_lattice_eq {Lp Lp' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : Lp'.lattice = Lp.lattice.map (LinearMap.mulLeft ℤ c)) : discr Lp' = (c ^ 12)⁻¹ * discr Lp := by
  simp only [discr, PeriodPair.g₂, PeriodPair.g₃, G_eq_of_lattice_eq hc h]
  field_simp

/-- **`Δ(Lc) = 1`**: the normalisation of the CM lattice. -/
theorem discr_cmLat {sd : ℝ} (hsd : sd ≠ 0) (hΔ : discr (baseLat sd) ≠ 0) : discr (cmLat sd) = 1 := by
  rw [discr_eq_of_lattice_eq (deltaC_ne_zero hΔ) (cmLat_lattice hsd hΔ), deltaC_pow, inv_mul_cancel₀ hΔ]

/-- **`t = δ/2` is a 2-torsion point killed by neither `(1 ± √−d)/2`**: `2t ∈ Lc`, `(1/2 ± i·sd)·t ∉ Lc` (the
clauses of `Pin.Canonical` on `t`; `(1 + √−d)t/2 = ω₂/2` and `(1 − √−d)t/2 = (ω₁ − ω₂)/2`). -/
theorem tC_spec {sd : ℝ} (hsd : sd ≠ 0) (hΔ : discr (baseLat sd) ≠ 0) :
    2 * tC sd ∈ (cmLat sd).lattice ∧ (1 / 2 + sd * I) * tC sd ∉ (cmLat sd).lattice ∧
      (1 / 2 - sd * I) * tC sd ∉ (cmLat sd).lattice := by
  obtain ⟨h1, h2⟩ := cmLat_ω hsd hΔ
  refine ⟨?_, ?_, ?_⟩
  · simpa [tC, h1, mul_div_cancel₀] using (cmLat sd).ω₁_mem_lattice
  · convert (cmLat sd).ω₂_div_two_notMem_lattice using 2
    rw [h2, tC, omegaD]
    ring
  · convert (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := cmLat sd) (α := 1 / 2) (β := -1 / 2)).not.mpr
      (by norm_num) using 2
    rw [h1, h2, tC, omegaD]
    push_cast
    ring

/-- **Every period pair has positive area** (`Im(ω̄₁ω₂) ≠ 0` by independence). -/
theorem area_pos (Lp : PeriodPair) : 0 < area Lp := by
  refine abs_pos.mpr fun h => ?_
  have hi := LinearIndependent.pair_iff.mp Lp.indep
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
  obtain ⟨h1, h2⟩ := hi Lp.ω₂.im (-Lp.ω₁.im) (Complex.ext (by simp; linarith) (by simp; ring))
  obtain ⟨-, h4⟩ := hi Lp.ω₂.re (-Lp.ω₁.re) (Complex.ext (by simp; ring) (by simp [h1, neg_eq_zero.mp h2]))
  exact Lp.indep.ne_zero 0 (Complex.ext (by simpa using neg_eq_zero.mp h4) (by simpa using neg_eq_zero.mp h2))

/-- **`s > 0`** (for every `sd`). -/
theorem sC_pos (sd : ℝ) : 0 < sC sd := inv_pos.mpr (area_pos _)

end Lattice

/-! ## The base theta -/

section Theta

variable {Φ : Type*}

/-- **The first slot** `v ↦ (v, 0, 0, 0)` of `ℂ^{Fin 4 × Φ}`. -/
def slot0 (v : Φ → ℂ) : Fin 4 × Φ → ℂ := fun q => if q.1 = 0 then v q.2 else 0

/-- **The slices of `(v, 0, 0, 0)`**: `v` at `0`, and `0` elsewhere. -/
theorem slice_slot0 (k : Fin 4) (v : Φ → ℂ) : slice k (slot0 v) = if k = 0 then v else 0 := by
  ext p
  by_cases hk : k = 0 <;> simp [slice, slot0, hk]

variable [Fintype Φ]

/-- **`G = (Iop(Lc^{4Φ}, g(Λ⁴)) F0) ∘ g`**, the fourth tensor power of `θ₀` (`IsTheta0` with `κ = 1`), for the
lattice `Λ = Λ_M` of `θ₀` and the isometry `g`, with the canonical `s`, `σ*_{Lc}` and `t`. -/
def bigG (sd : ℝ) (Λ : AddSubgroup (Φ → ℂ)) (g : (Fin 4 × Φ → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ → ℂ)) :
    (Fin 4 × Φ → ℂ) → ℂ :=
  Iop (sC sd) sd (stdLat4 (cmLat sd).lattice.toAddSubgroup) ((pow4 Λ).map g.toLinearMap.toAddMonoidHom)
    (F0 (sC sd) (sgStar (cmLat sd)) (tC sd)) ∘ g

/-- **The base theta, explicit**: `θ_std(z) = ∏_{i<b, j<a} G(z_{·ij}, 0, 0, 0)·G(0)^{−3ab/4}` on `Amb Φ a b`. It
is `tensPow θ₀` for `θ₀^{⊗4} = G` when `4 ∣ ab`, with no fourth root taken. -/
def thetaStd (sd : ℝ) (Λ : AddSubgroup (Φ → ℂ)) (g : (Fin 4 × Φ → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ → ℂ)) (a b : ℕ)
    (z : Amb Φ a b) : ℂ :=
  (∏ i : Fin b, ∏ j : Fin a, bigG sd Λ g (slot0 fun p => z (p, i, j))) * (bigG sd Λ g 0 ^ (3 * (a * b / 4)))⁻¹

variable (Φ) in
/-- **The canonical pin** (for the consumers' `IsTheta0`): `Lc`, `σ*_{Lc}`, `t = δ/2`, the lattice `Λ`, the isometry
`g` and `κ = 1`, for the form `s = sC sd`. -/
def canonPin (sd : ℝ) (Λ : AddSubgroup (Φ → ℂ)) (g : (Fin 4 × Φ → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ → ℂ)) : Pin Φ (sC sd) where
  Lc := (cmLat sd).lattice.toAddSubgroup
  σ := sgStar (cmLat sd)
  t := tC sd
  Λ := Λ
  g := g
  κ := 1

/-- **`bigG` is the `G` of `IsTheta0`** for the canonical pin: `θ₀ ∈ Th(Λ)` and `θ₀^{⊗4} = G`. -/
theorem isTheta0_canonPin_iff {sd : ℝ} {Λ : AddSubgroup (Φ → ℂ)} {g : (Fin 4 × Φ → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ → ℂ)}
    {θ₀ : (Φ → ℂ) → ℂ} : IsTheta0 sd (canonPin Φ sd Λ g) θ₀ ↔ θ₀ ∈ Th (sC sd) sd Λ ∧ tens4 θ₀ = bigG sd Λ g := by
  simp [IsTheta0, canonPin, bigG]

end Theta

/-! ## The constants -/

section Constants

variable {E : Type*} [Field E]

/-- **The ideal `𝔄 = 𝔟⁻¹`** `= {x ∈ E : x𝔟 ⊆ O_E}` of `θ₀` (`mem_ideA`). -/
def ideA (𝔟 : Ideal (𝓞 E)) : Submodule (𝓞 E) E := 1 / Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔟

/-- **`x ∈ 𝔟⁻¹` iff `xy` is integral for every `y ∈ 𝔟`** (the clause of `Pin.Canonical` on `AA0`). -/
theorem mem_ideA {𝔟 : Ideal (𝓞 E)} {x : E} : x ∈ ideA 𝔟 ↔ ∀ y ∈ 𝔟, IsIntegral ℤ (x * (y : E)) := by
  simp only [ideA, Submodule.mem_div_iff_forall_mul_mem, Submodule.mem_map, Submodule.mem_one,
    Algebra.linearMap_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun y _ => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨z, hz⟩
  exact hz ▸ RingOfIntegers.isIntegral_coe z

variable {L : Type*} [Field L] {Φ : Type*}

/-- **The constants of the chain's thetas**: `σ₀`, `δ = deltaC`, `s = 1/area(Lc)`, `sd`, `𝔄 = 𝔟⁻¹` and
`cD(τ) = σ₀(g_τ)`, for the ideal `𝔟` (`𝔟 + 𝔟̄ = O_E`, `𝔟𝔟̄ = 𝔡_{E/K₀}`) and generators `g_τ` of `τ(𝔟⁻¹)O_L`. -/
def chainTP (σ₀ : L →+* ℂ) (sd : ℝ) (𝔟 : Ideal (𝓞 E)) (gτ : Φ → L) : TP E L Φ where
  σ₀ := σ₀
  δ := deltaC sd
  s := sC sd
  sd := sd
  A := ideA 𝔟
  cD p := σ₀ (gτ p)

/-- **The lattice `Λ_M = ι(𝔄)`** of `θ₀` on `ℂ^Φ`: generated by the `(δ·σ₀(τ_p w))_p`, `w ∈ 𝔄` (as in
`Pin.Canonical`). -/
def lamM (τ : Φ → (E →+* L)) (P : TP E L Φ) : AddSubgroup (Φ → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ P.A, z = fun p => P.δ * P.σ₀ (τ p w)}

end Constants

end

end ChainCanon
