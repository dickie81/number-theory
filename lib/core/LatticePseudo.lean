import Mathlib
import KLatticeVolume
import HermFormsLattice

/-!
# Pseudo-bases and the volume of `O_E`-lattices

Part II of the exact slope bound for the source of the sharp frontier: the degree `deg N = −log covol ψ(N)` of an
`O_E`-lattice `N ⊆ E^n`, for a CM field `E`, with the standard metric (`degE`, through `klat`, where
`⟪ψ x, ψ y⟫_ℝ = Tr h(x, y)/2`), for pseudo-basis lattices, duals, unimodular lattices and the attached lattices
`Lsh(d)` of decorated lattices. `D(𝔞) = ∏_i 𝔞_i ⊆ E^n` is the diagonal lattice of fractional ideals `𝔞_i`
(`diagLat`), and `O_E^n = intVec E n` the standard lattice.

**P1, pseudo-bases** (`exists_pseudo`): every lattice is `γ·D(𝔞)` with `γ ∈ GL_n(E)` and all `𝔞_i ≠ 0`, Steinitz's
first half. By induction on `n` (`exists_cols`, in columns: `γ = colMat v`), with `π` the first coordinate: `π(N)`
is a fractional ideal `𝔞₀` (`FractionalIdeal.isFractional_of_fg`), nonzero as `N` spans. From `1 ∈ 𝔞₀𝔞₀⁻¹`, a
section `v₀` with `π v₀ = 1` and `𝔞₀v₀ ⊆ N`: for `x ∈ N` and `b ∈ 𝔞₀⁻¹`, `a·(b x) = (ab)·x ∈ N` for `a ∈ 𝔞₀`,
as `ab ∈ O_E`, and such `π(b x)` form a submodule. So `N = 𝔞₀v₀ ⊕ (N ∩ ker π)`, and `N ∩ ker π` is a lattice in
`E^{n−1}`: finitely generated as `O_E` is noetherian, spanning as `N` holds a nonzero integer multiple of every
vector (`HermForms.exists_int_smul_mem`).

**P2** (`degE_pseudo`): `deg γD(𝔞) = deg O_E^n − log |N_{E/ℚ}(det γ)| − Σ_i log N(𝔞_i)`, by K1 for `γ`
(`KLattice.degK_map`) and K2 for `D(𝔞)` (`KLattice.degK_pi`).

**P3, duals** (`dual_pseudo`): `(γD(𝔞))^# = conj((γᵀ)⁻¹D(𝔞⁻¹))`, with `conj` coordinatewise (`cj`). For
`u ∈ D(𝔞)`, `conj h(γu, x) = (γu)·x̄ = u·(γᵀx̄)` (`conj_herm`), and `u·w ∈ O_E` for all `u ∈ D(𝔞)` iff
`w ∈ D(𝔞⁻¹)` (`forall_dotProduct_mem_one`). This is the spec's `D(conj(𝔞)⁻¹)·(γᴴ)⁻¹`, with the conjugation kept
outside: conjugation keeps degrees (`degE_cj`: `⟪ψ x̄, ψ ȳ⟫_ℝ = Re Σ_v σ_v conj h(x, y) = ⟪ψ x, ψ y⟫_ℝ`), so no
fractional ideal or norm needs conjugating. In particular the dual of a lattice is a lattice (`isLattice_dual`).

**P4** (`degE_dual`): `deg N^# = 2·deg O_E^n − deg N`, from P1–P3, as `|N(det (γᵀ)⁻¹)| = |N(det γ)|⁻¹` and
`N(𝔞_i⁻¹) = N(𝔞_i)⁻¹`. **P5** (`degE_of_unimodular`): `deg N = deg O_E^n` for unimodular `N = N^#`.

**P6, CRT** (`relIndex_kerLat`): for nonzero decorations `f_P`, `[N : kerLat d] = ∏_{P ∈ ST} N(P)`. The reduction
`N → ∏_P O_E/P` (`redT`) has kernel `kerLat d` and is onto: each `f_P` is onto the field `O_E/P`, and
`e_Q ≡ δ_{PQ} mod P` (CRT) glue preimages. **P7** (`degE_Lsh`): for a good `d`,
`deg Lsh(d) = deg O_E^n + Σ_{P ∈ ST} log N(P)`: P5 for `N`, P6 with `KLattice.deg_withLattice` for `kerLat d`, and
P4 for its dual `Lsh(d)` (a lattice, `isLattice_Lsh`). The local description of `Lsh(d)` is not needed.
-/

namespace HermClasses

open NumberField IsDedekindDomain Matrix Module Submodule

open scoped nonZeroDivisors

noncomputable section

/-! ### Pseudo-bases -/

section Pseudo

variable {E : Type} [Field E] {n : ℕ}

/-- **The diagonal lattice** `D(𝔞) = ∏_i 𝔞_i ⊆ E^n` of fractional ideals `𝔞_i`. -/
def diagLat (𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun i => (𝔞 i : Submodule (𝓞 E) E)

/-- Membership in `D(𝔞)`: coordinatewise. -/
theorem mem_diagLat {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E} {x : Fin n → E} : x ∈ diagLat 𝔞 ↔ ∀ i, x i ∈ 𝔞 i := by
  simp [diagLat, Submodule.mem_pi]

/-- `y ↦ (0, y)`, the inclusion `E^n → E^{n+1}` off the first coordinate. -/
def consZ : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
  (Fin.consLinearEquiv E fun _ => E).toLinearMap ∘ₗ LinearMap.inr E E _

/-- `consZ y = (0, y)`. -/
theorem consZ_apply (y : Fin n → E) : consZ y = Fin.cons 0 y := rfl

variable [NumberField E]

/-- **Pseudo-bases, in columns** (Steinitz's first half): an `O_E`-lattice `N ⊆ E^n` is
`{Σᵢ cᵢ vᵢ : cᵢ ∈ 𝔞ᵢ}` for an `E`-basis `v` and nonzero fractional ideals `𝔞ᵢ`. By induction on `n`: the first
coordinates of `N` form a fractional ideal `𝔞₀ = π(N)`; from `1 ∈ 𝔞₀𝔞₀⁻¹` a vector `v₀` with `π v₀ = 1` and
`𝔞₀v₀ ⊆ N`, so `N = 𝔞₀v₀ ⊕ (N ∩ ker π)`, and `N ∩ ker π` is a lattice in `E^{n-1}`. -/
theorem exists_cols : ∀ (n : ℕ) (N : Submodule (𝓞 E) (Fin n → E)), N.IsLattice E →
    ∃ (v : Fin n → Fin n → E) (𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E), LinearIndependent E v ∧
      (∀ i, 𝔞 i ≠ 0) ∧ ∀ x, x ∈ N ↔ ∃ c ∈ diagLat 𝔞, x = ∑ i, c i • v i := by
  intro n
  induction n with
  | zero =>
    intro N _
    refine ⟨fun i => i.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => ⟨0, mem_diagLat.2 fun i => i.elim0, by simp⟩, fun _ => zero_mem _⟩
  | succ n ih =>
    intro N hN
    -- the first coordinates form a nonzero fractional ideal `𝔞₀`
    set π₀ : (Fin (n + 1) → E) →ₗ[𝓞 E] E := LinearMap.proj 0
    have hfrac : IsFractional (𝓞 E)⁰ (N.map π₀) := FractionalIdeal.isFractional_of_fg (hN.fg.map _)
    set 𝔞₀ : FractionalIdeal (𝓞 E)⁰ E := ⟨N.map π₀, hfrac⟩
    have hmem₀ {x : Fin (n + 1) → E} (hx : x ∈ N) : x 0 ∈ 𝔞₀ := Submodule.mem_map_of_mem (f := π₀) hx
    have h𝔞₀ : 𝔞₀ ≠ 0 := by
      intro h0
      have hle : span E (N : Set (Fin (n + 1) → E)) ≤ LinearMap.ker (LinearMap.proj 0 : (Fin (n + 1) → E) →ₗ[E] E) :=
        span_le.2 fun x hx => by
          have := hmem₀ hx
          rw [h0] at this
          exact (FractionalIdeal.mem_zero_iff _).1 this
      rw [hN.span_eq_top] at hle
      have := hle (mem_top : (Pi.single 0 (1 : E) : Fin (n + 1) → E) ∈ ⊤)
      simp at this
    -- a section `v₀`: `π v₀ = 1` and `𝔞₀ v₀ ⊆ N`
    obtain ⟨v₀, hv₀, hv₀N⟩ : ∃ v₀ : Fin (n + 1) → E, v₀ 0 = 1 ∧ ∀ a ∈ 𝔞₀, a • v₀ ∈ N := by
      let W : Submodule (𝓞 E) E :=
        { carrier := {z | ∃ v : Fin (n + 1) → E, v 0 = z ∧ ∀ a ∈ 𝔞₀, a • v ∈ N}
          add_mem' := by
            rintro _ _ ⟨v, rfl, hv⟩ ⟨w, rfl, hw⟩
            exact ⟨v + w, rfl, fun a ha => by rw [smul_add]; exact add_mem (hv a ha) (hw a ha)⟩
          zero_mem' := ⟨0, rfl, fun a _ => by rw [smul_zero]; exact zero_mem _⟩
          smul_mem' := by
            rintro c _ ⟨v, rfl, hv⟩
            exact ⟨c • v, rfl, fun a ha => by rw [smul_comm]; exact N.smul_mem c (hv a ha)⟩ }
      have hle : (𝔞₀ : Submodule (𝓞 E) E) * ((𝔞₀⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ≤ W := by
        refine Submodule.mul_le.2 fun m hm b hb => ?_
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hm
        refine ⟨b • x, by simp [π₀, mul_comm], fun a ha => ?_⟩
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff h𝔞₀).1 hb a ha)
        rw [smul_smul, mul_comm, ← hr, algebraMap_smul]
        exact N.smul_mem r hx
      have h1 : (1 : E) ∈ (𝔞₀ : Submodule (𝓞 E) E) * ((𝔞₀⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
        rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h𝔞₀, FractionalIdeal.coe_one]
        exact Submodule.one_le.1 le_rfl
      exact hle h1
    -- the kernel `N' = {y : (0, y) ∈ N}` is a lattice in `E^n`
    set N' : Submodule (𝓞 E) (Fin n → E) := N.comap (consZ.restrictScalars (𝓞 E))
    have hinj : Function.Injective (consZ (E := E) (n := n)) := fun y z h => by
      funext i
      simpa [consZ_apply] using congrFun h i.succ
    have hN' : N'.IsLattice E := by
      refine ⟨Submodule.fg_of_fg_map_injective (consZ.restrictScalars (𝓞 E)) hinj
        (Submodule.FG.of_le hN.fg (Submodule.map_comap_le _ _)), eq_top_iff.2 fun y _ => ?_⟩
      obtain ⟨a, ha, haN⟩ := HermForms.exists_int_smul_mem (N := N) (x := consZ y) (by simp [hN.span_eq_top])
      have : (a : E) • y ∈ N' := by
        show consZ ((a : E) • y) ∈ N
        rwa [map_smul]
      have h := smul_mem (span E (N' : Set (Fin n → E))) (a : E)⁻¹ (subset_span this)
      rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast ha), one_smul] at h
    obtain ⟨v', 𝔞', hli', h𝔞', hmem'⟩ := ih N' hN'
    -- assemble: `v = (v₀, (0, v'))`, `𝔞 = (𝔞₀, 𝔞')`
    set V : Fin (n + 1) → Fin (n + 1) → E := Fin.cons v₀ fun i => consZ (v' i)
    refine ⟨V, Fin.cons 𝔞₀ 𝔞', ?_, fun i => Fin.cases h𝔞₀ h𝔞' i, fun x => ?_⟩
    · refine linearIndependent_finCons.2 ⟨hli'.map' consZ (LinearMap.ker_eq_bot.2 hinj), fun h => ?_⟩
      have hle : span E (Set.range fun i => consZ (v' i)) ≤
          LinearMap.ker (LinearMap.proj 0 : (Fin (n + 1) → E) →ₗ[E] E) :=
        span_le.2 fun _ ⟨i, hi⟩ => by simp [← hi, consZ_apply]
      simpa [hv₀] using hle h
    have hsum (c : Fin (n + 1) → E) : ∑ i, c i • V i = c 0 • v₀ + consZ (∑ i, c i.succ • v' i) := by
      simp [V, Fin.sum_univ_succ, map_sum, map_smul]
    have hD (c : Fin (n + 1) → E) :
        c ∈ diagLat (Fin.cons 𝔞₀ 𝔞') ↔ c 0 ∈ 𝔞₀ ∧ (fun i => c i.succ) ∈ diagLat 𝔞' := by
      simp only [mem_diagLat, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · intro hx
      have hy : consZ (Fin.tail (x - x 0 • v₀)) ∈ N := by
        have : consZ (Fin.tail (x - x 0 • v₀)) = x - x 0 • v₀ := by
          rw [consZ_apply]
          refine funext fun i => Fin.cases ?_ (fun _ => rfl) i
          simp [hv₀]
        rw [this]
        exact sub_mem hx (hv₀N _ (hmem₀ hx))
      obtain ⟨c', hc', hyc⟩ := (hmem' _).1 hy
      refine ⟨Fin.cons (x 0) c', (hD _).2 ⟨by simpa using hmem₀ hx, by simpa using hc'⟩, ?_⟩
      rw [hsum]
      simp only [Fin.cons_zero, Fin.cons_succ, ← hyc]
      rw [consZ_apply]
      refine funext fun i => Fin.cases ?_ (fun j => ?_) i
      · simp [hv₀]
      · simp [Fin.tail]
    · rintro ⟨c, hc, rfl⟩
      rw [hsum]
      obtain ⟨hc0, hc'⟩ := (hD c).1 hc
      exact add_mem (hv₀N _ hc0) ((hmem' _).2 ⟨_, hc', rfl⟩)

/-- **P1, pseudo-bases**: every `O_E`-lattice `N ⊆ E^n` is `γ·D(𝔞)` for some `γ ∈ GL_n(E)` and nonzero fractional
ideals `𝔞ᵢ`; `γ` has the columns of `exists_cols` (`colMat`). -/
theorem exists_pseudo (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] :
    ∃ (𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E) (γ : GL (Fin n) E), (∀ i, 𝔞 i ≠ 0) ∧ N = (diagLat 𝔞).map (act γ) := by
  obtain ⟨v, 𝔞, hli, h𝔞, hN⟩ := exists_cols n N inferInstance
  refine ⟨𝔞, (isUnit_colMat hli).unit, h𝔞, Submodule.ext fun x => ?_⟩
  rw [hN, Submodule.mem_map]
  simp only [act_apply, IsUnit.unit_spec, colMat_mulVec]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩⟩

/-- **`D(𝔞)` is a lattice** for nonzero `𝔞ᵢ`: a finite sum of the finitely generated `𝔞ᵢ eᵢ`, containing a nonzero
multiple of each `eᵢ`. -/
theorem isLattice_diagLat {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : ∀ i, 𝔞 i ≠ 0) :
    (diagLat 𝔞).IsLattice E where
  fg := by
    rw [diagLat, ← Submodule.iSup_map_single]
    exact Submodule.fg_iSup _ fun i => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔞 i)).map _
  span_eq_top := by
    refine eq_top_iff.2 fun x _ => ?_
    have ha (i : Fin n) : ∃ a ∈ (𝔞 i : Submodule (𝓞 E) E), a ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot (by rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]; exact h𝔞 i)
    choose a ha ha0 using ha
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ => ?_
    have : Pi.single i (x i) = (x i * (a i)⁻¹) • (Pi.single i (a i) : Fin n → E) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [ha0 j]
      · simp [hj]
    rw [this]
    refine smul_mem _ _ (subset_span (mem_diagLat.2 fun j => ?_))
    by_cases hj : j = i
    · subst hj; simpa using ha j
    · rw [Pi.single_eq_of_ne hj]
      exact (𝔞 j : Submodule (𝓞 E) E).zero_mem

end Pseudo

/-! ### The degree of a pseudo-basis lattice -/

section Degree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/-- **The degree** `deg N = −log covol ψ(N)` of an `O_E`-lattice `N ⊆ E^n`, with the standard metric (`klat`). -/
abbrev degE (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] : ℝ := KLattice.degK (klat E n N)

omit [IsCMField E] in
/-- `O_E^n` is a lattice: `D(𝔞)` for `𝔞 = 1`. -/
instance isLattice_intVec : (intVec E n).IsLattice E := by
  have := isLattice_diagLat (E := E) (n := n) (𝔞 := fun _ => 1) fun _ => one_ne_zero
  rwa [diagLat, FractionalIdeal.coe_one] at this

omit [NumberField E] [IsCMField E] in
/-- `γ ∈ GL_n(E)` as an `E`-linear automorphism of `E^n`, for K1; it is `act γ` over `O_E`. -/
def glEquiv (γ : GL (Fin n) E) : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.ofLinearMap (mulVecLin (γ : Matrix (Fin n) (Fin n) E)) (mulVecLin ((γ⁻¹ : GL (Fin n) E) : Matrix _ _ E))
    (LinearMap.ext fun x => by simp [mulVec_mulVec]) (LinearMap.ext fun x => by simp [mulVec_mulVec])

omit [NumberField E] [IsCMField E] in
/-- `γM` is a lattice with `M` (`KLattice.isLattice_map`). -/
theorem isLattice_map_act (M : Submodule (𝓞 E) (Fin n → E)) [M.IsLattice E] (γ : GL (Fin n) E) :
    (M.map (act γ)).IsLattice E :=
  KLattice.isLattice_map M (glEquiv γ)

/-- **P2, the degree of a pseudo-basis lattice**: for `N = γ·D(𝔞)`,
`deg N = deg O_E^n − log |N_{E/ℚ}(det γ)| − Σᵢ log N(𝔞ᵢ)`, by K1 (`KLattice.degK_map`) for `γ` and K2
(`KLattice.degK_pi`) for `D(𝔞)`, both with the standard metric. -/
theorem degE_pseudo (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E}
    {γ : GL (Fin n) E} (hN : N = (diagLat 𝔞).map (act γ)) :
    degE N = degE (intVec E n) - Real.log |(Algebra.norm ℚ (γ : Matrix (Fin n) (Fin n) E).det : ℝ)| -
      ∑ i, Real.log (FractionalIdeal.absNorm (𝔞 i) : ℝ) := by
  have hD : diagLat 𝔞 = N.map (act γ⁻¹) := by
    ext x
    rw [hN, mem_map_act, mem_map_act, inv_inv, act_inv_act]
  have : (diagLat 𝔞).IsLattice E := by
    rw [hD]
    exact isLattice_map_act N γ⁻¹
  have h1 := KLattice.degK_map (klat E n (diagLat 𝔞)) (klat E n N) (glEquiv γ) hN rfl
  have h2 := KLattice.degK_pi (klat E n (diagLat 𝔞)) (klat E n (intVec E n)) 𝔞 rfl rfl rfl
  have hdet : LinearMap.det (glEquiv γ : (Fin n → E) →ₗ[E] (Fin n → E)) = (γ : Matrix (Fin n) (Fin n) E).det := by
    rw [← LinearMap.det_toLin', Matrix.toLin'_apply']
    rfl
  rw [hdet] at h1
  rw [degE, degE, h1, h2]
  ring

end Degree

/-! ### Duals -/

section Dual

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/-- Coordinatewise complex conjugation `x ↦ x̄` of `E^n`. -/
def cv (x : Fin n → E) : Fin n → E := fun i => IsCMField.complexConj E (x i)

/-- Conjugation is an involution. -/
@[simp] theorem cv_cv (x : Fin n → E) : cv (cv x) = x := by
  funext i
  simp [cv]

/-- Conjugation is additive. -/
theorem cv_add (x y : Fin n → E) : cv (x + y) = cv x + cv y := by
  funext i
  simp [cv]

/-- `0̄ = 0`. -/
theorem cv_zero : cv (0 : Fin n → E) = 0 := by
  funext i
  simp [cv]

/-- Conjugation is semilinear over `E`. -/
theorem cv_smul (c : E) (x : Fin n → E) : cv (c • x) = IsCMField.complexConj E c • cv x := by
  funext i
  simp [cv]

/-- Conjugation is semilinear over `O_E`. -/
theorem cv_smulO (c : 𝓞 E) (x : Fin n → E) : cv (c • x) = IsCMField.ringOfIntegersComplexConj E c • cv x := by
  funext i
  simp [cv, Algebra.smul_def]

/-- Conjugation carries spans to spans: `x ∈ span_R s → x̄ ∈ span_R s̄`, for `R = O_E` or `E`. -/
theorem cv_mem_span {R : Type*} [CommSemiring R] [Module R (Fin n → E)] (c : R → R)
    (hc : ∀ (r : R) (x : Fin n → E), cv (r • x) = c r • cv x) {s : Set (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ span R s) : cv x ∈ span R (cv '' s) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact subset_span ⟨x, hx, rfl⟩
  | zero => rw [cv_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [cv_add]; exact add_mem hx hy
  | smul r x _ hx => rw [hc]; exact smul_mem _ _ hx

/-- The conjugate `M̄ = {x̄ : x ∈ M}` of an `O_E`-submodule of `E^n`. -/
def cj (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {x | cv x ∈ M}
  add_mem' {x y} hx hy := by
    show cv (x + y) ∈ M
    rw [cv_add]
    exact add_mem hx hy
  zero_mem' := by
    show cv 0 ∈ M
    rw [cv_zero]
    exact M.zero_mem
  smul_mem' c x hx := by
    show cv (c • x) ∈ M
    rw [cv_smulO]
    exact M.smul_mem _ hx

/-- Membership in `M̄`. -/
theorem mem_cj {M : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} : x ∈ cj M ↔ cv x ∈ M := Iff.rfl

/-- **The conjugate of a lattice is a lattice**: conjugation carries generators to generators (`cv_mem_span`). -/
instance isLattice_cj (M : Submodule (𝓞 E) (Fin n → E)) [M.IsLattice E] : (cj M).IsLattice E where
  fg := by
    obtain ⟨S, hS⟩ := IsLattice.fg (M := M)
    have : cj M = span (𝓞 E) (cv '' (S : Set (Fin n → E))) := by
      refine le_antisymm (fun x hx => ?_) (span_le.2 ?_)
      · have := cv_mem_span _ cv_smulO (show cv x ∈ span (𝓞 E) (S : Set (Fin n → E)) from hS ▸ hx)
        rwa [cv_cv] at this
      · rintro _ ⟨y, hy, rfl⟩
        show cv (cv y) ∈ M
        rw [cv_cv, ← hS]
        exact subset_span hy
    rw [this]
    exact fg_span (S.finite_toSet.image _)
  span_eq_top := by
    refine eq_top_iff.2 fun y _ => ?_
    have := cv_mem_span _ cv_smul
      (show cv y ∈ span E (M : Set (Fin n → E)) by rw [IsLattice.span_eq_top]; trivial)
    rw [cv_cv] at this
    refine span_mono ?_ this
    rintro _ ⟨x, hx, rfl⟩
    show cv (cv x) ∈ M
    rwa [cv_cv]

/-- `h(x̄, ȳ) = conj h(x, y)`. -/
theorem herm_cv (x y : Fin n → E) : herm (cv x) (cv y) = IsCMField.complexConj E (herm x y) := by
  simp [herm_def, cv, map_sum]

/-- **Conjugation keeps the degree**: `x ↦ x̄` preserves `⟪ψ x, ψ y⟫_ℝ = Re Σ_v σ_v h(x, y)`, as
`σ_v(conj z) = conj σ_v(z)` (`herm_cv`), so `covol ψ(M̄) = covol ψ(M)` (`EuclidLattice.covol_sq_eq`). -/
theorem degE_cj (M : Submodule (𝓞 E) (Fin n → E)) [M.IsLattice E] : degE (cj M) = degE M := by
  set X := klat E n M
  set Y := klat E n (cj M)
  let e₁ : M.restrictScalars ℤ ≃ₗ[ℤ] X.lattice :=
    Submodule.equivMapOfInjective X.ψ.toIntLinearMap X.ψ_injective _
  let e₂ : (cj M).restrictScalars ℤ ≃ₗ[ℤ] Y.lattice :=
    Submodule.equivMapOfInjective Y.ψ.toIntLinearMap Y.ψ_injective _
  let e : M.restrictScalars ℤ ≃ₗ[ℤ] (cj M).restrictScalars ℤ :=
    { toFun := fun x => ⟨cv x, show cv (cv x) ∈ M by rw [cv_cv]; exact x.2⟩
      invFun := fun y => ⟨cv y, y.2⟩
      map_add' := fun x y => Subtype.ext (cv_add x.1 y.1)
      map_smul' := fun z x => Subtype.ext (funext fun i => map_zsmul (IsCMField.complexConj E) z (x.1 i))
      left_inv := fun x => Subtype.ext (cv_cv x.1)
      right_inv := fun y => Subtype.ext (cv_cv y.1) }
  have h := EuclidLattice.covol_sq_eq (e₁.symm.trans (e.trans e₂)) 1 fun x y => by
    obtain ⟨x, rfl⟩ := e₁.surjective x
    obtain ⟨y, rfl⟩ := e₁.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, one_mul]
    show inner ℝ (Y.ψ (cv x)) (Y.ψ (cv y)) = inner ℝ (X.ψ x) (X.ψ y)
    rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_ψ_eq, inner_ψ_eq, herm_cv]
    simp
  rw [one_pow, one_mul] at h
  have hc := (sq_eq_sq₀ (EuclidLattice.covol_pos _).le (EuclidLattice.covol_pos _).le).1 h
  show -Real.log (EuclidLattice.covol Y.lattice) = -Real.log (EuclidLattice.covol X.lattice)
  rw [hc]

/-- `conj z ∈ O_E ↔ z ∈ O_E`. -/
theorem conj_mem_one {z : E} :
    IsCMField.complexConj E z ∈ (1 : Submodule (𝓞 E) E) ↔ z ∈ (1 : Submodule (𝓞 E) E) := by
  have key {z : E} (hz : z ∈ (1 : Submodule (𝓞 E) E)) : IsCMField.complexConj E z ∈ (1 : Submodule (𝓞 E) E) := by
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hz
    exact Submodule.mem_one.2 ⟨IsCMField.ringOfIntegersComplexConj E y, rfl⟩
  exact ⟨fun h => by simpa using key h, key⟩

/-- `conj h(y, x) = y·x̄`, the bilinear pairing with the conjugate. -/
theorem conj_herm (y x : Fin n → E) : IsCMField.complexConj E (herm y x) = y ⬝ᵥ cv x := by
  simp [herm_def, cv, dotProduct, map_sum]

omit [IsCMField E] in
/-- **The bilinear dual of `D(𝔞)` is `D(𝔞⁻¹)`**: `u·w ∈ O_E` for all `u ∈ D(𝔞)` iff each `wᵢ ∈ 𝔞ᵢ⁻¹` (test on
`u = a eᵢ`, and `FractionalIdeal.mem_inv_iff`). -/
theorem forall_dotProduct_mem_one {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : ∀ i, 𝔞 i ≠ 0) (w : Fin n → E) :
    (∀ u ∈ diagLat 𝔞, u ⬝ᵥ w ∈ (1 : Submodule (𝓞 E) E)) ↔ w ∈ diagLat fun i => (𝔞 i)⁻¹ := by
  have h1 (z : E) : z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ z ∈ (1 : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
  simp_rw [mem_diagLat, FractionalIdeal.mem_inv_iff (h𝔞 _), h1]
  refine ⟨fun h i a ha => ?_, fun h u hu => ?_⟩
  · have := h (Pi.single i a) fun j => ?_
    · rwa [single_dotProduct, mul_comm] at this
    by_cases hj : j = i
    · subst hj; simpa using ha
    · rw [Pi.single_eq_of_ne hj]
      exact (𝔞 j : Submodule (𝓞 E) E).zero_mem
  · exact sum_mem fun i _ => by rw [mul_comm]; exact h i _ (hu i)

omit [NumberField E] [IsCMField E] in
/-- The transpose `γᵀ ∈ GL_n(E)`. -/
def tGL (γ : GL (Fin n) E) : GL (Fin n) E :=
  ⟨(γ : Matrix (Fin n) (Fin n) E)ᵀ, ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

/-- **P3, the dual of a pseudo-basis lattice**: `(γ·D(𝔞))^# = conj((γᵀ)⁻¹·D(𝔞⁻¹))`. For `u ∈ D(𝔞)`,
`conj h(γu, x) = (γu)·x̄ = u·(γᵀx̄)` (`conj_herm`), so `x ∈ (γD(𝔞))^#` iff `u·(γᵀx̄) ∈ O_E` for all `u ∈ D(𝔞)`, iff
`γᵀx̄ ∈ D(𝔞⁻¹)` (`forall_dotProduct_mem_one`). -/
theorem dual_pseudo {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : ∀ i, 𝔞 i ≠ 0) (γ : GL (Fin n) E) :
    dual ((diagLat 𝔞).map (act γ)) = cj ((diagLat fun i => (𝔞 i)⁻¹).map (act (tGL γ)⁻¹)) := by
  ext x
  rw [mem_cj, mem_map_act, inv_inv, ← forall_dotProduct_mem_one h𝔞, mem_dual]
  simp only [Submodule.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun u _ => ?_
  rw [← conj_mem_one, conj_herm, act_apply, act_apply, dotProduct_mulVec,
    show ((tGL γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) E)ᵀ from rfl,
    vecMul_transpose]

/-- **The dual of a lattice is a lattice**: by P1 and P3, it is the conjugate of a pseudo-basis lattice. -/
instance isLattice_dual (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] : (dual N).IsLattice E := by
  obtain ⟨𝔞, γ, h𝔞, rfl⟩ := exists_pseudo N
  have := isLattice_diagLat fun i => inv_ne_zero (h𝔞 i)
  have := isLattice_map_act (diagLat fun i => (𝔞 i)⁻¹) (tGL γ)⁻¹
  rw [dual_pseudo h𝔞]
  infer_instance

/-- **P4, the degree of the dual**: `deg N^# = 2·deg O_E^n − deg N`. With `N = γD(𝔞)` (P1),
`N^# = conj((γᵀ)⁻¹D(𝔞⁻¹))` (P3), whose degree is that of `(γᵀ)⁻¹D(𝔞⁻¹)` (`degE_cj`), which P2 gives:
`|N(det (γᵀ)⁻¹)| = |N(det γ)|⁻¹` and `N(𝔞ᵢ⁻¹) = N(𝔞ᵢ)⁻¹`. -/
theorem degE_dual (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] :
    degE (dual N) = 2 * degE (intVec E n) - degE N := by
  obtain ⟨𝔞, γ, h𝔞, hN⟩ := exists_pseudo N
  set M := (diagLat fun i => (𝔞 i)⁻¹).map (act (tGL γ)⁻¹)
  have := isLattice_diagLat fun i => inv_ne_zero (h𝔞 i)
  have : M.IsLattice E := isLattice_map_act _ _
  have hd : degE (dual N) = degE M := by
    rw [← degE_cj M]
    exact KLattice.degK_congr (show dual N = cj M by rw [hN, dual_pseudo h𝔞]) rfl
  have hdet : Algebra.norm ℚ (((tGL γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det *
      Algebra.norm ℚ (γ : Matrix (Fin n) (Fin n) E).det = 1 := by
    have ht : (((tGL γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det =
        ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det :=
      det_transpose _
    rw [ht, ← map_mul, ← det_mul, Units.inv_mul, det_one, map_one]
  rw [hd, degE_pseudo M rfl, degE_pseudo N hN, eq_inv_of_mul_eq_one_left hdet, Rat.cast_inv, abs_inv, Real.log_inv]
  simp only [map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  ring

/-- **P5, unimodular lattices**: `deg N = deg O_E^n` for `N = N^#`, by P4. -/
theorem degE_of_unimodular {N : Submodule (𝓞 E) (Fin n → E)} [N.IsLattice E] (hN : IsUnimodular N) :
    degE N = degE (intVec E n) := by
  have h := degE_dual N
  rw [show degE (dual N) = degE N from KLattice.degK_congr hN rfl] at h
  linarith

end Dual

/-! ### The level-`T` kernel and the attached lattice -/

section Level

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/-- A nonzero `O_E`-linear map to the residue field `O_E/P` is onto: its image is a nonzero ideal of a field. -/
theorem surjective_of_ne_zero {M : Type*} [AddCommGroup M] [Module (𝓞 E) M] {P : HeightOneSpectrum (𝓞 E)}
    {f : M →ₗ[𝓞 E] 𝓞 E ⧸ P.asIdeal} (hf : f ≠ 0) : Function.Surjective f := by
  have := P.isMaximal
  let := Ideal.Quotient.field P.asIdeal
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := not_forall.1 fun h => hf (LinearMap.ext h)
  intro s
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (s * (f x)⁻¹)
  refine ⟨r • x, ?_⟩
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, hr, inv_mul_cancel_right₀ hx]

/-- The level-`T` reduction `x ↦ (f_P x)_{P ∈ ST}` of a decorated lattice. -/
def redT (d : Deco E n ST SG) : d.N →ₗ[𝓞 E] ∀ P : ST, 𝓞 E ⧸ P.1.asIdeal := LinearMap.pi d.f

/-- **The reduction is onto** when every `f_P` is nonzero: each `f_P` is onto (`surjective_of_ne_zero`), and
`e_Q ≡ δ_{PQ} mod P` (CRT, `Ideal.exists_forall_sub_mem_ideal`, distinct primes being coprime) glue preimages `y_Q`
of the coordinates into `Σ_Q e_Q y_Q`. -/
theorem redT_surjective {d : Deco E n ST SG} (hd : ∀ P, d.f P ≠ 0) : Function.Surjective (redT d) := by
  classical
  intro t
  choose y hy using fun P => surjective_of_ne_zero (hd P) (t P)
  have hcop : Pairwise (Function.onFun IsCoprime fun P : ST => P.1.asIdeal) := fun P Q hPQ =>
    HeightOneSpectrum.isCoprime_of_ne P.1 Q.1 fun h => hPQ (Subtype.ext h)
  choose e he using fun Q : ST => Ideal.exists_forall_sub_mem_ideal hcop (Pi.single Q 1)
  have hmk (P Q : ST) : Ideal.Quotient.mk P.1.asIdeal (e Q) = if Q = P then 1 else 0 := by
    rw [Ideal.Quotient.eq.2 (he Q P), Pi.single_apply]
    split_ifs <;> simp_all [eq_comm]
  refine ⟨∑ Q, e Q • y Q, funext fun P => ?_⟩
  simp only [redT, LinearMap.pi_apply, map_sum, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, hmk]
  simp [hy]

/-- **P6, CRT**: for nonzero `f_P`, `[N : kerLat d] = ∏_{P ∈ ST} N(P)`, as `kerLat d` is the kernel of the reduction
`N ↠ ∏_P O_E/P` (`redT_surjective`). -/
theorem relIndex_kerLat {d : Deco E n ST SG} (hd : ∀ P, d.f P ≠ 0) :
    (kerLat d).toAddSubgroup.relIndex d.N.toAddSubgroup = ∏ P ∈ ST, Ideal.absNorm P.asIdeal := by
  have hker : (kerLat d).toAddSubgroup.addSubgroupOf d.N.toAddSubgroup = (redT d).toAddMonoidHom.ker := by
    ext x
    simp [AddSubgroup.mem_addSubgroupOf, kerLat, redT, funext_iff]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (redT_surjective hd),
    AddSubgroup.card_top, Nat.card_pi, ← Finset.prod_coe_sort ST]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

variable [IsCMField E]

/-- `kerLat d` is a lattice for unimodular `N`: it lies in `N` and contains `m·N`, for an integer `m` in every
`P ∈ ST` (`HermForms.exists_int_mem_all`). -/
theorem isLattice_kerLat {d : Deco E n ST SG} (hd : IsUnimodular d.N) : (kerLat d).IsLattice E := by
  have := isLattice_of_unimodular hd
  obtain ⟨m, hm0, hm⟩ := HermForms.exists_int_mem_all ST
  have hmx {y : Fin n → E} (hy : y ∈ d.N) : (m : E) • y ∈ kerLat d := by
    refine Submodule.mem_inf.2 ⟨HermForms.int_smul_mem hy m, Submodule.mem_iInf _ |>.2 fun P => ?_⟩
    refine ⟨(m : 𝓞 E) • ⟨y, hy⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 (hm P P.2), zero_mul]
    · simp [Int.cast_smul_eq_zsmul]
  refine ⟨(IsLattice.fg (M := d.N)).of_le inf_le_left, eq_top_iff.2 ?_⟩
  rw [← IsLattice.span_eq_top (M := d.N) (A := E)]
  refine span_le.2 fun y hy => ?_
  have h := smul_mem (span E (kerLat d : Set (Fin n → E))) (m : E)⁻¹ (subset_span (hmx hy))
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm0), one_smul] at h

/-- The attached lattice `Lsh(d) = (kerLat d)^#` of a unimodular `N` is a lattice (`isLattice_dual`). -/
theorem isLattice_Lsh {d : Deco E n ST SG} (hd : IsUnimodular d.N) : (Lsh d).IsLattice E :=
  have := isLattice_kerLat hd
  isLattice_dual (kerLat d)

/-- **P7, the degree of the attached lattice**: for a good `d`,
`deg Lsh(d) = deg O_E^n + Σ_{P ∈ ST} log N(P)`. With `deg N = deg O_E^n` (P5), the index gives
`deg kerLat(d) = deg O_E^n − Σ_P log N(P)` (P6, `KLattice.deg_withLattice`), and `Lsh(d)` is its dual (P4). -/
theorem degE_Lsh {d : Deco E n ST SG} (hd : d.Good) [(Lsh d).IsLattice E] :
    degE (Lsh d) = degE (intVec E n) + ∑ P ∈ ST, Real.log (Ideal.absNorm P.asIdeal : ℝ) := by
  have := isLattice_of_unimodular hd.unimod
  have := isLattice_kerLat hd.unimod
  have hk : degE (kerLat d) = degE d.N - Real.log ((kerLat d).toAddSubgroup.relIndex d.N.toAddSubgroup) :=
    KLattice.deg_withLattice (klat E n d.N) inf_le_left
  rw [relIndex_kerLat hd.f_ne, Nat.cast_prod, Real.log_prod fun P _ => Nat.cast_ne_zero.2 fun h =>
    P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), degE_of_unimodular hd.unimod] at hk
  have h4 := degE_dual (kerLat d)
  have : degE (Lsh d) = degE (dual (kerLat d)) := rfl
  linarith

end Level

end

end HermClasses
