import Mathlib

/-!
# The generalised index of commensurable lattices

The index term of the gain in (G↓) (`SharpInputs`, `SharpObj.Gain`) is `idx_ω = 2·logIdx(N_ω, M_ω)/rk`
(`SharpObj.idx`), and the gain bounds it below by a certificate (module `GainCert`). This module holds the generalised
index and the rules the certificate uses: through a common sub- or supergroup, the cocycle rule, monotonicity, the
scaling by an element of the field, and the gluing of finitely many local conditions.

**The index** (`AddSubgroup.logIdx`). For subgroups `X`, `Y` of an abelian group,
`logIdx X Y = log [X : X ∩ Y] − log [Y : X ∩ Y]` (Mathlib's `Y.relIndex X` is `[X : Y ∩ X]`). Indices multiply in
towers (`AddSubgroup.relIndex_mul_relIndex`), so for commensurable `X`, `Y` it is `log [X : W] − log [Y : W]` for any
common subgroup `W` of finite index in both (`logIdx_eq_of_le`), and `log [U : Y] − log [U : X]` for any common
supergroup `U` in which both have finite index (`logIdx_eq_of_ge`). For `X ≤ Y` it is `−log [Y : X]`
(`logIdx_of_le`). Hence the cocycle rule `logIdx X Z = logIdx X Y + logIdx Y Z` (`logIdx_add`): commensurability is
transitive (`AddSubgroup.relIndex_ne_zero_trans`), so `W = X ∩ Y ∩ Z` serves all three; and, as
`logIdx X′ X = log [X′ : X] ≥ 0` for `X ≤ X′`, monotonicity in the first argument (`logIdx_mono`).

**Scaling** (`Submodule.logIdx_smul`). For an `O_K`-lattice `L` in a `K`-space `V` of dimension `d` and `γ ∈ K^×`,
`logIdx(γL, L) = −d·log|N_{K/ℚ}(γ)|`. For integral `γ` it is `[L : γL] = |N_{K/ℚ}(γ)|^d` (`Submodule.relIndex_smul`).
Make `V` a `ℚ`-space through `K`. Then `L` is a `ℤ`-lattice in it: finite over `ℤ` as `O_K` is, and spanning, as its
`ℚ`-span is stable under `K = ℚ·O_K` (`IsAlgebraic.exists_nsmul_eq`). So a `ℤ`-basis of `L` is a `ℚ`-basis of `V`
(`Module.Basis.extendOfIsLattice`), its image under `γ` spans `γL`, and the index is the absolute value of the
`ℚ`-determinant of `γ` (`AddSubgroup.relIndex_eq_abs_det`), the norm of its `K`-determinant `γ^d`
(`LinearMap.det_restrictScalars`). A general `γ` is `s/m` with `s ∈ O_K` and `m ∈ ℕ` (`Submodule.exists_mul_eq_coe`);
scaling by `m` keeps indices (`Submodule.relIndex_smul_smul`) and turns `(γL, L)` into `(sL, mL)`, two integral
multiples of `L` (`logIdx_eq_of_ge` with `U = L`). The same reduction shows `γL` and `L` commensurable
(`Submodule.relIndex_smul_ne_zero`). No finiteness of `V` is assumed: a lattice spans.

**Gluing** (`Submodule.relIndex_inf_iInf_le`). The intersection of `M` with finitely many submodules `L_i` of finite
index in `M` has finite index, with `log [M : M ∩ ⋂_i L_i] ≤ Σ_i log [M : L_i]`: a sublattice cut out by local
conditions, one per place, has colength at most the sum of the local colengths.

**Normalised norms** (`NumberField.log_abs_norm_map_div`). For a ring map `τ : F → K` of number fields,
`log|N_{K/ℚ}(τγ)|/[K:ℚ] = log|N_{F/ℚ}(γ)|/[F:ℚ]`, as `N_{K/ℚ} = N_{F/ℚ} ∘ N_{K/F}` (`Algebra.norm_norm`) and
`N_{K/F}(γ) = γ^{[K:F]}`. With `F = ℚ(√−d)` it turns the certificate's `(2/[K:ℚ])·log|N_{K/ℚ}(α/β)|` into
`log N_{F/ℚ}(α₀/β₀)` for `α = τ(α₀)`, `β = τ(β₀)`.
-/

open NumberField Module Pointwise

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- **The generalised index** `logIdx X Y = log [X : X ∩ Y] − log [Y : X ∩ Y]` of two subgroups (Mathlib's
`Y.relIndex X` is `[X : Y ∩ X]`); meaningful for commensurable `X`, `Y`. -/
noncomputable def logIdx (X Y : AddSubgroup G) : ℝ := Real.log (Y.relIndex X) - Real.log (X.relIndex Y)

/-- **Through a common subgroup**: if `W ≤ X, Y` has finite index in both, `logIdx X Y = log [X : W] − log [Y : W]`. -/
theorem logIdx_eq_of_le {X Y W : AddSubgroup G} (hX : W ≤ X) (hY : W ≤ Y) (hWX : W.relIndex X ≠ 0)
    (hWY : W.relIndex Y ≠ 0) : logIdx X Y = Real.log (W.relIndex X) - Real.log (W.relIndex Y) := by
  have hW : W ≤ X ⊓ Y := le_inf hX hY
  have h1 : W.relIndex X = W.relIndex (X ⊓ Y) * Y.relIndex X := by
    rw [← inf_relIndex_left X Y, relIndex_mul_relIndex W (X ⊓ Y) X hW inf_le_left]
  have h2 : W.relIndex Y = W.relIndex (X ⊓ Y) * X.relIndex Y := by
    rw [← inf_relIndex_right X Y, relIndex_mul_relIndex W (X ⊓ Y) Y hW inf_le_right]
  rw [h1] at hWX
  rw [h2] at hWY
  rw [logIdx, h1, h2, Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (mod_cast left_ne_zero_of_mul hWX) (mod_cast right_ne_zero_of_mul hWX),
    Real.log_mul (mod_cast left_ne_zero_of_mul hWY) (mod_cast right_ne_zero_of_mul hWY)]
  ring

/-- **Through a common supergroup**: if `X, Y ≤ U` both have finite index in `U`,
`logIdx X Y = log [U : Y] − log [U : X]`. -/
theorem logIdx_eq_of_ge {X Y U : AddSubgroup G} (hX : X ≤ U) (hY : Y ≤ U) (hXU : X.relIndex U ≠ 0)
    (hYU : Y.relIndex U ≠ 0) : logIdx X Y = Real.log (Y.relIndex U) - Real.log (X.relIndex U) := by
  have h1 : (X ⊓ Y).relIndex U = Y.relIndex X * X.relIndex U := by
    rw [← relIndex_mul_relIndex (X ⊓ Y) X U inf_le_left hX, inf_relIndex_left]
  have h2 : (X ⊓ Y).relIndex U = X.relIndex Y * Y.relIndex U := by
    rw [← relIndex_mul_relIndex (X ⊓ Y) Y U inf_le_right hY, inf_relIndex_right]
  have h0 := relIndex_inf_ne_zero hXU hYU
  have ha : Y.relIndex X ≠ 0 := left_ne_zero_of_mul (h1 ▸ h0)
  have hb : X.relIndex Y ≠ 0 := left_ne_zero_of_mul (h2 ▸ h0)
  have h := congrArg (fun n : ℕ => Real.log n) (h1.symm.trans h2)
  simp only [Nat.cast_mul] at h
  rw [Real.log_mul (mod_cast ha) (mod_cast hXU), Real.log_mul (mod_cast hb) (mod_cast hYU)] at h
  rw [logIdx]
  linarith

/-- **A subgroup of a group**: for `X ≤ Y`, `logIdx X Y = −log [Y : X]`. -/
theorem logIdx_of_le {X Y : AddSubgroup G} (h : X ≤ Y) : logIdx X Y = -Real.log (X.relIndex Y) := by
  rw [logIdx, relIndex_eq_one.2 h, Nat.cast_one, Real.log_one, zero_sub]

/-- **The cocycle rule**: for `X`, `Y` commensurable and `Y`, `Z` commensurable,
`logIdx X Z = logIdx X Y + logIdx Y Z`. -/
theorem logIdx_add {X Y Z : AddSubgroup G} (hXY : Y.relIndex X ≠ 0 ∧ X.relIndex Y ≠ 0)
    (hYZ : Z.relIndex Y ≠ 0 ∧ Y.relIndex Z ≠ 0) : logIdx X Z = logIdx X Y + logIdx Y Z := by
  have hZX : Z.relIndex X ≠ 0 := relIndex_ne_zero_trans hYZ.1 hXY.1
  have hXZ : X.relIndex Z ≠ 0 := relIndex_ne_zero_trans hXY.2 hYZ.2
  have hX : (X ⊓ Y ⊓ Z).relIndex X ≠ 0 :=
    relIndex_inf_ne_zero (by rw [inf_relIndex_left]; exact hXY.1) hZX
  have hY : (X ⊓ Y ⊓ Z).relIndex Y ≠ 0 :=
    relIndex_inf_ne_zero (by rw [inf_relIndex_right]; exact hXY.2) hYZ.1
  have hZ : (X ⊓ Y ⊓ Z).relIndex Z ≠ 0 := by
    rw [inf_relIndex_right]
    exact relIndex_inf_ne_zero hXZ hYZ.2
  have hle : X ⊓ Y ⊓ Z ≤ X ⊓ Y := inf_le_left
  rw [logIdx_eq_of_le (hle.trans inf_le_left) inf_le_right hX hZ,
    logIdx_eq_of_le (hle.trans inf_le_left) (hle.trans inf_le_right) hX hY,
    logIdx_eq_of_le (hle.trans inf_le_right) inf_le_right hY hZ]
  ring

/-- **Monotonicity**: for `X ≤ X′` of finite index and `X`, `Y` commensurable, `logIdx X Y ≤ logIdx X′ Y`. -/
theorem logIdx_mono {X X' Y : AddSubgroup G} (h : X ≤ X') (hfin : X.relIndex X' ≠ 0)
    (hXY : Y.relIndex X ≠ 0 ∧ X.relIndex Y ≠ 0) : logIdx X Y ≤ logIdx X' Y := by
  have hX' : logIdx X' X = Real.log (X.relIndex X') := by
    rw [logIdx, relIndex_eq_one.2 h, Nat.cast_one, Real.log_one, sub_zero]
  rw [logIdx_add (Y := X) ⟨hfin, by rw [relIndex_eq_one.2 h]; exact one_ne_zero⟩ hXY, hX']
  linarith [Real.log_nonneg (show (1 : ℝ) ≤ X.relIndex X' by exact_mod_cast Nat.one_le_iff_ne_zero.2 hfin)]

end AddSubgroup

namespace Submodule

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [NumberField K] in
/-- **Scaling as a map**: `γL`, as a subgroup, is the image of `L` under `x ↦ γx`. -/
theorem toAddSubgroup_smul (L : Submodule (𝓞 K) V) (γ : K) :
    (γ • L).toAddSubgroup = L.toAddSubgroup.map (DistribSMul.toAddMonoidHom V γ) :=
  rfl

omit [NumberField K] in
/-- **Scaling keeps indices**: for `c ≠ 0`, `[cY : cX ∩ cY] = [Y : X ∩ Y]`. -/
theorem relIndex_smul_smul {c : K} (hc : c ≠ 0) (X Y : Submodule (𝓞 K) V) :
    (c • X).toAddSubgroup.relIndex (c • Y).toAddSubgroup = X.toAddSubgroup.relIndex Y.toAddSubgroup := by
  rw [toAddSubgroup_smul, toAddSubgroup_smul]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (smul_right_injective V hc)

omit [NumberField K] in
/-- **Integral multiples**: for `γ ∈ O_K`, `γL ≤ L`. -/
theorem smul_le_self (L : Submodule (𝓞 K) V) (γ : 𝓞 K) : (γ : K) • L ≤ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).1 hx
  show algebraMap (𝓞 K) K γ • y ∈ L
  rw [algebraMap_smul]
  exact L.smul_mem γ hy

/-- **Integral scaling**: for an `O_K`-lattice `L` and `0 ≠ γ ∈ O_K`, `[L : γL] = |N_{K/ℚ}(γ)|^d`, `d = dim_K V`. -/
theorem relIndex_smul (L : Submodule (𝓞 K) V) [L.IsLattice K] {γ : 𝓞 K} (hγ : γ ≠ 0) :
    (((γ : K) • L).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      |(Algebra.norm ℚ (γ : K) : ℝ)| ^ finrank K V := by
  classical
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  have : IsScalarTower ℚ K V := ⟨fun q k v => by
    show (q • k) • v = algebraMap ℚ K q • k • v
    rw [Algebra.smul_def, mul_smul]⟩
  have hγK : (γ : K) ≠ 0 := by exact_mod_cast hγ
  -- `K = ℚ·O_K`, so the `ℚ`-span of `L` is a `K`-subspace, hence everything
  have hstab : ∀ k : K, ∀ x ∈ span ℚ (L : Set V), k • x ∈ span ℚ (L : Set V) := by
    intro k x hx
    induction hx using Submodule.span_induction with
    | mem l hl =>
      have hk : IsAlgebraic ℤ k :=
        (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic k)
      obtain ⟨m, s, hm, hs⟩ := hk.exists_nsmul_eq (𝓞 K)
      have hkl : k • l = ((m : ℚ)⁻¹) • ((s : 𝓞 K) • l) := by
        show k • l = algebraMap ℚ K ((m : ℚ)⁻¹) • ((s : 𝓞 K) • l)
        rw [← algebraMap_smul K s l, smul_smul, ← hs, nsmul_eq_mul, map_inv₀, map_natCast, ← mul_assoc,
          inv_mul_cancel₀ (by exact_mod_cast hm), one_mul]
      rw [hkl]
      exact smul_mem _ _ (subset_span (L.smul_mem s hl))
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul q x _ hx => rw [smul_comm]; exact smul_mem _ q hx
  have : (L.restrictScalars ℤ).IsLattice ℚ := by
    refine ⟨(IsLattice.fg (A := K) (M := L)).restrictScalars, ?_⟩
    let W : Submodule K V := { (span ℚ (L : Set V)).toAddSubmonoid with smul_mem' := hstab }
    have hW : span K (L : Set V) ≤ W := span_le.2 fun x hx => subset_span hx
    rw [IsLattice.span_eq_top] at hW
    exact eq_top_iff.2 fun v _ => hW mem_top
  let bZ := Module.Free.chooseBasis ℤ (L.restrictScalars ℤ)
  let b₂ := bZ.extendOfIsLattice ℚ
  let e : V ≃ₗ[ℚ] V := (LinearEquiv.smulOfNeZero K V (γ : K) hγK).restrictScalars ℚ
  let b₁ := b₂.map e
  have h₂ : L.toAddSubgroup = AddSubgroup.closure (Set.range b₂) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    have h := congrArg (Submodule.map (L.restrictScalars ℤ).subtype) bZ.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    rw [show Set.range b₂ = Set.range ((L.restrictScalars ℤ).subtype ∘ bZ) from
      congrArg Set.range (funext fun i => bZ.extendOfIsLattice_apply ℚ i), h]
    rfl
  have h₁ : ((γ : K) • L).toAddSubgroup = AddSubgroup.closure (Set.range b₁) := by
    rw [toAddSubgroup_smul, h₂, AddMonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hle : ((γ : K) • L).toAddSubgroup ≤ L.toAddSubgroup := smul_le_self L γ
  have hdet : b₂.det b₁ = (Algebra.norm ℚ (γ : K)) ^ finrank K V := by
    have he : (e : V →ₗ[ℚ] V) = ((γ : K) • LinearMap.id : V →ₗ[K] V).restrictScalars ℚ := LinearMap.ext fun _ => rfl
    rw [Basis.coe_map, show ⇑e ∘ ⇑b₂ = ⇑(e : V →ₗ[ℚ] V) ∘ ⇑b₂ from rfl, Basis.det_comp, Basis.det_self, mul_one, he,
      LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow]
  have h := AddSubgroup.relIndex_eq_abs_det _ _ hle b₁ b₂ h₁ h₂
  rw [hdet, abs_pow] at h
  rw [← Rat.cast_natCast, h, Rat.cast_pow, Rat.cast_abs]

/-- **A denominator**: every `γ ≠ 0` of `K` is `s/m` with `0 ≠ s ∈ O_K` and `0 ≠ m ∈ ℕ`. -/
theorem exists_mul_eq_coe {γ : K} (hγ : γ ≠ 0) : ∃ (m : ℕ) (s : 𝓞 K), m ≠ 0 ∧ s ≠ 0 ∧ (m : K) * γ = s := by
  obtain ⟨m, s, hm, hs⟩ :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic γ)).exists_nsmul_eq (𝓞 K)
  rw [nsmul_eq_mul] at hs
  refine ⟨m, s, hm, fun h => ?_, hs⟩
  rw [h, map_zero, mul_eq_zero] at hs
  exact hs.elim (fun h' => hm (by exact_mod_cast h')) hγ

/-- **Integral multiples have finite index**: `[L : γL] = |N_{K/ℚ}(γ)|^d ≠ 0` for `0 ≠ γ ∈ O_K` (`relIndex_smul`). -/
theorem relIndex_smul_coe_ne_zero (L : Submodule (𝓞 K) V) [L.IsLattice K] {γ : 𝓞 K} (hγ : γ ≠ 0) :
    ((γ : K) • L).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := fun h0 =>
  have hN : (Algebra.norm ℚ (γ : K) : ℝ) ≠ 0 := Rat.cast_ne_zero.2 (Algebra.norm_ne_zero_iff.2 (by exact_mod_cast hγ))
  pow_ne_zero (finrank K V) (abs_ne_zero.2 hN) (by rw [← relIndex_smul L hγ, h0, Nat.cast_zero])

/-- **Scaling gives commensurable lattices**: for an `O_K`-lattice `L` and `γ ∈ K^×`, `γL` and `L` are
commensurable. With `γ = s/m`, scaling by `m` turns them into `sL` and `mL`, both of finite index in `L`. -/
theorem relIndex_smul_ne_zero (L : Submodule (𝓞 K) V) [L.IsLattice K] {γ : K} (hγ : γ ≠ 0) :
    (γ • L).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 ∧ L.toAddSubgroup.relIndex (γ • L).toAddSubgroup ≠ 0 := by
  obtain ⟨m, s, hm, hs, h⟩ := exists_mul_eq_coe hγ
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hmc : ((m : 𝓞 K) : K) = m := by simp
  have hm1 := relIndex_smul_coe_ne_zero L (γ := m) (by exact_mod_cast hm)
  have hm2 := smul_le_self L m
  rw [hmc] at hm1 hm2
  rw [← relIndex_smul_smul hmK, ← relIndex_smul_smul hmK L, smul_smul, h]
  exact ⟨mt (AddSubgroup.relIndex_eq_zero_of_le_right hm2) (relIndex_smul_coe_ne_zero L hs),
    mt (AddSubgroup.relIndex_eq_zero_of_le_right (smul_le_self L s)) hm1⟩

/-- **Scaling**: for an `O_K`-lattice `L` in a `K`-space of dimension `d` and `γ ∈ K^×`,
`logIdx(γL, L) = −d·log|N_{K/ℚ}(γ)|`. With `γ = s/m`, scaling by `m` gives `logIdx(sL, mL)`, which is
`log [L : mL] − log [L : sL]` (`logIdx_eq_of_ge`) `= d·log|N(m)| − d·log|N(s)|` (`relIndex_smul`). -/
theorem logIdx_smul (L : Submodule (𝓞 K) V) [L.IsLattice K] {γ : K} (hγ : γ ≠ 0) :
    AddSubgroup.logIdx (γ • L).toAddSubgroup L.toAddSubgroup =
      -(finrank K V : ℝ) * Real.log |(Algebra.norm ℚ γ : ℝ)| := by
  obtain ⟨m, s, hm, hs, h⟩ := exists_mul_eq_coe hγ
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hmc : ((m : 𝓞 K) : K) = m := by simp
  have hm0 : (m : 𝓞 K) ≠ 0 := by exact_mod_cast hm
  have hm1 := relIndex_smul L hm0
  have hm2 := relIndex_smul_coe_ne_zero L hm0
  have hm3 := smul_le_self L m
  rw [hmc] at hm1 hm2 hm3
  have hN {t : K} (ht : t ≠ 0) : |(Algebra.norm ℚ t : ℝ)| ≠ 0 :=
    abs_ne_zero.2 (Rat.cast_ne_zero.2 (Algebra.norm_ne_zero_iff.2 ht))
  have hγs : (Algebra.norm ℚ (m : K) : ℝ) * Algebra.norm ℚ γ = Algebra.norm ℚ (s : K) := by
    rw [← Rat.cast_mul, ← map_mul, h]
  rw [AddSubgroup.logIdx, ← relIndex_smul_smul hmK (γ • L) L, ← relIndex_smul_smul hmK L (γ • L), smul_smul, h,
    ← AddSubgroup.logIdx, AddSubgroup.logIdx_eq_of_ge (smul_le_self L s) hm3 (relIndex_smul_coe_ne_zero L hs) hm2,
    hm1, relIndex_smul L hs, Real.log_pow, Real.log_pow, ← hγs, abs_mul, Real.log_mul (hN hmK) (hN hγ)]
  ring

/-- **Gluing local conditions**: for finitely many submodules `L_i` of finite index in `M`, the intersection
`M ∩ ⋂_i L_i` has finite index in `M`, and `log [M : M ∩ ⋂_i L_i] ≤ Σ_i log [M : L_i]`
(`AddSubgroup.relIndex_inf_le`, one condition at a time). -/
theorem relIndex_inf_iInf_le {R W ι : Type*} [Ring R] [AddCommGroup W] [Module R W] (M : Submodule R W)
    (L : ι → Submodule R W) (s : Finset ι) (h : ∀ i ∈ s, (L i).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) :
    (M ⊓ ⨅ i ∈ s, L i).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 ∧
      Real.log ((M ⊓ ⨅ i ∈ s, L i).toAddSubgroup.relIndex M.toAddSubgroup) ≤
        ∑ i ∈ s, Real.log ((L i).toAddSubgroup.relIndex M.toAddSubgroup) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddSubgroup.relIndex_self]
  | insert a s ha ih =>
    obtain ⟨h0, hle⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    have heq : (M ⊓ ⨅ i ∈ insert a s, L i).toAddSubgroup =
        (M ⊓ ⨅ i ∈ s, L i).toAddSubgroup ⊓ (L a).toAddSubgroup := by
      rw [Finset.iInf_insert, inf_left_comm, inf_comm]
      rfl
    have hmul := AddSubgroup.relIndex_inf_le (H := (M ⊓ ⨅ i ∈ s, L i).toAddSubgroup) (K := (L a).toAddSubgroup)
      (L := M.toAddSubgroup)
    have hne := AddSubgroup.relIndex_inf_ne_zero h0 ha'
    rw [heq, Finset.sum_insert ha]
    refine ⟨hne, (Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero hne)) (Nat.cast_le.2 hmul)).trans ?_⟩
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.2 h0) (Nat.cast_ne_zero.2 ha')]
    linarith

end Submodule

namespace NumberField

/-- **Normalised norms do not depend on the field**: for a ring map `τ : F → K` of number fields,
`log|N_{K/ℚ}(τγ)|/[K:ℚ] = log|N_{F/ℚ}(γ)|/[F:ℚ]`, as `N_{K/ℚ}(τγ) = N_{F/ℚ}(N_{K/F}(τγ)) = N_{F/ℚ}(γ)^{[K:F]}`. -/
theorem log_abs_norm_map_div {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] (τ : F →+* K)
    (γ : F) : Real.log |(Algebra.norm ℚ (τ γ) : ℝ)| / finrank ℚ K =
      Real.log |(Algebra.norm ℚ γ : ℝ)| / finrank ℚ F := by
  let _ : Algebra F K := τ.toAlgebra
  have : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast τ q).symm
  have : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have hF : (0 : ℝ) < finrank ℚ F := Nat.cast_pos.2 finrank_pos
  have hKF : (0 : ℝ) < finrank F K := Nat.cast_pos.2 finrank_pos
  rw [show τ γ = algebraMap F K γ from rfl, ← Algebra.norm_norm (S := F), Algebra.norm_algebraMap, map_pow,
    Rat.cast_pow, abs_pow, Real.log_pow, ← Module.finrank_mul_finrank ℚ F K, Nat.cast_mul]
  field_simp

end NumberField
