import HermFormsLattice
import WeylSandwich
import PeriodTarget

/-!
# The integral rows span the row space and lie in a finitely generated module

A step of the frame of the sharp frontier (`ZetaBalance.SharpObj.frameExists_of`, module `SharpFrame`): the target
`C_u` of the frame (`PeriodTarget.Ctgt`) is the set of periods integral on the integral rows
`R = {F ∈ V0 : F(c) ∈ ∇_{Lsh(rep c)}(σ) ∀c}` (`PeriodTarget.rows`). It is an `O_L`-lattice in `W_u` when the rows
span the row space `V0` over `L` (the periods are linear on `V0`, so integrality on a spanning set leaves finitely
many conditions with no common kernel) and lie in a finitely generated `O_L`-module (so every period has a nonzero
integer multiple that is integral). Both hold for the row space of all `VV(σ)`-valued rows on finitely many classes,
with lattices between `a·O_E^n` and `b⁻¹O_E^n` (`HermForms.Sand`, e.g. unimodular ones) and an antitone weight
(`rows_span`, `rows_fg`).

**`∇_N` against `Δ_N`.** Both are defined place by place in some local basis of `O_{L,w}·τ(N)` (`WeylFock.nablaN`,
`WeylFock.DeltaN`), and the sandwich of `WeylSandwich` compares them in each: `Δ_A ⊆ ∇_A`
(`WeylSandwich.Delta_subset_nablaInt`), so `Δ_N ⊆ ∇_N` (`DeltaN_subset_nablaN`); and `κ·∇_A ⊆ Δ_A` for the integer
`κ = ⟨hw, hw⟩` (`kapN_smul_mem_Delta`: the Fock pairing of two polynomials with coefficients in `A` lies in `A`), so
`κ·∇_N ⊆ Δ_N` (`kapN_smul_mem_DeltaN`). The library's facts about `Δ_N` then transfer.
* *Spanning* (`exists_int_smul_mem_nablaN`): every vector of `VV(σ)` has a nonzero integer multiple in `Δ_N`
  (`HermForms.exists_int_smul_mem_DeltaN`), hence in `∇_N`.
* *Bounded denominators* (`exists_coeff_twist_mem_nablaN`): for `P ∈ ∇_N`, `κP ∈ Δ_N`, whose twist by `a·1` has
  `kden·D₀`-integral coefficients at every place (`HermForms.coeff_twist_mem`, `HermForms.exists_delta_den`).

**The rows.** *Spanning* (`rows_span`): a row is the sum of its values on single classes, and a value
`P ∈ VV(σ)` on one class has an integer multiple in `∇_N` there, the value `0 ∈ ∇_N` elsewhere. *Finite generation*
(`rows_fg`): the injection `F ↦ (k_c·twist_{a_c·1} F(c))_c` maps the rows into polynomials with coefficients in
`O_L` and monomials among those of the bideterminants (`HermForms.mem_bidetMonos`), the `O_L`-span of finitely many
vectors (`HermForms.mem_span_single_monomial`); `O_L` is noetherian.
-/

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock MvPolynomial WeylSandwich

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L]
  [NumberField L] (τ : Φ → (E →+* L)) {σ : Φ → Fin n → ℤ}

/-! ## `∇_N` against `Δ_N` -/

section Nabla

omit [NumberField E] in
/-- **`Δ_N ⊆ ∇_N`**, place by place in the same local basis (`WeylSandwich.Delta_subset_nablaInt`). -/
theorem DeltaN_subset_nablaN (hσ : ∀ ρ, Antitone (σ ρ)) (N : Submodule (𝓞 E) (Fin n → E)) :
    DeltaN τ σ N ⊆ (nablaN τ σ N : Set (Pol Φ n L)) := fun _ hP =>
  ⟨hP.1, fun w => let ⟨C, hC, hD⟩ := hP.2 w
    ⟨C, hC, Delta_subset_nablaInt (Ow w) (fun ρ => natW_antitone (hσ ρ)) hD⟩⟩

/-- **`κ·∇_A ⊆ Δ_A`** for the integer `κ = ⟨hw, hw⟩` (`WeylSandwich.kapN`): the pairing of `κF` with a bideterminant,
divided by `κ`, is `Σ_d F_d·β_d·d!`, with `F_d, β_d ∈ A` (`WeylSandwich.coeff_mem_of_nablaInt`,
`HermForms.coeff_bidet_mem`). -/
theorem kapN_smul_mem_Delta (A : Subring L) {ν : Φ → Fin n → ℕ} (hν : ∀ ρ, Antitone (ν ρ)) {F : Pol Φ n L}
    (hF : F ∈ nablaInt A ν) : (kapN ν : L) • F ∈ Delta A ν := by
  refine ⟨Submodule.smul_mem _ _ (nablaInt_subset_nabla A hν hF), fun rows => ?_⟩
  rw [fock_smul_left, fock_hw_eq_kapN, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (kapN_ne_zero ν)),
    fock_eq_sum_left (subset_refl _)]
  exact A.sum_mem fun d _ => A.mul_mem (A.mul_mem (coeff_mem_of_nablaInt A hF d) (coeff_bidet_mem A ν rows d))
    (by unfold fact; exact A.prod_mem fun _ _ => natCast_mem A _)

omit [NumberField E] in
/-- **`κ·∇_N ⊆ Δ_N`**, place by place in the same local basis (`kapN_smul_mem_Delta`). -/
theorem kapN_smul_mem_DeltaN (hσ : ∀ ρ, Antitone (σ ρ)) {N : Submodule (𝓞 E) (Fin n → E)} {P : Pol Φ n L}
    (hP : P ∈ nablaN τ σ N) : (kapN (fun ρ => natW (σ ρ)) : L) • P ∈ DeltaN τ σ N := by
  refine ⟨Submodule.smul_mem _ _ hP.1, fun w => ?_⟩
  obtain ⟨C, hC, hG⟩ := hP.2 w
  exact ⟨C, hC, by rw [twist_smul]; exact kapN_smul_mem_Delta (Ow w) (fun ρ => natW_antitone (hσ ρ)) hG⟩

variable {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ}

omit [NumberField E] in
/-- **Every vector of `VV(σ)` has a nonzero integer multiple in `∇_N`**: in `Δ_N`
(`HermForms.exists_int_smul_mem_DeltaN`), which lies in `∇_N`. -/
theorem exists_int_smul_mem_nablaN (hσ : ∀ ρ, Antitone (σ ρ)) (h : Sand N a b) {P : Pol Φ n L}
    (hP : P ∈ VV (n := n) (L := L) σ) : ∃ z : ℤ, z ≠ 0 ∧ (z : L) • P ∈ nablaN τ σ N := by
  obtain ⟨z, hz0, hz⟩ := exists_int_smul_mem_DeltaN τ σ h hP
  exact ⟨z, hz0, DeltaN_subset_nablaN τ hσ N hz⟩

omit [NumberField E] in
/-- **`0 ∈ ∇_N`** (`exists_int_smul_mem_nablaN` at `0`). -/
theorem zero_mem_nablaN (hσ : ∀ ρ, Antitone (σ ρ)) (h : Sand N a b) : (0 : Pol Φ n L) ∈ nablaN τ σ N := by
  obtain ⟨z, -, hz⟩ := exists_int_smul_mem_nablaN τ hσ h (zero_mem (VV (n := n) (L := L) σ))
  rwa [smul_zero] at hz

omit [NumberField E] in
/-- **`∇_N` has bounded denominators**: one nonzero integer `k` makes the twist by `a·1` of every `P ∈ ∇_N`
integral. `κP ∈ Δ_N` (`kapN_smul_mem_DeltaN`), and the twist of a vector of `Δ_N` by `a·1` has `kden·D₀`-integral
coefficients at every place (`HermForms.coeff_twist_mem`, with `D₀` of `HermForms.exists_delta_den`). -/
theorem exists_coeff_twist_mem_nablaN (hσ : ∀ ρ, Antitone (σ ρ)) (h : Sand N a b) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ P ∈ nablaN τ σ N, ∀ d,
      (k : L) * (twist σ (fun _ => (a : L) • 1) P).coeff d ∈ (1 : Submodule (𝓞 L) L) := by
  obtain ⟨D₀, hD₀0, hD₀⟩ := exists_delta_den (L := L) fun ρ => natW_antitone (hσ ρ)
  set κ := kapN fun ρ => natW (σ ρ)
  refine ⟨kden σ (a * b) * D₀ * κ, mul_ne_zero (mul_ne_zero ?_ (by exact_mod_cast hD₀0))
    (by exact_mod_cast kapN_ne_zero _), fun P hP d => mem_one_of_forall_Ow fun w => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun ρ _ => pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero h.a_ne h.b_ne))
  have := coeff_twist_mem τ σ h hD₀ (kapN_smul_mem_DeltaN τ hσ hP) w d
  rw [twist_smul, coeff_smul, smul_eq_mul] at this
  convert this using 1
  push_cast
  ring

end Nabla

/-! ## The rows -/

section Rows

variable {G X : Type} [Group G] [MulAction G X] (lsh : X → Submodule (𝓞 E) (Fin n → E))
  (V0 : Submodule L (Cl G X →₀ Pol Φ n L))

omit [NumberField E] in
/-- **The integral rows span the row space** of all `VV(σ)`-valued rows (`V0` holds the rows with values in
`VV(σ)`, and every single-class row with a value in `VV(σ)`): a row is the sum of its single-class parts, and each
has a nonzero integer multiple that is a row (`exists_int_smul_mem_nablaN` at its class, `0 ∈ ∇_N` elsewhere). -/
theorem rows_span (hσ : ∀ ρ, Antitone (σ ρ)) (hlsh : ∀ x, ∃ a b, Sand (lsh x) a b)
    (hV0 : ∀ F ∈ V0, ∀ c, F c ∈ VV (n := n) (L := L) σ)
    (hsingle : ∀ c, ∀ P ∈ VV (n := n) (L := L) σ, Finsupp.single c P ∈ V0) :
    Submodule.span L (PeriodTarget.rows τ σ lsh V0) = ⊤ := by
  classical
  refine eq_top_iff.2 fun F _ => ?_
  have hF : F = ∑ c ∈ (F : Cl G X →₀ Pol Φ n L).support,
      (⟨Finsupp.single c ((F : Cl G X →₀ Pol Φ n L) c), hsingle c _ (hV0 _ F.2 c)⟩ : V0) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    exact (Finsupp.sum_single _).symm
  rw [hF]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨a, b, hab⟩ := hlsh c.out
  obtain ⟨z, hz0, hz⟩ := exists_int_smul_mem_nablaN τ hσ hab (hV0 _ F.2 c)
  have hr : (⟨Finsupp.single c ((z : L) • (F : Cl G X →₀ Pol Φ n L) c),
      hsingle c _ (Submodule.smul_mem _ _ (hV0 _ F.2 c))⟩ : V0) ∈ PeriodTarget.rows τ σ lsh V0 := fun c' => by
    by_cases hc : c' = c
    · subst hc
      simpa using hz
    · obtain ⟨a', b', hab'⟩ := hlsh c'.out
      simpa [Finsupp.single_eq_of_ne hc] using zero_mem_nablaN τ hσ hab'
  have : (⟨Finsupp.single c ((F : Cl G X →₀ Pol Φ n L) c), hsingle c _ (hV0 _ F.2 c)⟩ : V0) =
      ((z : L))⁻¹ • ⟨Finsupp.single c ((z : L) • (F : Cl G X →₀ Pol Φ n L) c),
        hsingle c _ (Submodule.smul_mem _ _ (hV0 _ F.2 c))⟩ := by
    refine Subtype.ext ?_
    simp only [SetLike.val_smul, Finsupp.smul_single, smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hz0 : (z : L) ≠ 0),
      one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hr)

omit [NumberField E] in
/-- **The integral rows lie in a finitely generated `O_L`-module**, over finitely many classes: the injection
`F ↦ (k_c·twist_{a_c·1} F(c))_c`, with `a_c`, `b_c` of the lattice of the class and `k_c` of
`exists_coeff_twist_mem_nablaN`, maps the rows into the `O_L`-span of the `Pi.single c (monomial d 1)` over the
classes `c` and the monomials `d` of the bideterminants (`HermForms.mem_span_single_monomial`), and `O_L` is
noetherian. -/
theorem rows_fg (hfin : Finite (Cl G X)) (hσ : ∀ ρ, Antitone (σ ρ)) (hlsh : ∀ x, ∃ a b, Sand (lsh x) a b)
    (hV0 : ∀ F ∈ V0, ∀ c, F c ∈ VV (n := n) (L := L) σ) :
    ∃ Lm : Submodule (𝓞 L) V0, Lm.FG ∧ PeriodTarget.rows τ σ lsh V0 ⊆ Lm := by
  classical
  let := Fintype.ofFinite (Cl G X)
  set ν : Φ → Fin n → ℕ := fun ρ => natW (σ ρ)
  have hν : ∀ ρ, Antitone (ν ρ) := fun ρ => natW_antitone (hσ ρ)
  choose a b hab using fun c : Cl G X => hlsh c.out
  choose k hk0 hk using fun c => exists_coeff_twist_mem_nablaN τ hσ (hab c)
  set Ψ : V0 →ₗ[L] (Cl G X → Pol Φ n L) :=
    { toFun := fun F c => (k c : L) • twist σ (fun _ => (a c : L) • 1) ((F : Cl G X →₀ Pol Φ n L) c)
      map_add' := fun F F' => by
        funext c
        simp only [Submodule.coe_add, Finsupp.add_apply, twist_add, smul_add, Pi.add_apply]
      map_smul' := fun r F => by
        funext c
        simp only [SetLike.val_smul, Finsupp.smul_apply, twist_smul, smul_comm r, RingHom.id_apply,
          Pi.smul_apply] }
  have hΨ : Function.Injective Ψ := fun F F' h => Subtype.ext (Finsupp.ext fun c =>
    twist_smul_one_injective σ (Int.cast_ne_zero.2 (hab c).a_ne)
      (smul_right_injective (Pol Φ n L) (Int.cast_ne_zero.2 (hk0 c) : (k c : L) ≠ 0) (congrFun h c)))
  refine ⟨(Submodule.span (𝓞 L) (Set.range fun p : Cl G X × bidetMonos L ν =>
      Pi.single p.1 (monomial (p.2 : Φ × Fin n × Fin n →₀ ℕ) (1 : L)))).comap (Ψ.restrictScalars (𝓞 L)),
    Submodule.fg_of_fg_map_injective (Ψ.restrictScalars (𝓞 L)) hΨ
      ((Submodule.fg_span (Set.finite_range _)).of_le (Submodule.map_comap_le _ _)), fun F hF => ?_⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  refine mem_span_single_monomial (x := Ψ F) (fun c d => ?_) (fun c d hd => ?_)
  · show ((k c : L) • twist σ (fun _ => (a c : L) • 1) ((F : Cl G X →₀ Pol Φ n L) c)).coeff d ∈ _
    rw [coeff_smul, smul_eq_mul]
    exact hk c _ (hF c) d
  · exact mem_bidetMonos hν (Submodule.smul_mem _ _ (twist_mem_nabla σ _ (hV0 _ F.2 c))) hd

end Rows

end

end HermForms
