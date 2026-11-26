import HermForms
import WeylSpan
import HermFinite

/-!
# The forms are finite-dimensional, the integral forms a lattice, the Petersson form positive

The second piece of the proof of the sharp frontier (`SharpInputs.FormsLattice`, C2), for a CM field `E`, a number
field `L`, embeddings `τ : Φ → (E →+* L)`, a character `χ` of the level group and an antitone weight `λ`
(`formsLattice`, with the hypotheses of `FormsLattice`; the wrapper is `ZetaBalance.formsLattice_proved`).

**Finite dimension** (`finiteDimensional_Forms`). A form is determined by its values at the representatives of the
classes (`eq_zero_of_out`: every point is `g·rep c`, and `F(g·d) = chr(g)·ρ_λ(γ_g)F(d)`), finitely many
(`HermClasses.finite_DCl`), each in `VV_L(λ) = ∇_L(natW λ)`, which is finite-dimensional as the span of the finitely
many bideterminants (`WeylFock.span_bidet`). So `F ↦ (F(rep c))_c` embeds the forms in a finite-dimensional space.

**Positivity** (`gram_posDef`). At every `σ : L →+* ℂ`, `H_σ(F, F) = Σ_c mass(c)·fock(σF(rep c), σF(rep c))/κ`, with
`fock(G, G) = Σ_d |G_d|²·d!` and `κ = fock(hw, hw) > 0`. In the basis `b` of `V_ω`, the Gram matrix is `Bᴴ W B`
(`gram_eq`), with `B_{(c,d), j} = σ(coeff_d b_j(rep c))` over the classes `c` and the finitely many monomials `d` of
the `b_j(rep c)`, and `W` diagonal with the positive entries `mass(c)·d!/κ` (`mass c > 0` by
`HermClasses.finite_stab`). `B` is injective: over `L` because a form vanishing at every representative is `0`, and
over `ℂ` because an injective matrix has a left inverse, which `σ` maps to a left inverse of `B`
(`mulVec_map_injective`).

**The lattice** (`isLattice_Mlat`). Three inputs.
* *The attached lattices* (`exists_sand_Lsh`): for a good point `d`, `N = d.N ⊆ Lsh(d) ⊆ m⁻¹N` with `m` an integer
  in every `P ∈ ST` (`le_Lsh`, `smul_Lsh_mem`), and the unimodular `N` contains `a·O_E^n` and lies in `a⁻¹O_E^n`
  (`exists_sand_of_unimodular`). So `Lsh(d)` lies between `a·O_E^n` and `b⁻¹O_E^n` for nonzero integers `a`, `b`
  (`Sand`).
* *Local bases* (`exists_localBasis`): `N_w = O_{L,w}·σ(N)` lies in a free module of rank `n` over the principal ideal
  ring `O_{L,w}`, so it is free on at most `n` vectors, which padded with zeros give a local basis `C`; any local basis
  has `a·1 = C·U` with `U` integral (`exists_U`) and `b·C` integral (`smul_integral`). Where `ab` is a unit at `w`,
  `a·1` is itself a local basis (`isLocalBasis_smul_one`).
* *Bounded denominators of `Δ`* (`exists_delta_den`): one integer `D₀` with `D₀·G` integral for every `G ∈ Δ_A(ν)` and
  every subring `A`. Over `ℚ` the Gram matrix `Γ` of the bideterminants and their coefficient matrix `B` have
  `ker Γ ⊆ ker B` (the Fock form is definite over `ℚ`), so `B = YΓ`, and `G_d = Σ_r Y_{dr}⟨β_r, G⟩`.

*Spanning* (`span_Mlat`): every vector of `VV(λ)` has a nonzero integer multiple in `Δ_N` (`exists_int_smul_mem_DeltaN`:
a local basis at the finitely many places dividing `ab`, the basis `a·1` elsewhere, and an integer clearing the
finitely many Fock pairings in each), so every form has one in `M` (`exists_int_smul_mem_Mint`).
*Finite generation* (`fg_Mlat`): for `P ∈ Δ_N`, write `a·1 = C·U` at each `w`; the twist of `P` by `a·1` is the twist by
`U` of `twist_C P ∈ Δ_{O_{L,w}}` (`twist_twist`), so `kden·D₀` times it is integral at every `w` (`coeff_twist_mem`,
with `det U` controlled by `det(b·C)`, `det_zpow_mem`), hence over `O_L`. The injection
`F ↦ (kden·D₀·twist_{a·1} F(rep c))_c` maps the integral forms into the `O_L`-span of finitely many monomials, and
`O_L` is noetherian.
-/

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock MvPolynomial

open scoped Matrix

open scoped ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
  {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L] [NumberField L]

/-! ## Finite dimension -/

section FiniteDim

/-- `natW λ` is antitone when `λ` is. -/
theorem natW_antitone {w : Fin n → ℤ} (hw : Antitone w) : Antitone (natW w) :=
  fun _ _ hij => Int.toNat_le_toNat (sub_le_sub_right (hw hij) _)

omit [NumberField L] in
/-- `VV_L(λ)` is finite-dimensional: the span of the finitely many bideterminants (`span_bidet`). -/
theorem finiteDimensional_VV [CharZero L] {lam : Φ → Fin n → ℤ} (hlam : ∀ ρ, Antitone (lam ρ)) :
    FiniteDimensional L (nabla L fun ρ => natW (lam ρ)) := by
  rw [← span_bidet fun ρ => natW_antitone (hlam ρ)]
  exact FiniteDimensional.span_of_finite L (Set.finite_range _)

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

omit [NumberField L] in
/-- **A form vanishing at every representative is `0`**: every point is `g·rep c`, and
`F(g·d) = chr(g)·ρ_λ(γ_g)F(d)`. -/
theorem eq_zero_of_out {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam)
    (h0 : ∀ c : DCl E n ST Λ, F c.out = 0) : F = 0 := by
  funext d
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel (Grp E n SG Λ) _) d
  have hd : d = g⁻¹ • (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d).out := by
    rw [← hg, inv_smul_smul]
  rw [hd, hF.2, h0]
  simp [rho]

/-- The values at the representatives of the classes, `F ↦ (F(rep c))_c`. -/
def atReps : Forms ST τ χ lam →ₗ[L] (DCl E n ST Λ → VV (n := n) (L := L) lam) where
  toFun F c := ⟨(F : Fn ST Λ Φ L) c.out, F.2.1 c.out⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField L] in
/-- The values at the representatives determine a form (`eq_zero_of_out`). -/
theorem atReps_injective : Function.Injective (atReps ST τ χ lam) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  exact Subtype.ext (eq_zero_of_out ST τ χ lam F.2 fun c => congrArg Subtype.val (congrFun hF c))

/-- **The forms are finite-dimensional** (C2, first part): `F ↦ (F(rep c))_c` embeds them in `VV_L(λ)^{Cl}`,
finite-dimensional as there are finitely many classes (`finite_DCl`) and `VV_L(λ)` is (`finiteDimensional_VV`). -/
theorem finiteDimensional_Forms (hlam : ∀ ρ, Antitone (lam ρ)) : FiniteDimensional L (Forms ST τ χ lam) := by
  have := finite_DCl E n ST SG Λ
  have : FiniteDimensional L (VV (n := n) (L := L) lam) := finiteDimensional_VV hlam
  exact Module.Finite.of_injective (atReps ST τ χ lam) (atReps_injective ST τ χ lam)

/-- The cut `V_ω` is finite-dimensional, as a subspace of the forms. -/
theorem finiteDimensional_Vω (hlam : ∀ ρ, Antitone (lam ρ)) : FiniteDimensional L (Vω ST τ χ lam) :=
  have := finiteDimensional_Forms ST τ χ lam hlam
  Submodule.finiteDimensional_of_le inf_le_left

end FiniteDim

/-! ## Positivity of the Petersson form -/

section Linear

/-- If `A` has trivial kernel, so has its image under a field homomorphism `σ`: `A` has a left inverse `N`, and
`σ(N)` is a left inverse of `σ(A)`. -/
theorem mulVec_map_injective {K K' R m : Type*} [Field K] [Field K'] [Fintype R] [Fintype m] [DecidableEq R]
    [DecidableEq m] (σ : K →+* K') {A : Matrix R m K} (hA : Function.Injective A.mulVec) :
    Function.Injective (A.map σ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot.2 fun x y h => hA (by simpa only [Matrix.toLin'_apply] using h))
  have hNA : LinearMap.toMatrix' g * A = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at this
  have hNA' : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hNA, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa only [Matrix.mulVec_mulVec, hNA', Matrix.one_mulVec] using this

end Linear

section Fock

variable {K : Type*} [Field K]

omit [DecidableEq Φ] in
/-- The Fock form summed over any finite set of exponents containing the support of the second argument. -/
theorem fockWith_eq_sum (c : K →+* K) {P Q : Pol Φ n K} {S : Finset (Φ × Fin n × Fin n →₀ ℕ)}
    (hS : Q.support ⊆ S) : fockWith c P Q = ∑ d ∈ S, c (P.coeff d) * Q.coeff d * fact d := by
  unfold fockWith
  calc ∑ d ∈ Q.support, c (P.coeff d) * Q.coeff d * d.prod (fun _ k => (k.factorial : K))
      = ∑ d ∈ Q.support, c (P.coeff d) * Q.coeff d * fact d := Finset.sum_congr rfl fun d _ => by
        rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
        rfl
    _ = _ := Finset.sum_subset hS fun d _ hd => by rw [notMem_support_iff.1 hd]; ring

omit [DecidableEq Φ] in
/-- `d! > 0` in `ℂ`. -/
theorem fact_pos (d : Φ × Fin n × Fin n →₀ ℕ) : (0 : ℂ) < fact d :=
  Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _)

omit [DecidableEq Φ] in
/-- `fock(G, G) = Σ_d |G_d|²·d! > 0` over `ℂ` for `G ≠ 0`. -/
theorem fockWith_self_pos {P : Pol Φ n ℂ} (hP : P ≠ 0) : 0 < fockWith (starRingEnd ℂ) P P := by
  rw [fockWith_eq_sum _ (subset_refl _)]
  exact Finset.sum_pos (fun d hd => mul_pos (star_mul_self_pos (IsRegular.of_ne_zero (mem_support_iff.1 hd)))
    (fact_pos d)) (support_nonempty.2 hP)

omit [DecidableEq Φ] in
/-- `κ = fock(hw, hw) > 0` over `ℂ`. -/
theorem fock_hw_pos (ν : Φ → Fin n → ℕ) : 0 < fockWith (starRingEnd ℂ) (hw ℂ ν) (hw ℂ ν) :=
  fockWith_self_pos fun h => by simpa [h] using eval_one_hw (L := ℂ) (Φ := Φ) ν

end Fock

section Gram

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ) [FiniteDimensional L (Vω ST τ χ lam)]
  [Fintype (DCl E n ST Λ)]

/-- The monomials `d` of the basis forms `b_j` of `V_ω` at the representatives. -/
def monos : Finset (Φ × Fin n × Fin n →₀ ℕ) :=
  Finset.univ.biUnion fun p : Idx ST τ χ lam × DCl E n ST Λ =>
    ((Module.finBasis L (Vω ST τ χ lam) p.1 : Fn ST Λ Φ L) p.2.out).support

/-- The coefficient matrix `A_{(c,d), j} = coeff_d b_j(rep c)` of the basis of `V_ω`. -/
def coeffMat : Matrix (DCl E n ST Λ × monos ST τ χ lam) (Idx ST τ χ lam) L :=
  fun r j => ((Module.finBasis L (Vω ST τ χ lam) j : Fn ST Λ Φ L) r.1.out).coeff r.2

omit [NumberField L] in
/-- The monomials of `b_j(rep c)` lie in `monos`. -/
theorem support_subset_monos (j : Idx ST τ χ lam) (c : DCl E n ST Λ) :
    ((Module.finBasis L (Vω ST τ χ lam) j : Fn ST Λ Φ L) c.out).support ⊆ monos ST τ χ lam := fun _ hx =>
  Finset.mem_biUnion.2 ⟨(j, c), Finset.mem_univ _, hx⟩

omit [NumberField L] in
/-- The coefficient matrix is injective: a combination of the basis vanishing at every representative is `0`
(`eq_zero_of_out`). -/
theorem coeffMat_injective : Function.Injective (coeffMat ST τ χ lam).mulVec := by
  set b := Module.finBasis L (Vω ST τ χ lam)
  suffices h : ∀ y, coeffMat ST τ χ lam *ᵥ y = 0 → y = 0 by
    intro x y hxy
    exact sub_eq_zero.1 (h _ (by rw [Matrix.mulVec_sub, hxy, sub_self]))
  intro y hy
  set F : Vω ST τ χ lam := ∑ j, y j • b j
  have hF : ∀ c : DCl E n ST Λ, (F : Fn ST Λ Φ L) c.out = 0 := fun c => by
    ext d
    simp only [F, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, coeff_sum, coeff_smul,
      smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hd : d ∈ monos ST τ χ lam
    · have := congrFun hy (c, ⟨d, hd⟩)
      simp only [Matrix.mulVec, dotProduct, coeffMat, Pi.zero_apply] at this
      exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans this
    · exact Finset.sum_eq_zero fun j _ => by
        rw [notMem_support_iff.1 fun h => hd (support_subset_monos ST τ χ lam j c h), mul_zero]
  have h0 : F = 0 := Subtype.ext (eq_zero_of_out ST τ χ lam (Submodule.mem_inf.1 F.2).1 hF)
  funext j
  exact Fintype.linearIndependent_iff.1 b.linearIndependent y h0 j

/-- The weights `mass(c)·d!/κ` of the Gram matrix, `κ = fock(hw, hw)` over `ℂ`. -/
def gramW (r : DCl E n ST Λ × monos ST τ χ lam) : ℂ :=
  (mass r.1 : ℂ) * fact r.2.1 / fockWith (starRingEnd ℂ) (hw ℂ fun ρ => natW (lam ρ)) (hw ℂ fun ρ => natW (lam ρ))

omit [NumberField L] in
/-- **The Gram matrix factors** as `Bᴴ W B`, with `B = σ(A)` the coefficients and `W` the diagonal weights. -/
theorem gram_eq [DecidableEq (DCl E n ST Λ)] (σ : L →+* ℂ) : gram ST τ χ lam σ =
    Matrix.conjTranspose ((coeffMat ST τ χ lam).map σ) * Matrix.diagonal (gramW ST τ χ lam) *
      (coeffMat ST τ χ lam).map σ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [gram, Hω, petAt, classSum, finsum_eq_sum_of_fintype, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, Matrix.map_apply, fock, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fockWith_eq_sum _ ((support_map_subset _ _).trans (support_subset_monos ST τ χ lam j c)), Rat.smul_def,
    Finset.sum_div, Finset.mul_sum, ← Finset.sum_coe_sort (monos ST τ χ lam)]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [coeff_map, coeffMat, gramW, RCLike.star_def]
  ring

end Gram

section Pos

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ) [FiniteDimensional L (Vω ST τ χ lam)]

omit [NumberField L] in
/-- The mass weights are positive: the stabilisers are finite (`finite_stab`). -/
theorem mass_pos (c : DCl E n ST Λ) : (0 : ℂ) < (mass c : ℂ) := by
  have := finite_stab E n ST SG Λ c
  have h : (0 : ℚ) < mass c := inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  rw [← Complex.ofReal_ratCast]
  exact Complex.zero_lt_real.2 (Rat.cast_pos.2 h)

omit [NumberField L] in
/-- **The Petersson form is positive definite** at every `σ : L →+* ℂ` (C2, third part): its Gram matrix is
`Bᴴ W B` (`gram_eq`), with `W` diagonal positive and `B` injective (`coeffMat_injective`, `mulVec_map_injective`). -/
theorem gram_posDef (σ : L →+* ℂ) : (gram ST τ χ lam σ).PosDef := by
  classical
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  rw [gram_eq ST τ χ lam σ]
  refine Matrix.PosDef.conjTranspose_mul_mul_same (Matrix.PosDef.diagonal fun r => ?_)
    (mulVec_map_injective σ (coeffMat_injective ST τ χ lam))
  exact div_pos (mul_pos (mass_pos ST r.1) (fact_pos _)) (fock_hw_pos _)

end Pos

/-! ## Twists, and integrality under substitution -/

section Twist

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- Substituting `A`, then `B`, is substituting `B·A`: `lsub A ∘ lsub B = lsub (B·A)`. -/
theorem lsub_lsub (A B : Φ → Matrix (Fin n) (Fin n) L) (F : Pol Φ n L) :
    lsub A (lsub B F) = lsub (fun σ => B σ * A σ) F := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, lsub_X, map_sum, map_mul, lsub_C, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

omit [DecidableEq Φ] [NumberField L] in
/-- Twisting by `B`, then by `A`, is twisting by `B·A`. -/
theorem twist_twist (lam : Φ → Fin n → ℤ) (A B : Φ → Matrix (Fin n) (Fin n) L) (F : Pol Φ n L) :
    twist lam A (twist lam B F) = twist lam (fun σ => B σ * A σ) F := by
  simp only [twist, map_mul, lsub_C, lsub_lsub, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

omit [DecidableEq Φ] [NumberField L] in
/-- Twisting by the identity changes nothing. -/
theorem twist_one (lam : Φ → Fin n → ℤ) (F : Pol Φ n L) : twist lam (fun _ => 1) F = F := by
  simp [twist, lsub_one]

omit [DecidableEq Φ] [NumberField L] in
/-- A twist is `L`-linear: scalars. -/
theorem twist_smul (lam : Φ → Fin n → ℤ) (g : Φ → Matrix (Fin n) (Fin n) L) (a : L) (F : Pol Φ n L) :
    twist lam g (a • F) = a • twist lam g F := by
  simp only [twist, map_smul, mul_smul_comm]

omit [DecidableEq Φ] [NumberField L] in
/-- A twist is `L`-linear: sums. -/
theorem twist_add (lam : Φ → Fin n → ℤ) (g : Φ → Matrix (Fin n) (Fin n) L) (F G : Pol Φ n L) :
    twist lam g (F + G) = twist lam g F + twist lam g G := by
  simp only [twist, map_add, mul_add]

omit [NumberField L] in
/-- A twist keeps `∇`. -/
theorem twist_mem_nabla (lam : Φ → Fin n → ℤ) (g : Φ → Matrix (Fin n) (Fin n) L) {ν : Φ → Fin n → ℕ}
    {F : Pol Φ n L} (hF : F ∈ nabla L ν) : twist lam g F ∈ nabla L ν := by
  rw [twist, C_mul']
  exact Submodule.smul_mem _ _ (lsub_mem_nabla _ hF)

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- A substitution by a matrix with entries in a subring `A` keeps the polynomials with coefficients in `A`. -/
theorem lsub_coeff_mem {A : Subring L} {g : Φ → Matrix (Fin n) (Fin n) L} (hg : ∀ σ i j, g σ i j ∈ A)
    {F : Pol Φ n L} (hF : ∀ d, F.coeff d ∈ A) (d : Φ × Fin n × Fin n →₀ ℕ) : (lsub g F).coeff d ∈ A := by
  have key : ∀ F : Pol Φ n L, F ∈ (MvPolynomial.map A.subtype).range ↔ ∀ d, F.coeff d ∈ A := fun F => by
    rw [RingHom.mem_range, ← Set.mem_range, mem_range_map_iff_coeffs_subset]
    refine ⟨fun h d => ?_, fun h x hx => ?_⟩
    · by_cases hd : F.coeff d = 0
      · rw [hd]
        exact A.zero_mem
      · obtain ⟨a, ha⟩ := h (coeff_mem_coeffs d hd)
        rw [← ha]
        exact a.2
    · obtain ⟨d, -, rfl⟩ := mem_coeffs_iff.1 hx
      exact ⟨⟨_, h d⟩, rfl⟩
  have hC : ∀ a ∈ A, (C a : Pol Φ n L) ∈ (MvPolynomial.map A.subtype).range := fun a ha =>
    ⟨C ⟨a, ha⟩, by simp⟩
  have hX : ∀ p, (X p : Pol Φ n L) ∈ (MvPolynomial.map A.subtype).range := fun p => ⟨X p, by simp⟩
  obtain ⟨F', rfl⟩ := (key F).2 hF
  refine (key _).1 ?_ d
  clear hF
  induction F' using MvPolynomial.induction_on with
  | C a => rw [map_C, lsub_C]; exact hC _ (Subtype.coe_prop a)
  | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_X, lsub_X]
    exact mul_mem hp (sum_mem fun c _ => mul_mem (hC _ (hg _ _ _)) (hX _))

end Twist


/-! ## The Fock dual `Δ` has bounded denominators -/

section DeltaBound

variable {K : Type*} [Field K]

omit [DecidableEq Φ] in
/-- The bideterminants over `K` are the images of those over `ℚ`. -/
theorem map_bidet [CharZero K] (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) :
    MvPolynomial.map (algebraMap ℚ K) (bidet ℚ ν rows) = bidet K ν rows := by
  simp only [bidet, minor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  ext i j
  simp [xMat]

omit [DecidableEq Φ] in
/-- The Fock form commutes with `ℚ → K`. -/
theorem fock_map [CharZero K] (P Q : Pol Φ n ℚ) :
    fockWith (RingHom.id K) (MvPolynomial.map (algebraMap ℚ K) P) (MvPolynomial.map (algebraMap ℚ K) Q) =
      algebraMap ℚ K (fockWith (RingHom.id ℚ) P Q) := by
  rw [fock_eq_sum_left (support_map_subset _ _), fock_eq_sum_left (subset_refl P.support)]
  simp [coeff_map, fact]

omit [DecidableEq Φ] in
/-- The bilinear Fock form over `ℚ` is definite. -/
theorem fock_self_pos_rat {P : Pol Φ n ℚ} (hP : P ≠ 0) : 0 < fockWith (RingHom.id ℚ) P P := by
  rw [fock_eq_sum_left (subset_refl _)]
  exact Finset.sum_pos (fun d hd => mul_pos (mul_self_pos.2 (mem_support_iff.1 hd))
    (Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _))) (support_nonempty.2 hP)

/-- If `ker Γ ⊆ ker B`, then `B = Y·Γ` for some `Y`. -/
theorem exists_mul_eq_of_ker {R T : Type*} [Fintype R] [Fintype T] [DecidableEq R] [DecidableEq T]
    {Γ : Matrix R R K} {B : Matrix T R K} (h : ∀ u, Γ *ᵥ u = 0 → B *ᵥ u = 0) : ∃ Y : Matrix T R K, B = Y * Γ := by
  set f := Matrix.toLin' Γ
  set g := Matrix.toLin' B
  have hker : LinearMap.ker f.rangeRestrict ≤ LinearMap.ker g := by
    rw [LinearMap.ker_rangeRestrict]
    intro u hu
    simpa [f, g, Matrix.toLin'_apply] using h u (by simpa [f, Matrix.toLin'_apply] using hu)
  set h₀ := f.rangeRestrict.liftOfSurjective f.surjective_rangeRestrict ⟨g, hker⟩
  obtain ⟨k, hk⟩ := LinearMap.exists_extend h₀
  refine ⟨LinearMap.toMatrix' k, ?_⟩
  have hkf : k ∘ₗ f = g := LinearMap.ext fun u => by
    have := congrArg (fun φ => φ (f.rangeRestrict u)) hk
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.codRestrict_apply, h₀,
      LinearMap.equivOfSurjective_apply] at this
    exact this
  have := congrArg LinearMap.toMatrix' hkf
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin', eq_comm] at this

end DeltaBound

section W1

/-- **`Δ` has bounded denominators, uniformly in the subring**: there is `D ≠ 0` with `D·G` having coefficients in
`A` for every subring `A ⊆ L` and every `G ∈ Δ_A(ν)`. Over `ℚ`, the Gram matrix `Γ` of the bideterminants `β_r` and
their coefficient matrix `B` have `ker Γ ⊆ ker B` (the Fock form is definite over `ℚ`), so `B = YΓ`
(`exists_mul_eq_of_ker`); then `G_d = Σ_r Y_{dr}·⟨β_r, G⟩` for `G` in the span of the `β_r`, and `D` clears the
denominators of the `κ·Y_{dr}`. -/
theorem exists_delta_den {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ (A : Subring L) (G : Pol Φ n L), G ∈ Delta A ν → ∀ d, (D : L) * G.coeff d ∈ A := by
  classical
  set β := bidet ℚ ν
  set T : Finset (Φ × Fin n × Fin n →₀ ℕ) := Finset.univ.biUnion fun r => (β r).support
  set Γ : Matrix _ _ ℚ := fun r r' => fockWith (RingHom.id ℚ) (β r) (β r')
  set B : Matrix T _ ℚ := fun d r => (β r).coeff d
  have hker : ∀ u, Γ *ᵥ u = 0 → B *ᵥ u = 0 := by
    intro u hu
    set P := ∑ r, u r • β r with hPdef
    have hPP : fockWith (RingHom.id ℚ) P P = 0 := by
      rw [fock_sum_left]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [fock_smul_left, fock_sum_right]
      have := congrFun hu r
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Γ] at this
      rw [← mul_zero (u r), ← this]
      congr 1
      exact Finset.sum_congr rfl fun r' _ => by rw [← C_mul', fock_C_mul_right, mul_comm]
    have hP : P = 0 := by
      by_contra hne
      exact (fock_self_pos_rat hne).ne' hPP
    funext d
    have := congrArg (fun p : Pol Φ n ℚ => p.coeff d.1) hP
    simp only [P, coeff_sum, coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, B, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  obtain ⟨Y, hY⟩ := exists_mul_eq_of_ker hker
  set κ : ℚ := fockWith (RingHom.id ℚ) (hw ℚ ν) (hw ℚ ν)
  set D : ℕ := ∏ d : T, ∏ r, (κ * Y d r).den
  have hDint : ∀ d r, ∃ z : ℤ, (D : ℚ) * (κ * Y d r) = z := by
    intro d r
    obtain ⟨k, hk⟩ := (Finset.dvd_prod_of_mem (fun r => (κ * Y d r).den) (Finset.mem_univ r)).trans
      (Finset.dvd_prod_of_mem (fun d => ∏ r, (κ * Y d r).den) (Finset.mem_univ d))
    refine ⟨k * (κ * Y d r).num, ?_⟩
    have hk' : D = (κ * Y d r).den * k := hk
    rw [hk']
    push_cast
    rw [mul_comm ((κ * Y d r).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  refine ⟨D, Finset.prod_ne_zero_iff.2 fun d _ => Finset.prod_ne_zero_iff.2 fun r _ => (κ * Y d r).den_nz, ?_⟩
  intro A G hG d
  have hGs : G ∈ Submodule.span L (Set.range (bidet L ν)) := by rw [span_bidet hν]; exact hG.1
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hGs
  have hb : ∀ r, bidet L ν r = MvPolynomial.map (algebraMap ℚ L) (β r) := fun r => (map_bidet ν r).symm
  by_cases hd : d ∈ T
  · have hBd : ∀ r', (β r').coeff d = ∑ r, Y ⟨d, hd⟩ r * Γ r r' := fun r' => by
      have := congrFun (congrFun hY ⟨d, hd⟩) r'
      simpa [B, Matrix.mul_apply] using this
    have key : G.coeff d = ∑ r, algebraMap ℚ L (Y ⟨d, hd⟩ r) * fockWith (RingHom.id L) (bidet L ν r) G := by
      calc G.coeff d = ∑ r', u r' * algebraMap ℚ L ((β r').coeff d) := by
            rw [← hu, coeff_sum]
            exact Finset.sum_congr rfl fun r' _ => by rw [coeff_smul, smul_eq_mul, hb, coeff_map]
        _ = ∑ r', u r' * ∑ r, algebraMap ℚ L (Y ⟨d, hd⟩ r) * algebraMap ℚ L (Γ r r') := by
            simp only [hBd, map_sum, map_mul]
        _ = ∑ r, algebraMap ℚ L (Y ⟨d, hd⟩ r) * ∑ r', u r' * algebraMap ℚ L (Γ r r') := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = _ := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [← hu, fock_sum_right]
            congr 1
            refine Finset.sum_congr rfl fun r' _ => ?_
            rw [← C_mul', fock_C_mul_right, hb, hb, fock_map]
    have hκ : algebraMap ℚ L κ ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap ℚ L).injective).2 (fock_hw_hw_ne_zero ν)
    have hκL : fockWith (RingHom.id L) (hw L ν) (hw L ν) = algebraMap ℚ L κ := by rw [← WeylFock.map_hw, fock_map]
    rw [key, Finset.mul_sum]
    refine A.sum_mem fun r _ => ?_
    obtain ⟨z, hz⟩ := hDint ⟨d, hd⟩ r
    have hmem := hG.2 r
    rw [hκL, fock_comm] at hmem
    have hz' : (D : L) * (algebraMap ℚ L κ * algebraMap ℚ L (Y ⟨d, hd⟩ r)) = z := by
      have := congrArg (algebraMap ℚ L) hz
      simpa using this
    have : (D : L) * (algebraMap ℚ L (Y ⟨d, hd⟩ r) * fockWith (RingHom.id L) (bidet L ν r) G) =
        (z : L) * (fockWith (RingHom.id L) (bidet L ν r) G / algebraMap ℚ L κ) := by
      rw [← hz']
      field_simp
    rw [this]
    exact A.mul_mem (intCast_mem A z) hmem
  · have : G.coeff d = 0 := by
      rw [← hu, coeff_sum]
      exact Finset.sum_eq_zero fun r _ => by
        rw [coeff_smul, hb, coeff_map, notMem_support_iff.1 fun h => hd (Finset.mem_biUnion.2
          ⟨r, Finset.mem_univ _, h⟩), map_zero, smul_zero]
    rw [this, mul_zero]
    exact A.zero_mem

end W1


/-! ## The attached lattices lie between integral multiples of `O_E^n` -/

section Sand

omit [IsCMField E] in
/-- Every element of `E` has a nonzero integer multiple in `O_E`. -/
theorem exists_int_mul_mem (z : E) : ∃ d : ℤ, d ≠ 0 ∧ (d : E) * z ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨⟨x, ⟨s, hs⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) z
  obtain ⟨m, hm, rfl⟩ := Submonoid.mem_map.1 hs
  refine ⟨m, nonZeroDivisors.ne_zero hm, Submodule.mem_one.2 ⟨x, ?_⟩⟩
  simp only at h
  rw [mul_comm, ← h]
  simp

omit [NumberField E] [IsCMField E] in
/-- An `O_E`-lattice is stable under the integers. -/
theorem int_smul_mem {N : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} (hv : v ∈ N) (a : ℤ) :
    (a : E) • v ∈ N := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hv a

omit [IsCMField E] in
/-- A lattice contains a nonzero integer multiple of every vector. -/
theorem exists_int_smul_mem {N : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ Submodule.span E (N : Set (Fin n → E))) : ∃ a : ℤ, a ≠ 0 ∧ (a : E) • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have : ((a * b : ℤ) : E) • (x + y) = (b : E) • ((a : E) • x) + (a : E) • ((b : E) • y) := by
      rw [smul_add, smul_smul, smul_smul]; push_cast; ring_nf
    rw [this]
    exact add_mem (int_smul_mem hax b) (int_smul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, hdc⟩ := exists_int_mul_mem c
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 hdc
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have : ((d * a : ℤ) : E) • (c • x) = y • ((a : E) • x) := by
      rw [← algebraMap_smul E y, hy, smul_smul, smul_smul]
      push_cast
      ring_nf
    rw [this]
    exact N.smul_mem y hax

/-- `N` lies between `a·O_E^n` and `b⁻¹·O_E^n`: `a·eᵢ ∈ N` for every `i`, and `b·x` is integral for `x ∈ N`. -/
structure Sand (N : Submodule (𝓞 E) (Fin n → E)) (a b : ℤ) : Prop where
  /-- `a ≠ 0`. -/
  a_ne : a ≠ 0
  /-- `b ≠ 0`. -/
  b_ne : b ≠ 0
  /-- `a·O_E^n ⊆ N`. -/
  single_mem : ∀ i, (a : E) • (Pi.single i 1 : Fin n → E) ∈ N
  /-- `b·N ⊆ O_E^n`. -/
  int : ∀ x ∈ N, ∀ i, (b : E) * x i ∈ (1 : Submodule (𝓞 E) E)

omit [IsCMField E] in
/-- A lattice spanning `E^n` contains `a·O_E^n` for some nonzero integer `a`. -/
theorem exists_single_mem {N : Submodule (𝓞 E) (Fin n → E)} (hN : Submodule.span E (N : Set (Fin n → E)) = ⊤) :
    ∃ a : ℤ, a ≠ 0 ∧ ∀ i, (a : E) • (Pi.single i 1 : Fin n → E) ∈ N := by
  classical
  choose a ha hmem using fun i : Fin n => exists_int_smul_mem (N := N) (x := Pi.single i 1) (hN ▸ trivial)
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Int.cast_mul, mul_comm, mul_smul]
  exact int_smul_mem (hmem i) _

/-- `h(a·eᵢ, x) = a·xᵢ` for an integer `a`. -/
theorem herm_int_single (a : ℤ) (i : Fin n) (x : Fin n → E) :
    herm ((a : E) • (Pi.single i 1 : Fin n → E)) x = (a : E) * x i := by
  rw [herm_smul_left, map_intCast, herm_def]
  simp [Pi.single_apply]

/-- A unimodular lattice lies between `a·O_E^n` and `a⁻¹·O_E^n`: `h(a·eᵢ, x) = a·xᵢ` is integral. -/
theorem exists_sand_of_unimodular {N : Submodule (𝓞 E) (Fin n → E)} (hN : IsUnimodular N) :
    ∃ a : ℤ, Sand N a a := by
  obtain ⟨a, ha, hmem⟩ := exists_single_mem (span_eq_top_of_unimodular hN)
  exact ⟨a, ha, ha, hmem, fun x hx i => herm_int_single a i x ▸ herm_mem_one hN (hmem i) hx⟩

omit [IsCMField E] in
/-- A nonzero integer in every `P ∈ ST`: the product of their norms. -/
theorem exists_int_mem_all (ST : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ P ∈ ST, (m : 𝓞 E) ∈ P.asIdeal := by
  refine ⟨∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℤ), Finset.prod_ne_zero_iff.2 fun P _ => ?_, fun P hP => ?_⟩
  · exact Nat.cast_ne_zero.2 fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun P : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm P.asIdeal : ℤ)) hP
    rw [hk, Int.cast_mul]
    exact Ideal.mul_mem_right _ _ (by simpa using Ideal.absNorm_mem P.asIdeal)

/-- `N ⊆ Lsh(d)` for a good `d`: `kerLat d ⊆ N` and `N^# = N`. -/
theorem le_Lsh {d : Deco E n ST SG} (hd : IsUnimodular d.N) : d.N ≤ Lsh d := fun _ hx =>
  mem_dual.2 fun _ hy => herm_mem_one hd (Submodule.mem_inf.1 hy).1 hx

/-- `m·Lsh(d) ⊆ N` for an integer `m` in every `P ∈ ST`: `m·N ⊆ kerLat d`. -/
theorem smul_Lsh_mem {d : Deco E n ST SG} (hd : IsUnimodular d.N) {m : ℤ} (hm : ∀ P ∈ ST, (m : 𝓞 E) ∈ P.asIdeal)
    {x : Fin n → E} (hx : x ∈ Lsh d) : (m : E) • x ∈ d.N := by
  rw [← show dual d.N = d.N from hd]
  refine mem_dual.2 fun y hy => ?_
  have hmy : (m : E) • y ∈ kerLat d := by
    refine Submodule.mem_inf.2 ⟨int_smul_mem hy m, Submodule.mem_iInf _ |>.2 fun P => ?_⟩
    refine ⟨(m : 𝓞 E) • ⟨y, hy⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 (hm P P.2), zero_mul]
    · simp [Int.cast_smul_eq_zsmul]
  have := mem_dual.1 hx _ hmy
  rwa [herm_smul_left, map_intCast, ← herm_smul_right] at this

/-- **The attached lattice of a good point** lies between `a·O_E^n` and `b⁻¹·O_E^n`. -/
theorem exists_sand_Lsh {d : Deco E n ST SG} (hd : IsUnimodular d.N) : ∃ a b : ℤ, Sand (Lsh d) a b := by
  obtain ⟨a, ha⟩ := exists_sand_of_unimodular hd
  obtain ⟨m, hm0, hm⟩ := exists_int_mem_all ST
  refine ⟨a, a * m, ha.a_ne, mul_ne_zero ha.a_ne hm0, fun i => le_Lsh hd (ha.single_mem i), fun x hx i => ?_⟩
  have := ha.int _ (smul_Lsh_mem hd hm hx) i
  simpa [mul_assoc] using this

end Sand


/-! ## Local bases of `O_{L,w}·σ(N)` -/

section Local

/-- `O_{L,w}` is a principal ideal ring: it is the localisation of `O_L` at `w`, local and Dedekind. -/
instance (w : HeightOneSpectrum (𝓞 L)) : IsPrincipalIdealRing (Ow w) := by
  have h : IsPrincipalIdealRing (HeightOneSpectrum.valuationSubringAtPrime L w) := inferInstance
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h
  exact h

/-- The `O_{L,w}`-span of `σ(N)`. -/
abbrev Nw (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) (N : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (Ow w) (Fin n → L) :=
  Submodule.span (Ow w) ((fun v i => σ (v i)) '' (N : Set (Fin n → E)))

/-- The `O_{L,w}`-span of `a·O_L^n`. -/
abbrev Sw (w : HeightOneSpectrum (𝓞 L)) (a : ℤ) : Submodule (Ow w) (Fin n → L) :=
  Submodule.span (Ow w) (Set.range fun j : Fin n => (a : L) • (Pi.single j 1 : Fin n → L))

variable {w : HeightOneSpectrum (𝓞 L)} {σ : E →+* L} {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ}

omit [NumberField E] [IsCMField E] in
/-- `a·eⱼ ∈ N_w`, as `a·eⱼ ∈ N`. -/
theorem single_mem_Nw (h : Sand N a b) (j : Fin n) : (a : L) • (Pi.single j 1 : Fin n → L) ∈ Nw w σ N := by
  refine Submodule.subset_span ⟨_, h.single_mem j, ?_⟩
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

omit [NumberField E] [IsCMField E] in
/-- `ab·N_w ⊆ a·O_{L,w}^n`: for `x ∈ N`, `ab·σ(x) = Σⱼ σ(b·xⱼ)·a·eⱼ` with `b·xⱼ ∈ O_E`. -/
theorem smul_mem_Sw (h : Sand N a b) {y : Fin n → L} (hy : y ∈ Nw w σ N) :
    ((a * b : ℤ) : L) • y ∈ Sw (n := n) w a := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    choose r hr using fun i => Submodule.mem_one.1 (h.int x hx i)
    have : ((a * b : ℤ) : L) • (fun i => σ (x i)) =
        ∑ j, (⟨σ (r j), map_mem_Ow w σ (r j)⟩ : Ow w) • ((a : L) • (Pi.single j 1 : Fin n → L)) := by
      funext i
      simp only [Pi.smul_apply, Finset.sum_apply, Subring.smul_def, smul_eq_mul, Pi.single_apply, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      have := congrArg σ (hr i)
      rw [map_mul, map_intCast] at this
      rw [show σ (algebraMap (𝓞 E) E (r i)) = σ (r i) from rfl] at this
      rw [this]
      push_cast
      ring
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

omit [NumberField E] [IsCMField E] in
/-- For `C` whose columns span `N_w`: `a·1 = C·U` with `U` integral at `w`. -/
theorem exists_U (h : Sand N a b) {C : Matrix (Fin n) (Fin n) L}
    (hC : Submodule.span (Ow w) (Set.range fun j i => C i j) = Nw w σ N) :
    ∃ U : Matrix (Fin n) (Fin n) L, (∀ i j, U i j ∈ Ow w) ∧ (a : L) • (1 : Matrix (Fin n) (Fin n) L) = C * U := by
  have hj : ∀ j, ∃ c : Fin n → Ow w, ∑ k, c k • (fun i => C i k) = (a : L) • (Pi.single j 1 : Fin n → L) :=
    fun j => (Submodule.mem_span_range_iff_exists_fun (Ow w)).1 (hC ▸ single_mem_Nw h j)
  choose c hc using hj
  refine ⟨Matrix.of fun k j => (c j k : L), fun k j => (c j k).2, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_apply] at this
  simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul]
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

omit [NumberField E] [IsCMField E] in
/-- For `C` whose columns lie in `N_w`: `b·C` is integral at `w`. -/
theorem smul_integral (h : Sand N a b) {C : Matrix (Fin n) (Fin n) L}
    (hC : ∀ j, (fun i => C i j) ∈ Nw w σ N) (i j : Fin n) : (b : L) * C i j ∈ Ow w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Ow w)).1 (smul_mem_Sw h (hC j))
  have := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
  have ha : (a : L) ≠ 0 := Int.cast_ne_zero.2 h.a_ne
  have : (b : L) * C i j = c i := by
    apply mul_left_cancel₀ ha
    rw [mul_comm (a : L) (c i : L), this]
    push_cast
    ring
  rw [this]
  exact (c i).2

omit [NumberField E] [IsCMField E] in
/-- **Local bases exist** at every `w`: `N_w` lies in the free module on `b⁻¹eⱼ`, so it is free over the PID
`O_{L,w}` (`Submodule.basisOfPidOfLESpan`), on at most `n` vectors; padded with zeros they are the columns of `C`, and
`det C ≠ 0` as `a·1 = C·U` (`exists_U`). -/
theorem exists_localBasis (h : Sand N a b) : ∃ C, IsLocalBasis w σ N C := by
  classical
  have hb : (b : L) ≠ 0 := Int.cast_ne_zero.2 h.b_ne
  have ha : (a : L) ≠ 0 := Int.cast_ne_zero.2 h.a_ne
  set v : Fin n → (Fin n → L) := fun j => ((b : L))⁻¹ • Pi.single j 1
  have hv : LinearIndependent (Ow w) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrFun hc i
    simp only [v, Finset.sum_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply] at this
    exact Subtype.ext (by simpa [hb] using this)
  have hle : Nw w σ N ≤ Submodule.span (Ow w) (Set.range v) := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Ow w)).1 (smul_mem_Sw h hy)
    refine (Submodule.mem_span_range_iff_exists_fun (Ow w)).2 ⟨c, ?_⟩
    funext i
    have := congrFun hc i
    simp only [v, Finset.sum_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this ⊢
    have h2 : (c i : L) = b * y i := by
      apply mul_left_cancel₀ ha
      rw [mul_comm (a : L) (c i : L), this]
      push_cast
      ring
    rw [h2]
    field_simp
  obtain ⟨m, bN⟩ := Submodule.basisOfPidOfLESpan hv hle
  have hm : m ≤ n := by
    have hli : LinearIndependent (Ow w) (Submodule.inclusion hle ∘ bN) :=
      bN.linearIndependent.map' _ (Submodule.ker_inclusion _ _ hle)
    have := Module.Finite.of_basis (Module.Basis.span hv)
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis (Module.Basis.span hv), Fintype.card_fin] at this
  set cols : Fin n → (Fin n → L) := fun j => if hj : (j : ℕ) < m then (bN ⟨j, hj⟩ : Fin n → L) else 0
  set C : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => cols j i
  have hspan : Submodule.span (Ow w) (Set.range fun j i => C i j) = Nw w σ N := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : (j : ℕ) < m
      · simp [C, cols, hj]
      · have : (fun i => C i j) = 0 := by funext i; simp [C, cols, hj]
        show (fun i => C i j) ∈ Nw w σ N
        rw [this]
        exact zero_mem _
    · intro y hy
      have h1 : (⟨y, hy⟩ : Nw w σ N) ∈ Submodule.span (Ow w) (Set.range bN) := by
        rw [bN.span_eq]; trivial
      have h2 := Submodule.mem_map_of_mem (f := (Nw w σ N).subtype) h1
      rw [Submodule.map_span, ← Set.range_comp] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨k, rfl⟩
      refine ⟨⟨k, by omega⟩, ?_⟩
      funext i
      simp [C, cols, k.isLt]
  obtain ⟨U, -, hU⟩ := exists_U h hspan
  refine ⟨C, fun h0 => ?_, hspan.symm⟩
  have := congrArg Matrix.det hU
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  exact pow_ne_zero _ ha this

omit [NumberField E] [IsCMField E] in
/-- **At the good places** (`a·b` a unit at `w`), `a·1` is a local basis. -/
theorem isLocalBasis_smul_one (h : Sand N a b) (hw : ((a * b : ℤ) : L)⁻¹ ∈ Ow w) :
    IsLocalBasis w σ N ((a : L) • 1) := by
  have ha : (a : L) ≠ 0 := Int.cast_ne_zero.2 h.a_ne
  have hab : ((a * b : ℤ) : L) ≠ 0 := Int.cast_ne_zero.2 (mul_ne_zero h.a_ne h.b_ne)
  refine ⟨by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact pow_ne_zero _ ha, ?_⟩
  have hcols : (fun j i => ((a : L) • (1 : Matrix (Fin n) (Fin n) L)) i j) =
      fun j => (a : L) • (Pi.single j 1 : Fin n → L) := by
    funext j i
    simp [Matrix.one_apply, Pi.single_apply]
  rw [hcols]
  apply le_antisymm
  · intro y hy
    have h1 := smul_mem_Sw h hy
    have : y = (⟨_, hw⟩ : Ow w) • (((a * b : ℤ) : L) • y) := by
      rw [Subring.smul_def, smul_smul]
      simp only [inv_mul_cancel₀ hab, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ h1
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact single_mem_Nw h j

end Local


/-! ## The integral forms span -/

section Span

/-- An integral element of `L` is integral at every `w`. -/
theorem mem_Ow_of_mem_one {x : L} (hx : x ∈ (1 : Submodule (𝓞 L) L)) (w : HeightOneSpectrum (𝓞 L)) :
    x ∈ Ow w := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact w.valuation_le_one r

/-- A nonzero integer clears the denominators of finitely many elements of `L`, and so does each of its
multiples. -/
theorem exists_int_mul_mem_one {ι : Type*} [Fintype ι] (x : ι → L) :
    ∃ z : ℤ, z ≠ 0 ∧ ∀ z' : ℤ, z ∣ z' → ∀ i, (z' : L) * x i ∈ (1 : Submodule (𝓞 L) L) := by
  classical
  choose d hd hdx using fun i => exists_int_mul_mem (E := L) (x i)
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.2 fun i _ => hd i, fun z' hz' i => ?_⟩
  obtain ⟨k, rfl⟩ := hz'
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hdx i)
  refine Submodule.mem_one.2 ⟨((k * ∏ j ∈ Finset.univ.erase i, d j : ℤ) : 𝓞 L) * r, ?_⟩
  rw [map_mul, map_intCast, hr, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  push_cast
  ring

/-- An integer not in `w` is a unit at `w`. -/
theorem inv_mem_Ow {w : HeightOneSpectrum (𝓞 L)} {M : ℤ} (hM : (M : 𝓞 L) ∉ w.asIdeal) : ((M : L))⁻¹ ∈ Ow w := by
  have h1 : w.valuation L (M : L) = 1 := by
    have e : (M : L) = algebraMap (𝓞 L) L (M : 𝓞 L) := (map_intCast _ M).symm
    rw [e, w.valuation_of_algebraMap, w.intValuation_eq_one_iff_mem_primeCompl]
    exact hM
  show w.valuation L (M : L)⁻¹ ≤ 1
  rw [map_inv₀, h1, inv_one]

/-- The places containing a nonzero integer are finitely many. -/
theorem finite_bad {M : ℤ} (hM : M ≠ 0) : {w : HeightOneSpectrum (𝓞 L) | (M : 𝓞 L) ∈ w.asIdeal}.Finite := by
  have hI : Ideal.span {(M : 𝓞 L)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 hw

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` is stable under integers. -/
theorem int_smul_mem_DeltaN {N : Submodule (𝓞 E) (Fin n → E)} {P : Pol Φ n L} (hP : P ∈ DeltaN τ lam N)
    (z : ℤ) : (z : L) • P ∈ DeltaN τ lam N := by
  refine ⟨Submodule.smul_mem _ _ hP.1, fun w => ?_⟩
  obtain ⟨g, hg, hD⟩ := hP.2 w
  refine ⟨g, hg, ?_⟩
  rw [twist_smul]
  refine ⟨Submodule.smul_mem _ _ hD.1, fun rows => ?_⟩
  rw [fock_smul_left, mul_div_assoc]
  exact (Ow w).mul_mem (intCast_mem _ z) (hD.2 rows)

omit [NumberField E] [IsCMField E] in
/-- **Every vector of `VV(λ)` has an integer multiple in `Δ_N`**, for `N` between `a·O_E^n` and `b⁻¹O_E^n`: at the
finitely many places dividing `ab`, in a local basis (`exists_localBasis`); elsewhere in the basis `a·1`
(`isLocalBasis_smul_one`); in each, a nonzero integer clears the finitely many Fock pairings. -/
theorem exists_int_smul_mem_DeltaN {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ} (h : Sand N a b)
    {P : Pol Φ n L} (hP : P ∈ VV (n := n) (L := L) lam) : ∃ z : ℤ, z ≠ 0 ∧ (z : L) • P ∈ DeltaN τ lam N := by
  classical
  set ν : Φ → Fin n → ℕ := fun σ => natW (lam σ)
  set κ := fockWith (RingHom.id L) (hw L ν) (hw L ν)
  -- the pairings of a twist of `P`
  let pr : (Φ → Matrix (Fin n) (Fin n) L) → _ → L := fun g rows =>
    fockWith (RingHom.id L) (twist lam g P) (bidet L ν rows) / κ
  have hM : a * b ≠ 0 := mul_ne_zero h.a_ne h.b_ne
  set Bad := (finite_bad (L := L) hM).toFinset
  choose g hg using fun (w : HeightOneSpectrum (𝓞 L)) (σ : Φ) => exists_localBasis (w := w) (σ := τ σ) h
  choose zw hzw0 hzw using fun w : HeightOneSpectrum (𝓞 L) => exists_int_mul_mem_one (pr (fun σ => g w σ))
  obtain ⟨z₀, hz₀0, hz₀⟩ := exists_int_mul_mem_one (pr fun _ => (a : L) • 1)
  refine ⟨z₀ * ∏ w ∈ Bad, zw w, mul_ne_zero hz₀0 (Finset.prod_ne_zero_iff.2 fun w _ => hzw0 w), ?_⟩
  refine ⟨Submodule.smul_mem _ _ hP, fun w => ?_⟩
  have key : ∀ g' : Φ → Matrix (Fin n) (Fin n) L, (∀ rows, ((z₀ * ∏ w ∈ Bad, zw w : ℤ) : L) * pr g' rows ∈ Ow w) →
      twist lam g' (((z₀ * ∏ w ∈ Bad, zw w : ℤ) : L) • P) ∈ Delta (Ow w) ν := fun g' hg' => by
    rw [twist_smul]
    refine ⟨Submodule.smul_mem _ _ (twist_mem_nabla lam g' hP), fun rows => ?_⟩
    rw [fock_smul_left, mul_div_assoc]
    exact hg' rows
  by_cases hw : w ∈ Bad
  · refine ⟨fun σ => g w σ, hg w, key _ fun rows => mem_Ow_of_mem_one (hzw w _ ?_ rows) w⟩
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hw) _
  · have hw' : ((a * b : ℤ) : L)⁻¹ ∈ Ow w := inv_mem_Ow (by simpa [Bad] using hw)
    exact ⟨fun _ => (a : L) • 1, fun σ => isLocalBasis_smul_one h hw',
      key _ fun rows => mem_Ow_of_mem_one (hz₀ _ (dvd_mul_right _ _) rows) w⟩

variable (ST) (χ : Λ →* L)

/-- **Every form has a nonzero integer multiple that is integral** (in `M`): at each of the finitely many classes,
`exists_int_smul_mem_DeltaN`, the attached lattice lying between `a·O_E^n` and `b⁻¹O_E^n` (`exists_sand_Lsh`). -/
theorem exists_int_smul_mem_Mint {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) :
    ∃ z : ℤ, z ≠ 0 ∧ (z : L) • F ∈ Mint ST τ χ lam := by
  classical
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  have hsand : ∀ c : DCl E n ST Λ, ∃ a b : ℤ, Sand (Lsh c.rep) a b := fun c =>
    exists_sand_Lsh (show (c.out : Deco E n ST SG).Good from c.out.2).unimod
  choose a b hab using hsand
  choose z hz0 hz using fun c => exists_int_smul_mem_DeltaN τ lam (hab c) (hF.1 c.out)
  refine ⟨∏ c, z c, Finset.prod_ne_zero_iff.2 fun c _ => hz0 c, Submodule.smul_mem _ _ hF, fun c => ?_⟩
  rw [Pi.smul_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Int.cast_mul, mul_comm, mul_smul]
  exact int_smul_mem_DeltaN τ lam (hz c) _

/-- **The integral forms span** (`IsLattice.span_eq_top` for `Mlat`): every form of the cut is a multiple of an
integral one (`exists_int_smul_mem_Mint`). -/
theorem span_Mlat [FiniteDimensional L (Vω ST τ χ lam)] :
    Submodule.span L (Mlat ST τ χ lam : Set (Idx ST τ χ lam → L)) = ⊤ := by
  set S := {F : Vω ST τ χ lam | (F : Fn ST Λ Φ L) ∈ Mω ST τ χ lam}
  have hS : Submodule.span L S = ⊤ := by
    refine eq_top_iff.2 fun F _ => ?_
    obtain ⟨z, hz0, hz⟩ := exists_int_smul_mem_Mint ST τ lam χ (Submodule.mem_inf.1 F.2).1
    have hzF : (z : L) • F ∈ S := ⟨hz, ((z : L) • F).2⟩
    have : F = ((z : L))⁻¹ • ((z : L) • F) := by
      rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hz0), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hzF)
  rw [Mlat, Submodule.span_span_of_tower,
    show (coords ST τ χ lam '' S) = (coords ST τ χ lam).toLinearMap '' S from rfl, Submodule.span_image, hS,
    Submodule.map_top, LinearEquiv.range]

end Span


/-! ## The integral forms are finitely generated -/

section FG

omit [NumberField L] in
/-- The determinant of a matrix with entries in a subring lies in it. -/
theorem det_mem {A : Subring L} {U : Matrix (Fin n) (Fin n) L} (hU : ∀ i j, U i j ∈ A) : U.det ∈ A := by
  rw [Matrix.det_apply]
  exact A.sum_mem fun σ _ => by rw [Units.smul_def]; exact zsmul_mem (A.prod_mem fun i _ => hU _ _) _

/-- For integral `U`, `V` with `VU = M·1`, `(Mⁿ)^{|s|}·det(U)^s` is integral: `det(U)⁻¹ = det(V)/Mⁿ`. -/
theorem det_zpow_mem {A : Subring L} {U V : Matrix (Fin n) (Fin n) L} (hU : ∀ i j, U i j ∈ A)
    (hV : ∀ i j, V i j ∈ A) {M : ℤ} (hM : M ≠ 0) (hVU : V * U = (M : L) • 1) (s : ℤ) :
    ((M : L) ^ n) ^ s.natAbs * U.det ^ s ∈ A := by
  have hdet : V.det * U.det = (M : L) ^ n := by
    rw [← Matrix.det_mul, hVU, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hU0 : U.det ≠ 0 := fun h => by
    rw [h, mul_zero] at hdet
    exact pow_ne_zero n (Int.cast_ne_zero.2 hM) hdet.symm
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg s
  · rw [Int.natAbs_natCast, zpow_natCast]
    exact A.mul_mem (A.pow_mem (A.pow_mem (intCast_mem A M) _) _) (A.pow_mem (det_mem hU) _)
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← hdet, mul_pow, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hU0), mul_one]
    exact A.pow_mem (det_mem hV) _

/-- The scalar `∏_σ (Mⁿ)^{|λ_{σ,n−1}|}` that clears the determinant twists. -/
def kden (lam : Φ → Fin n → ℤ) (M : ℤ) : ℤ := ∏ σ, (M ^ n) ^ (detShift (lam σ)).natAbs

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

omit [NumberField E] [IsCMField E] in
/-- **The integral bound at one place**: for `P ∈ Δ_N`, with `N` between `a·O_E^n` and `b⁻¹O_E^n`, the twist of `P` by
`a·1` has `kden·D₀`-integral coefficients at `w`. In a local basis `C` with `C·U = a·1`, it is the twist by `U` of
`G = twist_C P ∈ Δ_{O_{L,w}}`: `D₀G` is integral (`exists_delta_den`), `U` is integral, and `det U` is controlled by
`V = b·C` (`det_zpow_mem`). -/
theorem coeff_twist_mem {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ} (h : Sand N a b) {D₀ : ℕ}
    (hD₀ : ∀ (A : Subring L) (G : Pol Φ n L), G ∈ Delta A (fun σ => natW (lam σ)) → ∀ d, (D₀ : L) * G.coeff d ∈ A)
    {P : Pol Φ n L} (hP : P ∈ DeltaN τ lam N) (w : HeightOneSpectrum (𝓞 L)) (d : Φ × Fin n × Fin n →₀ ℕ) :
    ((kden lam (a * b) * D₀ : ℤ) : L) * (twist lam (fun _ => (a : L) • 1) P).coeff d ∈ Ow w := by
  obtain ⟨g, hg, hG⟩ := hP.2 w
  choose U hUi hU using fun σ => exists_U h (hg σ).2.symm
  have hcol : ∀ σ j, (fun i => g σ i j) ∈ Nw w (τ σ) N := fun σ j => by
    rw [Nw, (hg σ).2]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hVi : ∀ σ i j, ((b : L) • g σ) i j ∈ Ow w := fun σ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact smul_integral h (hcol σ) i j
  have hVU : ∀ σ, ((b : L) • g σ) * U σ = ((a * b : ℤ) : L) • 1 := fun σ => by
    rw [Matrix.smul_mul, ← hU σ, smul_smul]
    congr 1
    push_cast
    ring
  have htw : twist lam (fun _ => (a : L) • 1) P = twist lam U (twist lam g P) := by
    rw [twist_twist]
    congr 1
    funext σ
    exact hU σ
  rw [htw]
  set G := twist lam g P
  simp only [twist, coeff_C_mul]
  have h1 : ((kden lam (a * b) : ℤ) : L) * ∏ σ, (U σ).det ^ detShift (lam σ) ∈ Ow w := by
    rw [kden, Int.cast_prod, ← Finset.prod_mul_distrib]
    exact Subring.prod_mem _ fun σ _ => by
      rw [Int.cast_pow, Int.cast_pow]
      exact det_zpow_mem (hUi σ) (hVi σ) (mul_ne_zero h.a_ne h.b_ne) (hVU σ) _
  have h2 : (D₀ : L) * (lsub U G).coeff d ∈ Ow w := by
    have : (D₀ : L) * (lsub U G).coeff d = (lsub U (C (D₀ : L) * G)).coeff d := by
      rw [map_mul, lsub_C, coeff_C_mul]
    rw [this]
    exact lsub_coeff_mem (fun σ i j => hUi σ i j) (fun d' => by rw [coeff_C_mul]; exact hD₀ _ _ hG d') d
  have := (Ow w).mul_mem h1 h2
  convert this using 1
  push_cast
  ring

/-- An element of `L` integral at every finite place lies in `O_L`. -/
theorem mem_one_of_forall_Ow {x : L} (h : ∀ w : HeightOneSpectrum (𝓞 L), x ∈ Ow w) :
    x ∈ (1 : Submodule (𝓞 L) L) := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L x h
  exact Submodule.mem_one.2 ⟨r, hr⟩

omit [DecidableEq Φ] [NumberField L] in
/-- A twist by a nonzero scalar matrix is injective: the twist by its inverse undoes it. -/
theorem twist_smul_one_injective {a : L} (ha : a ≠ 0) :
    Function.Injective (twist lam (fun _ : Φ => a • (1 : Matrix (Fin n) (Fin n) L))) := by
  intro P Q h
  have h2 := congrArg (twist lam (fun _ : Φ => a⁻¹ • (1 : Matrix (Fin n) (Fin n) L))) h
  have e : (fun _ : Φ => a • (1 : Matrix (Fin n) (Fin n) L) * a⁻¹ • 1) = fun _ => 1 := by
    funext
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha, one_smul, Matrix.one_mul]
  rwa [twist_twist, twist_twist, e, twist_one, twist_one] at h2

variable (L) in
/-- The monomials of the bideterminants of shape `ν`. -/
def bidetMonos (ν : Φ → Fin n → ℕ) : Finset (Φ × Fin n × Fin n →₀ ℕ) :=
  Finset.univ.biUnion fun rows => (bidet L ν rows).support

omit [NumberField L] in
/-- The monomials of `∇_L(ν)` are those of the bideterminants, which span it (`span_bidet`). -/
theorem mem_bidetMonos [CharZero L] {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) {Q : Pol Φ n L}
    (hQ : Q ∈ nabla L ν) {d : Φ × Fin n × Fin n →₀ ℕ} (hd : Q.coeff d ≠ 0) : d ∈ bidetMonos L ν := by
  have : nabla L ν ≤ restrictSupport L (bidetMonos L ν : Set (Φ × Fin n × Fin n →₀ ℕ)) := by
    rw [← span_bidet hν, Submodule.span_le]
    rintro _ ⟨rows, rfl⟩
    rw [SetLike.mem_coe, mem_restrictSupport_iff]
    intro d hd
    exact Finset.mem_biUnion.2 ⟨rows, Finset.mem_univ _, hd⟩
  exact (mem_restrictSupport_iff L).1 (this hQ) (mem_support_iff.2 hd)

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- A family of polynomials with coefficients in `O_L` and monomials in `T` lies in the `O_L`-span of the
`Pi.single c (monomial d 1)`. -/
theorem mem_span_single_monomial {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset (Φ × Fin n × Fin n →₀ ℕ)}
    {x : ι → Pol Φ n L} (hint : ∀ c d, (x c).coeff d ∈ (1 : Submodule (𝓞 L) L))
    (hsupp : ∀ c d, (x c).coeff d ≠ 0 → d ∈ T) :
    x ∈ Submodule.span (𝓞 L)
      (Set.range fun p : ι × T => Pi.single p.1 (monomial (p.2 : Φ × Fin n × Fin n →₀ ℕ) (1 : L))) := by
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun c _ => ?_
  have : (Pi.single c (x c) : ι → Pol Φ n L) =
      ∑ d ∈ (x c).support, (Pi.single c (monomial d ((x c).coeff d)) : ι → Pol Φ n L) := by
    conv_lhs => rw [← support_sum_monomial_coeff (x c)]
    exact map_sum (AddMonoidHom.single (fun _ : ι => Pol Φ n L) c) _ _
  rw [this]
  refine Submodule.sum_mem _ fun d hd => ?_
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hint c d)
  have hdT : d ∈ T := hsupp c d (mem_support_iff.1 hd)
  have : (Pi.single c (monomial d ((x c).coeff d)) : ι → Pol Φ n L) =
      r • (Pi.single c (monomial d (1 : L)) : ι → Pol Φ n L) := by
    funext c'
    rw [Pi.smul_apply]
    by_cases hc : c' = c
    · subst hc
      rw [Pi.single_eq_same, Pi.single_eq_same, Algebra.smul_def,
        show (algebraMap (𝓞 L) (Pol Φ n L)) r = C (algebraMap (𝓞 L) L r) from rfl, C_mul_monomial, mul_one, hr]
    · rw [Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc]
      exact (smul_zero _).symm
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c, ⟨d, hdT⟩), rfl⟩)

variable (ST) (χ : Λ →* L)

/-- **The integral forms are finitely generated** (`IsLattice.fg` for `Mlat`). The `L`-linear injection
`Ψ(F) = (k_c·twist_{a_c·1} F(rep c))_c` (`k_c = kden·D₀`) maps every integral form to a family of polynomials with
coefficients in `O_L` (integral at every place, `coeff_twist_mem`) and monomials among those of the bideterminants;
these lie in a finitely generated `O_L`-module, and `O_L` is noetherian. -/
theorem fg_Mlat [FiniteDimensional L (Vω ST τ χ lam)] (hlam : ∀ ρ, Antitone (lam ρ)) : (Mlat ST τ χ lam).FG := by
  classical
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  set ν : Φ → Fin n → ℕ := fun σ => natW (lam σ)
  have hν : ∀ σ, Antitone (ν σ) := fun σ => natW_antitone (hlam σ)
  obtain ⟨D₀, hD₀0, hD₀⟩ := exists_delta_den (L := L) hν
  choose a b hab using fun c : DCl E n ST Λ =>
    exists_sand_Lsh (show (c.out : Deco E n ST SG).Good from c.out.2).unimod
  set k : DCl E n ST Λ → ℤ := fun c => kden lam (a c * b c) * D₀
  have hk : ∀ c, (k c : L) ≠ 0 := fun c => by
    refine Int.cast_ne_zero.2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun σ _ => ?_) (by exact_mod_cast hD₀0))
    exact pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero (hab c).a_ne (hab c).b_ne))
  set Ψ : (Idx ST τ χ lam → L) →ₗ[L] (DCl E n ST Λ → Pol Φ n L) :=
    { toFun := fun v c => (k c : L) • twist lam (fun _ => (a c : L) • 1)
        (((coords ST τ χ lam).symm v : Fn ST Λ Φ L) c.out)
      map_add' := fun v v' => by
        funext c
        simp only [map_add, Submodule.coe_add, Pi.add_apply, twist_add, smul_add]
      map_smul' := fun r v => by
        funext c
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, twist_smul, RingHom.id_apply, smul_comm r] }
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ∀ c : DCl E n ST Λ, ((coords ST τ χ lam).symm v : Fn ST Λ Φ L) c.out = 0 := fun c => by
      have := congrFun hv c
      simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, smul_eq_zero, hk c, false_or] at this
      refine twist_smul_one_injective lam (Int.cast_ne_zero.2 (hab c).a_ne) ?_
      rw [this]
      simp [twist]
    have : (coords ST τ χ lam).symm v = 0 :=
      Subtype.ext (eq_zero_of_out ST τ χ lam (Submodule.mem_inf.1 ((coords ST τ χ lam).symm v).2).1 h0)
    exact (LinearEquiv.map_eq_zero_iff _).1 this
  refine Submodule.fg_of_fg_map_injective (Ψ.restrictScalars (𝓞 L)) hΨ ?_
  refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun p : DCl E n ST Λ × bidetMonos L ν =>
    Pi.single p.1 (monomial (p.2 : Φ × Fin n × Fin n →₀ ℕ) (1 : L)))) ?_
  rw [Mlat, Submodule.map_span_le]
  rintro _ ⟨F, hF, rfl⟩
  have hΨF : (Ψ.restrictScalars (𝓞 L)) (coords ST τ χ lam F) =
      fun c => (k c : L) • twist lam (fun _ => (a c : L) • 1) ((F : Fn ST Λ Φ L) c.out) := by
    funext c
    simp only [Ψ, LinearMap.restrictScalars_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply]
  rw [hΨF]
  refine mem_span_single_monomial (fun c d => ?_) (fun c d hd => ?_)
  · rw [coeff_smul, smul_eq_mul]
    refine mem_one_of_forall_Ow fun w => ?_
    have := coeff_twist_mem τ lam (hab c) hD₀ (hF.1.2 c) w d
    simpa [k] using this
  · exact mem_bidetMonos hν (Submodule.smul_mem _ _ (twist_mem_nabla lam _ (hF.1.1.1 c.out))) hd

end FG

/-! ## The piece `FormsLattice` -/

section Main

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- **The integral forms of the cut are a lattice** (C2, second part): finitely generated (`fg_Mlat`) and spanning
(`span_Mlat`). -/
theorem isLattice_Mlat [FiniteDimensional L (Vω ST τ χ lam)] (hlam : ∀ ρ, Antitone (lam ρ)) :
    (Mlat ST τ χ lam).IsLattice L :=
  ⟨fg_Mlat ST τ lam χ hlam, span_Mlat ST τ lam χ⟩

/-- **The piece `FormsLattice`** (C2), with the hypotheses of `SharpInputs.FormsLattice`: the forms are
finite-dimensional (`finiteDimensional_Forms`), the integral forms of the cut a lattice (`isLattice_Mlat`), and the
Gram matrix of the Petersson form positive definite at every complex place (`gram_posDef`). -/
theorem formsLattice (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))
    (Φ : Type) [Fintype Φ] [DecidableEq Φ] (L : Type) [Field L] [NumberField L] (τ : Φ → (E →+* L))
    (χ : Λ →* L) (lam : Φ → Fin n → ℤ) (hlam : ∀ ρ, Antitone (lam ρ)) :
    FiniteDimensional L (Forms ST τ χ lam) ∧
      ∃ _ : FiniteDimensional L (Vω ST τ χ lam), (Mlat ST τ χ lam).IsLattice L ∧
        ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef := by
  have := finiteDimensional_Vω ST τ χ lam hlam
  exact ⟨finiteDimensional_Forms ST τ χ lam hlam, this, isLattice_Mlat ST τ χ lam hlam,
    fun v => gram_posDef ST τ χ lam v.1.embedding⟩

/-- **The integral forms in any subspace of the cut are a lattice**: for a subspace `X` of the forms and an
identification `e : V ≃ X ⊓ V_ω`, the `O_L`-span of the `φ` with `e φ` integral is finitely generated (it embeds in
`Mlat` by the coordinates of `V_ω`, and `O_L` is noetherian) and spans `V` (every form has a nonzero integral integer
multiple, `exists_int_smul_mem_Mint`). -/
theorem isLattice_span_Mω [FiniteDimensional L (Vω ST τ χ lam)] (hlam : ∀ ρ, Antitone (lam ρ))
    {X : Submodule L (Fn ST Λ Φ L)} {V : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] (e : V ≃ₗ[L] ↥(X ⊓ Vω ST τ χ lam)) :
    (Submodule.span (𝓞 L) {φ : V | (e φ : Fn ST Λ Φ L) ∈ Mω ST τ χ lam}).IsLattice L := by
  let k : V →ₗ[L] (Idx ST τ χ lam → L) :=
    (coords ST τ χ lam).toLinearMap ∘ₗ Submodule.inclusion inf_le_right ∘ₗ e.toLinearMap
  have hk : Function.Injective k :=
    (coords ST τ χ lam).injective.comp ((Submodule.inclusion_injective (inf_le_right : X ⊓ Vω ST τ χ lam ≤ _)).comp
      e.injective)
  refine ⟨Submodule.fg_of_fg_map_injective (k.restrictScalars (𝓞 L)) hk
    (Submodule.FG.of_le (isLattice_Mlat ST τ χ lam hlam).fg ?_), eq_top_iff.2 fun φ _ => ?_⟩
  · rw [Submodule.map_span_le]
    exact fun φ hφ => Submodule.subset_span ⟨⟨_, (Submodule.mem_inf.1 (e φ).2).2⟩, hφ, rfl⟩
  · obtain ⟨z, hz0, hz⟩ := exists_int_smul_mem_Mint ST τ lam χ
      (Submodule.mem_inf.1 (Submodule.mem_inf.1 (e φ).2).2).1
    have hzφ : (z : L) • φ ∈ Submodule.span (𝓞 L) {φ : V | (e φ : Fn ST Λ Φ L) ∈ Mω ST τ χ lam} := by
      refine Submodule.subset_span ⟨?_, ?_⟩
      · rw [map_smul]
        exact hz
      · rw [map_smul]
        exact ((z : L) • e φ).2.2
    have : φ = ((z : L))⁻¹ • ((z : L) • φ) := by
      rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hz0), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hzφ)

end Main

end

end HermForms
