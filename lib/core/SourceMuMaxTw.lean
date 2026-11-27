import TwistSlope
import TwistPair
import FormSlopeExact

/-!
# The maximal slope of the source of the forms

The twin of `HermForms.muArch_source_ge`: for any coordinates `c : V_ω ≃ L^ι` of the cut, the source `X` (the
`O_L`-span of the integral forms, with the Petersson Gram metrics) has every member of its slope lattice of archive
slope at most `2n·negW λ·log|m|`, for any nonzero integer `m` in every place of `ST`
(`HermForms.slopeLe_source`). It is Theorem A (`KLattice.slopeLe_of_twPair`) fed by Theorem B
(`HermForms.petTw_mem_of_Mint`).

* **The coefficient coordinates.** With `R = Cl × S`, `S` a finite set of monomials containing the supports of the
  values of the basis forms at the class representatives, the coefficient matrix
  `E_{(cl,d), i} = coeff_d((c⁻¹e_i)(rep cl))` and the weights `w_{(cl,d)} = d!/κ` (the masses are `1`, the
  stabilisers being trivial, `free_of_uniAt`), the Petersson Gram matrix at every place is `σ_v(E)ᴴ W σ_v(E)`
  (`fockWith_eq_sum`, `fockWith_hw_C`).
* **The twisted pairing** of these coordinates is the twisted Petersson form,
  `h_c(x, y) = H_c(c⁻¹x, c⁻¹y)` (`petTw`), for `c` complex conjugation at one place (`exists_conj_ringEquiv`), which
  is complex conjugation on every `τ_ρ(E)` (`conj_comp_of_isConj`).
* **Integrality on the span** (`KLattice.twPair_mem_one_span`). `h_c` is `c`-semilinear in `x` and linear in `y`,
  and `c(O_L) = O_L`, so integrality passes from the integral forms (Theorem B, with `D = |m|^{2n·negW λ}`, as
  `m^{2k} = |m|^{2k}`) to their `O_L`-span.
-/

namespace KLattice

open NumberField Matrix

variable {K : Type} [Field K] {ι R : Type} [Fintype R]

/-- The twisted pairing is additive in its first argument. -/
theorem twPair_add_left (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) [Fintype ι] (x x' y : ι → K) :
    twPair c w E (x + x') y = twPair c w E x y + twPair c w E x' y := by
  simp only [twPair, mulVec_add, Pi.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

/-- The twisted pairing is additive in its second argument. -/
theorem twPair_add_right (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) [Fintype ι] (x y y' : ι → K) :
    twPair c w E x (y + y') = twPair c w E x y + twPair c w E x y' := by
  simp only [twPair, mulVec_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The twisted pairing is `c`-semilinear in its first argument: `h_c(a·x, y) = c(a)·h_c(x, y)`. -/
theorem twPair_smul_left (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) [Fintype ι] (a : K) (x y : ι → K) :
    twPair c w E (a • x) y = c a * twPair c w E x y := by
  rw [twPair, twPair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- The twisted pairing is linear in its second argument: `h_c(x, a·y) = a·h_c(x, y)`. -/
theorem twPair_smul_right (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) [Fintype ι] (a : K) (x y : ι → K) :
    twPair c w E x (a • y) = a * twPair c w E x y := by
  rw [twPair, twPair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The twisted pairing vanishes when its first argument does. -/
theorem twPair_zero_left (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) [Fintype ι] (y : ι → K) :
    twPair c w E 0 y = 0 := by
  simp [twPair]

/-- The twisted pairing vanishes when its second argument does. -/
theorem twPair_zero_right (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) [Fintype ι] (x : ι → K) :
    twPair c w E x 0 = 0 := by
  simp [twPair]

variable [NumberField K]

omit [NumberField K] in
/-- **Integrality passes to the `O_K`-span** (B5): if `D·h_c(x, y) ∈ O_K` for `x, y` in a set `s`, then for `x, y`
in the `O_K`-span of `s`. `h_c` is `c`-semilinear in `x`, linear in `y`, and `c` maps `O_K` onto itself
(`RingOfIntegers.mapRingEquiv`). -/
theorem twPair_mem_one_span (c : K ≃+* K) (w : R → ℚ) (E : Matrix R ι K) [Fintype ι] (D : K) {s : Set (ι → K)}
    (h : ∀ x ∈ s, ∀ y ∈ s, D * twPair (c : K →+* K) w E x y ∈ (1 : Submodule (𝓞 K) K)) :
    ∀ x ∈ Submodule.span (𝓞 K) s, ∀ y ∈ Submodule.span (𝓞 K) s,
      D * twPair (c : K →+* K) w E x y ∈ (1 : Submodule (𝓞 K) K) := by
  have hy : ∀ x ∈ s, ∀ y ∈ Submodule.span (𝓞 K) s, D * twPair (c : K →+* K) w E x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero =>
      rw [twPair_zero_right, mul_zero]
      exact zero_mem _
    | add y y' _ _ h1 h2 =>
      rw [twPair_add_right, mul_add]
      exact add_mem h1 h2
    | smul k y _ h1 =>
      rw [← algebraMap_smul K k y, twPair_smul_right, mul_left_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ k h1
  intro x hx y hy'
  induction hx using Submodule.span_induction with
  | mem x hx => exact hy x hx y hy'
  | zero =>
    rw [twPair_zero_left, mul_zero]
    exact zero_mem _
  | add x x' _ _ h1 h2 =>
    rw [twPair_add_left, mul_add]
    exact add_mem h1 h2
  | smul k x _ h1 =>
    rw [← algebraMap_smul K k x, twPair_smul_left, mul_left_comm,
      show (c : K →+* K) (algebraMap (𝓞 K) K k) = algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv c k) from rfl,
      ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ h1

end KLattice

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock MvPolynomial Matrix

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
  {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L] [NumberField L]
  (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

omit [DecidableEq Φ] in
/-- The rational factorial `d!` cast to a field of characteristic `0` is the factorial there. -/
theorem ratCast_fact {K : Type} [Field K] [CharZero K] (d : Φ × Fin n × Fin n →₀ ℕ) :
    ((fact d : ℚ) : K) = fact d := by
  simp [fact]

open KLattice in
/-- (SM1) **`μ_max` of the source of the forms** (the twin of `muArch_source_ge`): if the level group is unipotent
at two places of distinct residue characteristics, then for any coordinates `c` of the cut `V_ω`, the source `X` (the
`O_L`-span of the integral forms of the cut in these coordinates, with the Petersson metrics) has every member of its
slope lattice of archive slope at most `2n·negW λ·log|m|`, for any nonzero integer `m` in every place of `ST`.
Theorem A (`slopeLe_of_twPair`) with `R = classes × monomials`, `w = d!/κ`, the coefficient matrix
(`fockWith_eq_sum`), `c` complex conjugation at one place (`exists_conj_ringEquiv`), `D = |m|^{2n·negW λ}`; and
Theorem B (`petTw_mem_of_Mint`) extended to the `O_L`-span (`twPair_mem_one_span`). -/
theorem slopeLe_source [IsTotallyComplex L] [Normal ℚ L] (hlam : ∀ ρ, Antitone (lam ρ)) (w₀ w₁ : SG) {p₀ p₁ : ℕ}
    (hp₀ : p₀.Prime) (hp₁ : p₁.Prime) (hp : p₀ ≠ p₁) (h₀ : (p₀ : 𝓞 E) ∈ w₀.1.asIdeal)
    (h₁ : (p₁ : 𝓞 E) ∈ w₁.1.asIdeal) (hu₀ : UniAt Λ w₀) (hu₁ : UniAt Λ w₁) {m : ℤ} (hm0 : m ≠ 0)
    (hm : ∀ P ∈ ST, (m : 𝓞 E) ∈ P.asIdeal) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Vω ST τ χ lam ≃ₗ[L] (ι → L)) (X : KLattice L ι)
    (hM : X.M = Submodule.span (𝓞 L) (c '' {F | (F : Fn ST Λ Φ L) ∈ Mω ST τ χ lam}))
    (hG : ∀ v i j, X.G v i j = petAt ST lam v.1.embedding (c.symm (Pi.single i 1) : Fn ST Λ Φ L)
      (c.symm (Pi.single j 1) : Fn ST Λ Φ L)) :
    (X.toPlaceLattice.slopeLattice.rescale (-Real.log 2 + Real.log |(discr L : ℝ)| / Module.finrank ℚ L)).SlopeLe
      (2 * n * negW lam * Real.log |(m : ℝ)|) := by
  obtain ⟨hst, -⟩ := free_of_uniAt (ST := ST) w₀ w₁ hp₀ hp₁ hp h₀ h₁ hu₀ hu₁
  obtain ⟨c₀, v₀, hv₀⟩ := exists_conj_ringEquiv (K := L)
  have hc (ρ : Φ) (z : E) : c₀ (τ ρ z) = τ ρ (IsCMField.complexConj E z) := conj_comp_of_isConj c₀ v₀ hv₀ (τ ρ) z
  let _ : Fintype (DCl E n ST Λ) := @Fintype.ofFinite _ (finite_DCl E n ST SG Λ)
  -- the basis forms, and a finite set of monomials containing the supports of their values
  set f : ι → Fn ST Λ Φ L := fun i => (c.symm (Pi.single i 1) : Fn ST Λ Φ L) with hfdef
  have hf (y : ι → L) : ((c.symm y : Vω ST τ χ lam) : Fn ST Λ Φ L) = ∑ i, y i • f i := by
    have hx : y = ∑ a, y a • (Pi.single a 1 : ι → L) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hfdef]
  set S : Finset (Φ × Fin n × Fin n →₀ ℕ) :=
    Finset.univ.biUnion fun p : DCl E n ST Λ × ι => (f p.2 p.1.out).support
  have hSf (i : ι) (cl : DCl E n ST Λ) : (f i cl.out).support ⊆ S :=
    Finset.subset_biUnion_of_mem (fun p : DCl E n ST Λ × ι => (f p.2 p.1.out).support) (Finset.mem_univ (cl, i))
  have hS (y : ι → L) (cl : DCl E n ST Λ) : (((c.symm y : Vω ST τ χ lam) : Fn ST Λ Φ L) cl.out).support ⊆ S := by
    rw [hf, Finset.sum_apply]
    refine (support_sum).trans (Finset.biUnion_subset.2 fun i _ => ?_)
    exact (support_smul).trans (hSf i cl)
  -- the coefficient matrix and the weights
  let w : DCl E n ST Λ × S → ℚ := fun r => fact r.2.1 / kappa lam
  have hw (r : DCl E n ST Λ × S) : 0 < w r :=
    div_pos (Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _)) (kappa_pos lam)
  let Em : Matrix (DCl E n ST Λ × S) ι L := fun r i => (f i r.1.out).coeff r.2.1
  have hEm (y : ι → L) (r : DCl E n ST Λ × S) :
      (Em *ᵥ y) r = (((c.symm y : Vω ST τ χ lam) : Fn ST Λ Φ L) r.1.out).coeff r.2.1 := by
    rw [hf, Finset.sum_apply, coeff_sum, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, coeff_smul, smul_eq_mul, mul_comm]
  -- the metrics: `G_v = σ_v(E)ᴴ W σ_v(E)`
  have hGm (v : HermitianLattice.Pl L) : X.G v =
      (Em.map v.1.embedding)ᴴ * diagonal (fun r => (w r : ℂ)) * Em.map v.1.embedding := by
    ext i j
    rw [hG v i j, mul_diagonal_mul_apply, petAt, classSum, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun cl _ => ?_
    rw [mass_eq_one (hst cl), one_smul, fock, fockWith_hw_C lam,
      fockWith_eq_sum _ ((support_map_subset _ _).trans (hSf j cl)), Finset.sum_div, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply]
    simp only [coeff_map, RCLike.star_def, w, Em, hfdef, Rat.cast_div, ratCast_fact]
    ring
  -- the twisted pairing of the coordinates is the twisted Petersson form
  have htw (y y' : ι → L) : twPair (c₀ : L →+* L) w Em y y' =
      petTw ST Λ (c₀ : L →+* L) lam (c.symm y : Fn ST Λ Φ L) (c.symm y' : Fn ST Λ Φ L) := by
    rw [twPair, petTw, classSum, finsum_eq_sum_of_fintype, Finset.sum_div, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun cl _ => ?_
    rw [mass_eq_one (hst cl), one_smul, fockWith_eq_sum _ (hS y' cl), Finset.sum_div, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hEm, hEm]
    simp only [w, Rat.cast_div, ratCast_fact]
    ring
  -- `D = |m|^{2n·negW λ}`
  set D : ℕ := m.natAbs ^ (2 * n * negW lam) with hDdef
  have hD : 0 < D := pow_pos (Int.natAbs_pos.2 hm0) _
  have hDL : (D : L) = (m : L) ^ (2 * n * negW lam) := by
    have h2 : ((m.natAbs : ℕ) : L) ^ 2 = (m : L) ^ 2 := by
      have := congrArg (fun z : ℤ => (z : L)) (Int.natAbs_sq m)
      simpa only [Int.cast_pow, Int.cast_natCast] using this
    rw [hDdef, Nat.cast_pow, mul_assoc, pow_mul, h2, ← pow_mul]
  -- integrality on the span of the integral forms
  have hint : ∀ x ∈ X.M, ∀ y ∈ X.M, (D : L) * twPair (c₀ : L →+* L) w Em x y ∈ (1 : Submodule (𝓞 L) L) := by
    rw [hM]
    refine twPair_mem_one_span c₀ w Em _ ?_
    rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG', rfl⟩
    rw [htw, c.symm_apply_apply, c.symm_apply_apply, hDL]
    exact petTw_mem_of_Mint τ χ hlam c₀ hc hst hm0 hm hF.1 hG'.1
  have h := slopeLe_of_twPair X w hw Em hGm c₀ ⟨v₀, hv₀⟩ hD hint
  have hlog : Real.log (D : ℝ) = 2 * n * negW lam * Real.log |(m : ℝ)| := by
    rw [hDdef, Nat.cast_pow, Real.log_pow, Nat.cast_natAbs, Int.cast_abs]
    push_cast
    ring
  rwa [hlog] at h

end HermForms
