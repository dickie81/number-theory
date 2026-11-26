import HermFormsLattice

/-!
# Tools for the slope bound (F)

The forms-level facts that the exact slope bound (F) (`FormSlopeExact`, `HermForms.muArch_source_ge`) uses.

* **The Petersson form is sesquilinear** (`petAt_eq_sum`, `petAt_sum_smul`), the Fock form likewise
  (`fockWith_star`, `fock_sum_smul`).
* **Unitarity.** The hermitian Fock form is unitary for unitary substitutions (`fock_lsub_unitary`, from the
  adjointness `fock_lsub` on the conjugate), the blocks `σ(τ(γ))` of a unitary `γ` are unitary since
  `σ ∘ conj = conj ∘ σ` on the CM field (`conjTranspose_mul_map`), and `ρ_λ` is a representation (`rho_mul`,
  `rho_one`) that is Fock-unitary at every embedding (`fockWith_map_rho`).
* **`Δ_N` tested in every local basis** (`DeltaA`, closed under sums and `O_L`, unlike the library's `DeltaN`,
  which asks some basis; `DeltaA_subset` for a lattice between `a·O_E^n` and `b⁻¹O_E^n`); `ρ_λ(γ)` moves `Δ_N` to
  `Δ_{γN}` (`rho_mem_DeltaA`: local bases move with `γ`, `isLocalBasis_map`), and `Lsh(g·d) = γ·Lsh(d)`
  (`Lsh_smul`). Integrality of the coefficients of bideterminants (`coeff_bidet_mem`).
* **The character** takes roots of unity, units at every place of absolute value one (`chr_mem_Ow`,
  `norm_map_chr`), so the action on values `actP g = chr(g)·ρ_λ(γ_g)` is Fock-unitary (`fockWith_map_actP`) and
  keeps the integral vectors (`actP_mem_DeltaA`).
* **Forms on one class**: `ext c P` is supported on `c` with value `P` at its representative (`ext_out`,
  `ext_mem_Forms` for stabiliser-invariant `P`), and every form is the sum over its classes (`eq_sum_ext`).
* **The normaliser** `κ = ⟨hw_ν, hw_ν⟩ > 0` (`kappa`, `kappa_pos`), the same over `ℚ`, `L` and `ℂ`
  (`map_fockWith_id`, `fockWith_star_map_rat`, `fockWith_hw_C`).
* **The diamond operators** form a commutative action (`dOp_dOp`) keeping the attached lattice (`Lsh_dia`), hence
  the integral forms tested in every local basis (`MintA`, `dOp_mem_MintA`, closed under `ℤ`-combinations), which
  lie in the library's integral forms (`MintA_subset`, with one pair of comparison constants for all classes,
  `exists_sand_uniform`).
-/

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock MvPolynomial

open scoped ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
  {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L] [NumberField L]

/-! ## The Petersson form is sesquilinear -/

section Sesq

omit [Fintype Φ] [DecidableEq Φ] in
/-- The hermitian Fock form is the bilinear one on the conjugate. -/
theorem fockWith_star (P Q : Pol Φ n ℂ) :
    fockWith (starRingEnd ℂ) P Q = fockWith (RingHom.id ℂ) (map (starRingEnd ℂ) P) Q := by
  simp only [fockWith, coeff_map, RingHom.id_apply]

omit [DecidableEq Φ] in
/-- **The normalised Fock form is sesquilinear**: `⟨Σ aᵢPᵢ, Σ bⱼQⱼ⟩ = Σ conj(aᵢ)bⱼ⟨Pᵢ, Qⱼ⟩`. -/
theorem fock_sum_smul (ν : Φ → Fin n → ℕ) {I J : Type*} [Fintype I] [Fintype J] (a : I → ℂ) (P : I → Pol Φ n ℂ)
    (b : J → ℂ) (Q : J → Pol Φ n ℂ) :
    fock ν (∑ i, C (a i) * P i) (∑ j, C (b j) * Q j) =
      ∑ i, ∑ j, starRingEnd ℂ (a i) * b j * fock ν (P i) (Q j) := by
  unfold fock
  rw [fockWith_star (∑ i, C (a i) * P i)]
  simp only [map_sum, map_mul, map_C, fock_sum_left, fock_C_mul_left, fock_sum_right, fock_C_mul_right,
    ← fockWith_star, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (ST) (lam : Φ → Fin n → ℤ)

omit [DecidableEq Φ] [NumberField L] in
/-- The Petersson form at `σ` over the finitely many classes. -/
theorem petAt_eq_sum [Fintype (DCl E n ST Λ)] (σ : L →+* ℂ) (F G : Fn ST Λ Φ L) :
    petAt ST lam σ F G = ∑ c : DCl E n ST Λ,
      (mass c : ℂ) * fock (fun ρ => natW (lam ρ)) (map σ (F c.out)) (map σ (G c.out)) := by
  simp only [petAt, classSum, finsum_eq_sum_of_fintype, Rat.smul_def]

omit [DecidableEq Φ] [NumberField L] in
/-- **The Petersson form at `σ` is sesquilinear**:
`H_σ(Σ xᵢFᵢ, Σ yⱼGⱼ) = Σ conj(σxᵢ)·σyⱼ·H_σ(Fᵢ, Gⱼ)`. -/
theorem petAt_sum_smul (σ : L →+* ℂ) {I J : Type*} [Fintype I] [Fintype J] (x : I → L) (F : I → Fn ST Λ Φ L)
    (y : J → L) (G : J → Fn ST Λ Φ L) :
    petAt ST lam σ (∑ i, x i • F i) (∑ j, y j • G j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (x i)) * σ (y j) * petAt ST lam σ (F i) (G j) := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  simp only [petAt_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_C_mul, map_sum, map_mul, map_C,
    fock_sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end Sesq

/-! ## Unitarity of the Fock form -/

section Unitary

open scoped Matrix

omit [Fintype Φ] [DecidableEq Φ] in
/-- A ring map on the coefficients commutes with a substitution, the matrices mapped too. -/
theorem map_lsub {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (g : Φ → Matrix (Fin n) (Fin n) K)
    (P : Pol Φ n K) : map φ (lsub g P) = lsub (fun σ => (g σ).map φ) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp, lsub_X, map_sum]

/-- **The Fock form is unitary**: a substitution by unitary blocks, `U_σ U_σᴴ = 1`, keeps it. By adjointness
(`fock_lsub`), `⟨P(Ux), Q(Ux)⟩ = ⟨P((Ū Uᵀ)x), Q⟩` on the conjugate, and `Ū Uᵀ = conj(U Uᴴ) = 1`. -/
theorem fock_lsub_unitary (U : Φ → Matrix (Fin n) (Fin n) ℂ) (hU : ∀ σ, U σ * (U σ)ᴴ = 1) (P Q : Pol Φ n ℂ) :
    fockWith (starRingEnd ℂ) (lsub U P) (lsub U Q) = fockWith (starRingEnd ℂ) P Q := by
  rw [fockWith_star, fockWith_star, map_lsub, ← fock_lsub, lsub_lsub]
  have h1 : (fun σ => (U σ).map (starRingEnd ℂ) * (U σ)ᵀ) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) :=
    funext fun σ => by
      have h := congrArg (Matrix.map · (starRingEnd ℂ)) (hU σ)
      simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
      rw [← h]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
  rw [h1, lsub_one]
  rfl

/-- At an embedding `φ : E → ℂ`, a unitary `γ` is a unitary matrix, `φ(γ)ᴴφ(γ) = 1`, as `φ ∘ conj = conj ∘ φ`
(`emb_herm`). -/
theorem conjTranspose_mul_map {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (φ : E →+* ℂ) :
    ((γ : Matrix (Fin n) (Fin n) E).map φ)ᴴ * (γ : Matrix (Fin n) (Fin n) E).map φ = 1 := by
  ext i j
  have h := congrArg φ (hγ (Pi.single i 1) (Pi.single j 1))
  rw [emb_herm, emb_herm] at h
  simp only [act_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, RCLike.star_def]
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij, Finset.sum_ite_eq']

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ(γ)` is the twist by `τ(γ⁻¹)`. -/
theorem rho_eq_twist (γ : GL (Fin n) E) (F : Pol Φ n L) :
    rho τ lam γ F = twist lam (fun σ => (τ σ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) F := by
  unfold rho twist
  congr 2
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← RingHom.map_det, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, inv_zpow']

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ` is multiplicative: `ρ(γδ) = ρ(γ)ρ(δ)` (`twist_twist`). -/
theorem rho_mul (γ δ : GL (Fin n) E) (F : Pol Φ n L) :
    rho τ lam (γ * δ) F = rho τ lam γ (rho τ lam δ F) := by
  rw [rho_eq_twist, rho_eq_twist, rho_eq_twist, twist_twist]
  congr 1
  funext σ
  rw [← map_mul, mul_inv_rev, Units.val_mul]

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ` is additive. -/
theorem rho_add (γ : GL (Fin n) E) (F G : Pol Φ n L) : rho τ lam γ (F + G) = rho τ lam γ F + rho τ lam γ G := by
  rw [rho_eq_twist, rho_eq_twist, rho_eq_twist, twist_add]

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ` is `L`-linear. -/
theorem rho_smul (γ : GL (Fin n) E) (a : L) (F : Pol Φ n L) : rho τ lam γ (a • F) = a • rho τ lam γ F := by
  rw [rho_eq_twist, rho_eq_twist, twist_smul]

omit [NumberField E] [IsCMField E] [DecidableEq Φ] [NumberField L] in
/-- `ρ_λ(1)` is the identity. -/
theorem rho_one (F : Pol Φ n L) : rho τ lam 1 F = F := by
  rw [rho_eq_twist, inv_one, Units.val_one]
  simp only [map_one]
  exact twist_one lam F

omit [DecidableEq Φ] in
/-- `‖φ(det γ)‖ = 1` for a unitary `γ`. -/
theorem norm_map_det {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (φ : E →+* ℂ) :
    ‖φ (γ : Matrix (Fin n) (Fin n) E).det‖ = 1 := by
  have h := congrArg Matrix.det (conjTranspose_mul_map hγ φ)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have h2 : ‖φ (γ : Matrix (Fin n) (Fin n) E).det‖ ^ 2 = 1 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm, ← RCLike.star_def]
    simpa using h
  nlinarith [norm_nonneg (φ (γ : Matrix (Fin n) (Fin n) E).det)]

omit [NumberField L] in
/-- **`ρ_λ` is Fock-unitary at every embedding**: for `γ ∈ U_n(E)` and `σ : L → ℂ`, the blocks `σ(τ(γ⁻¹))` are
unitary (`conjTranspose_mul_map`) and the determinant factor has modulus `1` (`norm_map_det`). -/
theorem fockWith_map_rho {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (σ : L →+* ℂ) (F G : Pol Φ n L) :
    fockWith (starRingEnd ℂ) (map σ (rho τ lam γ F)) (map σ (rho τ lam γ G)) =
      fockWith (starRingEnd ℂ) (map σ F) (map σ G) := by
  set c := ∏ ρ, τ ρ (γ : Matrix (Fin n) (Fin n) E).det ^ (-detShift (lam ρ))
  have hc : ‖σ c‖ = 1 := by
    simp only [c, map_prod, map_zpow₀, norm_prod, norm_zpow]
    exact Finset.prod_eq_one fun ρ _ => by
      rw [show σ (τ ρ (γ : Matrix (Fin n) (Fin n) E).det) = (σ.comp (τ ρ)) (γ : Matrix (Fin n) (Fin n) E).det
        from rfl, norm_map_det hγ, one_zpow]
  have hU : ∀ ρ, ((τ ρ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).map σ *
      (((τ ρ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).map σ)ᴴ = 1 := fun ρ => by
    have h := conjTranspose_mul_map (inv_mem hγ) (σ.comp (τ ρ))
    exact mul_eq_one_comm.1 h
  unfold rho
  rw [map_mul, map_mul, map_C, map_lsub, map_lsub, fockWith_star, map_mul, map_C, fock_C_mul_left,
    fock_C_mul_right, ← fockWith_star, fock_lsub_unitary _ hU]
  have : starRingEnd ℂ (σ c) * σ c = 1 := by
    rw [mul_comm, Complex.mul_conj', hc]
    simp
  rw [← mul_assoc, this, one_mul]

end Unitary

/-! ## Integral vectors: `Δ_N` tested in every local basis -/

section Integral

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- The polynomials with coefficients in a subring `A` are the image of `A[x]`. -/
theorem mem_range_map_iff {A : Subring L} {F : Pol Φ n L} :
    F ∈ (map A.subtype).range ↔ ∀ d, F.coeff d ∈ A := by
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

omit [DecidableEq Φ] [NumberField L] in
/-- **Bideterminants have integer coefficients**: they lie in every subring. -/
theorem coeff_bidet_mem (A : Subring L) (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) (d : Φ × Fin n × Fin n →₀ ℕ) :
    (bidet L ν rows).coeff d ∈ A := by
  set R := (map A.subtype : MvPolynomial (Φ × Fin n × Fin n) A →+* Pol Φ n L).range
  have hX : ∀ p, (X p : Pol Φ n L) ∈ R := fun p => ⟨X p, by simp⟩
  have hminor : ∀ τ s I, (minor τ s I : Pol Φ n L) ∈ R := fun τ s I => by
    rw [minor, Matrix.det_apply]
    exact R.sum_mem fun σ _ => by
      rw [Units.smul_def]
      exact zsmul_mem (R.prod_mem fun i _ => hX _) _
  have : bidet L ν rows ∈ R := R.prod_mem fun τ _ => R.prod_mem fun s _ => R.prod_mem fun c _ => hminor _ _ _
  exact mem_range_map_iff.1 this d

end Integral

/-! ## `Δ_N` in every local basis -/

section DeltaA

variable (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

/-- `Δ_N(λ)` tested in **every** tuple of local bases (`DeltaN` asks some): closed under sums
(`add_mem_DeltaA`), and moved by `ρ_λ(γ)` to `Δ_{γN}` (`rho_mem_DeltaA`). It lies in `Δ_N` (`DeltaA_subset`). -/
def DeltaA (N : Submodule (𝓞 E) (Fin n → E)) : Set (Pol Φ n L) :=
  {F | F ∈ VV lam ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (C : Φ → Matrix (Fin n) (Fin n) L),
    (∀ σ, IsLocalBasis w (τ σ) N (C σ)) → twist lam C F ∈ Delta (Ow w) fun σ => natW (lam σ)}

variable {τ lam}

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` in every local basis lies in `Δ_N`, local bases existing (`exists_localBasis`). -/
theorem DeltaA_subset {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ} (h : Sand N a b) :
    DeltaA τ lam N ⊆ DeltaN τ lam N := fun F hF =>
  ⟨hF.1, fun w => by
    choose C hC using fun σ => exists_localBasis (w := w) (σ := τ σ) h
    exact ⟨C, hC, hF.2 w C hC⟩⟩

omit [NumberField L] in
/-- `Δ_A` is closed under sums. -/
theorem add_mem_Delta {A : Subring L} {ν : Φ → Fin n → ℕ} {F G : Pol Φ n L} (hF : F ∈ Delta A ν)
    (hG : G ∈ Delta A ν) : F + G ∈ Delta A ν :=
  ⟨add_mem hF.1 hG.1, fun rows => by rw [fock_add_left, add_div]; exact A.add_mem (hF.2 rows) (hG.2 rows)⟩

omit [NumberField L] in
/-- `Δ_A` is closed under `A`. -/
theorem smul_mem_Delta {A : Subring L} {ν : Φ → Fin n → ℕ} {F : Pol Φ n L} (hF : F ∈ Delta A ν) {c : L}
    (hc : c ∈ A) : c • F ∈ Delta A ν :=
  ⟨Submodule.smul_mem _ _ hF.1, fun rows => by rw [fock_smul_left, mul_div_assoc]; exact A.mul_mem hc (hF.2 rows)⟩

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` in every local basis is closed under sums. -/
theorem add_mem_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} {F G : Pol Φ n L} (hF : F ∈ DeltaA τ lam N)
    (hG : G ∈ DeltaA τ lam N) : F + G ∈ DeltaA τ lam N :=
  ⟨add_mem hF.1 hG.1, fun w C hC => by rw [twist_add]; exact add_mem_Delta (hF.2 w C hC) (hG.2 w C hC)⟩

omit [NumberField E] [IsCMField E] in
/-- `Δ_N` in every local basis is closed under the elements of `L` integral at every `w`. -/
theorem smul_mem_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} {F : Pol Φ n L} (hF : F ∈ DeltaA τ lam N) {c : L}
    (hc : ∀ w : HeightOneSpectrum (𝓞 L), c ∈ Ow w) : c • F ∈ DeltaA τ lam N :=
  ⟨Submodule.smul_mem _ _ hF.1, fun w C hC => by rw [twist_smul]; exact smul_mem_Delta (hF.2 w C hC) (hc w)⟩

omit [NumberField E] [IsCMField E] in
/-- `0 ∈ Δ_N`. -/
theorem zero_mem_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} : (0 : Pol Φ n L) ∈ DeltaA τ lam N :=
  ⟨zero_mem _, fun w C hC => ⟨by simp [twist], fun rows => by simp [twist, fockWith]⟩⟩

omit [NumberField E] [IsCMField E] in
/-- **Local bases move with `γ`**: `σ(γ)·C` is a local basis of `γN` when `C` is one of `N`. -/
theorem isLocalBasis_map {w : HeightOneSpectrum (𝓞 L)} {σ : E →+* L} {N : Submodule (𝓞 E) (Fin n → E)}
    {C : Matrix (Fin n) (Fin n) L} (hC : IsLocalBasis w σ N C) (γ : GL (Fin n) E) :
    IsLocalBasis w σ (N.map (act γ)) (σ.mapMatrix (γ : Matrix (Fin n) (Fin n) E) * C) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero σ).2 (Matrix.isUnits_det_units γ).ne_zero) hC.1
  · let T : (Fin n → L) →ₗ[Ow w] (Fin n → L) :=
      (Matrix.mulVecLin (σ.mapMatrix (γ : Matrix (Fin n) (Fin n) E))).restrictScalars (Ow w)
    have h1 : (fun v i => σ (v i)) '' ((N.map (act γ) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
        T '' ((fun v i => σ (v i)) '' (N : Set (Fin n → E))) := by
      ext y
      simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, act_apply]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩, funext fun i => by simp [T, RingHom.map_mulVec]; rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩, funext fun i => by simp [T, RingHom.map_mulVec]; rfl⟩
    have h2 : Set.range (fun j i => (σ.mapMatrix (γ : Matrix (Fin n) (Fin n) E) * C) i j) =
        T '' Set.range (fun j i => C i j) := by
      rw [← Set.range_comp]
      congr 1
    rw [h1, h2, Submodule.span_image, Submodule.span_image, hC.2]

omit [NumberField E] [IsCMField E] in
/-- **`ρ_λ(γ)` moves `Δ_N` to `Δ_{γN}`**: a local basis `C'` of `γN` is `τ(γ)C` for the local basis
`C = τ(γ⁻¹)C'` of `N`, and `twist_{C'}(ρ(γ)F) = twist_C F` (`twist_twist`). -/
theorem rho_mem_DeltaA (γ : GL (Fin n) E) {N : Submodule (𝓞 E) (Fin n → E)} {F : Pol Φ n L}
    (hF : F ∈ DeltaA τ lam N) : rho τ lam γ F ∈ DeltaA τ lam (N.map (act γ)) := by
  refine ⟨?_, fun w C' hC' => ?_⟩
  · rw [rho_eq_twist]
    exact twist_mem_nabla _ _ hF.1
  · have hN : (N.map (act γ)).map (act γ⁻¹) = N := by
      rw [← Submodule.map_comp]
      convert Submodule.map_id N
      exact LinearMap.ext fun x => act_inv_act γ x
    have hC : ∀ σ, IsLocalBasis w (τ σ) N ((τ σ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * C' σ) :=
      fun σ => hN ▸ isLocalBasis_map (hC' σ) γ⁻¹
    rw [rho_eq_twist, twist_twist]
    exact hF.2 w _ hC

end DeltaA

/-! ## The character is a root of unity -/

section Chr

omit [IsCMField E] in
/-- The level group is finite: the residue rings at `SG` are finite (`finite_residue`). -/
theorem finite_Λ : Finite Λ := by
  have : ∀ w : SG, Finite (𝓞 E ⧸ w.1.asIdeal) := fun w => finite_residue w.1
  infer_instance

omit [NumberField L] in
/-- `χ_SG(h)` is a root of unity, `Λ` being finite. -/
theorem exists_pow_chr (χ : Λ →* L) (g : Grp E n SG Λ) : ∃ m : ℕ, 0 < m ∧ chr χ g ^ m = 1 := by
  have := finite_Λ (Λ := Λ)
  refine ⟨orderOf g.2, orderOf_pos g.2, ?_⟩
  rw [chr, MonoidHom.comp_apply, ← map_pow]
  show χ (g.2 ^ orderOf g.2) = 1
  rw [pow_orderOf_eq_one, map_one]

/-- The character is integral at every finite place. -/
theorem chr_mem_Ow (χ : Λ →* L) (g : Grp E n SG Λ) (w : HeightOneSpectrum (𝓞 L)) : chr χ g ∈ Ow w := by
  obtain ⟨m, hm, h⟩ := exists_pow_chr χ g
  have hi : IsIntegral ℤ (chr χ g) := IsIntegral.of_pow hm (h ▸ isIntegral_one)
  have := w.valuation_le_one (K := L) (⟨chr χ g, hi⟩ : 𝓞 L)
  exact this

omit [NumberField L] in
/-- The character has modulus `1` at every embedding. -/
theorem norm_map_chr (χ : Λ →* L) (g : Grp E n SG Λ) (σ : L →+* ℂ) : ‖σ (chr χ g)‖ = 1 := by
  obtain ⟨m, hm, h⟩ := exists_pow_chr χ g
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, h, map_one]) hm.ne'

end Chr

/-! ## The action on values, and the forms supported on one class -/

section Ext

omit [NumberField E] [IsCMField E] in
/-- Membership in the image of a kernel in `E^n`. -/
theorem mem_map_subtype_ker {N : Submodule (𝓞 E) (Fin n → E)} {M : Type*} [AddCommGroup M] [Module (𝓞 E) M]
    (f : N →ₗ[𝓞 E] M) {x : Fin n → E} : x ∈ (LinearMap.ker f).map N.subtype ↔ ∃ hx : x ∈ N, f ⟨x, hx⟩ = 0 :=
  ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨y.2, hy⟩, fun ⟨hx, h⟩ => ⟨⟨x, hx⟩, h, rfl⟩⟩

/-- The level-`T` kernel moves with `g`: `kerLat(g·d) = γ·kerLat(d)`. -/
theorem kerLat_smul (g : Grp E n SG Λ) (d : Deco E n ST SG) : kerLat (g • d) = (kerLat d).map (act g.1.1) := by
  ext x
  rw [mem_map_act]
  simp only [kerLat, Submodule.mem_inf, Submodule.mem_iInf, mem_map_subtype_ker]
  constructor
  · rintro ⟨hx, h⟩
    have hx' : act g.1.1⁻¹ x ∈ d.N := mem_map_act.1 hx
    refine ⟨hx', fun P => ⟨hx', ?_⟩⟩
    obtain ⟨_, hP⟩ := h P
    rw [smul_f] at hP
    convert hP using 2
    exact Subtype.ext rfl
  · rintro ⟨hx', h⟩
    have hx : x ∈ (g • d).N := mem_map_act.2 hx'
    refine ⟨hx, fun P => ⟨hx, ?_⟩⟩
    obtain ⟨_, hP⟩ := h P
    rw [smul_f]
    convert hP using 2
    exact Subtype.ext rfl

/-- **The attached lattice moves with `g`**: `Lsh(g·d) = γ·Lsh(d)` (`kerLat_smul`, `dual_map`). -/
theorem Lsh_smul (g : Grp E n SG Λ) (d : Deco E n ST SG) : Lsh (g • d) = (Lsh d).map (act g.1.1) := by
  rw [Lsh, Lsh, kerLat_smul, dual_map g.1.2]

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- The action `chr(g)·ρ_λ(γ_g)` on the values of forms: `F(g·d) = actP g (F d)` for a form. -/
def actP (g : Grp E n SG Λ) (P : Pol Φ n L) : Pol Φ n L := chr χ g • rho τ lam g.1.1 P

omit [DecidableEq Φ] [NumberField L] in
/-- The action is multiplicative. -/
theorem actP_mul (g h : Grp E n SG Λ) (P : Pol Φ n L) :
    actP τ χ lam (g * h) P = actP τ χ lam g (actP τ χ lam h P) := by
  simp only [actP, map_mul, rho_smul, smul_smul]
  rw [show (g * h).1.1 = g.1.1 * h.1.1 from rfl, rho_mul]

omit [DecidableEq Φ] [NumberField L] in
/-- `actP 1` is the identity. -/
theorem actP_one (P : Pol Φ n L) : actP τ χ lam 1 P = P := by
  simp only [actP, map_one, one_smul]
  exact rho_one τ lam P

omit [DecidableEq Φ] [NumberField L] in
/-- The action is additive. -/
theorem actP_add (g : Grp E n SG Λ) (P Q : Pol Φ n L) :
    actP τ χ lam g (P + Q) = actP τ χ lam g P + actP τ χ lam g Q := by
  simp only [actP, rho_add, smul_add]

omit [DecidableEq Φ] [NumberField L] in
/-- The action is `L`-linear. -/
theorem actP_smul (g : Grp E n SG Λ) (a : L) (P : Pol Φ n L) :
    actP τ χ lam g (a • P) = a • actP τ χ lam g P := by
  simp only [actP, rho_smul, smul_comm a]

omit [DecidableEq Φ] [NumberField L] in
/-- `actP g 0 = 0`. -/
theorem actP_zero (g : Grp E n SG Λ) : actP τ χ lam g (0 : Pol Φ n L) = 0 := by
  simpa using actP_smul τ χ lam g 0 0

omit [DecidableEq Φ] [NumberField L] in
/-- The action commutes with finite sums. -/
theorem actP_sum (g : Grp E n SG Λ) {ι : Type*} (s : Finset ι) (P : ι → Pol Φ n L) :
    actP τ χ lam g (∑ i ∈ s, P i) = ∑ i ∈ s, actP τ χ lam g (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using actP_zero τ χ lam g
  | insert i s hi ih => rw [Finset.sum_insert hi, actP_add, ih, Finset.sum_insert hi]

omit [NumberField L] in
/-- The action keeps `VV(λ)`. -/
theorem actP_mem_VV (g : Grp E n SG Λ) {P : Pol Φ n L} (hP : P ∈ VV lam) : actP τ χ lam g P ∈ VV lam := by
  rw [actP, rho_eq_twist]
  exact Submodule.smul_mem _ _ (twist_mem_nabla _ _ hP)

/-- **The action moves integral vectors**: `actP g` maps `Δ_{Lsh(d)}` to `Δ_{Lsh(g·d)}` in every local basis
(`rho_mem_DeltaA`, `Lsh_smul`, `chr_mem_Ow`). -/
theorem actP_mem_DeltaA (g : Grp E n SG Λ) {d : Deco E n ST SG} {P : Pol Φ n L}
    (hP : P ∈ DeltaA τ lam (Lsh d)) : actP τ χ lam g P ∈ DeltaA τ lam (Lsh (g • d)) := by
  rw [Lsh_smul]
  exact smul_mem_DeltaA (rho_mem_DeltaA g.1.1 hP) (chr_mem_Ow χ g)

omit [NumberField L] in
/-- **The action is Fock-unitary at every embedding** (`fockWith_map_rho`, `norm_map_chr`). -/
theorem fockWith_map_actP (g : Grp E n SG Λ) (σ : L →+* ℂ) (P Q : Pol Φ n L) :
    fockWith (starRingEnd ℂ) (map σ (actP τ χ lam g P)) (map σ (actP τ χ lam g Q)) =
      fockWith (starRingEnd ℂ) (map σ P) (map σ Q) := by
  simp only [actP, smul_eq_C_mul, map_mul, map_C]
  rw [fockWith_star, map_mul, map_C, fock_C_mul_left, fock_C_mul_right, ← fockWith_star,
    fockWith_map_rho τ lam g.1.2]
  have h : starRingEnd ℂ (σ (chr χ g)) * σ (chr χ g) = 1 := by
    rw [mul_comm, Complex.mul_conj', norm_map_chr]
    simp
  rw [← mul_assoc, h, one_mul]

/-- A point in the class `c` is `g·rep c`. -/
theorem exists_smul_out {c : DCl E n ST Λ} {d : points (E := E) (n := n) (ST := ST) Λ}
    (h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) = c) :
    ∃ g : Grp E n SG Λ, g • c.out = d := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel (Grp E n SG Λ) _) d
  subst h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

open Classical in
/-- **The form supported on the class `c`** with value `P` at its representative: `F(g·rep c) = actP g P`, and `0`
off the class. It is a form when `P` is invariant under the stabiliser (`ext_mem_Forms`). -/
def ext (c : DCl E n ST Λ) (P : Pol Φ n L) : Fn ST Λ Φ L := fun d =>
  if h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) = c then
    actP τ χ lam (Classical.choose (exists_smul_out h)) P else 0

/-- `P` is invariant under the stabiliser of the representative of `c`. -/
def Inv (c : DCl E n ST Λ) (P : Pol Φ n L) : Prop := ∀ h ∈ stab c, actP τ χ lam h P = P

omit [DecidableEq Φ] [NumberField L] in
/-- The value of `ext c P` at `g·rep c` is `actP g P`, for invariant `P`. -/
theorem ext_smul_out {c : DCl E n ST Λ} {P : Pol Φ n L} (hP : Inv τ χ lam c P) (g : Grp E n SG Λ) :
    ext τ χ lam c P (g • c.out) = actP τ χ lam g P := by
  have h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • c.out) : DCl E n ST Λ) = c :=
    (Quotient.sound ⟨g, rfl⟩ : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • c.out) : DCl E n ST Λ) =
      Quotient.mk _ c.out).trans (Quotient.out_eq c)
  rw [ext, dite_eq_left_of_eq_true (eq_true h)]
  set g' := Classical.choose (exists_smul_out h)
  have hg' : g' • c.out = g • c.out := Classical.choose_spec (exists_smul_out h)
  have hs : g⁻¹ * g' ∈ stab c := by
    show (g⁻¹ * g') • c.out = c.out
    rw [mul_smul, hg', inv_smul_smul]
  rw [show g' = g * (g⁻¹ * g') by group, actP_mul, hP _ hs]

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c P` has the value `P` at the representative of `c`. -/
theorem ext_out {c : DCl E n ST Λ} {P : Pol Φ n L} (hP : Inv τ χ lam c P) : ext τ χ lam c P c.out = P := by
  have := ext_smul_out τ χ lam hP 1
  rwa [one_smul, actP_one] at this

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c P` vanishes off the class `c`. -/
theorem ext_eq_zero {c : DCl E n ST Λ} {d : points (E := E) (n := n) (ST := ST) Λ}
    (h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) ≠ c) (P : Pol Φ n L) :
    ext τ χ lam c P d = 0 := by
  rw [ext, dite_eq_right_of_eq_false (eq_false h)]

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c P` vanishes at the representatives of the other classes. -/
theorem ext_out_ne {c c' : DCl E n ST Λ} (hc : c' ≠ c) (P : Pol Φ n L) : ext τ χ lam c P c'.out = 0 :=
  ext_eq_zero τ χ lam (by rwa [Quotient.out_eq]) P

omit [NumberField L] in
/-- **`ext c P` is a form** for `P ∈ VV(λ)` invariant under the stabiliser. -/
theorem ext_mem_Forms {c : DCl E n ST Λ} {P : Pol Φ n L} (hV : P ∈ VV lam) (hP : Inv τ χ lam c P) :
    ext τ χ lam c P ∈ Forms ST τ χ lam := by
  refine ⟨fun d => ?_, fun g d => ?_⟩
  · unfold ext
    split_ifs
    · exact actP_mem_VV τ χ lam _ hV
    · exact zero_mem _
  · by_cases h : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d : DCl E n ST Λ) = c
    · obtain ⟨g', rfl⟩ := exists_smul_out h
      rw [← mul_smul, ext_smul_out τ χ lam hP, ext_smul_out τ χ lam hP, actP_mul]
      rfl
    · have h' : (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • d) : DCl E n ST Λ) ≠ c := by
        rwa [show (Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) (g • d) : DCl E n ST Λ) =
          Quotient.mk _ d from Quotient.sound ⟨g, rfl⟩]
      rw [ext_eq_zero τ χ lam h, ext_eq_zero τ χ lam h']
      exact (actP_zero τ χ lam g).symm

omit [DecidableEq Φ] [NumberField L] in
/-- `ext c` is linear in the value. -/
theorem ext_sum_smul (c : DCl E n ST Λ) {ι : Type*} (s : Finset ι) (a : ι → L) (P : ι → Pol Φ n L) :
    ext τ χ lam c (∑ i ∈ s, a i • P i) = ∑ i ∈ s, a i • ext τ χ lam c (P i) := by
  funext d
  simp only [Finset.sum_apply, Pi.smul_apply]
  unfold ext
  split_ifs
  · rw [actP_sum]
    exact Finset.sum_congr rfl fun i _ => actP_smul τ χ lam _ _ _
  · simp

omit [NumberField L] in
/-- **A form is the sum of the forms supported on its classes**: `F = Σ_c ext c (F(rep c))`. -/
theorem eq_sum_ext [Fintype (DCl E n ST Λ)] {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) :
    F = ∑ c, ext τ χ lam c (F c.out) := by
  have hinv : ∀ c : DCl E n ST Λ, Inv τ χ lam c (F c.out) := fun c h hh => by
    show chr χ h • rho τ lam h.1.1 (F c.out) = F c.out
    rw [← hF.2]
    exact congrArg F hh
  funext d
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : DCl E n ST Λ, Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d = c₀ := ⟨_, rfl⟩
  obtain ⟨g, rfl⟩ := exists_smul_out hc₀
  rw [Finset.sum_apply, Finset.sum_eq_single c₀]
  · rw [ext_smul_out τ χ lam (hinv c₀), hF.2]
    rfl
  · intro c _ hc
    exact ext_eq_zero τ χ lam (hc₀.trans_ne (Ne.symm hc)) _
  · simp

end Ext

/-! ## The constants `κ` and `‖β‖²`, and the Petersson norm of a form on one class -/

section Consts

variable (lam : Φ → Fin n → ℤ)

/-- `κ = ⟨hw_ν, hw_ν⟩ = Σ_d (hw_ν)_d²·d!`, `ν = natW λ`: the Fock norm of the highest-weight vector, a positive
rational (an integer). -/
def kappa : ℚ := fockWith (RingHom.id ℚ) (hw ℚ fun ρ => natW (lam ρ)) (hw ℚ fun ρ => natW (lam ρ))

omit [DecidableEq Φ] in
/-- `κ > 0`. -/
theorem kappa_pos : 0 < kappa lam :=
  fock_self_pos_rat fun h => by simpa [h] using eval_one_hw (L := ℚ) (Φ := Φ) fun ρ => natW (lam ρ)

omit [DecidableEq Φ] in
/-- Bideterminants map to bideterminants under a ring map. -/
theorem map_bidet' {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) :
    map φ (bidet K ν rows) = bidet K' ν rows := by
  simp only [bidet, minor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  ext i j
  simp [xMat]

omit [Fintype Φ] [DecidableEq Φ] in
/-- An embedding commutes with the bilinear Fock form. -/
theorem map_fockWith_id {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (P Q : Pol Φ n K) :
    φ (fockWith (RingHom.id K) P Q) = fockWith (RingHom.id K') (map φ P) (map φ Q) := by
  simp only [fockWith, map_sum, map_mul, coeff_map, support_map_of_injective _ φ.injective, Finsupp.prod,
    map_prod, map_natCast, RingHom.id_apply]

omit [Fintype Φ] [DecidableEq Φ] in
/-- The hermitian Fock norm of a polynomial with rational coefficients is the rational one. -/
theorem fockWith_star_map_rat (P : Pol Φ n ℚ) :
    fockWith (starRingEnd ℂ) (map (algebraMap ℚ ℂ) P) (map (algebraMap ℚ ℂ) P) =
      ((fockWith (RingHom.id ℚ) P P : ℚ) : ℂ) := by
  rw [fockWith_star, map_map]
  have : (starRingEnd ℂ).comp (algebraMap ℚ ℂ) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  rw [this, ← map_fockWith_id]
  rfl

omit [DecidableEq Φ] in
/-- The normaliser of `fock` over `ℂ` is `κ`. -/
theorem fockWith_hw_C : fockWith (starRingEnd ℂ) (hw ℂ fun ρ => natW (lam ρ)) (hw ℂ fun ρ => natW (lam ρ)) =
    (kappa lam : ℂ) := by
  rw [← map_hw (algebraMap ℚ ℂ), fockWith_star_map_rat]
  rfl

end Consts

/-! ## The diamond operators -/

section Dia

omit [NumberField E] [IsCMField E] in
/-- `dia_a ∘ dia_b = dia_{ab}`. -/
theorem dia_dia (a b : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : Deco E n ST SG) : dia a (dia b d) = dia (a * b) d :=
  Deco.ext' rfl (fun P x _ _ => by
    simp only [dia, smul_smul, Pi.mul_apply, Units.val_mul]
    rfl) (fun _ _ _ _ => rfl)

omit [NumberField E] [IsCMField E] in
/-- `dia_1` is the identity. -/
theorem dia_one (d : Deco E n ST SG) : dia 1 d = d :=
  Deco.ext' rfl (fun P x _ _ => by simp [dia]; rfl) (fun _ _ _ _ => rfl)

/-- `dia_a ∘ dia_b = dia_{ab}` on points. -/
theorem diaPt_diaPt (a b : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : points (E := E) (n := n) (ST := ST) Λ) :
    diaPt a (diaPt b d) = diaPt (a * b) d :=
  Subtype.ext (dia_dia a b d.1)

/-- `dia_1` is the identity on points. -/
theorem diaPt_one (d : points (E := E) (n := n) (ST := ST) Λ) : diaPt 1 d = d := Subtype.ext (dia_one d.1)

/-- `dia_a` commutes with `𝒢` on points. -/
theorem diaPt_smul (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (g : Grp E n SG Λ)
    (d : points (E := E) (n := n) (ST := ST) Λ) : diaPt a (g • d) = g • diaPt a d :=
  Subtype.ext (dia_smul Λ a g d.1)

omit [NumberField E] [IsCMField E] in
/-- The diamond operators keep the level-`T` kernel: `u·f_P` has the kernel of `f_P` for a unit `u`. -/
theorem kerLat_dia (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : Deco E n ST SG) : kerLat (dia a d) = kerLat d := by
  ext x
  simp only [kerLat, Submodule.mem_inf, Submodule.mem_iInf, mem_map_subtype_ker]
  refine and_congr_right fun _ => forall_congr' fun P => exists_congr fun hx => ?_
  show (a P : 𝓞 E ⧸ P.1.asIdeal) • d.f P ⟨x, hx⟩ = 0 ↔ _
  rw [smul_eq_mul, Units.mul_right_eq_zero]

/-- **The diamond operators keep the attached lattice** (`kerLat_dia`). -/
theorem Lsh_dia (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : Deco E n ST SG) : Lsh (dia a d) = Lsh d := by
  rw [Lsh, Lsh, kerLat_dia]

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- `⟨a⟩⟨b⟩ = ⟨ba⟩`. -/
theorem dOp_dOp (a b : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (F : Fn ST Λ Φ L) :
    dOp a (dOp b F) = dOp (b * a) F := by
  funext d
  simp only [dOp, LinearMap.funLeft_apply, diaPt_diaPt]

/-- The order `N_P = |(O_E/P)^×|` of the diamond group at `P`. -/
def NP (P : ST) : ℕ := Nat.card (𝓞 E ⧸ P.1.asIdeal)ˣ

omit [IsCMField E] in
/-- The units of a residue field are finite. -/
theorem finite_units (P : ST) : Finite (𝓞 E ⧸ P.1.asIdeal)ˣ := by
  have := finite_residue P.1
  infer_instance

end Dia

/-! ## The diamond operators on integral forms and on the Petersson norm -/

section DiaForms

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- **The integral forms in every local basis**: `F(rep c) ∈ Δ_{Lsh(rep c)}` tested in every local basis. They lie
in `M` (`MintA_subset`) and are stable under sums, integers and the diamond operators (`dOp_mem_MintA`). -/
def MintA : Set (Fn ST Λ Φ L) :=
  {F | F ∈ Forms ST τ χ lam ∧ ∀ c : DCl E n ST Λ, F c.out ∈ DeltaA τ lam (Lsh c.rep)}

/-- `MintA ⊆ M`, local bases existing. -/
theorem MintA_subset {a b : ℤ} (hab : ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b) :
    MintA τ χ lam ⊆ Mint ST τ χ lam := fun _ hF => ⟨hF.1, fun c => DeltaA_subset (hab c) (hF.2 c)⟩

/-- An integral form is integral at every point: `F(g·rep c) = actP g F(rep c)` (`actP_mem_DeltaA`). -/
theorem MintA_apply {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) (d : points (E := E) (n := n) (ST := ST) Λ) :
    F d ∈ DeltaA τ lam (Lsh d.1) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : DCl E n ST Λ, Quotient.mk (MulAction.orbitRel (Grp E n SG Λ) _) d = c₀ := ⟨_, rfl⟩
  obtain ⟨g, rfl⟩ := exists_smul_out hc₀
  rw [hF.1.2]
  exact actP_mem_DeltaA τ χ lam g (hF.2 _)

/-- The diamond operators keep the integral forms (`Lsh_dia`). -/
theorem dOp_mem_MintA (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) :
    dOp a F ∈ MintA τ χ lam := by
  refine ⟨dOp_mem ST τ χ lam a hF.1, fun c => ?_⟩
  have := MintA_apply τ χ lam hF (diaPt a c.out)
  rwa [show (diaPt a c.out).1 = dia a c.rep from rfl, Lsh_dia] at this

/-- Integral forms in every local basis are closed under sums. -/
theorem add_mem_MintA {F G : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) (hG : G ∈ MintA τ χ lam) :
    F + G ∈ MintA τ χ lam :=
  ⟨add_mem hF.1 hG.1, fun c => add_mem_DeltaA (hF.2 c) (hG.2 c)⟩

/-- Integral forms in every local basis are closed under integers. -/
theorem zsmul_mem_MintA (z : ℤ) {F : Fn ST Λ Φ L} (hF : F ∈ MintA τ χ lam) : (z : L) • F ∈ MintA τ χ lam :=
  ⟨Submodule.smul_mem _ _ hF.1, fun c => smul_mem_DeltaA (hF.2 c) fun _ => intCast_mem _ z⟩

/-- Integral forms in every local basis are closed under finite sums. -/
theorem sum_mem_MintA {ι : Type*} (s : Finset ι) {F : ι → Fn ST Λ Φ L} (h : ∀ i ∈ s, F i ∈ MintA τ χ lam) :
    ∑ i ∈ s, F i ∈ MintA τ χ lam := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact ⟨zero_mem _, fun c => zero_mem_DeltaA⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_mem_MintA τ χ lam (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end DiaForms

/-! ## Uniform comparison constants -/

section Uniform

attribute [local instance] InnerProductSpace.complexToReal

omit [NumberField E] [IsCMField E] in
/-- A comparison `a·O_E^n ⊆ N ⊆ b⁻¹O_E^n` survives multiplying `a` and `b` by nonzero integers. -/
theorem Sand.mul {N : Submodule (𝓞 E) (Fin n → E)} {a b : ℤ} (h : Sand N a b) {k k' : ℤ} (hk : k ≠ 0)
    (hk' : k' ≠ 0) : Sand N (a * k) (b * k') where
  a_ne := mul_ne_zero h.a_ne hk
  b_ne := mul_ne_zero h.b_ne hk'
  single_mem i := by
    have := int_smul_mem (h.single_mem i) k
    rwa [smul_smul, ← Int.cast_mul, mul_comm k] at this
  int x hx i := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h.int x hx i)
    refine Submodule.mem_one.2 ⟨(k' : 𝓞 E) * r, ?_⟩
    rw [map_mul, hr, map_intCast]
    push_cast
    ring

/-- **Uniform comparison constants exist**: one pair `a, b` of nonzero integers with
`a·O_E^n ⊆ Lsh(rep c) ⊆ b⁻¹O_E^n` for every class (`exists_sand_Lsh` for each of the finitely many classes, and
the products). -/
theorem exists_sand_uniform : ∃ a b : ℤ, ∀ c : DCl E n ST Λ, Sand (Lsh c.rep) a b := by
  classical
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  choose a b hab using fun c : DCl E n ST Λ =>
    exists_sand_Lsh (show (c.out : Deco E n ST SG).Good from c.out.2).unimod
  refine ⟨∏ c, a c, ∏ c, b c, fun c => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ b (Finset.mem_univ c)]
  exact (hab c).mul (Finset.prod_ne_zero_iff.2 fun c' _ => (hab c').a_ne)
    (Finset.prod_ne_zero_iff.2 fun c' _ => (hab c').b_ne)

end Uniform

end

end HermForms
