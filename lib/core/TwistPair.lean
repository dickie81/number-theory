import DeltaVolume
import LocalLattice
import WeylSandwich

/-!
# The twisted Petersson pairing is integral

Theorem B of the twisted-Petersson route to `ZetaBalance.SharpMuMax`. Let `c` be a ring automorphism of the
coefficient field `L` that is complex conjugation on every `τ_ρ(E)` (`c ∘ τ_ρ = τ_ρ ∘ conj_E`), let every class have
trivial stabiliser, and let `m ≠ 0` be an integer in every place of `ST`. Then the `c`-twisted Petersson form
`H_c(F, G) = Σᶠ_cl mass(cl)·fock_c(F(cl), G(cl))/κ` (`petTw`) satisfies `m^{2n·negW λ}·H_c(F, G) ∈ O_L` on the
integral forms (`petTw_mem_of_Mint`), with `negW λ = Σ_ρ max(0, −λ_{ρ,n−1})` (`negW`). With the abstract slope bound
for a lattice carrying an integral twisted pairing (Theorem A), it bounds the maximal slope of the source of the forms.

The proof is local, place by place, and uses only integral substitutions.

* **Pair** (`pair_mem_one`): for an `O_E`-lattice `Y`, `P ∈ Δ_Y` and `Q ∈ Δ_{Y^#}`, `fock_c(P, Q)/κ ∈ O_L`. At a
  finite place `w`, let `w′` be the place with `x ∈ O_{w′} ⇔ c(x) ∈ O_w` (`TwistPair.exists_comapPlace`). Write
  `Y = γ·D(𝔞)` (`exists_pseudo`). With generators `a_{ρ,i}` of `O_{w′}·τ_ρ(𝔞_i)` whose inverses generate
  `O_{w′}·τ_ρ(𝔞_i⁻¹)` (`exists_gen_inv`), `B_ρ = τ_ρ(γ)·diag(a_ρ)` is a local basis of `Y` at `w′`, and
  `B′_ρ = τ_ρ((γᵀ)⁻¹)·diag(a_ρ⁻¹)` one of `(γᵀ)⁻¹·D(𝔞⁻¹)` (`isLocalBasis_pseudo`), so `c(B′_ρ)` is one of
  `Y^# = conj((γᵀ)⁻¹·D(𝔞⁻¹))` at `w` (`dual_pseudo`, `isLocalBasis_map_conj`), and `c(B′_ρ)·c(B_ρ)ᵀ = 1`. The twist
  of `c(P)` by `c(B)` is `c` of the twist of `P` by `B`, which lies in `Δ_{O_{w′}} ⊆ ∇_{O_{w′}}`
  (`WeylSandwich.Delta_subset_nablaInt`), so it lies in `∇_{O_w}` (`map_twist`, `map_mem_nablaInt`); the twist of
  `Q` by `c(B′)` lies in `Δ_{O_w}` (`DeltaN_subset_DeltaA`); the two twists cancel in the Fock form (`fock_twist`),
  and `∇_{O_w}` pairs with `Δ_{O_w}` into `O_w` (`fock_div_mem_of_nablaInt_Delta`).
* **Sub** (`pow_smul_mem_DeltaN_of_le`): for `Y₁ ⊆ Y₂` with `m·Y₂ ⊆ Y₁`, `m^{n·negW λ}·Δ_{Y₂} ⊆ Δ_{Y₁}`. Local bases
  satisfy `C₁ = C₂·S` and `m·C₂ = C₁·S′` with `S`, `S′` integral (`exists_mul_eq_of_span_le`), so `S′·S = m·1`. The
  twist by `C₁` is the twist by `S` of the twist by `C₂`: the substitution by `S` keeps `Δ_{O_w}`
  (`WeylFock.lsub_mem_Delta`), and `m^{n·max(0, −s)}·det(S)^s` is integral (`pow_toNat_mul_det_zpow_mem`). Only the
  negative determinant twists cost: the lattice only ever shrinks, so the polynomial degree never enters.
* **The attached lattice** (`dual_Lsh_le`, `sq_smul_mem_dual_Lsh`): for a good `d`, `Lsh(d)^# ⊆ Lsh(d)` and
  `m²·Lsh(d) ⊆ Lsh(d)^#`.
* **Per class, then the sum** (`fockWith_mem_of_Mint`, `petTw_mem_of_Mint`): Sub for `Lsh^# ⊆ Lsh` with `m²`, then
  Pair for `Y = Lsh`. The masses are `1`, and a `finsum` of integral elements is integral (`finsum_induction`), so the
  finiteness of the classes is not needed.

No other denominator enters: `κ = HermForms.kappa λ` only normalises the pairing of `∇_A` with `Δ_A`, whose
definition divides by it (`kappa_cast`), and the shape of the class representatives never enters, as integrality is
tested in local bases of each `Lsh(rep cl)`.
-/

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock MvPolynomial

open scoped nonZeroDivisors Matrix

/-! ## The place conjugate under `c` -/

namespace TwistPair

variable {L : Type} [Field L] [NumberField L]

/-- **Membership in `O_{L,w}`** by a denominator prime to `w`: `x ∈ O_{L,w}` iff `x·d ∈ O_L` for some `d ∈ O_L`
outside `w`. -/
theorem mem_Ow_iff {w : HeightOneSpectrum (𝓞 L)} {x : L} :
    x ∈ Ow w ↔ ∃ a d : 𝓞 L, d ∉ w.asIdeal ∧ x * (d : L) = a := by
  constructor
  · intro hx
    obtain ⟨a, d, h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w x hx
    exact ⟨a, d, d.2, h⟩
  · rintro ⟨a, d, hd, h⟩
    show w.valuation L x ≤ 1
    have h1 : w.valuation L (d : L) = 1 := by
      rw [show (d : L) = algebraMap (𝓞 L) L d from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (w.intValuation_eq_one_iff_mem_primeCompl d).2 hd
    have h2 : w.valuation L (x * (d : L)) ≤ 1 := by
      rw [h, show (a : L) = algebraMap (𝓞 L) L a from rfl]
      exact w.valuation_le_one a
    rwa [map_mul, h1, mul_one] at h2

/-- **The place conjugate under `c`**: for a ring automorphism `c` of `L` and a finite place `w`, the place `w′` of
the prime `c⁻¹(w)` has `x ∈ O_{w′}` iff `c(x) ∈ O_w` (`mem_Ow_iff` on both sides, along `c` on `O_L`). -/
theorem exists_comapPlace (c : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) :
    ∃ w' : HeightOneSpectrum (𝓞 L), ∀ x : L, x ∈ Ow w' ↔ c x ∈ Ow w := by
  let cO : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c
  have hcO (r : 𝓞 L) : ((cO r : 𝓞 L) : L) = c r := rfl
  let w' : HeightOneSpectrum (𝓞 L) :=
    { asIdeal := w.asIdeal.comap (cO : 𝓞 L →+* 𝓞 L)
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        apply w.ne_bot
        have := congrArg (Ideal.map (cO : 𝓞 L →+* 𝓞 L)) h
        rwa [Ideal.map_comap_of_surjective (cO : 𝓞 L →+* 𝓞 L) cO.surjective, Ideal.map_bot] at this }
  refine ⟨w', fun x => ?_⟩
  rw [mem_Ow_iff, mem_Ow_iff]
  constructor
  · rintro ⟨a, d, hd, h⟩
    refine ⟨cO a, cO d, hd, ?_⟩
    rw [hcO, hcO, ← map_mul, h]
  · rintro ⟨a, d, hd, h⟩
    refine ⟨cO.symm a, cO.symm d, ?_, ?_⟩
    · show cO (cO.symm d) ∉ w.asIdeal
      rwa [RingEquiv.apply_symm_apply]
    · apply c.injective
      rw [map_mul]
      have e1 : c ((cO.symm d : 𝓞 L) : L) = d := by rw [← hcO, RingEquiv.apply_symm_apply]
      have e2 : c ((cO.symm a : 𝓞 L) : L) = a := by rw [← hcO, RingEquiv.apply_symm_apply]
      rw [e1, e2, h]

end TwistPair

/-! ## Local bases: conjugation, pseudo-bases, existence -/

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {L : Type} [Field L] [NumberField L]

/-- **`c` carries `O_{w′}`-spans to `O_w`-spans**, coordinatewise, for `w′` the place conjugate to `w` under `c`
(`TwistPair.exists_comapPlace`): `c` is additive and `c(a·v) = c(a)·c(v)`, with `c(O_{w′}) = O_w`. -/
theorem span_map_ringEquiv (c : L ≃+* L) {w w' : HeightOneSpectrum (𝓞 L)} (hww : ∀ x, x ∈ Ow w' ↔ c x ∈ Ow w)
    (S : Set (Fin n → L)) :
    ((Submodule.span (Ow w) ((fun v i => c (v i)) '' S) : Submodule (Ow w) (Fin n → L)) : Set (Fin n → L)) =
      (fun v i => c (v i)) '' (Submodule.span (Ow w') S : Set (Fin n → L)) := by
  set f : (Fin n → L) → (Fin n → L) := fun v i => c (v i)
  have hadd (u v : Fin n → L) : f (u + v) = f u + f v := funext fun i => map_add c _ _
  have hsmul (a : L) (v : Fin n → L) : f (a • v) = c a • f v := funext fun i => map_mul c _ _
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, Submodule.subset_span hy, rfl⟩
    | zero => exact ⟨0, zero_mem _, funext fun i => map_zero c⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', add_mem hx' hy', hadd _ _⟩
    | smul a x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      have ha : c.symm (a : L) ∈ Ow w' := (hww _).2 (by rw [RingEquiv.apply_symm_apply]; exact a.2)
      refine ⟨(⟨_, ha⟩ : Ow w') • x', Submodule.smul_mem _ _ hx', ?_⟩
      show f (c.symm (a : L) • x') = (a : L) • f x'
      rw [hsmul, RingEquiv.apply_symm_apply]
  · rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      rw [show f 0 = 0 from funext fun i => map_zero c]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [hadd]
      exact add_mem hx hy
    | smul a x _ hx =>
      have ha : c (a : L) ∈ Ow w := (hww _).1 a.2
      show f ((a : L) • x) ∈ _
      rw [hsmul]
      exact Submodule.smul_mem _ (⟨_, ha⟩ : Ow w) hx

/-- **Conjugating a local basis**: for `c ∘ τ = τ ∘ conj_E`, a local basis `C` of `τ(N)` at `w′` gives the local
basis `c(C)` of `τ(N̄)` at `w`, as `τ(N̄) = c(τ(N))` (`span_map_ringEquiv`). -/
theorem isLocalBasis_map_conj (τ : E →+* L) (c : L ≃+* L) (hc : ∀ z, c (τ z) = τ (IsCMField.complexConj E z))
    {w w' : HeightOneSpectrum (𝓞 L)} (hww : ∀ x, x ∈ Ow w' ↔ c x ∈ Ow w) {N : Submodule (𝓞 E) (Fin n → E)}
    {C : Matrix (Fin n) (Fin n) L} (hC : IsLocalBasis w' τ N C) : IsLocalBasis w τ (cj N) (C.map c) := by
  refine ⟨?_, ?_⟩
  · have h := (c : L →+* L).map_det C
    rw [RingHom.mapMatrix_apply] at h
    rw [show C.map c = C.map (c : L →+* L) from rfl, ← h]
    exact (map_ne_zero _).2 hC.1
  · have h1 : (fun v i => τ (v i)) '' ((cj N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
        (fun v i => c (v i)) '' ((fun v i => τ (v i)) '' (N : Set (Fin n → E))) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨_, ⟨cv v, hv, rfl⟩, funext fun i => by simp [cv, hc]⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨cv u, show cv (cv u) ∈ N by rwa [cv_cv], funext fun i => ?_⟩
        simp [cv, hc]
    have h2 : Set.range (fun j i => C.map c i j) = (fun v i => c (v i)) '' Set.range (fun j i => C i j) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, h2]
    apply SetLike.coe_injective
    rw [span_map_ringEquiv c hww, span_map_ringEquiv c hww, hC.2]

omit [NumberField E] [IsCMField E] in
/-- **The local basis of a pseudo-basis lattice**: for generators `a_i ≠ 0` of `O_{L,w}·σ(𝔞_i)`, `σ(γ)·diag(a)` is a
local basis of `γ·D(𝔞)` (`isLocalBasis_diagonal`, moved by `γ`, `isLocalBasis_map`). -/
theorem isLocalBasis_pseudo (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E}
    (γ : GL (Fin n) E) {a : Fin n → L} (ha0 : ∀ i, a i ≠ 0)
    (ha : ∀ i, Submodule.span (Ow w) (σ '' ((𝔞 i : FractionalIdeal (𝓞 E)⁰ E) : Set E)) =
      Submodule.span (Ow w) {a i}) :
    IsLocalBasis w σ ((diagLat 𝔞).map (act γ)) (σ.mapMatrix (γ : Matrix (Fin n) (Fin n) E) * Matrix.diagonal a) :=
  isLocalBasis_map (isLocalBasis_diagonal (I := fun i => (𝔞 i : Submodule (𝓞 E) E)) ha0 ha) γ

omit [IsCMField E] in
/-- **Inverse ideals have inverse local generators**: for `𝔞 ≠ 0`, some `a ≠ 0` generates `O_{L,w}·σ(𝔞)` while `a⁻¹`
generates `O_{L,w}·σ(𝔞⁻¹)`. With `a` from `exists_gen`, localisation and extension are ring homs (`locw`, `extT`),
so `O_{L,w}·σ(𝔞⁻¹)·a = O_{L,w}·σ(𝔞⁻¹𝔞) = O_{L,w}`. -/
theorem exists_gen_inv (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) :
    ∃ a : L, a ≠ 0 ∧ Submodule.span (Ow w) (σ '' (𝔞 : Set E)) = Submodule.span (Ow w) {a} ∧
      Submodule.span (Ow w) (σ '' ((𝔞⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) = Submodule.span (Ow w) {a⁻¹} := by
  obtain ⟨a, ha0, hloc, hspan⟩ := exists_gen w σ h𝔞
  refine ⟨a, ha0, hspan, ?_⟩
  have h1 : locw w (extT σ 𝔞⁻¹) * FractionalIdeal.spanSingleton (Ow w)⁰ a = 1 := by
    rw [← hloc, ← map_mul, ← map_mul, inv_mul_cancel₀ h𝔞, map_one, map_one]
  have hinv : locw w (extT σ 𝔞⁻¹) = FractionalIdeal.spanSingleton (Ow w)⁰ a⁻¹ := by
    calc locw w (extT σ 𝔞⁻¹) = locw w (extT σ 𝔞⁻¹) * FractionalIdeal.spanSingleton (Ow w)⁰ a *
          FractionalIdeal.spanSingleton (Ow w)⁰ a⁻¹ := by
          rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ ha0,
            FractionalIdeal.spanSingleton_one, mul_one]
      _ = _ := by rw [h1, one_mul]
  rw [← span_Ow_extT]
  ext x
  rw [← mem_locw, hinv, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_spanSingleton]

omit [IsCMField E] in
/-- **Local bases exist** for every `O_E`-lattice, at every `w`: write `Y = γ·D(𝔞)` (`exists_pseudo`) and take
`σ(γ)·diag(a)` (`exists_gen`, `isLocalBasis_pseudo`). -/
theorem exists_isLocalBasis (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) (Y : Submodule (𝓞 E) (Fin n → E))
    [Y.IsLattice E] : ∃ C, IsLocalBasis w σ Y C := by
  obtain ⟨𝔞, γ, h𝔞, rfl⟩ := exists_pseudo Y
  choose a ha0 ha using fun i => exists_gen w σ (h𝔞 i)
  exact ⟨_, isLocalBasis_pseudo w σ γ ha0 fun i => (ha i).2⟩

end Local

/-! ## The Fock form under `c`, and twists -/

section Fock

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type} [Field L] [NumberField L]

omit [DecidableEq Φ] [NumberField L] in
/-- **Ring maps commute with twists**: `c(twist_C F) = twist_{c(C)} c(F)` (`map_lsub`, `RingHom.map_det`). -/
theorem map_twist (c : L →+* L) (lam : Φ → Fin n → ℤ) (C : Φ → Matrix (Fin n) (Fin n) L) (F : Pol Φ n L) :
    MvPolynomial.map c (twist lam C F) = twist lam (fun ρ => (C ρ).map c) (MvPolynomial.map c F) := by
  simp only [twist, map_mul, map_C, map_lsub, map_prod, map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]

omit [DecidableEq Φ] in
/-- **`c` carries `∇_{O_{w′}}` into `∇_{O_w}`**, for `w′` conjugate to `w` under `c`: bideterminants have integer
coefficients (`map_bidet'`), and `c(O_{w′}) ⊆ O_w`. -/
theorem map_mem_nablaInt (c : L ≃+* L) {w w' : HeightOneSpectrum (𝓞 L)} (hww : ∀ x, x ∈ Ow w' ↔ c x ∈ Ow w)
    {ν : Φ → Fin n → ℕ} {G : Pol Φ n L} (hG : G ∈ nablaInt (Ow w') ν) :
    MvPolynomial.map (c : L →+* L) G ∈ nablaInt (Ow w) ν := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨rows, rfl⟩ := hG
    rw [map_bidet']
    exact Submodule.subset_span ⟨rows, rfl⟩
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add G G' _ _ hG hG' =>
    rw [map_add]
    exact add_mem hG hG'
  | smul a G _ hG =>
    have ha : c (a : L) ∈ Ow w := (hww _).1 a.2
    have e : MvPolynomial.map (c : L →+* L) (a • G) =
        (⟨c a, ha⟩ : Ow w) • MvPolynomial.map (c : L →+* L) G := by
      rw [Subring.smul_def, Subring.smul_def, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hG

omit [NumberField L] in
/-- **`∇_A` and `Δ_A` pair into `A`**: `⟨P, Q⟩/κ ∈ A` for `P ∈ ∇_A(ν)` and `Q ∈ Δ_A(ν)`, by the definition of `Δ_A`
on the bideterminants (`fock_comm`) and bilinearity. -/
theorem fock_div_mem_of_nablaInt_Delta {A : Subring L} {ν : Φ → Fin n → ℕ} {P Q : Pol Φ n L}
    (hP : P ∈ nablaInt A ν) (hQ : Q ∈ Delta A ν) :
    fockWith (RingHom.id L) P Q / fockWith (RingHom.id L) (hw L ν) (hw L ν) ∈ A := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨rows, rfl⟩ := hP
    rw [fock_comm]
    exact hQ.2 rows
  | zero => simp [fockWith]
  | add P P' _ _ hP hP' =>
    rw [fock_add_left, add_div]
    exact A.add_mem hP hP'
  | smul a P _ hP =>
    rw [Subring.smul_def, fock_smul_left, mul_div_assoc]
    exact A.mul_mem a.2 hP

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- The `c`-Fock form is the bilinear Fock form of `c(P)` and `Q`. -/
theorem fockWith_eq_map (c : L →+* L) (P Q : Pol Φ n L) :
    fockWith c P Q = fockWith (RingHom.id L) (MvPolynomial.map c P) Q := by
  simp only [fockWith, coeff_map, RingHom.id_apply]

omit [DecidableEq Φ] [NumberField L] in
/-- The `c`-Fock form is linear in its second argument: scalars. -/
theorem fockWith_smul_right (c : L →+* L) (P Q : Pol Φ n L) (a : L) :
    fockWith c P (a • Q) = a * fockWith c P Q := by
  rw [fockWith_eq_map, smul_eq_C_mul, fock_C_mul_right, ← fockWith_eq_map]

omit [DecidableEq Φ] in
/-- **`κ` over `L`**: the rational `HermForms.kappa λ` is the Fock norm of `hw_ν` over `L`, `ν = natW λ`
(`WeylSandwich.fock_hw_eq_kapN`, `WeylSandwich.kapN_cast`). -/
theorem kappa_cast (lam : Φ → Fin n → ℤ) :
    (kappa lam : L) = fockWith (RingHom.id L) (hw L fun ρ => natW (lam ρ)) (hw L fun ρ => natW (lam ρ)) := by
  rw [WeylSandwich.fock_hw_eq_kapN,
    show kappa lam = ((WeylSandwich.kapN fun ρ => natW (lam ρ) : ℕ) : ℚ) from (WeylSandwich.kapN_cast _).symm,
    Rat.cast_natCast]

/-- **Adjointness of twists**, for the bilinear Fock form: `⟨twist_g F, G⟩ = ⟨F, twist_{gᵀ} G⟩`
(`LocalLattice.nf_twist`, with the normaliser `κ ≠ 0` cleared). -/
theorem fock_twist (lam : Φ → Fin n → ℤ) (g : Φ → Matrix (Fin n) (Fin n) L) (F G : Pol Φ n L) :
    fockWith (RingHom.id L) (twist lam g F) G = fockWith (RingHom.id L) F (twist lam (fun ρ => (g ρ)ᵀ) G) := by
  have h := LocalLattice.nf_twist lam g F G
  simp only [LocalLattice.nf_apply] at h
  exact (div_left_inj' (by simpa using (kappa_pos lam).ne')).1 h

end Fock

/-! ## Pair: `Δ_Y` against `Δ_{Y^#}` -/

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L] [NumberField L]

/-- **Pair: the `c`-twisted pairing of `Δ_Y` with `Δ_{Y^#}` is integral.** For `c ∘ τ_ρ = τ_ρ ∘ conj_E`, an
`O_E`-lattice `Y`, `P ∈ Δ_Y(λ)` and `Q ∈ Δ_{Y^#}(λ)`: `fock_c(P, Q)/κ ∈ O_L`. At `w`, with `w′` conjugate to `w` and
`Y = γ·D(𝔞)`, the local bases `B = τ(γ)·diag(a)` of `Y` and `B′ = τ((γᵀ)⁻¹)·diag(a⁻¹)` of `(γᵀ)⁻¹·D(𝔞⁻¹)` at `w′`
(`exists_gen_inv`) give `c(B′)`, a local basis of `Y^#` at `w` (`dual_pseudo`), with `c(B′)·c(B)ᵀ = 1`; the twist of
`c(P)` by `c(B)` lies in `∇_{O_w}`, that of `Q` by `c(B′)` in `Δ_{O_w}`, and the twists cancel (`fock_twist`). -/
theorem pair_mem_one (τ : Φ → (E →+* L)) (c : L ≃+* L) (hc : ∀ ρ z, c (τ ρ z) = τ ρ (IsCMField.complexConj E z))
    {lam : Φ → Fin n → ℤ} (hlam : ∀ ρ, Antitone (lam ρ)) {Y : Submodule (𝓞 E) (Fin n → E)} [Y.IsLattice E]
    {P Q : Pol Φ n L} (hP : P ∈ DeltaN τ lam Y) (hQ : Q ∈ DeltaN τ lam (dual Y)) :
    fockWith (c : L →+* L) P Q / (kappa lam : L) ∈ (1 : Submodule (𝓞 L) L) := by
  have hνa : ∀ ρ, Antitone (natW (lam ρ)) := fun ρ => natW_antitone (hlam ρ)
  obtain ⟨𝔞, γ, h𝔞, rfl⟩ := exists_pseudo Y
  rw [dual_pseudo h𝔞] at hQ
  refine mem_one_of_forall_Ow fun w => ?_
  obtain ⟨w', hww⟩ := TwistPair.exists_comapPlace c w
  choose a ha0 ha ha' using fun (ρ : Φ) (i : Fin n) => exists_gen_inv w' (τ ρ) (h𝔞 i)
  let B : Φ → Matrix (Fin n) (Fin n) L := fun ρ =>
    (τ ρ).mapMatrix (γ : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (a ρ)
  let B' : Φ → Matrix (Fin n) (Fin n) L := fun ρ =>
    (τ ρ).mapMatrix (((tGL γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      Matrix.diagonal (fun i => (a ρ i)⁻¹)
  have hB : ∀ ρ, IsLocalBasis w' (τ ρ) ((diagLat 𝔞).map (act γ)) (B ρ) := fun ρ =>
    isLocalBasis_pseudo w' (τ ρ) γ (ha0 ρ) (ha ρ)
  have hB' : ∀ ρ, IsLocalBasis w' (τ ρ) ((diagLat fun i => (𝔞 i)⁻¹).map (act (tGL γ)⁻¹)) (B' ρ) := fun ρ =>
    isLocalBasis_pseudo w' (τ ρ) (𝔞 := fun i => (𝔞 i)⁻¹) (tGL γ)⁻¹ (fun i => inv_ne_zero (ha0 ρ i)) (ha' ρ)
  have hcB' : ∀ ρ, IsLocalBasis w (τ ρ) (cj ((diagLat fun i => (𝔞 i)⁻¹).map (act (tGL γ)⁻¹)))
      ((B' ρ).map (c : L →+* L)) :=
    fun ρ => isLocalBasis_map_conj (τ ρ) c (hc ρ) hww (hB' ρ)
  have hBB : ∀ ρ, (B' ρ).map (c : L →+* L) * ((B ρ).map (c : L →+* L))ᵀ = 1 := by
    intro ρ
    have e : B' ρ * (B ρ)ᵀ = 1 := by
      simp only [B, B', Matrix.transpose_mul, Matrix.diagonal_transpose]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal,
        show (fun i => (a ρ i)⁻¹ * a ρ i) = fun _ => (1 : L) from funext fun i => inv_mul_cancel₀ (ha0 ρ i),
        Matrix.diagonal_one, Matrix.one_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        ← Matrix.transpose_map, ← Matrix.map_mul,
        show (((tGL γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (γ : Matrix (Fin n) (Fin n) E)ᵀ = 1 from
          Units.inv_mul (tGL γ), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.transpose_map, ← Matrix.map_mul, e, Matrix.map_one _ (map_zero _) (map_one _)]
  have hP1 : twist lam B P ∈ Delta (Ow w') fun ρ => natW (lam ρ) := (DeltaN_subset_DeltaA τ lam hP).2 w' B hB
  have hP2 : twist lam (fun ρ => (B ρ).map (c : L →+* L)) (MvPolynomial.map (c : L →+* L) P) ∈
      nablaInt (Ow w) fun ρ => natW (lam ρ) := by
    rw [← map_twist]
    exact map_mem_nablaInt c hww (WeylSandwich.Delta_subset_nablaInt (Ow w') hνa hP1)
  have hQ1 : twist lam (fun ρ => (B' ρ).map (c : L →+* L)) Q ∈ Delta (Ow w) fun ρ => natW (lam ρ) :=
    (DeltaN_subset_DeltaA τ lam hQ).2 w _ hcB'
  have key := fock_div_mem_of_nablaInt_Delta hP2 hQ1
  rwa [fock_twist, twist_twist, show (fun ρ => (B' ρ).map (c : L →+* L) * ((B ρ).map (c : L →+* L))ᵀ) =
    fun _ => (1 : Matrix (Fin n) (Fin n) L) from funext hBB, twist_one, ← fockWith_eq_map, ← kappa_cast] at key

end Pair

/-! ## Sub: shrinking the lattice costs only the negative determinant twists -/

section Sub

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {Φ : Type} [Fintype Φ] [DecidableEq Φ]
  {L : Type} [Field L] [NumberField L]

/-- **The negative part of the determinant twists**, `negW λ = Σ_ρ max(0, −λ_{ρ,n−1})`. -/
def negW (lam : Φ → Fin n → ℤ) : ℕ := ∑ ρ, (-detShift (lam ρ)).toNat

/-- **The determinant twist of an integral matrix with an integral cofactor**: for `S`, `S′` with entries in `A` and
`S′·S = m·1`, `(mⁿ)^{max(0, −s)}·det(S)^s ∈ A`: `det(S)^s` for `s ≥ 0`, `det_zpow_mem` for `s < 0`. -/
theorem pow_toNat_mul_det_zpow_mem {A : Subring L} {S S' : Matrix (Fin n) (Fin n) L} (hS : ∀ i j, S i j ∈ A)
    (hS' : ∀ i j, S' i j ∈ A) {m : ℤ} (hm : m ≠ 0) (h : S' * S = (m : L) • 1) (s : ℤ) :
    ((m : L) ^ n) ^ (-s).toNat * S.det ^ s ∈ A := by
  rcases le_or_gt 0 s with hs | hs
  · rw [Int.toNat_eq_zero.2 (by omega), pow_zero, one_mul]
    lift s to ℕ using hs
    rw [zpow_natCast]
    exact A.pow_mem (det_mem hS) _
  · rw [show (-s).toNat = s.natAbs by omega]
    exact det_zpow_mem hS hS' hm h s

/-- **Sub: shrinking the lattice.** For `O_E`-lattices `Y₁ ⊆ Y₂` with `m·Y₂ ⊆ Y₁`, `m ≠ 0`:
`m^{n·negW λ}·Δ_{Y₂} ⊆ Δ_{Y₁}`. At `w`, local bases `C₁` of `Y₁` and `C₂` of `Y₂` satisfy `C₁ = C₂·S` and
`m·C₂ = C₁·S′` with `S`, `S′` over `O_{L,w}` (`exists_mul_eq_of_span_le`), so `S′·S = m·1`; the twist by `C₁` is
`det(S)^λ` times the substitution by `S` of the twist by `C₂`, which keeps `Δ_{O_{L,w}}` (`lsub_mem_Delta`), and
`m^{n·negW λ}·det(S)^λ` is integral (`pow_toNat_mul_det_zpow_mem`). The substitution is integral (the lattice
shrinks), so the polynomial degree never enters. -/
theorem pow_smul_mem_DeltaN_of_le (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)
    {Y₁ Y₂ : Submodule (𝓞 E) (Fin n → E)} [Y₁.IsLattice E] (h12 : Y₁ ≤ Y₂) {m : ℤ} (hm : m ≠ 0)
    (h21 : ∀ x ∈ Y₂, (m : E) • x ∈ Y₁) {F : Pol Φ n L} (hF : F ∈ DeltaN τ lam Y₂) :
    ((m : L) ^ (n * negW lam)) • F ∈ DeltaN τ lam Y₁ := by
  refine ⟨Submodule.smul_mem _ _ hF.1, fun w => ?_⟩
  obtain ⟨C₂, hC₂, hG⟩ := hF.2 w
  choose C₁ hC₁ using fun σ => exists_isLocalBasis w (τ σ) Y₁
  refine ⟨C₁, hC₁, ?_⟩
  have hsub : ∀ σ, Submodule.span (Ow w) (Set.range fun j i => C₁ σ i j) ≤
      Submodule.span (Ow w) (Set.range fun j i => C₂ σ i j) := by
    intro σ
    rw [← (hC₁ σ).2, ← (hC₂ σ).2]
    exact Submodule.span_mono (Set.image_mono h12)
  have hsub' : ∀ σ, Submodule.span (Ow w) (Set.range fun j i => ((m : L) • C₂ σ) i j) ≤
      Submodule.span (Ow w) (Set.range fun j i => C₁ σ i j) := by
    intro σ
    rw [← (hC₁ σ).2, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (fun i => C₂ σ i j) ∈ Submodule.span (Ow w) ((fun v i => τ σ (v i)) '' (Y₂ : Set (Fin n → E))) := by
      rw [(hC₂ σ).2]
      exact Submodule.subset_span ⟨j, rfl⟩
    have key : ∀ v ∈ Submodule.span (Ow w) ((fun v i => τ σ (v i)) '' (Y₂ : Set (Fin n → E))),
        (m : L) • v ∈ Submodule.span (Ow w) ((fun v i => τ σ (v i)) '' (Y₁ : Set (Fin n → E))) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨y, hy, rfl⟩ := hv
        refine Submodule.subset_span ⟨(m : E) • y, h21 y hy, funext fun i => ?_⟩
        simp
      | zero =>
        rw [smul_zero]
        exact zero_mem _
      | add u v _ _ hu hv =>
        rw [smul_add]
        exact add_mem hu hv
      | smul a v _ hv =>
        rw [smul_comm]
        exact Submodule.smul_mem _ _ hv
    convert key _ hj using 1
  choose S hS hCS using fun σ => exists_mul_eq_of_span_le (hsub σ)
  choose S' hS' hCS' using fun σ => exists_mul_eq_of_span_le (hsub' σ)
  have hSS : ∀ σ, S' σ * S σ = (m : L) • 1 := by
    intro σ
    have hinv : (C₁ σ)⁻¹ * C₁ σ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hC₁ σ).1)
    calc S' σ * S σ = (C₁ σ)⁻¹ * C₁ σ * (S' σ * S σ) := by rw [hinv, Matrix.one_mul]
      _ = (C₁ σ)⁻¹ * ((C₁ σ * S' σ) * S σ) := by simp only [Matrix.mul_assoc]
      _ = (C₁ σ)⁻¹ * ((m : L) • C₁ σ) := by rw [← hCS', Matrix.smul_mul, ← hCS]
      _ = (m : L) • 1 := by rw [Matrix.mul_smul, hinv]
  have e : twist lam C₁ ((m : L) ^ (n * negW lam) • F) =
      ((m : L) ^ (n * negW lam) * ∏ σ, (S σ).det ^ detShift (lam σ)) • lsub S (twist lam C₂ F) := by
    rw [twist_smul, show C₁ = fun σ => C₂ σ * S σ from funext hCS, ← twist_twist]
    set G := twist lam C₂ F
    rw [twist, C_mul', smul_smul]
  rw [e]
  refine smul_mem_Delta (lsub_mem_Delta hS hG) ?_
  rw [pow_mul, negW, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Subring.prod_mem _ fun σ _ => pow_toNat_mul_det_zpow_mem (hS σ) (hS' σ) hm (hSS σ) _

end Sub

/-! ## The attached lattice, and the twisted Petersson form on integral forms -/

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L] [NumberField L]
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/-- **`Lsh(d)^# ⊆ Lsh(d)`** for unimodular `N = d.N`: `Lsh(d)^# ⊆ N^# = N ⊆ Lsh(d)` (`dual` is antitone, `le_Lsh`). -/
theorem dual_Lsh_le {d : Deco E n ST SG} (hd : IsUnimodular d.N) : dual (Lsh d) ≤ Lsh d := by
  intro x hx
  have hN : x ∈ dual d.N := mem_dual.2 fun y hy => mem_dual.1 hx y (le_Lsh hd hy)
  rw [hd] at hN
  exact le_Lsh hd hN

/-- **`m²·Lsh(d) ⊆ Lsh(d)^#`** for unimodular `d.N` and an integer `m` in every `P ∈ ST`: for `x, y ∈ Lsh(d)`,
`h(y, m²x) = h(my, mx) ∈ h(N, N) ⊆ O_E` (`smul_Lsh_mem`, `herm_mem_one`). -/
theorem sq_smul_mem_dual_Lsh {d : Deco E n ST SG} (hd : IsUnimodular d.N) {m : ℤ}
    (hm : ∀ P ∈ ST, (m : 𝓞 E) ∈ P.asIdeal) {x : Fin n → E} (hx : x ∈ Lsh d) :
    ((m ^ 2 : ℤ) : E) • x ∈ dual (Lsh d) := by
  refine mem_dual.2 fun y hy => ?_
  have h := herm_mem_one hd (smul_Lsh_mem hd hm hy) (smul_Lsh_mem hd hm hx)
  rw [herm_smul_left, herm_smul_right, map_intCast, ← mul_assoc] at h
  rw [herm_smul_right]
  convert h using 2
  push_cast
  ring

variable {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}

variable (ST Λ) in
/-- **The `c`-twisted Petersson form** `H_c(F, G) = Σᶠ_cl mass(cl)·fock_c(F(rep cl), G(rep cl))/κ ∈ L`, for a ring
endomorphism `c` of `L`. For `c` complex conjugation at the place `v₀`, `σ_{v₀}(H_c)` is the Petersson form at `v₀`;
at the other places it need not be hermitian. -/
noncomputable def petTw (c : L →+* L) (lam : Φ → Fin n → ℤ) (F G : Fn ST Λ Φ L) : L :=
  classSum (fun cl : DCl E n ST Λ => fockWith c (F cl.out) (G cl.out)) / (kappa lam : L)

/-- A class with trivial stabiliser has mass `1`. -/
theorem mass_eq_one {cl : DCl E n ST Λ} (hst : stab cl = ⊥) : mass cl = 1 := by
  rw [mass, hst, Subgroup.card_bot, Nat.cast_one, inv_one]

/-- **One class**: for integral forms `F`, `G` and a class `cl`, `m^{2n·negW λ}·fock_c(F(cl), G(cl))/κ ∈ O_L`. Sub
for `Lsh^# ⊆ Lsh` with `m²` (`dual_Lsh_le`, `sq_smul_mem_dual_Lsh`) puts `m^{2n·negW λ}·G(cl)` in `Δ_{Lsh^#}`, and
Pair for `Y = Lsh(rep cl)` applies. -/
theorem fockWith_mem_of_Mint (τ : Φ → (E →+* L)) (χ : Λ →* L) {lam : Φ → Fin n → ℤ}
    (hlam : ∀ ρ, Antitone (lam ρ)) (c : L ≃+* L) (hc : ∀ ρ z, c (τ ρ z) = τ ρ (IsCMField.complexConj E z))
    {m : ℤ} (hm0 : m ≠ 0) (hm : ∀ P ∈ ST, (m : 𝓞 E) ∈ P.asIdeal) {F G : Fn ST Λ Φ L}
    (hF : F ∈ Mint ST τ χ lam) (hG : G ∈ Mint ST τ χ lam) (cl : DCl E n ST Λ) :
    (m : L) ^ (2 * n * negW lam) * fockWith (c : L →+* L) (F cl.out) (G cl.out) / (kappa lam : L) ∈
      (1 : Submodule (𝓞 L) L) := by
  have hd : IsUnimodular (DCl.rep cl).N := (show (cl.out : Deco E n ST SG).Good from cl.out.2).unimod
  have : (Lsh (DCl.rep cl)).IsLattice E := isLattice_Lsh hd
  have hG' : ((m ^ 2 : ℤ) : L) ^ (n * negW lam) • G cl.out ∈ DeltaN τ lam (dual (Lsh (DCl.rep cl))) :=
    pow_smul_mem_DeltaN_of_le τ lam (dual_Lsh_le hd) (pow_ne_zero 2 hm0) (fun x hx => sq_smul_mem_dual_Lsh hd hm hx)
      (hG.2 cl)
  have h := pair_mem_one τ c hc hlam (hF.2 cl) hG'
  rw [fockWith_smul_right] at h
  convert h using 3
  push_cast
  ring

/-- **Theorem B: the twisted Petersson form is integral up to `m^{2n·negW λ}` on integral forms.** For a ring
automorphism `c` of `L` with `c ∘ τ_ρ = τ_ρ ∘ conj_E`, trivial stabilisers, a nonzero integer `m` in every place of
`ST`, and integral forms `F`, `G`: `m^{2n·negW λ}·H_c(F, G) ∈ O_L`. Every class has mass `1`, each term is integral
(`fockWith_mem_of_Mint`), and integrality passes to the `finsum` (`finsum_induction`). -/
theorem petTw_mem_of_Mint (τ : Φ → (E →+* L)) (χ : Λ →* L) {lam : Φ → Fin n → ℤ} (hlam : ∀ ρ, Antitone (lam ρ))
    (c : L ≃+* L) (hc : ∀ ρ z, c (τ ρ z) = τ ρ (IsCMField.complexConj E z))
    (hst : ∀ cl : DCl E n ST Λ, stab cl = ⊥) {m : ℤ} (hm0 : m ≠ 0) (hm : ∀ P ∈ ST, (m : 𝓞 E) ∈ P.asIdeal)
    {F G : Fn ST Λ Φ L} (hF : F ∈ Mint ST τ χ lam) (hG : G ∈ Mint ST τ χ lam) :
    (m : L) ^ (2 * n * negW lam) * petTw ST Λ (c : L →+* L) lam F G ∈ (1 : Submodule (𝓞 L) L) := by
  rw [petTw, classSum, mul_div_assoc']
  refine finsum_induction (fun x => (m : L) ^ (2 * n * negW lam) * x / (kappa lam : L) ∈ (1 : Submodule (𝓞 L) L))
    (by rw [mul_zero, zero_div]; exact zero_mem _) (fun x y hx hy => by rw [mul_add, add_div]; exact add_mem hx hy)
    fun cl => ?_
  rw [mass_eq_one (hst cl), one_smul]
  exact fockWith_mem_of_Mint τ χ hlam c hc hm0 hm hF hG cl

end Forms

end HermForms
