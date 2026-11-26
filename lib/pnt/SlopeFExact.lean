import SlopeV
import FormSlopeExact

/-!
# The piece (F) + (V) from the exact slope bound

`SharpObj.SlopeFV` for an object whose sources are the whole cut (`X_c = ⊤`, the archive's choice), with antitone
step-0 weights and `c_F` at least the exact constant of every word (`SharpObj.slopeFV_exact`). The index bookkeeping
(V) reduces the piece to `μ_arch(M_ω) ≥ −c_F` in every realising frame (`SharpObj.slopeFV_of_slopeM`), and the exact
bound gives it (`HermForms.muArch_source_ge`): the frame's source metric is the Petersson Gram matrix
(`SharpObj.RealWith`), the lattice is the span of the integral forms of the cut in the frame's coordinates, and the
level group `uniUT` is unipotent at the places of `SG` over the design's split primes `g₀ ≠ g₁`, which the pins
supply (`SharpObj.exists_SG_over`). What is left of the piece is the construction's: `X_c = ⊤`, the weights, and
the budget `c_F ≤ x^ε Σ_t a_t/8`, where the exact constant `3|ν| log n + 2(Σλ)⁺ Σ_P log N(P)/(n[E:ℚ]) + |ST| log 2`
is of size `Σ_t a_t·log x` at the archive's sizes.
-/

namespace ZetaBalance.SharpObj

open NumberField IsDedekindDomain HermForms

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

/-- **A place of `SG` over each split prime of the design**: from the pin that every place over `g₀g₁` is in `SG`
or conjugate to a place of `SG`, a rational prime `g ∣ g₀g₁` lies in some place of `SG`. -/
theorem exists_SG_over {u : S.A} (hP : b.Pinned u) {g : ℕ} (hg : g.Prime) (hgd : g ∣ Dg.g₀ * Dg.g₁) :
    ∃ w : b.SG, (g : 𝓞 S.E) ∈ w.1.asIdeal := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, hSG, -⟩, -⟩ := hP
  -- a prime of `O_E` over `g` (lying over, `O_E` integral over `ℤ`)
  have hgp : (Ideal.span {(g : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.ne_zero)).2 (Nat.prime_iff_prime_int.1 hg)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(g : ℤ)})
    (⊥ : Ideal (𝓞 S.E)) (by
      rw [Ideal.under, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 S.E)).injective_int]
      exact bot_le)
  have hgQ : (g : 𝓞 S.E) ∈ Q := by
    have : (g : ℤ) ∈ Q.under ℤ := hQc ▸ Ideal.subset_span rfl
    simpa [Ideal.under] using this
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    have : (g : 𝓞 S.E) = 0 := (Submodule.mem_bot _).1 hgQ
    exact hg.ne_zero (by exact_mod_cast this)
  let v : HeightOneSpectrum (𝓞 S.E) := ⟨Q, hQ, hQ0⟩
  have hv : ((Dg.g₀ * Dg.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hgd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hgQ
  rcases hSG v hv with hvS | ⟨w, hwS, hw⟩
  · exact ⟨⟨v, hvS⟩, hgQ⟩
  · refine ⟨⟨w, hwS⟩, ?_⟩
    have : (g : 𝓞 S.E) ∈ w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj S.E : 𝓞 S.E →+* 𝓞 S.E) :=
      hw ▸ hgQ
    simpa using this


open Classical in
/-- **(F) + (V) from the exact slope bound**: for an object pinned at `u` whose sources are the whole cut
(`X_c = ⊤`), with antitone step-0 weights and `0 ≤ c_F ≤ x^ε Σ_t a_t/8` at least the exact constant
`HermForms.cFx` of every word, the piece `SlopeFV` holds. -/
theorem slopeFV_exact {u : S.A} (hP : b.Pinned u) (hXc : ∀ ω, b.Xc ω = ⊤) (hlam : ∀ ω ρ, Antitone (b.lam0 ω ρ))
    (h0 : 0 ≤ b.cF) (hcF : ∀ ω, cFx b.n0 (b.lam0 ω) (b.ST ω) ≤ b.cF)
    (h1 : b.cF ≤ x ^ ε * (∑ s ∈ Dg.TT, Dg.a s) / 8) : b.SlopeFV := by
  obtain ⟨w₀, h₀⟩ := b.exists_SG_over hP Dg.g₀_prime (dvd_mul_right _ _)
  obtain ⟨w₁, h₁⟩ := b.exists_SG_over hP Dg.g₁_prime (dvd_mul_left _ _)
  refine b.slopeFV_of_slopeM h0 h1 fun F c eC hF ω => ⟨b.isLattice_map_M ω (hlam ω) (c ω), ?_⟩
  -- the frame's coordinates of the whole cut
  have hV : b.Xc ω ⊓ Vω (b.ST ω) C.τK (b.χ0 ω) (b.lam0 ω) = Vω (b.ST ω) C.τK (b.χ0 ω) (b.lam0 ω) := by
    rw [hXc, top_inf_eq]
  let c' := (LinearEquiv.ofEq _ _ hV).symm.trans ((b.e ω).symm.trans (c ω))
  have hc' (y : F.n ω → C.K) : (c'.symm y : Fn (b.ST ω) (ThetaChain.uniUT b.SG b.n0) (Φ S.A) C.K) =
      (b.e ω ((c ω).symm y) : Fn (b.ST ω) (ThetaChain.uniUT b.SG b.n0) (Φ S.A) C.K) := rfl
  refine (neg_le_neg (hcF ω)).trans (muArch_source_ge C.τK (b.χ0 ω) (b.lam0 ω) (hlam ω) w₀ w₁ Dg.g₀_prime
    Dg.g₁_prime Dg.g₀_ne_g₁ h₀ h₁ (HermClasses.uniAt_uniUT _) (HermClasses.uniAt_uniUT _) c' _ ?_ ?_)
  · -- the lattice: the integral forms of the cut, in the frame's coordinates
    show (b.M ω).map _ = _
    rw [M, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨⟨_, (Submodule.mem_inf.1 (b.e ω φ).2).2⟩, hφ, ?_⟩
      have he : (LinearEquiv.ofEq _ _ hV).symm ⟨_, (Submodule.mem_inf.1 (b.e ω φ).2).2⟩ = b.e ω φ :=
        Subtype.ext rfl
      simp only [c', LinearEquiv.trans_apply, he, LinearEquiv.symm_apply_apply]
      rfl
    · rintro ⟨G, hG, rfl⟩
      refine ⟨(b.e ω).symm (LinearEquiv.ofEq _ _ hV |>.symm G), ?_, by simp [c']⟩
      simpa using hG
  · -- the metric: the Petersson Gram matrix
    intro v i j
    rw [hc', hc']
    exact hF.2.2.2.2.1 ω v i j

end ZetaBalance.SharpObj
