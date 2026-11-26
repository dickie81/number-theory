import SharpAdm
import CoeffField
import QuadSub

/-!
# The setting-level data of the construction

The data of the construction of the six-term frontier's proof (`SharpInputs`, the field `SharpPieces.cons`) that do
not depend on the theta chain: the setting's coefficient field (`sharpField`), the elements of norm `p` and their
places, the auxiliary prime of each translate and its places `ST`, the level places `SG` and the step-0 weights. The
explicit Stage-U theta chain, the coefficient field it needs and the assembled construction `sharpCons` are in
`SharpChainU`. The order is forced: the chain's field (`ChainField`) reads `sharpField` (its fallback) and `sharpSG`
(its local constants), so this module comes first. The pieces proved so far (`SharpCores`: (T) and (F) + (V)) read
only the data defined here.

**The setting's coefficient field** (`sharpField`) depends on the setting alone: `K ⊆ ℂ` is the normal closure of the
images `τ_ρ(b_i)` of a `ℚ`-basis of `E` (`CoeffField.coeffClosure`), a number field, normal over `ℚ`. The chain's
field `ChainField.chainField` contains it, and falls back to it when its generators are not finite-dimensional.

**The auxiliary prime** (`sharpT`, one per translate): the least prime `T` with `ArithT` and
`Λ_u − x^{2ε} < log T ≤ Λ_u − x^{2ε} + log 2`, which `ShortNorm` gives once `x` is large; `2` if there is none. The
window sits `x^{2ε}` below `Λ_u` (`sharpCT`, the slack `c_T` of (T)): the second-moment route to the rank of the
period map needs `T` below a threshold `T*` with `Λ_u − log T* ≈ x^{7ε/8}`, and the shift puts it there with room,
at a cost of `x^{2ε}Σ_t a_t` in the budget. Its element
`π_T = (a + b√−d)/2` (`sharpTz`) is the `halfO` of `QuadSub` at the `(a, b)` of `ArithT`, and the places `ST` are
those over `conj π_T` (`sharpST`). The places `SG` are those over `conj π_{g₀}` and `conj π_{g₁}` (`sharpSG`), with
`π_g` from the design's split data (A11). One definition serves both elements (`normPi`): `(a + b√−d)/2` of norm `p`
at a modulus `M`, `1` if there is no such `(a, b)`; and `placesOf z` is the finite set of places over `z`.

**Step 0** (`n0 = k`, `λ_0 = wt_0(hc u)`): the archive's step-0 weights of the base word (`sharpLam0`).
-/

namespace ZetaBalance

open NumberField IsDedekindDomain CoeffField

noncomputable section

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}

/-! ## The setting's coefficient field -/

/-- **The generators of the coefficient field**: the images `τ_ρ(b_i)`, over all `ρ`, of a `ℚ`-basis `b` of `E`. -/
def sharpGens (S : Setting) : Set ℂ :=
  Set.range fun p : Φ S.A × Fin (Module.finrank ℚ S.E) => S.τ p.1 (Module.finBasis ℚ S.E p.2)

/-- **The generators are algebraic**: `τ_ρ` maps the algebraic `b_i` to algebraic numbers. -/
theorem isIntegral_sharpGens : ∀ z ∈ sharpGens S, IsIntegral ℚ z := by
  rintro _ ⟨p, rfl⟩
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) (Module.finBasis ℚ S.E p.2)).map (S.τ p.1).toRatAlgHom

/-- **The setting's coefficient field** `K ⊆ ℂ`: the normal closure of `ℚ(τ_ρ(E) : ρ)` (`coeffClosure`). -/
def sharpField (S : Setting) : IntermediateField ℚ ℂ := coeffClosure (sharpGens S)

/-- **`τ_ρ` lands in the coefficient field**, as the images of a basis do (`CoeffField.map_mem_of_basis`). -/
theorem τ_mem_sharpField (ρ : Φ S.A) (z : S.E) : S.τ ρ z ∈ sharpField S :=
  map_mem_of_basis (Module.finBasis ℚ S.E) (S.τ ρ) (fun i => subset_coeffClosure (sharpGens S) ⟨(ρ, i), rfl⟩) z

/-! ## Elements of norm `p` and their places -/

open Classical in
/-- **The element `π = (a + b√−d)/2` of norm `p` at the modulus `M`**: for `4p = a² + db²` with `M ∣ b` and
`a ≡ b + 2 (mod 2M)` (so `a ≡ b (mod 2)`) and `d ≡ 3 (mod 4)`, `QuadSub`'s `halfO` at some such `(a, b)` with
`√−d = gaussE`; `1` if there is none. At `M = N` it is the design's `π_g` (A11), at `M = QS·q·d·(g₀g₁)²` the
auxiliary prime's (`ArithT`). -/
def normPi (S : Setting) (M p : ℕ) : 𝓞 S.E :=
  if h : S.d % 4 = 3 ∧ ∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M] then
    Setting.halfO (S.gaussE_sq h.1) h.1 (a := h.2.choose) (b := h.2.choose_spec.choose)
      ((h.2.choose_spec.choose_spec.2.2.of_mul_right M).trans (Int.modEq_iff_dvd.2 ⟨-1, by ring⟩))
  else 1

open Classical in
/-- **The places over `z`**, `{v : z ∈ v}`, as a `Finset`: finite for `z ≠ 0` (`Ideal.finite_factors`); the dite
spares that proof here, and its `else` branch, `∅`, is taken only at `z = 0`. -/
def placesOf (z : 𝓞 S.E) : Finset (HeightOneSpectrum (𝓞 S.E)) :=
  if h : {v : HeightOneSpectrum (𝓞 S.E) | z ∈ v.asIdeal}.Finite then h.toFinset else ∅

/-! ## The places of a translate -/

/-- **The slack of (T)**: `c_T = x^{2ε}`, the depth of the auxiliary prime's window below `Λ_u`. -/
def sharpCT (x ε : ℝ) : ℝ := x ^ (2 * ε)

open Classical in
/-- **The auxiliary prime of the translate `u`** ((T), one per translate): the least prime `T` with `ArithT` and
`Λ_u − c_T < log T ≤ Λ_u − c_T + log 2`, `Λ_u = S.lam w_u v_E log(g₀g₁)`, `c_T = x^{2ε}` (`sharpCT`), which
`ShortNorm` gives once `x` is large (`SharpDesign.exists_prime_arithT`); `2` if there is none. -/
def sharpT (Dg : SharpDesign S κ x ε X) (u : S.A) : ℕ :=
  if h : ∃ T : ℕ, T.Prime ∧ Dg.ArithT T ∧
      S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) - sharpCT x ε < Real.log T ∧
      Real.log T ≤ S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) - sharpCT x ε + Real.log 2 then Nat.find h
  else 2

/-- **`π_T = (a + b√−d)/2`** for the `(a, b)` of `ArithT T`, `T` the translate's auxiliary prime (`normPi` at the
modulus `QS·q·d·(g₀g₁)²`); `1` if there is none. -/
def sharpTz (Dg : SharpDesign S κ x ε X) (u : S.A) : 𝓞 S.E :=
  normPi S (S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2) (sharpT Dg u)

/-- **The places `ST`** of the translate: those over `conj π_T`, `{v : v(conj π_T) < 1}`. -/
def sharpST (Dg : SharpDesign S κ x ε X) (u : S.A) : Finset (HeightOneSpectrum (𝓞 S.E)) :=
  placesOf (IsCMField.ringOfIntegersComplexConj S.E (sharpTz Dg u))

open Classical in
/-- **The places `SG`**: those over `conj π_{g₀}` and over `conj π_{g₁}`, with `π_g = (α + β√−d)/2` of norm `g` from
the design's split data (A11; `normPi` at the modulus `N`). -/
def sharpSG (Dg : SharpDesign S κ x ε X) : Finset (HeightOneSpectrum (𝓞 S.E)) :=
  placesOf (IsCMField.ringOfIntegersComplexConj S.E (normPi S S.N Dg.g₀)) ∪
    placesOf (IsCMField.ringOfIntegersComplexConj S.E (normPi S S.N Dg.g₁))

/-- **The step-0 weights** `λ_0 = wt_0(hc u)` on `Fin k` (`n0 = k`): the archive's step-0 weights of the base
word. -/
def sharpLam0 (Dg : SharpDesign S κ x ε X) (u : S.A) : Φ S.A → Fin Dg.R.k → ℤ :=
  Dg.R.wt0 (Dg.hc u) (by rw [zero_mul, add_zero])

end

end ZetaBalance
