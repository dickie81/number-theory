import LocalLattice

/-!
# Letters, the Fock form, the lift substitution and the flat model

The letter/Fock toolkit of the two local theorems of the gain (L5 and L6), at one orbit of an inert prime `p` in the
setting `Unram` of `InertModel`: polynomials in *letters* with the `gl_k` action and the Fock form, the Frobenius
congruence, the lift substitution `ℓ_g` with its normalised degree, and the flat model `θ°`, which identifies the dual
Weyl module of the flat weight `(d_s, 0, …, 0)` with the letter polynomials of multidegree `d`, together with its
lattices and its edge lattices.

**Conventions** (shared by L5's C9, C11, B4, B12–B16 and L6's N8–N15; fixed here once).
* *Coordinates.* There are `k` coordinates. At type `r` the coordinates `c < r` are the *plane* coordinates and the
  `c ≥ r` the *normal* (tangent) ones: for `r = 1` coordinate `0` is the plane, `1, …, k − 1` are tangent. In adapted
  coordinates an edge of type `r` is `D·W^k ⊂ W^k` with `D = diag(p on the plane)` (`planeDiag`).
* *Letters.* A letter `l` has `k` coordinates, the variables `(l, c)` (`LPol α k R`), a flag `vec l` (`true`: vector
  letter, `false`: covector letter) and an orbit position `pos l`, for the Frobenius twist. The flags follow `lamAt`:
  the positive part of `lamAt λ s` gives the vector letters of position `s`, the negative part the covector letters.
  L5's top model has the letters `(s, true)`, a vector letter of degree `a_s` at even `s` and `b_s` at odd `s`, and
  `(s, false)`, a covector letter of degree `b_s`, resp. `a_s`. L6's flat model has one letter per position, a vector
  letter at even `s` and a covector letter at odd `s` (`vecF`), as `lamAt` turns `(d_s, 0, …, 0)` into
  `(0, …, 0, −d_s)` at odd `s`.
* *The action, the weights, raising.* `E_{ab} = Σ_{vector} X_{l,a}∂_{l,b} − Σ_{covector} X_{l,b}∂_{l,a}` (`letE` for one
  letter); the weight of `X^μ` in coordinate `c` is `Σ_{vector} μ_{l,c} − Σ_{covector} μ_{l,c}`; `E_{ab}` with `a < b`
  is *raising*, and highest-weight vectors are those killed by the raising operators. The Fock form
  `⟨X^μ, X^ν⟩ = δ_{μν}·μ!` (`lfock`) is contravariant: `⟨E_{ab}F, G⟩ = ⟨F, E_{ba}G⟩` (`lfock_letE`). The tie model
  (B4, B12–B16) uses the same `E_{ab}` (its `+` letters are vector letters, its `−` letters covector letters) and the
  same Fock form, in the `k − 1` tangent coordinates renumbered from `0` (tangent coordinate `c + 1` is the tie model's
  column `c`); its column `ρ` is the last one, and the letter added by freezing is a covector letter.
* *The lift substitution* (`liftSub`, the `ℓ_g` of C9, C11 and the `Φ_g` of N8–N13): for `g ∈ GL_k(W)` and a letter
  at position `s`, `X_{l,c} ↦ Σ_b ϖ^{[b ≥ r]}·X_{l,b}·σ^s(g⁻¹)_{bc}` for a vector letter and
  `X_{l,c} ↦ Σ_b ϖ^{[b < r]}·X_{l,b}·σ^s(g)_{cb}` for a covector letter. So the *scaled* variables (`scaled`) are the
  normal coordinates of the vector letters and the plane coordinates of the covector letters, and `nd` counts them;
  `ord_g F ≥ i` means `OrdGe ϖ i (ℓ_g F)`. At `g = 1` it is the scaling of the scaled variables (`liftSub_one_X`).
* *Lines and planes.* `planeOf p r g` is the span over `W/p` of the rows `i < r` of `g⁻¹` modulo `p`, `lineOf` the
  case `r = 1`. For a basis `h` of a source lattice `L″ = h·W^k`, the edge *adapted to `g`* is the one with adapted
  basis `h·g^{−T}`: source `L″`, target `L = h·g^{−T}D^{−1}W^k`. In the coordinates of `h`, `pL/pL″ ⊆ L″/pL″` is the
  span of the columns `< r` of `g^{−T}`, that is `planeOf p r g`; `g = 1` gives the edge of the plane coordinates.
* *Odd positions* (L6, recomputed from `edgeLat`, `twist`, `lamAt` and `midBlk` in `thetaB_mem_edgeLat_iff`): on the
  flat model `ϖ` falls on the normal columns `c ≥ r` at even positions and on the plane columns `c < r` at odd
  positions; the edge condition is the order of the lift substitution, the factor `ϖ^{A_r}`, `A_r = Σ_{s even} d_s`,
  being absorbed by the even positions.

**The Fock form and contravariant forms.** `lfock` is the bilinear Fock form on polynomials in any variables (on block
polynomials it is `fockWith (RingHom.id K)`), with the adjunction `⟨F·X_v, G⟩ = ⟨F, ∂_vG⟩` (`lfock_mul_X`). A bilinear
form `B` on letter polynomials with `B(X_{l,a}∂_{l,b}P, Q) = B(P, X_{l,b}∂_{l,a}Q)` for `a ≠ b` is determined by its
value at an extreme monomial `X^ε` (the whole degree of each letter in one coordinate `e_l`, `extr`):
`B(P, Q)·∏_l d_l! = ⟨P, Q⟩·B(X^ε, X^ε)` on multidegree `d` (`bilin_eq_lfock`). By induction on the number of
non-extreme coordinates of `X^μ`, moving them to `e_l` one at a time: `X^μ` is a multiple of `X_v∂_{e}X^{μ'}`, and the
adjoint `X_e∂_v` lowers `X^ν` (`bilin_monomial`).

**Main results.**
* *Frobenius* (`frob_pow`): `σ^s(x) ≡ x^{p^s} (mod p)` on `W`, from `Unram.frob` by induction (`a − b ∣ a^n − b^n`).
* *Coefficient divisibility* (`liftSub_mem_gInt`): `ℓ_g` maps integral polynomials into the `ϖ`-graded integral
  subalgebra `gInt` (coefficient of `X^m` in `ϖ^{nd m}·O`): the twisted matrices are integral and `gInt` is a
  subalgebra, generated by the `ϖ^{[v scaled]}·X_v`.
* *The flat model* `θ°` (`theta0`): `X_{s,c} ↦ x_{s,c,0}` at even `s`, `X_{s,c} ↦ adj(x_s)_{k−1,c}` (the signed cofactor
  of the last column) at odd `s`; `k ≥ 2` throughout.
  - (Θ1) `θ°` maps multidegree `d` into `∇_{Kf}` of `flatWt d` (`theta0_mem_nabla`), injectively (`theta0_injOn`) and
    onto (`theta0_surj`).
  - (Θ2, the shape condition, `theta_shape`): a twist of `θ°` by invertible block matrices `g_b` is `c·θ°∘linSub A`,
    `c ≠ 0`, `A_s` invertible: `g_s` at even `s` and `adj(g_s)ᵀ` at odd `s` (`lsub_theta0`, from
    `adj(g·x) = adj(x)·adj(g)`).
  - (D12, the intertwining, `rowOp_theta0`): `R_{s,a,b}(θ°P) = θ°(E_{s,a,b}P)` for the row operators
    `R_{s,a,b} = Σ_c x_{s,a,c}∂_{s,b,c}`, with the vector action at even `s` and the covector action
    `δ_{ab}·deg − X_{s,b}∂_{s,a}` at odd `s` (`flatE`); nondegeneracy is `theta0_nondeg`.
  - (N2-e, the Fock comparison, `nf_theta0`): `nf(θ°P, θ°Q) = ⟨P, Q⟩/∏_s d_s!` on multidegree `d`.
  - (N2-b, `theta0_mem_nablaInt_iff`, `thetaB_mem_nab_iff`): `θ°P ∈ ∇_A` iff `P` has coefficients in `A`, for every
    subring `A ⊆ Kf`; so `Θ_h = twist_{ι σ^s(h)⁻¹} ∘ θ°` (`thetaB`) maps the integral letter polynomials onto
    `∇(h·W^k)`.
  - (N2-c, `thetaB_mem_edgeLat_iff`): for the edge adapted to `g` and `1 ≤ r < k`, `Θ_h F ∈ ϖ^i·𝓡(e)` iff
    `ord_g F ≥ i`.

**The routes.** D12 is checked on the letters, `R_{s,a,b}` and `E_{s,a,b}` being derivations (`derivation_comp`): on a
cofactor `C_c = det(x with row c replaced by e_{k−1})` the derivative of a determinant is the sum of the determinants
with one row differentiated (`derivation_det`), and only row `b` changes, to row `a`: two equal rows, the cofactor
itself, or `−C_b` after a swap (`rowOp_adj`). N2-e is `bilin_eq_lfock` for `B = nf(θ°·, θ°·)`: the row operators are
Fock-contravariant (`fock_rowOp`), so by D12 `B` is contravariant for the letters (`theta0_X_mul_pderiv`), and `θ°` of
the extreme monomial (coordinate `0` at even, `k − 1` at odd positions, `extF`) is the highest-weight vector
(`hw_flatWt`), of normalised norm `1`. For N2-b every bideterminant of the flat weight is `0` or `±θ°` of a monomial
(`bidet_flatWt`): a minor on the first `k − 1` columns with arbitrary rows is `0` or `±` the cofactor of the missing row
(`minor_eq_zero_or`, `adj_eq_minor`); conversely the bideterminants span `∇_{Kf}` (`span_bidet`) and `θ°` is injective,
so the monomials they give are all of them. For N2-c the midpoint blocks of the edge have the basis matrices
`ι σ^s(h g^{−T}D^{−1})·diag(ϖ on the plane)` (`isBasisOf_midBlk`), and the twist of `θ°` by
`G_s = σ^s(g⁻¹)ᵀ·diag(ϖ⁻¹ on the plane)` is `ϖ^{−A_r}·θ°∘ℓ_g` on multidegree `d` (`twist_theta0_liftSub`): by Θ2 the
letter change at a vector letter is `ϖ⁻¹·ℓ_g`, at a covector letter `adj(G_s)ᵀ = det(G_s)·σ^s(g)·diag(ϖ on the plane)`
is `det(G_s)·ℓ_g` (`map_eq_smul_of_row`), and the determinant twist `det(G_s)^{−d_s}` cancels it.

**Readings of the planning statements.** `liftSub` substitutes through `σ^s(g⁻¹)` rather than `σ^s(g)⁻¹`; they agree
for `g ∈ GL_k(W)` (`twK_inv_mul`), and the first keeps `ℓ_g` integral for every `g` over `W`. The L5 sub-spec's
`Dvd ϖ i F` is `OrdGe ϖ i F` (the name `Dvd` is Mathlib's). The flat model is L6's (one letter per position); L5's
two-letter flat weight `(α, 0, …, 0, −β)` needs the two-letter identification and the harmonic splitting, not done
here.
-/

namespace LetterFock

open MvPolynomial WeylFock InertModel LocalLattice

open scoped Matrix Pointwise

noncomputable section

/-! ## Letter polynomials, the Fock form and the `gl_k` action -/

section Fock

/-- **Letter polynomials**: the variable `(l, c)` is the coordinate `c` of the letter `l`. -/
abbrev LPol (α : Type*) (k : ℕ) (R : Type*) [CommSemiring R] := MvPolynomial (α × Fin k) R

/-- **The row weight** of a letter polynomial: `X_{l,c}` counts once in the letter `l`. -/
def rowW (α : Type*) [DecidableEq α] (k : ℕ) : α × Fin k → α → ℕ := fun v => Pi.single v.1 1

variable {σ K : Type*} [Field K]

/-- **The factorial** `μ! = ∏_v (μ_v)!` of an exponent. -/
def mfact [Fintype σ] (μ : σ →₀ ℕ) : K := ∏ v, ((μ v).factorial : K)

/-- **The Fock form** `⟨F, G⟩ = Σ_μ F_μ·G_μ·μ!` (on block polynomials it is `fockWith (RingHom.id K)`). -/
def lfock (F G : MvPolynomial σ K) : K :=
  ∑ d ∈ G.support, F.coeff d * G.coeff d * d.prod fun _ n => (n.factorial : K)

variable [Fintype σ]

/-- **The Fock form as a sum** over any finite set containing the support of the second argument. -/
theorem lfock_eq_sum {F G : MvPolynomial σ K} {S : Finset (σ →₀ ℕ)} (hS : G.support ⊆ S) :
    lfock F G = ∑ d ∈ S, F.coeff d * G.coeff d * mfact d := by
  unfold lfock
  calc ∑ d ∈ G.support, F.coeff d * G.coeff d * d.prod (fun _ n => (n.factorial : K))
      = ∑ d ∈ G.support, F.coeff d * G.coeff d * mfact d := Finset.sum_congr rfl fun d _ => by
        rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
        rfl
    _ = _ := Finset.sum_subset hS fun d _ hd => by rw [notMem_support_iff.1 hd]; ring

/-- **The Fock form is symmetric.** -/
theorem lfock_comm (F G : MvPolynomial σ K) : lfock F G = lfock G F := by
  rw [lfock_eq_sum (S := F.support ∪ G.support) Finset.subset_union_right,
    lfock_eq_sum (S := F.support ∪ G.support) Finset.subset_union_left]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- **The Fock form is additive** in the first argument. -/
theorem lfock_add_left (F F' G : MvPolynomial σ K) : lfock (F + F') G = lfock F G + lfock F' G := by
  simp [lfock_eq_sum (subset_refl G.support), add_mul, Finset.sum_add_distrib]

/-- **The Fock form is homogeneous** in the first argument. -/
theorem lfock_smul_left (c : K) (F G : MvPolynomial σ K) : lfock (c • F) G = c * lfock F G := by
  simp only [lfock_eq_sum (subset_refl G.support), coeff_smul, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- **The Fock form as a bilinear map.** -/
def lfockB : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂ K lfock lfock_add_left (fun c F G => by rw [lfock_smul_left, smul_eq_mul])
    (fun F G G' => by rw [lfock_comm, lfock_add_left, lfock_comm, lfock_comm G'])
    (fun c F G => by rw [lfock_comm, lfock_smul_left, lfock_comm, smul_eq_mul])

/-- **The bilinear Fock form, applied.** -/
theorem lfockB_apply (F G : MvPolynomial σ K) : lfockB F G = lfock F G := rfl

/-- **`(μ + e_v)! = μ!·(μ_v + 1)`.** -/
theorem mfact_add_single [DecidableEq σ] (μ : σ →₀ ℕ) (v : σ) :
    (mfact (μ + Finsupp.single v 1) : K) = mfact μ * ((μ v : K) + 1) := by
  unfold mfact
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),
    ← Finset.mul_prod_erase Finset.univ (fun w => ((μ w).factorial : K)) (Finset.mem_univ v)]
  have h : ∀ w ∈ Finset.univ.erase v,
      (((μ + Finsupp.single v 1 : σ →₀ ℕ) w).factorial : K) = ((μ w).factorial : K) :=
    fun w hw => by rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hw), add_zero]
  rw [Finset.prod_congr rfl h, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

/-- **Fock adjunction**: multiplication by `X_v` is adjoint to `∂/∂X_v`. -/
theorem lfock_mul_X [DecidableEq σ] (F G : MvPolynomial σ K) (v : σ) :
    lfock (F * X v) G = lfock F (pderiv v G) := by
  induction F using MvPolynomial.induction_on' with
  | add F F' hF hF' => rw [add_mul, lfock_add_left, lfock_add_left, hF, hF']
  | monomial μ a =>
    rw [X, monomial_mul_monomial, mul_one, lfock_comm, lfock_comm _ (pderiv v G),
      lfock_eq_sum (S := {μ + Finsupp.single v 1}) support_monomial_subset,
      lfock_eq_sum (S := {μ}) support_monomial_subset, Finset.sum_singleton, Finset.sum_singleton,
      coeff_monomial, coeff_monomial, coeff_pderiv, mfact_add_single]
    simp only [↓reduceIte]
    ring

/-- **Fock adjunction**, the other side. -/
theorem lfock_X_mul [DecidableEq σ] (F G : MvPolynomial σ K) (v : σ) :
    lfock F (X v * G) = lfock (pderiv v F) G := by
  rw [lfock_comm, mul_comm, lfock_mul_X, lfock_comm]

/-- **The Fock form on monomials**: `⟨X^μ, X^ν⟩ = δ_{μν}·μ!`. -/
theorem lfock_monomial (μ ν : σ →₀ ℕ) (a b : K) :
    lfock (monomial μ a) (monomial ν b) = if μ = ν then a * b * mfact μ else 0 := by
  classical
  rw [lfock_eq_sum (S := {ν}) support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial]
  simp only [↓reduceIte]
  split_ifs with h
  · subst h; ring
  · ring

end Fock

/-- **A finite sum of derivations, applied.** -/
theorem derivation_sum_apply {R A ι' : Type*} [CommRing R] [CommRing A] [Algebra R A] (t : Finset ι')
    (D : ι' → Derivation R A A) (x : A) : (∑ i ∈ t, D i) x = ∑ i ∈ t, D i x := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

section Action

variable {α K : Type*} [Field K] {k : ℕ}

/-- **The `gl_k` operator `E_{ab}` on one letter**: `X_{l,a}∂_{l,b}` on a vector letter, `−X_{l,b}∂_{l,a}` on a
covector letter (`vec l = false`). -/
def letE (vec : α → Bool) (l : α) (a b : Fin k) : Derivation K (LPol α k K) (LPol α k K) :=
  if vec l then (X (l, a) : LPol α k K) • pderiv (l, b) else -((X (l, b) : LPol α k K) • pderiv (l, a))

/-- **The Euler operator of one letter**, `Σ_c X_{l,c}∂_{l,c}`: the letter degree on homogeneous polynomials. -/
def eul (l : α) : Derivation K (LPol α k K) (LPol α k K) := ∑ c, (X (l, c) : LPol α k K) • pderiv (l, c)

/-- **`E_{ab}` on a generator.** -/
theorem letE_X [DecidableEq α] (vec : α → Bool) (l : α) (a b : Fin k) (v : α × Fin k) :
    letE vec l a b (X v : LPol α k K) =
      if vec l then (if v = (l, b) then X (l, a) else 0) else -(if v = (l, a) then X (l, b) else 0) := by
  unfold letE
  split_ifs <;> simp_all [pderiv_X]

/-- **The Euler operator on a generator.** -/
theorem eul_X [DecidableEq α] (l : α) (v : α × Fin k) : eul l (X v : LPol α k K) = if v.1 = l then X v else 0 := by
  rw [eul, derivation_sum_apply]
  simp only [Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single v.2 (fun c _ hc => by rw [ite_eq_right (fun h' => hc (by rw [h']))]; ring)
      (by simp)]
    simp [← h]
  · exact Finset.sum_eq_zero fun c _ => by rw [ite_eq_right (fun h' => h (by rw [h']))]; ring

variable [Fintype α] [DecidableEq α]

/-- **Contravariance** of the Fock form: `⟨E_{ab}F, G⟩ = ⟨F, E_{ba}G⟩`. -/
theorem lfock_letE (vec : α → Bool) (l : α) (a b : Fin k) (F G : LPol α k K) :
    lfock (letE vec l a b F) G = lfock F (letE vec l b a G) := by
  unfold letE
  split_ifs
  · simp only [Derivation.smul_apply, smul_eq_mul]
    rw [mul_comm, lfock_mul_X, ← lfock_X_mul]
  · simp only [Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul, ← lfockB_apply, map_neg,
      LinearMap.neg_apply]
    rw [lfockB_apply, lfockB_apply, mul_comm, lfock_mul_X, ← lfock_X_mul]

end Action

/-! ## Contravariant forms are multiples of the Fock form -/

section Unique

variable {α K : Type*} [Fintype α] [DecidableEq α] [Field K] {k : ℕ}

variable (K) in
/-- **The letter polynomials of multidegree `d`**: degree `d_l` in the letter `l`. -/
def LHom (d : α → ℕ) : Submodule K (LPol α k K) := weightedHomogeneousSubmodule K (rowW α k) d

/-- **The extreme exponent** `Σ_l d_l·e_{(l, e_l)}`: the whole degree of the letter `l` in its coordinate `e_l`. -/
def extr (e : α → Fin k) (d : α → ℕ) : α × Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v.2 = e v.1 then d v.1 else 0

/-- **The number of non-extreme coordinates** of an exponent. -/
def nonExt (e : α → Fin k) : (α × Fin k →₀ ℕ) →+ ℕ := Finsupp.weight fun v => if v.2 = e v.1 then 0 else 1

/-- **The row weight of an exponent**: its degree in the letter `l`. -/
theorem weight_rowW_apply (μ : α × Fin k →₀ ℕ) (l : α) : Finsupp.weight (rowW α k) μ l = ∑ c, μ (l, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun c _ => Finset.sum_ite_eq _ _ _]
  simp

omit [DecidableEq α] in
/-- **No non-extreme coordinates**: the exponent vanishes off the extreme coordinates. -/
theorem nonExt_eq_zero {e : α → Fin k} {μ : α × Fin k →₀ ℕ} :
    nonExt e μ = 0 ↔ ∀ v : α × Fin k, v.2 ≠ e v.1 → μ v = 0 := by
  rw [nonExt, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_eq_zero_iff]
  refine ⟨fun h v hv => ?_, fun h v _ => ?_⟩
  · simpa [hv] using h v (Finset.mem_univ v)
  · by_cases hv : v.2 = e v.1 <;> simp [hv, h v]

/-- **The exponent of multidegree `d` with no non-extreme coordinate** is the extreme exponent. -/
theorem eq_extr {e : α → Fin k} {d : α → ℕ} {μ : α × Fin k →₀ ℕ} (hμ : Finsupp.weight (rowW α k) μ = d)
    (hn : nonExt e μ = 0) : μ = extr e d := by
  rw [nonExt_eq_zero] at hn
  ext ⟨l, c⟩
  simp only [extr, Finsupp.coe_equivFunOnFinite_symm]
  split_ifs with hc
  · rw [← hμ, weight_rowW_apply, Finset.sum_eq_single c (fun b _ hb => hn (l, b) (by rw [hc] at hb; exact hb))
      (by simp)]
  · exact hn (l, c) hc

omit [DecidableEq α] in
/-- **The factorial of the extreme exponent** is `∏_l d_l!`. -/
theorem mfact_extr [CharZero K] (e : α → Fin k) (d : α → ℕ) :
    (mfact (extr e d) : K) = ∏ l, ((d l).factorial : K) := by
  rw [mfact, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Finset.prod_eq_single (e l) (fun c _ hc => by simp [extr, hc]) (by simp)]
  simp [extr]

omit [Fintype α] [DecidableEq α] in
/-- **Moving one unit** of an exponent from the coordinate `v` to `w`: `X_w∂_v X^ν = ν_v·X^{ν − e_v + e_w}`. -/
theorem X_mul_pderiv_monomial' (v w : α × Fin k) (ν : α × Fin k →₀ ℕ) :
    (X w * pderiv v (monomial ν 1) : LPol α k K) =
      monomial (ν - Finsupp.single v 1 + Finsupp.single w 1) (ν v : K) := by
  rw [pderiv_monomial, X, monomial_mul_monomial, one_mul, one_mul, add_comm]

omit [Fintype α] [DecidableEq α] in
/-- **Moving a unit from `v` to `w` and back** gives the exponent back, when `μ_v > 0`. -/
theorem move_back {v w : α × Fin k} {μ : α × Fin k →₀ ℕ} (hμ : 0 < μ v) :
    μ - Finsupp.single v 1 + Finsupp.single w 1 - Finsupp.single w 1 + Finsupp.single v 1 = μ := by
  rw [add_tsub_cancel_right, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hμ)]

omit [Fintype α] [DecidableEq α] in
/-- **The moved exponent at `w`** is `μ_w + 1`. -/
theorem move_apply {v w : α × Fin k} (hvw : v ≠ w) (μ : α × Fin k →₀ ℕ) :
    (μ - Finsupp.single v 1 + Finsupp.single w 1 : α × Fin k →₀ ℕ) w = μ w + 1 := by
  simp [Finsupp.single_eq_of_ne' hvw]

/-- **The factorial of a moved exponent**: `(μ − e_v + e_w)!·μ_v = μ!·(μ_w + 1)`. -/
theorem mfact_move [CharZero K] {v w : α × Fin k} (hvw : v ≠ w) {μ : α × Fin k →₀ ℕ} (hμ : 0 < μ v) :
    (mfact (μ - Finsupp.single v 1 + Finsupp.single w 1) : K) * (μ v : K) = mfact μ * ((μ w : K) + 1) := by
  set m0 := μ - Finsupp.single v 1
  have h1 : μ = m0 + Finsupp.single v 1 := (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hμ)).symm
  have hw : m0 w = μ w := by simp [m0, Finsupp.single_eq_of_ne' hvw]
  have hv : (m0 v : K) + 1 = μ v := by
    have : m0 v + 1 = μ v := by rw [h1]; simp
    exact_mod_cast this
  conv_rhs => rw [h1]
  rw [mfact_add_single, mfact_add_single, hw, hv, ← h1]
  ring

omit [Fintype α] in
/-- **Moving within a letter keeps the multidegree.** -/
theorem weight_move {v w : α × Fin k} (h1 : v.1 = w.1) {μ : α × Fin k →₀ ℕ} (hμ : 0 < μ v) :
    Finsupp.weight (rowW α k) (μ - Finsupp.single v 1 + Finsupp.single w 1) = Finsupp.weight (rowW α k) μ := by
  have h : μ = μ - Finsupp.single v 1 + Finsupp.single v 1 := (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hμ)).symm
  conv_rhs => rw [h]
  simp only [map_add, Finsupp.weight_single, rowW, h1]

omit [Fintype α] [DecidableEq α] in
/-- **Moving a unit to the extreme coordinate** lowers the number of non-extreme coordinates by one. -/
theorem nonExt_move {e : α → Fin k} {v w : α × Fin k} (hv : v.2 ≠ e v.1) (hw : w.2 = e w.1)
    {μ : α × Fin k →₀ ℕ} (hμ : 0 < μ v) :
    nonExt e (μ - Finsupp.single v 1 + Finsupp.single w 1) + 1 = nonExt e μ := by
  have h : μ = μ - Finsupp.single v 1 + Finsupp.single v 1 := (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hμ)).symm
  conv_rhs => rw [h]
  simp [nonExt, Finsupp.weight_single, hv, hw]

variable [CharZero K]

/-- **Contravariant forms on monomials.** A bilinear form `B` on letter polynomials with
`B(X_{l,a}∂_{l,b}P, Q) = B(P, X_{l,b}∂_{l,a}Q)` for `a ≠ b` has `B(X^μ, X^ν)·∏_l d_l! = δ_{μν}·μ!·B(X^ε, X^ε)` on
monomials of multidegree `d`, `ε` the extreme exponent: by induction on the number of non-extreme coordinates of `μ`,
moving them one by one to the extreme coordinate. -/
theorem bilin_monomial (B : LPol α k K →ₗ[K] LPol α k K →ₗ[K] K) (e : α → Fin k)
    (hB : ∀ l a b, a ≠ b → ∀ P Q, B (X (l, a) * pderiv (l, b) P) Q = B P (X (l, b) * pderiv (l, a) Q))
    (d : α → ℕ) (n : ℕ) : ∀ μ ν : α × Fin k →₀ ℕ, nonExt e μ = n → Finsupp.weight (rowW α k) μ = d →
      Finsupp.weight (rowW α k) ν = d → B (monomial μ 1) (monomial ν 1) * ∏ l, ((d l).factorial : K) =
        (if μ = ν then mfact μ else 0) * B (monomial (extr e d) 1) (monomial (extr e d) 1) := by
  -- a non-extreme coordinate with positive exponent, and the monomial as a lowering of a monomial
  have hex : ∀ ν : α × Fin k →₀ ℕ, Finsupp.weight (rowW α k) ν = d → ν ≠ extr e d →
      ∃ l c, c ≠ e l ∧ 0 < ν (l, c) := fun ν hν hne => by
    by_contra h
    push Not at h
    exact hne (eq_extr hν (nonExt_eq_zero.2 fun v hv => Nat.eq_zero_of_le_zero (h v.1 v.2 hv)))
  have hm : ∀ (μ : α × Fin k →₀ ℕ) (a : K), (monomial μ a : LPol α k K) = a • monomial μ 1 := fun μ a => by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hlow : ∀ (l : α) (c : Fin k), c ≠ e l → ∀ ν : α × Fin k →₀ ℕ, 0 < ν (l, c) →
      (monomial ν 1 : LPol α k K) = ((ν (l, e l) : K) + 1)⁻¹ • (X (l, c) * pderiv (l, e l)
        (monomial (ν - Finsupp.single (l, c) 1 + Finsupp.single (l, e l) 1) 1)) := fun l c hc ν hν => by
    have hvw : (l, c) ≠ (l, e l) := fun h => hc (Prod.ext_iff.1 h).2
    rw [X_mul_pderiv_monomial', move_back hν, move_apply hvw, smul_monomial, smul_eq_mul, Nat.cast_add,
      Nat.cast_one, inv_mul_cancel₀ (Nat.cast_add_one_ne_zero _)]
  induction n with
  | zero =>
    intro μ ν hn hμ hν
    obtain rfl := eq_extr hμ hn
    by_cases hνe : extr e d = ν
    · subst hνe
      rw [ite_eq_left rfl, mfact_extr, mul_comm]
    rw [ite_eq_right hνe, zero_mul]
    obtain ⟨l, c, hc, hνc⟩ := hex ν hν (Ne.symm hνe)
    rw [hlow l c hc ν hνc, map_smul, ← hB l (e l) c (Ne.symm hc), pderiv_monomial]
    simp [extr, hc]
  | succ n ih =>
    intro μ ν hn hμ hν
    obtain ⟨l, c, hc, hμc⟩ := hex μ hμ (fun h => by
      rw [h, (nonExt_eq_zero.2 fun v hv => by simp [extr, hv] : nonExt e (extr e d) = 0)] at hn
      exact Nat.succ_ne_zero n hn.symm)
    have hvw : (l, c) ≠ (l, e l) := fun h => hc (Prod.ext_iff.1 h).2
    set μ' := μ - Finsupp.single (l, c) 1 + Finsupp.single (l, e l) 1 with hμ'
    set ν' := ν - Finsupp.single (l, c) 1 + Finsupp.single (l, e l) 1 with hν'
    have key : B (monomial μ 1) (monomial ν 1) =
        ((μ (l, e l) : K) + 1)⁻¹ * ((ν (l, c) : K) * B (monomial μ' 1) (monomial ν' 1)) := by
      rw [hlow l c hc μ hμc, map_smul, LinearMap.smul_apply, hB l c (e l) hc, X_mul_pderiv_monomial', ← hν',
        hm ν' (ν (l, c) : K), map_smul, smul_eq_mul, smul_eq_mul]
    rw [key]
    by_cases hνc : ν (l, c) = 0
    · have hne : μ ≠ ν := fun h => by rw [h, hνc] at hμc; exact lt_irrefl 0 hμc
      rw [hνc, Nat.cast_zero, zero_mul, mul_zero, zero_mul, ite_eq_right hne, zero_mul]
    have hνc' : 0 < ν (l, c) := Nat.pos_of_ne_zero hνc
    have hn' : nonExt e μ' = n := by
      have := nonExt_move (e := e) (v := (l, c)) (w := (l, e l)) hc rfl hμc
      rw [hn] at this
      exact Nat.succ.inj this
    have hwμ : Finsupp.weight (rowW α k) μ' = d := (weight_move (v := (l, c)) (w := (l, e l)) rfl hμc).trans hμ
    have hwν : Finsupp.weight (rowW α k) ν' = d := (weight_move (v := (l, c)) (w := (l, e l)) rfl hνc').trans hν
    have hih := ih μ' ν' hn' hwμ hwν
    calc ((μ (l, e l) : K) + 1)⁻¹ * ((ν (l, c) : K) * B (monomial μ' 1) (monomial ν' 1)) *
          ∏ l, ((d l).factorial : K)
        = ((μ (l, e l) : K) + 1)⁻¹ * (ν (l, c) : K) *
          (B (monomial μ' 1) (monomial ν' 1) * ∏ l, ((d l).factorial : K)) := by ring
      _ = _ := by
        rw [hih]
        by_cases hμν : μ = ν
        · subst hμν
          have hmf := mfact_move (K := K) hvw hμc
          rw [← hμ'] at hmf
          rw [ite_eq_left rfl, ite_eq_left rfl]
          rw [show ((μ (l, e l) : K) + 1)⁻¹ * (μ (l, c) : K) *
              (mfact μ' * B (monomial (extr e d) 1) (monomial (extr e d) 1)) = ((μ (l, e l) : K) + 1)⁻¹ *
              (mfact μ' * (μ (l, c) : K)) * B (monomial (extr e d) 1) (monomial (extr e d) 1) by ring, hmf]
          field_simp
        · have : μ' ≠ ν' := fun h => hμν (by rw [← move_back hμc, ← move_back hνc', ← hμ', ← hν', h])
          rw [ite_eq_right this, ite_eq_right hμν]
          ring

/-- **Contravariant forms are multiples of the Fock form**: under the hypothesis of `bilin_monomial`,
`B(P, Q)·∏_l d_l! = ⟨P, Q⟩·B(X^ε, X^ε)` on the letter polynomials of multidegree `d`. -/
theorem bilin_eq_lfock (B : LPol α k K →ₗ[K] LPol α k K →ₗ[K] K) (e : α → Fin k)
    (hB : ∀ l a b, a ≠ b → ∀ P Q, B (X (l, a) * pderiv (l, b) P) Q = B P (X (l, b) * pderiv (l, a) Q))
    {d : α → ℕ} {P Q : LPol α k K} (hP : P ∈ LHom K d) (hQ : Q ∈ LHom K d) :
    B P Q * ∏ l, ((d l).factorial : K) = lfock P Q * B (monomial (extr e d) 1) (monomial (extr e d) 1) := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hP hQ
  have hm : ∀ (μ : α × Fin k →₀ ℕ) (a : K), (monomial μ a : LPol α k K) = a • monomial μ 1 := fun μ a => by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hBPQ : B P Q = ∑ μ ∈ P.support, ∑ ν ∈ Q.support,
      P.coeff μ * Q.coeff ν * B (monomial μ 1) (monomial ν 1) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun μ _ => ?_
    conv_lhs => rw [Q.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hm μ, hm ν]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hBPQ, Finset.sum_mul, lfock_comm, lfock_eq_sum (subset_refl P.support), Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Finset.sum_mul, Finset.sum_congr rfl fun ν hν => by
    rw [mul_assoc, bilin_monomial B e hB d _ μ ν rfl (hP (mem_support_iff.1 hμ)) (hQ (mem_support_iff.1 hν))]]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · ring
  · rw [notMem_support_iff.1 h]
    ring

omit [CharZero K] [Fintype α] in
/-- **Letter-preserving algebra maps keep the multidegree**: if each `φ(X_{l,c})` is linear in the letter `l`, `φ`
maps multidegree `d` to multidegree `d`. -/
theorem map_mem_LHom {φ : LPol α k K →ₐ[K] LPol α k K}
    (h : ∀ v, IsWeightedHomogeneous (rowW α k) (φ (X v)) (rowW α k v)) {d : α → ℕ} {F : LPol α k K}
    (hF : F ∈ LHom K d) : φ F ∈ LHom K d := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hF
  rw [F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  rw [LHom, mem_weightedHomogeneousSubmodule, monomial_eq, map_mul, algHom_C, MvPolynomial.algebraMap_eq,
    Finsupp.prod, map_prod, ← hF (mem_support_iff.1 hμ), Finsupp.weight_apply]
  exact (IsWeightedHomogeneous.prod _ _ _ fun v _ => by rw [map_pow]; exact (h v).pow _).C_mul _

omit [CharZero K] in
/-- **Algebra maps that agree up to a scalar per letter** agree on multidegree `d` up to `∏_l λ_l^{d_l}`. -/
theorem map_eq_smul_of_row {φ ψ : LPol α k K →ₐ[K] LPol α k K} (lam : α → K)
    (h : ∀ v, ψ (X v) = lam v.1 • φ (X v)) {d : α → ℕ} {F : LPol α k K} (hF : F ∈ LHom K d) :
    ψ F = (∏ l, lam l ^ d l) • φ F := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hF
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd := hF (mem_support_iff.1 hμ)
  rw [monomial_eq, map_mul, map_mul, algHom_C, algHom_C, Finsupp.prod, map_prod, map_prod, ← mul_smul_comm]
  congr 1
  have e : ∀ x, ψ (X x ^ μ x) = C (lam x.1 ^ μ x) * φ (X x ^ μ x) := fun x => by
    rw [map_pow, h, smul_pow, MvPolynomial.smul_eq_C_mul]
    simp only [map_pow]
  rw [Finset.prod_congr rfl fun x _ => e x, Finset.prod_mul_distrib, ← map_prod, MvPolynomial.smul_eq_C_mul]
  congr 2
  rw [Finset.prod_subset (Finset.subset_univ _) (fun v _ hv => by rw [Finsupp.notMem_support_iff.1 hv, pow_zero]),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun l _ => ?_
  show ∏ c, lam l ^ μ (l, c) = _
  rw [Finset.prod_pow_eq_pow_sum, ← hd, weight_rowW_apply]

end Unique

/-! ## Frobenius -/

section Frob

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' : ℕ}

/-- **Frobenius congruence**: `σ^s(x) ≡ x^{p^s} (mod p)` on `W`. -/
theorem frob_pow (hU : Unram p n' W Qq O Kf ι σ j ϖ) (s : ℕ) (x : W) :
    ∃ y : W, (σ ^ s) (algebraMap W Qq x) = algebraMap W Qq (x ^ p ^ s + p * y) := by
  induction s generalizing x with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
    obtain ⟨y, hy⟩ := hU.frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + p * y)
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (x ^ p + p * y) (x ^ p) (p ^ s)
    refine ⟨y * t + z, ?_⟩
    rw [pow_succ]
    refine (congrArg (σ ^ s) hy).trans (hz.trans (congrArg _ ?_))
    rw [pow_succ', pow_mul]
    linear_combination ht

end Frob

/-! ## The lift substitution, the normalised degree and the plane of a matrix -/

section Lift

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' k : ℕ} {α : Type*}

/-- **The twisted matrix** `σ^s(g)` in `Kf`, for `g` over `W`. -/
def twK (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (g : Matrix (Fin k) (Fin k) W) : Matrix (Fin k) (Fin k) Kf :=
  g.map fun x => ι ((σ ^ s) (algebraMap W Qq x))

/-- **The scaled variables** at type `r`: the normal coordinates `c ≥ r` of the vector letters and the plane
coordinates `c < r` of the covector letters. -/
def scaled (r : ℕ) (vec : α → Bool) (v : α × Fin k) : Bool :=
  if vec v.1 then decide (r ≤ v.2.val) else decide (v.2.val < r)

/-- **The normalised degree** of a monomial: its total exponent in the scaled variables. -/
def nd (r : ℕ) (vec : α → Bool) : (α × Fin k →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun v => if scaled r vec v then 1 else 0

/-- **The lift substitution** `ℓ_g` at type `r`: a vector letter at position `s` goes through `σ^s(g⁻¹)`, a
covector letter through `σ^s(g)ᵀ`, and the scaled variables are multiplied by `ϖ`:
`X_{l,c} ↦ Σ_b ϖ^{[b ≥ r]}·X_{l,b}·σ^s(g⁻¹)_{bc}` (vector), `X_{l,c} ↦ Σ_b ϖ^{[b < r]}·X_{l,b}·σ^s(g)_{cb}`
(covector). -/
def liftSub (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (r : ℕ) (vec : α → Bool) (pos : α → ℕ)
    (g : Matrix (Fin k) (Fin k) W) : LPol α k Kf →ₐ[Kf] LPol α k Kf :=
  aeval fun v => ∑ b : Fin k, C ((if scaled r vec (v.1, b) then algebraMap O Kf ϖ else 1) *
    if vec v.1 then twK ι σ (pos v.1) g⁻¹ b v.2 else twK ι σ (pos v.1) g v.2 b) * X (v.1, b)

/-- **Order at least `i`**: every coefficient lies in `ϖ^i·O` (`OrdGe ϖ 0` is integrality). With the lift
substitution, `ord_g F ≥ i` is `OrdGe ϖ i (liftSub … g F)`. -/
def OrdGe {τ : Type*} (ϖ : O) (i : ℕ) (F : MvPolynomial τ Kf) : Prop :=
  ∀ m, ∃ c : O, F.coeff m = algebraMap O Kf (ϖ ^ i * c)

/-- **The `ϖ`-graded integral subalgebra**: the polynomials whose coefficient at `X^m` lies in `ϖ^{nd m}·O`. -/
def gInt (ϖ : O) (r : ℕ) (vec : α → Bool) : Subalgebra O (LPol α k Kf) where
  carrier := {F | ∀ m, ∃ c : O, F.coeff m = algebraMap O Kf (ϖ ^ nd r vec m * c)}
  mul_mem' {F G} hF hG m := by
    classical
    choose cF hcF using hF
    choose cG hcG using hG
    refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, cF x.1 * cG x.2, ?_⟩
    rw [coeff_mul, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hcF, hcG, ← map_mul, ← (Finset.HasAntidiagonal.mem_antidiagonal.1 hx), map_add, pow_add]
    ring_nf
  add_mem' {F G} hF hG m := by
    obtain ⟨a, ha⟩ := hF m
    obtain ⟨b, hb⟩ := hG m
    exact ⟨a + b, by simp [ha, hb, mul_add]⟩
  algebraMap_mem' o m := by
    classical
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · exact ⟨o, by rw [← h, map_zero, pow_zero, one_mul]⟩
    · exact ⟨0, by rw [mul_zero, map_zero]⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Generators of the graded subalgebra**: `ϖ^{[v scaled]}·c·X_v` lies in it for `c ∈ O`. -/
theorem C_mul_X_mem_gInt (ϖ : O) (r : ℕ) (vec : α → Bool) (v : α × Fin k) (c : O) :
    C ((if scaled r vec v then algebraMap O Kf ϖ else 1) * algebraMap O Kf c) * X v ∈ gInt ϖ r vec := by
  classical
  intro m
  rw [coeff_C_mul]
  by_cases hm : Finsupp.single v 1 = m
  · subst hm
    refine ⟨c, ?_⟩
    have e : nd r vec (Finsupp.single v 1) = if scaled r vec v then 1 else 0 := by
      simp [nd, Finsupp.weight_single]
    rw [coeff_X_same, e]
    split_ifs <;> simp [map_mul]
  · exact ⟨0, by simp [coeff_X, hm]⟩

/-- **Coefficient divisibility**: the lift substitution maps integral polynomials into the `ϖ`-graded integral
subalgebra, so the coefficient of `X^m` in `ℓ_g F` lies in `ϖ^{nd m}·O` (the twisted matrices are integral, as `σ`
keeps `W`). -/
theorem liftSub_mem_gInt (hU : Unram p n' W Qq O Kf ι σ j ϖ) (r : ℕ) (vec : α → Bool) (pos : α → ℕ)
    (g : Matrix (Fin k) (Fin k) W) {F : LPol α k Kf} (hF : OrdGe ϖ 0 F) :
    liftSub ι σ ϖ r vec pos g F ∈ gInt ϖ r vec := by
  have hX : ∀ v, liftSub ι σ ϖ r vec pos g (X v) ∈ gInt ϖ r vec := fun v => by
    rw [liftSub, aeval_X]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    obtain ⟨o, ho⟩ : ∃ o : O, (if vec v.1 then twK ι σ (pos v.1) g⁻¹ b v.2 else twK ι σ (pos v.1) g v.2 b) =
        algebraMap O Kf o := by
      split_ifs
      · exact hU.exists_map_eq _ _
      · exact hU.exists_map_eq _ _
    rw [ho]
    exact C_mul_X_mem_gInt ϖ r vec (v.1, b) o
  rw [F.as_sum, map_sum]
  refine Subalgebra.sum_mem _ fun m _ => ?_
  obtain ⟨c, hc⟩ := hF m
  rw [monomial_eq, map_mul, algHom_C, hc, pow_zero, one_mul, MvPolynomial.algebraMap_eq,
    ← MvPolynomial.algebraMap_apply, Finsupp.prod, map_prod]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
    (Subalgebra.prod_mem _ fun v _ => by rw [map_pow]; exact Subalgebra.pow_mem _ (hX v) _)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The lift substitution at `g = 1`** is the scaling of the scaled variables by `ϖ`. -/
theorem liftSub_one_X (r : ℕ) (vec : α → Bool) (pos : α → ℕ) (v : α × Fin k) :
    liftSub ι σ ϖ r vec pos (1 : Matrix (Fin k) (Fin k) W) (X v) =
      C (if scaled r vec v then algebraMap O Kf ϖ else 1) * X v := by
  classical
  have h1 : ∀ s, twK ι σ s (1 : Matrix (Fin k) (Fin k) W) = 1 := fun s => by
    rw [twK, Matrix.map_one] <;> simp
  rw [liftSub, aeval_X, inv_one, h1]
  rw [Finset.sum_eq_single v.2]
  · split_ifs <;> simp
  · intro b _ hb
    split_ifs <;> simp [hb, Ne.symm hb]
  · simp

/-- **The plane of a matrix** at type `r`: the span over `W/p` of the rows `i < r` of `g⁻¹` modulo `p` (the edge
out of the source that `g` is adapted to; `lineOf` for `r = 1`). -/
def planeOf (p r : ℕ) (g : Matrix (Fin k) (Fin k) W) :
    Submodule (W ⧸ Ideal.span {(p : W)}) (Fin k → W ⧸ Ideal.span {(p : W)}) :=
  Submodule.span _ {v | ∃ i : Fin k, i.val < r ∧ v = fun c => Ideal.Quotient.mk _ (g⁻¹ i c)}

/-- **The line of a matrix**: the plane at type `1`, spanned by row `0` of `g⁻¹` modulo `p`. -/
abbrev lineOf (p : ℕ) (g : Matrix (Fin k) (Fin k) W) := planeOf p 1 g

end Lift

/-! ## Derivations of determinants -/

section Deriv

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Leibniz for a finite product**: `D(∏ f) = Σ_i (∏_{j ≠ i} f_j)·D f_i`. -/
theorem derivation_prod {ι' : Type*} [DecidableEq ι'] (D : Derivation R A A) (s : Finset ι') (f : ι' → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha, smul_eq_mul,
      smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi ha).symm,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

/-- **The derivative of a determinant** is the sum over the rows of the determinants with that row differentiated. -/
theorem derivation_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j => D (M i j)).det := by
  simp only [Matrix.det_apply, map_sum, Units.smul_def, map_zsmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.smul_sum, derivation_prod]
  congr 1
  conv_rhs => rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (M.updateRow (π i) fun l => D (M (π i) l)) (π j) j)
    (Finset.mem_univ i), mul_comm]
  congr 1
  · simp only [Matrix.updateRow_self]
  · refine Finset.prod_congr rfl fun l hl => ?_
    rw [Matrix.updateRow_apply, ite_eq_right (fun h => Finset.ne_of_mem_erase hl (π.injective h))]

/-- **Derivations along an algebra map** from polynomials are determined by the generators. -/
theorem derivation_comp {σ B : Type*} {K : Type*} [Field K] [CommRing B] [Algebra K B]
    (φ : MvPolynomial σ K →ₐ[K] B) (D₁ : Derivation K B B) (D₂ : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (h : ∀ v, D₁ (φ (X v)) = φ (D₂ (X v))) (P : MvPolynomial σ K) : D₁ (φ P) = φ (D₂ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [algHom_C, Derivation.map_algebraMap, ← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add, map_add]
  | mul_X P v hP =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, h, hP, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, map_mul, map_mul]

end Deriv

/-! ## The flat model -/

section Flat

variable {Kf : Type} [Field Kf] {n' k : ℕ}

/-- **The flags of the flat model**: the letter of position `s` is a vector letter at even `s`, a covector letter at
odd `s` (`lamAt` dualises the odd positions). -/
def vecF (n' : ℕ) : Fin n' → Bool := fun s => decide (Even s.val)

/-- **The last coordinate** `k − 1`. -/
def lastC (k : ℕ) [NeZero k] : Fin k := ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩

variable [NeZero k]

/-- **The flat weight** `(d_s, 0, …, 0)` at every position, in the convention of `lam0` (so `lamAt` gives
`(0, …, 0, −d_s)` at odd `s`). -/
def flatWt (d : Fin n' → ℕ) : Fin n' → Fin k → ℤ := fun s => Pi.single 0 (d s : ℤ)

variable (Kf) in
/-- **The plain identification** `θ°` of the flat model: the vector letter `X_{s,c}` (even `s`) goes to the entry
`x_{s,c,0}` of the block `s`, the covector letter (odd `s`) to the signed cofactor `adj(x_s)_{k−1,c}` of the last
column. -/
def theta0 : LPol (Fin n') k Kf →ₐ[Kf] Pol (Unit × Fin n') k Kf :=
  aeval fun v => if Even v.1.val then X (((), v.1), v.2, 0) else (xMat ((), v.1)).adjugate (lastC k) v.2

/-- **The letter change** `X_{s,c} ↦ Σ_b A_s(c, b)·X_{s,b}`. -/
def linSub (A : Fin n' → Matrix (Fin k) (Fin k) Kf) : LPol (Fin n') k Kf →ₐ[Kf] LPol (Fin n') k Kf :=
  aeval fun v => ∑ b, C (A v.1 v.2 b) * X (v.1, b)

/-- **The letter matrices of a block substitution**: `g_s` at even `s`, `adj(g_s)ᵀ` at odd `s`. -/
def letMat (g : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf) (s : Fin n') : Matrix (Fin k) (Fin k) Kf :=
  if Even s.val then g ((), s) else (g ((), s)).adjugateᵀ

/-- **The row operator** `R_{s,a,b} = Σ_c x_{s,a,c}∂/∂x_{s,b,c}` on the block `s`. -/
def rowOp (s : Fin n') (a b : Fin k) : Derivation Kf (Pol (Unit × Fin n') k Kf) (Pol (Unit × Fin n') k Kf) :=
  ∑ c, (X (((), s), a, c) : Pol (Unit × Fin n') k Kf) • pderiv (((), s), b, c)

/-- **The letter operator of the flat model**: `E_{s,a,b}` of `letE`, plus `δ_{ab}` times the Euler operator at odd
`s` (on letter degree `d_s` this is the covector action `δ_{ab}d_s − X_{s,b}∂_{s,a}`). -/
def flatE (s : Fin n') (a b : Fin k) : Derivation Kf (LPol (Fin n') k Kf) (LPol (Fin n') k Kf) :=
  letE (vecF n') s a b + if ¬Even s.val ∧ a = b then eul s else 0

/-- **`θ°` on a generator.** -/
theorem theta0_X (s : Fin n') (c : Fin k) : theta0 Kf (X (s, c)) =
    if Even s.val then X (((), s), c, 0) else (xMat ((), s)).adjugate (lastC k) c := aeval_X _ _

/-- **The shape condition** (Θ2), substitution form: `θ°(P)(g·x) = θ°(letter change of P)`. -/
theorem lsub_theta0 (g : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf) (P : LPol (Fin n') k Kf) :
    lsub g (theta0 Kf P) = theta0 Kf (linSub (letMat g) P) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨s, c⟩ := v
  simp only [AlgHom.comp_apply, theta0, linSub, aeval_X, map_sum, map_mul, algHom_C, letMat]
  split_ifs with hs
  · rw [lsub_X]
    simp only [MvPolynomial.algebraMap_eq]
  · have hx : (lsub g).mapMatrix (xMat (Φ := Unit × Fin n') (L := Kf) ((), s)) =
        (C : Kf →+* Pol (Unit × Fin n') k Kf).mapMatrix (g ((), s)) * xMat ((), s) := by
      ext a b
      simp [xMat, lsub_X, Matrix.mul_apply]
    have e := congrFun (congrFun (AlgHom.map_adjugate (lsub g) (xMat ((), s))) (lastC k)) c
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply] at e
    rw [e, hx, Matrix.adjugate_mul_distrib, Matrix.mul_apply, ← RingHom.map_adjugate]
    simp only [MvPolynomial.algebraMap_eq, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

omit [NeZero k] in
/-- **The row operator on a generator.** -/
theorem rowOp_X (s : Fin n') (a b : Fin k) (q : (Unit × Fin n') × Fin k × Fin k) :
    rowOp s a b (X q : Pol (Unit × Fin n') k Kf) =
      if q.1 = ((), s) ∧ q.2.1 = b then X (((), s), a, q.2.2) else 0 := by
  classical
  rw [rowOp, derivation_sum_apply]
  simp only [Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply]
  obtain ⟨⟨u, s'⟩, i, j⟩ := q
  by_cases h : s' = s ∧ i = b
  · obtain ⟨rfl, rfl⟩ := h
    rw [Finset.sum_eq_single j (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
    simp
  · rw [ite_eq_right (by simpa using h)]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with he
    · simp_all
    · rw [mul_zero]

/-- **The row operators on the cofactors of the last column** (the covector rule): `R_{ab}C_c = δ_{ab}C_c − δ_{ac}C_b`
on the block `s`, and `0` on the other blocks. -/
theorem rowOp_adj (s s' : Fin n') (a b c : Fin k) :
    rowOp s a b ((xMat (Φ := Unit × Fin n') (L := Kf) ((), s')).adjugate (lastC k) c) =
      if s = s' then (if a = b then (xMat ((), s')).adjugate (lastC k) c else 0) -
        (if a = c then (xMat ((), s')).adjugate (lastC k) b else 0) else 0 := by
  classical
  rw [Matrix.adjugate_apply, derivation_det]
  set x := xMat (Φ := Unit × Fin n') (L := Kf) ((), s')
  set M := x.updateRow c (Pi.single (lastC k) 1)
  have hD : ∀ i, (fun l => rowOp s a b (M i l)) =
      if i ≠ c ∧ s = s' ∧ i = b then (fun l => X (((), s), a, l)) else 0 := fun i => by
    funext l
    by_cases hi : i = c
    · have h0 : rowOp s a b (M i l) = 0 := by
        rw [hi]
        simp only [M, Matrix.updateRow_self]
        by_cases hl : l = lastC k
        · rw [hl, Pi.single_eq_same, Derivation.map_one_eq_zero]
        · rw [Pi.single_eq_of_ne hl, map_zero]
      rw [h0, ite_eq_right (fun h => h.1 hi)]
      rfl
    · have hM : M i l = X (((), s'), i, l) := by simp [M, Matrix.updateRow_apply, hi, x, xMat]
      rw [hM, rowOp_X]
      by_cases h : s = s' ∧ i = b
      · obtain ⟨rfl, rfl⟩ := h
        simp [hi]
      · rw [ite_eq_right (fun h' => h ⟨by simpa using h'.1.symm, h'.2⟩), ite_eq_right (by tauto)]
        rfl
  rw [Finset.sum_congr rfl fun i _ => by rw [hD i]]
  by_cases hs : s = s'
  swap
  · rw [ite_eq_right hs]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right (by tauto)]
    exact Matrix.det_eq_zero_of_row_eq_zero i fun l => by simp
  subst hs
  rw [ite_eq_left rfl]
  have hMa : x.adjugate (lastC k) c = M.det := Matrix.adjugate_apply _ _ _
  have h0 : ∀ i, ¬(i ≠ c ∧ s = s ∧ i = b) →
      (M.updateRow i (if i ≠ c ∧ s = s ∧ i = b then (fun l => X (((), s), a, l)) else 0)).det = 0 :=
    fun i hi => by
      rw [ite_eq_right hi]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun l => by simp
  by_cases hbc : b = c
  · subst hbc
    rw [Finset.sum_eq_zero fun i _ => h0 i (by tauto)]
    by_cases hab : a = b <;> simp [hab, hMa]
  rw [Finset.sum_eq_single b (fun i _ hib => h0 i (by tauto)) (by simp), ite_eq_left ⟨hbc, rfl, rfl⟩]
  by_cases hab : a = b
  · subst hab
    have hM : M.updateRow a (fun l => X (((), s), a, l)) = M := by
      ext i l
      by_cases hi : i = a
      · subst hi; simp [M, Matrix.updateRow_apply, hbc, x, xMat]
      · simp [Matrix.updateRow_apply, hi]
    rw [hM, ite_eq_left rfl, ite_eq_right hbc, sub_zero]
  by_cases hac : a = c
  · subst hac
    rw [ite_eq_right hab, ite_eq_left rfl, zero_sub, Matrix.adjugate_apply]
    have hsw : M.updateRow b (fun l => X (((), s), a, l)) =
        (x.updateRow b (Pi.single (lastC k) 1)).submatrix (Equiv.swap b a) id := by
      ext i l
      by_cases hib : i = b
      · subst hib; simp [M, Matrix.updateRow_apply, Equiv.swap_apply_left, hab, x, xMat]
      by_cases hia : i = a
      · subst hia; simp [M, Matrix.updateRow_apply, Equiv.swap_apply_right, hib]
      · simp [M, Matrix.updateRow_apply, Equiv.swap_apply_of_ne_of_ne hib hia, hib, hia]
    rw [hsw, Matrix.det_permute, Equiv.Perm.sign_swap hbc]
    simp
  · rw [ite_eq_right hab, ite_eq_right hac, sub_zero]
    refine Matrix.det_zero_of_row_eq (Ne.symm hab) ?_
    funext l
    simp [M, Matrix.updateRow_apply, hab, hac, x, xMat]

/-- **The letter/row intertwining** (D12): `R_{s,a,b}(θ°P) = θ°(E_{s,a,b}P)`, with the vector action at even `s` and
the covector action `δ_{ab}·deg − X_{s,b}∂_{s,a}` at odd `s` (`flatE`). -/
theorem rowOp_theta0 (s : Fin n') (a b : Fin k) (P : LPol (Fin n') k Kf) :
    rowOp s a b (theta0 Kf P) = theta0 Kf (flatE s a b P) := by
  classical
  refine derivation_comp _ _ _ (fun v => ?_) P
  obtain ⟨s', c⟩ := v
  have hE : flatE s a b (X (s', c) : LPol (Fin n') k Kf) = if s = s' then (if Even s.val then
      (if c = b then X (s, a) else 0) else (if a = b then X (s, c) else 0) - if a = c then X (s, b) else 0) else 0 := by
    rw [flatE, Derivation.add_apply, letE_X, apply_ite (fun D : Derivation Kf _ _ => D (X (s', c)))]
    simp only [eul_X, Derivation.zero_apply, vecF, decide_eq_true_eq, Prod.mk.injEq]
    by_cases hss : s = s'
    · subst hss
      by_cases hs : Even s.val <;> by_cases hab : a = b <;> simp [hs, hab, sub_eq_add_neg, add_comm, eq_comm]
    · simp [hss, Ne.symm hss]
  rw [theta0_X, hE]
  by_cases hss : s = s'
  · subst hss
    rw [ite_eq_left rfl]
    by_cases hs : Even s.val
    · rw [ite_eq_left hs, ite_eq_left hs, rowOp_X]
      by_cases hcb : c = b
      · subst hcb
        rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl, theta0_X, ite_eq_left hs]
      · rw [ite_eq_right (fun h => hcb h.2), ite_eq_right hcb, map_zero]
    · rw [ite_eq_right hs, ite_eq_right hs, rowOp_adj, ite_eq_left rfl, map_sub, apply_ite (theta0 Kf),
        apply_ite (theta0 Kf), theta0_X, theta0_X, map_zero, ite_eq_right hs, ite_eq_right hs]
  · rw [ite_eq_right hss, map_zero]
    split_ifs with hs'
    · rw [rowOp_X, ite_eq_right (fun h => hss (by simpa using h.1.symm))]
    · rw [rowOp_adj, ite_eq_right hss]

omit [NeZero k] in
/-- **Row operators are Fock-contravariant**: `⟨R_{s,a,b}F, G⟩ = ⟨F, R_{s,b,a}G⟩`. -/
theorem fock_rowOp (s : Fin n') (a b : Fin k) (F G : Pol (Unit × Fin n') k Kf) :
    fockWith (RingHom.id Kf) (rowOp s a b F) G = fockWith (RingHom.id Kf) F (rowOp s b a G) := by
  rw [rowOp, rowOp, derivation_sum_apply, derivation_sum_apply, fock_sum_left, fock_sum_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Derivation.smul_apply, Derivation.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm (X _), fock_mul_X,
    fock_X_mul]

/-- **Lowering and raising letters through `θ°`**: for `a ≠ b`, `θ°(X_{s,a}∂_{s,b}P)` is `R_{s,a,b}(θ°P)` at even
`s` and `−R_{s,b,a}(θ°P)` at odd `s`. -/
theorem theta0_X_mul_pderiv (s : Fin n') {a b : Fin k} (hab : a ≠ b) (P : LPol (Fin n') k Kf) :
    theta0 Kf (X (s, a) * pderiv (s, b) P) =
      if Even s.val then rowOp s a b (theta0 Kf P) else -rowOp s b a (theta0 Kf P) := by
  have hE : ∀ a b : Fin k, a ≠ b → flatE s a b P = letE (vecF n') s a b P := fun a b hab => by
    rw [flatE, Derivation.add_apply, ite_eq_right (fun h => hab h.2), Derivation.zero_apply, add_zero]
  by_cases hs : Even s.val
  · rw [ite_eq_left hs, rowOp_theta0, hE a b hab, letE, ite_eq_left (by simp [vecF, hs]), Derivation.smul_apply,
      smul_eq_mul]
  · rw [ite_eq_right hs, rowOp_theta0, hE b a (Ne.symm hab), letE, ite_eq_right (by simp [vecF, hs]),
      Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul, map_neg, neg_neg]

variable [CharZero Kf]

omit [NeZero k] in
/-- **Row operators are contravariant for the normalised Fock form.** -/
theorem nf_rowOp (lam : Unit × Fin n' → Fin k → ℤ) (s : Fin n') (a b : Fin k) (F G : Pol (Unit × Fin n') k Kf) :
    nf lam (rowOp s a b F) G = nf lam F (rowOp s b a G) := by
  rw [nf_apply, nf_apply, fock_rowOp]

omit [NeZero k] [CharZero Kf] in
/-- **The last coordinate of `Fin (m + 1)`** is `Fin.last m`. -/
theorem lastC_succ (m : ℕ) : lastC (m + 1) = Fin.last m := Fin.ext (by simp [lastC])

omit [CharZero Kf] in
/-- **The shape of `∇` at the flat weight**: `(d_s, 0, …, 0)` at even `s` and `(d_s, …, d_s, 0)` at odd `s`. -/
theorem nu1_flatWt (hk : 2 ≤ k) (d : Fin n' → ℕ) (s : Fin n') (i : Fin k) :
    nu1 (flatWt d) ((), s) i =
      if Even s.val then (if i = 0 then d s else 0) else (if i = lastC k then 0 else d s) := by
  have hl0 : lastC k ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp [lastC] at this
    omega
  have hd : ∀ w : Fin k → ℤ, detShift w = w (lastC k) := fun w => by
    simp only [detShift, dite_eq_left (NeZero.pos k)]
    rfl
  have hrev : ∀ i : Fin k, i.rev = 0 ↔ i = lastC k := fun i => by
    simp only [Fin.ext_iff, Fin.val_rev, Fin.val_zero, lastC]
    omega
  have hlr : (lastC k).rev = 0 := (hrev _).2 rfl
  simp only [nu1, natW, hd, wt1, blockWt, lamAt, flatWt]
  by_cases hs : Even s.val
  · simp only [hs, ite_true, Pi.single_apply, hl0, ite_false, sub_zero]
    split_ifs <;> simp
  · simp only [hs, ite_false, Pi.single_apply, hlr, ite_true]
    by_cases hi : i = lastC k
    · simp [hi, hlr]
    · simp [hi, (hrev i).not.2 hi]

/-- **The extreme letters of the flat model**: coordinate `0` at even positions, `k − 1` at odd positions. -/
def extF (n' k : ℕ) [NeZero k] : Fin n' → Fin k := fun s => if Even s.val then 0 else lastC k

omit [CharZero Kf] in
/-- **The cofactors of the last column are signed minors** of the first `k − 1` columns. -/
theorem adj_eq_minor (m : ℕ) (s : Fin n') (c : Fin (m + 2)) :
    (xMat (Φ := Unit × Fin n') (L := Kf) ((), s)).adjugate (Fin.last (m + 1)) c =
      (-1) ^ (c.val + (m + 1)) * minor ((), s) (⟨m, by omega⟩ : Fin (m + 2)) c.succAbove := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  rfl

omit [CharZero Kf] in
/-- **The multiplicities of the leading minors** at the flat weight: `d_s` at size `1` (even `s`) or `k − 1` (odd `s`),
`0` otherwise. -/
theorem mult_flatWt (m : ℕ) (d : Fin n' → ℕ) (s : Fin n') (s' : Fin (m + 2)) :
    mult (nu1 (flatWt (k := m + 2) d) ((), s)) s' = if s'.val = (if Even s.val then 0 else m) then d s else 0 := by
  have hν := nu1_flatWt (k := m + 2) (by omega) d s
  rw [mult]
  simp only [hν, lastC_succ, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  split_ifs <;> first | omega | simp_all

omit [CharZero Kf] in
/-- **The highest-weight vector of the flat weight** is `θ°` of the extreme monomial. -/
theorem hw_flatWt (hk : 2 ≤ k) (d : Fin n' → ℕ) :
    hw Kf (nu1 (flatWt (k := k) d)) = theta0 Kf (monomial (extr (extF n' k) d) 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hR : theta0 Kf (monomial (extr (extF n' (m + 2)) d) 1) =
      ∏ s, theta0 Kf (X (s, extF n' (m + 2) s)) ^ d s := by
    rw [monomial_eq, map_mul, algHom_C, map_one, one_mul, Finsupp.prod, map_prod,
      Finset.prod_subset (Finset.subset_univ _) (fun v _ hv => by
        rw [Finsupp.notMem_support_iff.1 hv, pow_zero, map_one]), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Finset.prod_eq_single (extF n' (m + 2) s) (fun c _ hc => by simp [extr, hc]) (by simp)]
    simp [extr]
  rw [hR, hw, Fintype.prod_prod_type, Fintype.prod_unique]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hmult := mult_flatWt m d s
  simp only [hmult, theta0_X, extF, lastC_succ]
  by_cases hs : Even s.val
  · rw [Finset.prod_eq_single ⟨0, by omega⟩ (fun b _ hb => by
      rw [ite_eq_left hs, ite_eq_right (fun h => hb (Fin.ext h)), pow_zero]) (by simp)]
    simp only [hs, ite_true]
    rw [minor, Matrix.det_fin_one]
    rfl
  · rw [Finset.prod_eq_single ⟨m, by omega⟩ (fun b _ hb => by
      rw [ite_eq_right hs, ite_eq_right (fun h => hb (Fin.ext h)), pow_zero]) (by simp)]
    simp only [hs, ite_false, ite_true]
    rw [adj_eq_minor, Fin.val_last, Fin.succAbove_last, Even.neg_one_pow ⟨m + 1, rfl⟩, one_mul]
    rfl

omit [CharZero Kf] in
/-- **The column weight of `θ°` of a letter**: `x_{s,c,0}` has degree one in column `0`, the cofactor `C_c` degree one
in each column but the last. -/
theorem theta0_X_isWH (hk : 2 ≤ k) (s : Fin n') (c : Fin k) :
    IsWeightedHomogeneous (colW (Unit × Fin n') k) (theta0 Kf (X (s, c)))
      (Pi.single ((), s) (if Even s.val then Pi.single 0 1 else fun b => if b = lastC k then 0 else 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [theta0_X]
  by_cases hs : Even s.val
  · rw [ite_eq_left hs, ite_eq_left hs]
    exact isWeightedHomogeneous_X Kf _ _
  · rw [ite_eq_right hs, ite_eq_right hs, lastC_succ, adj_eq_minor,
      show ((-1 : Pol (Unit × Fin n') (m + 2) Kf) ^ (c.val + (m + 1))) = C ((-1) ^ (c.val + (m + 1))) by simp]
    convert (minor_isWH (L := Kf) ((), s) (⟨m, by omega⟩ : Fin (m + 2)) c.succAbove).C_mul _ using 2
    funext b
    simp only [Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega

omit [CharZero Kf] in
/-- **`θ°` lands in `∇`** (Θ1): `θ°` maps the letter polynomials of multidegree `d` into `∇_{Kf}` of the flat weight;
its images are invariant under `x ↦ x·u` as the cofactors of the last column are, and the column degrees add up. -/
theorem theta0_mem_nabla (hk : 2 ≤ k) {d : Fin n' → ℕ} {P : LPol (Fin n') k Kf} (hP : P ∈ LHom Kf d) :
    theta0 Kf P ∈ nabla Kf (nu1 (flatWt d)) := by
  rw [mem_nabla_iff]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [LHom, mem_weightedHomogeneousSubmodule] at hP
    rw [P.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun μ hμ => ?_
    rw [mem_weightedHomogeneousSubmodule, monomial_eq, map_mul, algHom_C, MvPolynomial.algebraMap_eq,
      Finsupp.prod, map_prod]
    have hsum : ∑ v ∈ μ.support, μ v • (Pi.single ((), v.1) (if Even v.1.val then Pi.single 0 1 else
        fun b => if b = lastC k then 0 else 1) : Unit × Fin n' → Fin k → ℕ) = nu1 (flatWt d) := by
      rw [Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by rw [Finsupp.notMem_support_iff.1 hv, zero_smul])]
      funext τ b
      obtain ⟨⟨⟩, s⟩ := τ
      have hd := congrFun (hP (mem_support_iff.1 hμ)) s
      rw [weight_rowW_apply] at hd
      rw [nu1_flatWt hk, Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type,
        Finset.sum_eq_single s (fun s' _ hs' => Finset.sum_eq_zero fun c _ => by
          simp [Ne.symm hs']) (by simp)]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      rw [← hd]
      by_cases hs : Even s.val
      · simp only [hs, ite_true]
        by_cases hb : b = 0 <;> simp [hb]
      · simp only [hs, ite_false]
        by_cases hb : b = lastC k <;> simp [hb]
    rw [← hsum]
    exact (IsWeightedHomogeneous.prod _ _ _ fun v _ => by
      rw [map_pow]
      exact (theta0_X_isWH (Kf := Kf) hk v.1 v.2).pow (μ v)).C_mul _
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hθ : (rsub u).comp (theta0 Kf) = theta0 Kf := by
      refine MvPolynomial.algHom_ext fun v => ?_
      obtain ⟨s, c⟩ := v
      rw [AlgHom.comp_apply, theta0_X]
      by_cases hs : Even s.val
      · rw [ite_eq_left hs, rsub_X, Finset.sum_eq_single 0 (fun e _ he => by
          rw [(hu _).1 (Fin.pos_iff_ne_zero.2 he), map_zero, mul_zero]) (by simp), (hu _).2, map_one, mul_one]
      · rw [ite_eq_right hs, lastC_succ, adj_eq_minor, map_mul, map_pow, map_neg, map_one, rsub_minor_rows hu]
    rw [← AlgHom.comp_apply, hθ]

/-- **Factorials are nonzero** in characteristic `0`. -/
theorem mfact_ne_zero {σ' : Type*} [Fintype σ'] (μ : σ' →₀ ℕ) : (mfact μ : Kf) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

/-- **The Fock comparison** (N2-e): `nf(θ°P, θ°Q) = ⟨P, Q⟩/∏_s d_s!` on the letter polynomials of multidegree `d`.
Both sides are contravariant for the letter operators (the row operators are Fock-contravariant and `θ°` intertwines
them with the letter operators, `rowOp_theta0`), so they agree up to the value at the extreme monomial
(`bilin_eq_lfock`), whose image is the highest-weight vector (`hw_flatWt`), of normalised norm `1`. -/
theorem nf_theta0 (hk : 2 ≤ k) {d : Fin n' → ℕ} {P Q : LPol (Fin n') k Kf} (hP : P ∈ LHom Kf d)
    (hQ : Q ∈ LHom Kf d) :
    nf (wt1 (flatWt d)) (theta0 Kf P) (theta0 Kf Q) = lfock P Q / ∏ s, ((d s).factorial : Kf) := by
  set B := (nf (wt1 (flatWt (k := k) d))).compl₁₂ (theta0 Kf).toLinearMap (theta0 Kf).toLinearMap
  have hB : ∀ l a b, a ≠ b → ∀ P Q : LPol (Fin n') k Kf,
      B (X (l, a) * pderiv (l, b) P) Q = B P (X (l, b) * pderiv (l, a) Q) := by
    intro l a b hab P Q
    simp only [B, LinearMap.compl₁₂_apply, AlgHom.toLinearMap_apply, theta0_X_mul_pderiv l hab,
      theta0_X_mul_pderiv l (Ne.symm hab)]
    split_ifs
    · exact nf_rowOp _ _ _ _ _ _
    · rw [map_neg, LinearMap.neg_apply, nf_rowOp, map_neg]
  have h := bilin_eq_lfock B (extF n' k) hB hP hQ
  have h1 : B (monomial (extr (extF n' k) d) 1) (monomial (extr (extF n' k) d) 1) = 1 := by
    simp only [B, LinearMap.compl₁₂_apply, AlgHom.toLinearMap_apply, ← hw_flatWt hk, nf_apply]
    rw [fock_hw_eq_kappa Kf (wt1 (flatWt d))]
    exact div_self ((map_ne_zero _).2 (HermForms.kappa_pos _).ne')
  rw [h1, mul_one] at h
  rw [eq_div_iff (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)), ← h]
  rfl

/-- **`θ°` is nondegenerate** (D12): a letter polynomial of multidegree `d` whose image pairs to `0` with the images
of all of them is `0` (by the Fock comparison, `⟨P, X^μ⟩ = P_μ·μ!`). -/
theorem theta0_nondeg (hk : 2 ≤ k) {d : Fin n' → ℕ} {P : LPol (Fin n') k Kf} (hP : P ∈ LHom Kf d)
    (h : ∀ Q ∈ LHom Kf d, nf (wt1 (flatWt d)) (theta0 Kf P) (theta0 Kf Q) = 0) : P = 0 := by
  refine MvPolynomial.ext _ _ fun μ => ?_
  rw [show (0 : LPol (Fin n') k Kf).coeff μ = 0 by simp]
  by_cases hμ : Finsupp.weight (rowW (Fin n') k) μ = d
  · have hQ : (monomial μ 1 : LPol (Fin n') k Kf) ∈ LHom Kf d := isWeightedHomogeneous_monomial _ _ _ hμ
    have := h _ hQ
    rw [nf_theta0 hk hP hQ, div_eq_zero_iff, lfock_eq_sum (S := {μ}) support_monomial_subset,
      Finset.sum_singleton, coeff_monomial, ite_eq_left rfl, mul_one] at this
    rcases this with h1 | h1
    · exact (mul_eq_zero.1 h1).resolve_right (mfact_ne_zero μ)
    · exact absurd h1 (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  · rw [LHom, mem_weightedHomogeneousSubmodule] at hP
    by_contra hc
    exact hμ (hP hc)

/-- **`θ°` is injective** on the letter polynomials of multidegree `d`. -/
theorem theta0_injOn (hk : 2 ≤ k) (d : Fin n' → ℕ) :
    Set.InjOn (theta0 Kf) (LHom Kf (k := k) d : Set (LPol (Fin n') k Kf)) := by
  intro P hP Q hQ hPQ
  have h := theta0_nondeg hk (sub_mem hP hQ) fun R _ => by rw [map_sub, hPQ, sub_self, map_zero, LinearMap.zero_apply]
  exact sub_eq_zero.1 h

omit [CharZero Kf] in
/-- **The shape condition** (Θ2): a twist of `θ°` by invertible block matrices is a nonzero multiple of `θ°` after an
invertible letter change (by `g_s` at even `s`, by `adj(g_s)ᵀ` at odd `s`). -/
theorem theta_shape (lam : Unit × Fin n' → Fin k → ℤ) {g : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf}
    (hg : ∀ b, IsUnit (g b).det) :
    ∃ c : Kf, c ≠ 0 ∧ ∃ A : Fin n' → Matrix (Fin k) (Fin k) Kf, (∀ s, IsUnit (A s).det) ∧
      ∀ P, twist lam g (theta0 Kf P) = c • theta0 Kf (linSub A P) := by
  refine ⟨∏ b, (g b).det ^ detShift (lam b), Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (hg b).ne_zero,
    letMat g, fun s => ?_, fun P => ?_⟩
  · unfold letMat
    split_ifs
    · exact hg _
    · rw [Matrix.det_transpose, Matrix.det_adjugate]
      exact (hg _).pow _
  · rw [twist, lsub_theta0, C_mul']

/-! ### `θ°` and the bideterminants: the integral structure (N2-b) -/

omit [CharZero Kf] in
/-- **A minor on the first `k − 1` columns with arbitrary rows** is `0` (two equal rows) or `±` the cofactor of the
missing row (sort the rows). -/
theorem minor_eq_zero_or (m : ℕ) (s : Fin n') (I : Fin (m + 1) → Fin (m + 2)) :
    minor ((), s) (⟨m, by omega⟩ : Fin (m + 2)) I = (0 : Pol (Unit × Fin n') (m + 2) Kf) ∨
      ∃ c : Fin (m + 2), minor (L := Kf) ((), s) ⟨m, by omega⟩ I = (xMat ((), s)).adjugate (Fin.last (m + 1)) c ∨
        minor (L := Kf) ((), s) ⟨m, by omega⟩ I = -(xMat ((), s)).adjugate (Fin.last (m + 1)) c := by
  by_cases hI : Function.Injective I
  · obtain ⟨c, hc⟩ : ∃ c, ∀ j, I j ≠ c := by
      by_contra h
      push Not at h
      have := Fintype.card_le_of_surjective I fun c => (h c).imp fun _ hj => hj
      simp at this
    choose π hπ using fun j => Fin.exists_succAbove_eq (hc j)
    have hπi : Function.Injective π := fun a b h => hI (by rw [← hπ a, ← hπ b, h])
    set e := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπi)
    have hmin : minor (L := Kf) ((), s) (⟨m, by omega⟩ : Fin (m + 2)) I =
        ((Equiv.Perm.sign e : ℤ) : Pol (Unit × Fin n') (m + 2) Kf) *
          minor ((), s) (⟨m, by omega⟩ : Fin (m + 2)) c.succAbove := by
      rw [minor, minor, ← Matrix.det_permute]
      congr 1
      ext i j
      simp [e, hπ]
    have hadj := adj_eq_minor (Kf := Kf) m s c
    have hsq : ((-1 : Pol (Unit × Fin n') (m + 2) Kf) ^ (c.val + (m + 1))) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hmin' : minor (L := Kf) ((), s) (⟨m, by omega⟩ : Fin (m + 2)) c.succAbove =
        (-1) ^ (c.val + (m + 1)) * (xMat ((), s)).adjugate (Fin.last (m + 1)) c := by
      rw [hadj, ← mul_assoc, ← sq, hsq, one_mul]
    right
    refine ⟨c, ?_⟩
    rw [hmin, hmin']
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;>
      rcases neg_one_pow_eq_or (Pol (Unit × Fin n') (m + 2) Kf) (c.val + (m + 1)) with h' | h' <;>
      simp [h, h']
  · left
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hI
    exact Matrix.det_zero_of_row_eq hne (funext fun j => by simp [hab])

/-- **`F` is `±θ°(X^ν)`.** -/
def SgnIm (F : Pol (Unit × Fin n') k Kf) (ν : Fin n' × Fin k →₀ ℕ) : Prop :=
  F = theta0 Kf (monomial ν 1) ∨ F = -theta0 Kf (monomial ν 1)

omit [CharZero Kf] in
/-- **Products of signed images.** -/
theorem prod_sgnIm {ι' : Type*} (t : Finset ι') (f : ι' → Pol (Unit × Fin n') k Kf) (w : ι' → Fin n' → ℕ)
    (h : ∀ i ∈ t, f i = 0 ∨ ∃ ν, Finsupp.weight (rowW (Fin n') k) ν = w i ∧ SgnIm (f i) ν) :
    ∏ i ∈ t, f i = 0 ∨ ∃ ν, Finsupp.weight (rowW (Fin n') k) ν = ∑ i ∈ t, w i ∧ SgnIm (∏ i ∈ t, f i) ν := by
  classical
  induction t using Finset.induction_on with
  | empty => exact Or.inr ⟨0, by simp, Or.inl (by simp)⟩
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    rcases h a (Finset.mem_insert_self a t) with h0 | ⟨νa, hwa, hsa⟩
    · exact Or.inl (by rw [h0, zero_mul])
    rcases ih fun i hi => h i (Finset.mem_insert_of_mem hi) with h0 | ⟨νt, hwt, hst⟩
    · exact Or.inl (by rw [h0, mul_zero])
    refine Or.inr ⟨νa + νt, by rw [map_add, hwa, hwt], ?_⟩
    have hm : theta0 Kf (monomial (νa + νt) 1 : LPol (Fin n') k Kf) =
        theta0 Kf (monomial νa 1) * theta0 Kf (monomial νt 1) := by
      rw [← map_mul, monomial_mul_monomial, one_mul]
    rcases hsa with h1 | h1 <;> rcases hst with h2 | h2 <;> simp [SgnIm, h1, h2, hm]

omit [CharZero Kf] in
/-- **Every bideterminant of the flat weight is `0` or `±θ°` of a monomial** of multidegree `d`: at an even block it is
a product of entries of column `0`, at an odd block a product of minors on the first `k − 1` columns, each `0` or `±` a
cofactor of the last column. -/
theorem bidet_flatWt (hk : 2 ≤ k) (d : Fin n' → ℕ)
    (rows : (τ : Unit × Fin n') → (s : Fin k) → Fin (mult (nu1 (flatWt (k := k) d) τ) s) → Fin (s + 1) → Fin k) :
    bidet Kf (nu1 (flatWt d)) rows = 0 ∨
      ∃ ν, Finsupp.weight (rowW (Fin n') k) ν = d ∧ SgnIm (bidet Kf (nu1 (flatWt d)) rows) ν := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hd : (∑ τ : Unit × Fin n', d τ.2 • (Pi.single τ.2 1 : Fin n' → ℕ)) = d := by
    funext s
    rw [Finset.sum_apply, Fintype.sum_prod_type, Fintype.sum_unique,
      Finset.sum_eq_single s (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  rw [bidet]
  suffices H : ∀ τ ∈ (Finset.univ : Finset (Unit × Fin n')),
      (∏ s', ∏ c, minor τ s' (rows τ s' c)) = (0 : Pol (Unit × Fin n') (m + 2) Kf) ∨
        ∃ ν, Finsupp.weight (rowW (Fin n') (m + 2)) ν = d τ.2 • (Pi.single τ.2 1 : Fin n' → ℕ) ∧
          SgnIm (∏ s', ∏ c, minor τ s' (rows τ s' c)) ν by
    rcases prod_sgnIm _ _ _ H with h | ⟨ν, hν, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨ν, hν.trans hd, h⟩
  intro τ _
  obtain ⟨⟨⟩, s⟩ := τ
  have hs : (∑ s' : Fin (m + 2), mult (nu1 (flatWt (k := m + 2) d) ((), s)) s' • (Pi.single s 1 : Fin n' → ℕ)) =
      d s • Pi.single s 1 := by
    rw [← Finset.sum_smul]
    congr 1
    simp only [mult_flatWt]
    rw [Finset.sum_eq_single (⟨if Even s.val then 0 else m, by split_ifs <;> omega⟩ : Fin (m + 2))
      (fun b _ hb => by rw [ite_eq_right (fun h => hb (Fin.ext h))]) (by simp)]
    simp
  refine (prod_sgnIm (Finset.univ : Finset (Fin (m + 2)))
    (fun s' => ∏ c, minor (L := Kf) ((), s) s' (rows ((), s) s' c))
    (fun s' => mult (nu1 (flatWt (k := m + 2) d) ((), s)) s' • (Pi.single s 1 : Fin n' → ℕ))
    fun s' _ => ?_).imp id fun ⟨ν, hν, h⟩ => ⟨ν, hν.trans hs, h⟩
  have hc : (∑ _c : Fin (mult (nu1 (flatWt (k := m + 2) d) ((), s)) s'), (Pi.single s 1 : Fin n' → ℕ)) =
      mult (nu1 (flatWt (k := m + 2) d) ((), s)) s' • Pi.single s 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  refine (prod_sgnIm (Finset.univ : Finset (Fin (mult (nu1 (flatWt (k := m + 2) d) ((), s)) s')))
    (fun c => minor (L := Kf) ((), s) s' (rows ((), s) s' c)) (fun _ => (Pi.single s 1 : Fin n' → ℕ))
    fun c _ => ?_).imp id fun ⟨ν, hν, h⟩ => ⟨ν, hν.trans hc, h⟩
  have hs' : s'.val = if Even s.val then 0 else m := by
    by_contra h
    have hm := mult_flatWt m d s s'
    rw [ite_eq_right h] at hm
    have := c.isLt
    omega
  by_cases he : Even s.val
  · rw [ite_eq_left he] at hs'
    obtain rfl : s' = ⟨0, Nat.zero_lt_succ (m + 1)⟩ := Fin.ext hs'
    refine Or.inr ⟨Finsupp.single (s, rows ((), s) ⟨0, Nat.zero_lt_succ (m + 1)⟩ c 0) 1,
      by rw [Finsupp.weight_single, one_smul]; rfl, Or.inl ?_⟩
    rw [← X, theta0_X, ite_eq_left he, minor, Matrix.det_fin_one]
    rfl
  · rw [ite_eq_right he] at hs'
    obtain rfl : s' = ⟨m, Nat.lt_add_of_pos_right two_pos⟩ := Fin.ext hs'
    rcases minor_eq_zero_or (Kf := Kf) m s (rows ((), s) ⟨m, Nat.lt_add_of_pos_right two_pos⟩ c) with h0 | ⟨b, hb⟩
    · exact Or.inl h0
    refine Or.inr ⟨Finsupp.single (s, b) 1, by rw [Finsupp.weight_single, one_smul]; rfl, ?_⟩
    rw [SgnIm, ← X, theta0_X, ite_eq_right he, lastC_succ]
    exact hb

omit [CharZero Kf] in
/-- **The flat weight is dominant**: its `∇`-shapes are antitone. -/
theorem antitone_nu1_flatWt (hk : 2 ≤ k) (d : Fin n' → ℕ) (b : Unit × Fin n') :
    Antitone (nu1 (flatWt (k := k) d) b) := by
  obtain ⟨⟨⟩, s⟩ := b
  intro i j hij
  have hij' := Fin.le_def.1 hij
  have hjk := j.isLt
  simp only [nu1_flatWt hk]
  by_cases hs : Even s.val
  · simp only [hs, ite_true]
    by_cases hj : j = 0
    · have : i = 0 := Fin.ext (by have := Fin.ext_iff.1 hj; simp only [Fin.val_zero] at this ⊢; omega)
      simp [hj, this]
    · rw [ite_eq_right hj]
      exact Nat.zero_le _
  · simp only [hs, ite_false]
    by_cases hi : i = lastC k
    · have : j = lastC k := Fin.ext (by have := Fin.ext_iff.1 hi; simp only [lastC] at this ⊢; omega)
      simp [hi, this]
    · rw [ite_eq_right hi]
      split_ifs <;> simp

/-- **`θ°` is onto `∇`** (Θ1): every element of `∇_{Kf}` of the flat weight is `θ°` of a letter polynomial of
multidegree `d` (the bideterminants span, `span_bidet`). -/
theorem theta0_surj (hk : 2 ≤ k) {d : Fin n' → ℕ} {F : Pol (Unit × Fin n') k Kf}
    (hF : F ∈ nabla Kf (nu1 (flatWt d))) : ∃ P ∈ LHom Kf d, theta0 Kf P = F := by
  rw [← span_bidet (antitone_nu1_flatWt hk d)] at hF
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨rows, rfl⟩ := hy
    rcases bidet_flatWt (Kf := Kf) hk d rows with h0 | ⟨ν, hν, h | h⟩
    · exact ⟨0, zero_mem _, by rw [h0, map_zero]⟩
    · exact ⟨monomial ν 1, isWeightedHomogeneous_monomial _ _ _ hν, h.symm⟩
    · exact ⟨-monomial ν 1, neg_mem (isWeightedHomogeneous_monomial _ _ _ hν), by rw [map_neg, h]⟩
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, rfl⟩ := hx
    obtain ⟨Q, hQ, rfl⟩ := hy
    exact ⟨P + Q, add_mem hP hQ, map_add _ _ _⟩
  | smul a x _ hx =>
    obtain ⟨P, hP, rfl⟩ := hx
    exact ⟨a • P, Submodule.smul_mem _ a hP, map_smul _ _ _⟩

omit [CharZero Kf] in
/-- **The `A`-structure** (N2-b), one direction: the elements of `∇_A` of the flat weight are the `θ°` of letter
polynomials of multidegree `d` with coefficients in `A`, for every subring `A ⊆ Kf`. -/
theorem exists_theta0_of_mem_nablaInt (hk : 2 ≤ k) {A : Subring Kf} {d : Fin n' → ℕ}
    {F : Pol (Unit × Fin n') k Kf} (hF : F ∈ nablaInt A (nu1 (flatWt d))) :
    ∃ P ∈ LHom Kf d, (∀ μ, P.coeff μ ∈ A) ∧ theta0 Kf P = F := by
  classical
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨rows, rfl⟩ := hy
    rcases bidet_flatWt (Kf := Kf) hk d rows with h0 | ⟨ν, hν, h | h⟩
    · exact ⟨0, zero_mem _, fun _ => by simp, by rw [h0, map_zero]⟩
    · exact ⟨monomial ν 1, isWeightedHomogeneous_monomial _ _ _ hν, fun μ => by
        rw [coeff_monomial]; split_ifs <;> simp, h.symm⟩
    · exact ⟨-monomial ν 1, neg_mem (isWeightedHomogeneous_monomial _ _ _ hν), fun μ => by
        rw [coeff_neg, coeff_monomial]; split_ifs <;> simp, by rw [map_neg, h]⟩
  | zero => exact ⟨0, zero_mem _, fun _ => by simp, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, hPA, rfl⟩ := hx
    obtain ⟨Q, hQ, hQA, rfl⟩ := hy
    refine ⟨P + Q, add_mem hP hQ, fun μ => ?_, map_add _ _ _⟩
    rw [show (P + Q).coeff μ = P.coeff μ + Q.coeff μ by simp]
    exact add_mem (hPA μ) (hQA μ)
  | smul a x _ hx =>
    obtain ⟨P, hP, hPA, rfl⟩ := hx
    refine ⟨(a : Kf) • P, Submodule.smul_mem _ _ hP, fun μ => ?_, by rw [map_smul]; rfl⟩
    rw [coeff_smul, smul_eq_mul]
    exact mul_mem a.2 (hPA μ)

/-- **The `A`-structure** (N2-b): for a letter polynomial `P` of multidegree `d`, `θ°P ∈ ∇_A` of the flat weight iff
the coefficients of `P` lie in `A`. `⇐`: each `θ°(X^μ)` is `±` a bideterminant, as the bideterminants span `∇_{Kf}`
and `θ°` is injective on multidegree `d`, so the monomials they give (`bidet_flatWt`) are all of them. -/
theorem theta0_mem_nablaInt_iff (hk : 2 ≤ k) {A : Subring Kf} {d : Fin n' → ℕ} {P : LPol (Fin n') k Kf}
    (hP : P ∈ LHom Kf d) : theta0 Kf P ∈ nablaInt A (nu1 (flatWt d)) ↔ ∀ μ, P.coeff μ ∈ A := by
  classical
  constructor
  · intro h
    obtain ⟨Q, hQ, hQA, hQP⟩ := exists_theta0_of_mem_nablaInt hk h
    rw [theta0_injOn hk d hQ hP hQP] at hQA
    exact hQA
  intro hA
  -- the monomials of multidegree `d` that are `±θ°`-images of bideterminants
  set S : Set (Fin n' × Fin k →₀ ℕ) := {ν | Finsupp.weight (rowW (Fin n') k) ν = d ∧
    ∃ rows, SgnIm (bidet Kf (nu1 (flatWt d)) rows) ν}
  have hmono : ∀ μ, Finsupp.weight (rowW (Fin n') k) μ = d → μ ∈ S := fun μ hμ => by
    have hQ : (monomial μ 1 : LPol (Fin n') k Kf) ∈ LHom Kf d := isWeightedHomogeneous_monomial _ _ _ hμ
    have hsp := theta0_mem_nabla hk hQ
    rw [← span_bidet (antitone_nu1_flatWt hk d)] at hsp
    have hsub : Submodule.span Kf (Set.range (bidet Kf (nu1 (flatWt (k := k) d)))) ≤
        (restrictSupport Kf S).map (theta0 Kf).toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨rows, rfl⟩
      rcases bidet_flatWt (Kf := Kf) hk d rows with h0 | ⟨ν, hν, h | h⟩
      · rw [h0]; exact zero_mem _
      · exact ⟨monomial ν 1, (monomial_mem_restrictSupport Kf).2 (Or.inl ⟨hν, rows, Or.inl h⟩), h.symm⟩
      · exact ⟨-monomial ν 1, neg_mem ((monomial_mem_restrictSupport Kf).2 (Or.inl ⟨hν, rows, Or.inr h⟩)),
          by rw [map_neg, h]; rfl⟩
    obtain ⟨R, hR, hRθ⟩ := hsub hsp
    have hRd : R ∈ LHom Kf d := by
      rw [LHom, mem_weightedHomogeneousSubmodule]
      intro ν hν
      exact ((mem_restrictSupport_iff Kf).1 hR (mem_support_iff.2 hν)).1
    have := theta0_injOn hk d hRd hQ hRθ
    have hμR : μ ∈ R.support := by
      rw [this, support_monomial, ite_eq_right one_ne_zero]
      exact Finset.mem_singleton_self μ
    exact (mem_restrictSupport_iff Kf).1 hR hμR
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  obtain ⟨-, rows, h⟩ := hmono μ (hP (mem_support_iff.1 hμ))
  rw [show (monomial μ (P.coeff μ) : LPol (Fin n') k Kf) = P.coeff μ • monomial μ 1 by
    rw [smul_monomial, smul_eq_mul, mul_one], map_smul]
  have hb : theta0 Kf (monomial μ 1) ∈ nablaInt A (nu1 (flatWt (k := k) d)) := by
    rcases h with h | h
    · rw [← h]; exact Submodule.subset_span ⟨rows, rfl⟩
    · rw [← neg_neg (theta0 Kf (monomial μ 1)), ← h]; exact neg_mem (Submodule.subset_span ⟨rows, rfl⟩)
  exact Submodule.smul_mem _ (⟨P.coeff μ, hA μ⟩ : A) hb

/-! ### The edge lattices in the flat model (N2-c) -/

section Edge

variable {W Qq O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p : ℕ}

/-- **The plane matrix** `diag(x on the plane)`: `x` at the coordinates `< r`, `1` at the others. -/
def planeDiag {R : Type*} [Zero R] [One R] (r : ℕ) (x : R) : Matrix (Fin k) (Fin k) R :=
  Matrix.diagonal fun i => if i.val < r then x else 1

variable (W) in
/-- **The lattice spanned by the columns** of `B`. -/
def colSpan (B : Matrix (Fin k) (Fin k) Qq) : Submodule W (Fin k → Qq) :=
  Submodule.span W (Set.range fun l i => B i l)

/-- **The flat model at a basis matrix** `h`: `Θ_h = twist_{ι σ^s(h)⁻¹} ∘ θ°`, so that `Θ_h` of the integral letter
polynomials is `∇(h·W^k)` (`thetaB_mem_nab_iff`). -/
def thetaB (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (d : Fin n' → ℕ) (h : Matrix (Fin k) (Fin k) Qq)
    (F : LPol (Fin n') k Kf) : Pol (Unit × Fin n') k Kf :=
  twist (wt1 (flatWt d)) (fun b => ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix h)⁻¹) (theta0 Kf F)

omit [CharZero Kf] in
/-- **The determinant twist of the flat weight**: `0` at even positions, `−d_s` at odd positions. -/
theorem detShift_flatWt (hk : 2 ≤ k) (d : Fin n' → ℕ) (s : Fin n') :
    detShift (wt1 (flatWt (k := k) d) ((), s)) = if Even s.val then 0 else -(d s : ℤ) := by
  have hl0 : lastC k ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp [lastC] at this
    omega
  have hlr : (lastC k).rev = 0 := Fin.ext (by simp [lastC]; omega)
  simp only [detShift, dite_eq_left (NeZero.pos k), wt1, blockWt, lamAt, flatWt]
  rw [show (⟨k - 1, _⟩ : Fin k) = lastC k from rfl]
  split_ifs with hs
  · simp [hl0]
  · simp [hlr]

omit [NeZero k] [CharZero Kf] in
/-- **`A_r` of the flat weight** is `Σ_{s even} d_s` (for `1 ≤ r < k`). -/
theorem topA_flatWt [NeZero k] {r : ℕ} (hr : 1 ≤ r) (hrk : r < k) (d : Fin n' → ℕ) :
    topA r (flatWt (k := k) d) = ((∑ s : Fin n', if Even s.val then d s else 0 : ℕ) : ℤ) := by
  rw [topA, topSum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [lamAt, flatWt]
  split_ifs with hs
  · rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (by simp; omega)]
    simp
  · refine Finset.sum_eq_zero fun b hb => ?_
    have hb' := (Finset.mem_filter.1 hb).2
    have : b.rev ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp [Fin.val_rev] at this
      omega
    simp [this]

omit [CharZero Kf] [NeZero k] [IsDomain W] [IsDiscreteValuationRing W] in
/-- **Twisted matrices of inverse matrices are inverse.** -/
theorem twK_inv_mul (s : ℕ) {g : Matrix (Fin k) (Fin k) W} (hg : IsUnit g.det) :
    twK ι σ s g⁻¹ * twK ι σ s g = 1 ∧ twK ι σ s g * twK ι σ s g⁻¹ = 1 := by
  have e : ∀ M : Matrix (Fin k) (Fin k) W,
      twK ι σ s M = (ι.comp ((σ ^ s).toRingHom.comp (algebraMap W Qq))).mapMatrix M := fun M => rfl
  rw [e, e, ← map_mul, ← map_mul, Matrix.nonsing_inv_mul _ hg, Matrix.mul_nonsing_inv _ hg, map_one]
  exact ⟨rfl, rfl⟩

omit [CharZero Kf] in
/-- **The edge twist of `θ°` is the lift substitution** (the core of N2-c): with
`G_s = σ^s(g⁻¹)ᵀ·diag(ϖ⁻¹ on the plane)`, `twist_G(θ°F) = ϖ^{−A_r}·θ°(ℓ_g F)` on multidegree `d`. On a vector letter
the letter change by `G_s` is `ϖ⁻¹·ℓ_g`, on a covector letter `adj(G_s)ᵀ = det(G_s)·σ^s(g)·diag(ϖ on the plane)` is
`det(G_s)·ℓ_g`; the determinant twist cancels the `det(G_s)^{d_s}` and `A_r = Σ_{s even} d_s`. -/
theorem twist_theta0_liftSub (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r)
    (hrk : r < k) {d : Fin n' → ℕ} {g : Matrix (Fin k) (Fin k) W} (hg : IsUnit g.det) {F : LPol (Fin n') k Kf}
    (hF : F ∈ LHom Kf d) :
    twist (wt1 (flatWt d)) (fun b => (twK ι σ b.2.val g⁻¹)ᵀ * planeDiag r (algebraMap O Kf ϖ)⁻¹) (theta0 Kf F) =
      (algebraMap O Kf ϖ ^ (-topA r (flatWt (k := k) d))) •
        theta0 Kf (liftSub ι σ ϖ r (vecF n') (fun s => s.val) g F) := by
  classical
  have hϖ := varpiK_ne_zero hU
  set G : Unit × Fin n' → Matrix (Fin k) (Fin k) Kf :=
    fun b => (twK ι σ b.2.val g⁻¹)ᵀ * planeDiag r (algebraMap O Kf ϖ)⁻¹ with hGdef
  have hpd : ∀ x : Kf, x ≠ 0 → planeDiag (k := k) r x * planeDiag r x⁻¹ = 1 := fun x hx => by
    rw [planeDiag, planeDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [hx]
  -- the inverse of `G_s`
  have hGinv : ∀ b, (G b)⁻¹ = planeDiag r (algebraMap O Kf ϖ) * (twK ι σ b.2.val g)ᵀ := fun b => by
    refine Matrix.inv_eq_left_inv ?_
    rw [hGdef, ← Matrix.mul_assoc, Matrix.mul_assoc (planeDiag _ _), ← Matrix.transpose_mul,
      (twK_inv_mul b.2.val hg).1, Matrix.transpose_one, Matrix.mul_one, hpd _ hϖ]
  have hGdet : ∀ b, IsUnit (G b).det := fun b => by
    refine Matrix.isUnit_det_of_left_inverse (B := planeDiag r (algebraMap O Kf ϖ) * (twK ι σ b.2.val g)ᵀ) ?_
    rw [hGdef, ← Matrix.mul_assoc, Matrix.mul_assoc (planeDiag _ _), ← Matrix.transpose_mul,
      (twK_inv_mul b.2.val hg).1, Matrix.transpose_one, Matrix.mul_one, hpd _ hϖ]
  -- the letter change is a multiple of the lift substitution on each letter
  set lamS : Fin n' → Kf := fun s => if Even s.val then (algebraMap O Kf ϖ)⁻¹ else (G ((), s)).det
  have hgen : ∀ v, linSub (letMat G) (X v) = lamS v.1 • liftSub ι σ ϖ r (vecF n') (fun s => s.val) g (X v) := by
    rintro ⟨s, c⟩
    simp only [linSub, liftSub, aeval_X, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2
    by_cases hs : Even s.val
    · simp only [letMat, hs, ite_true, lamS, hGdef, planeDiag, Matrix.mul_diagonal, Matrix.transpose_apply, scaled,
        vecF, decide_true]
      by_cases hb : b.val < r
      · simp [hb, Nat.not_le.2 hb]
        ring
      · simp [hb, Nat.le_of_not_lt hb, hϖ]
    · have hadj : (G ((), s)).adjugate = (G ((), s)).det • (G ((), s))⁻¹ := by
        rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ (hGdet _), one_smul]
      simp only [letMat, hs, ite_false, lamS, hadj, Matrix.transpose_smul, Matrix.smul_apply, smul_eq_mul, hGinv,
        Matrix.transpose_mul, Matrix.transpose_transpose, scaled, vecF, decide_false, Bool.false_eq_true]
      rw [planeDiag, Matrix.diagonal_transpose, Matrix.mul_diagonal]
      by_cases hb : b.val < r
      · simp [hb]
        ring
      · simp [hb]
  rw [twist, lsub_theta0, map_eq_smul_of_row lamS hgen hF, map_smul, C_mul', smul_smul]
  congr 1
  -- the scalars
  rw [Fintype.prod_prod_type, Fintype.prod_unique, topA_flatWt hr hrk, zpow_neg, zpow_natCast, ← inv_pow,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [show ((default : Unit), s) = ((), s) from rfl, detShift_flatWt hk]
  by_cases hs : Even s.val
  · simp [lamS, hs]
  · simp only [lamS, hs, ite_false, pow_zero, zpow_neg, zpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ (hGdet _).ne_zero)

omit [CharZero Kf] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`ϖ^{−i}·P` is integral** iff all coefficients of `P` lie in `ϖ^i·O`. -/
theorem ordGe_iff {τ' : Type*} (hϖ : algebraMap O Kf ϖ ≠ 0) (i : ℕ) (P : MvPolynomial τ' Kf) :
    OrdGe ϖ i P ↔ ∀ μ, ((algebraMap O Kf ϖ ^ i)⁻¹ • P).coeff μ ∈ Oint O Kf := by
  refine ⟨fun h μ => ?_, fun h μ => ?_⟩
  · obtain ⟨c, hc⟩ := h μ
    refine ⟨c, ?_⟩
    rw [coeff_smul, hc, smul_eq_mul, map_mul, map_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hϖ), one_mul]
  · obtain ⟨c, hc⟩ := h μ
    refine ⟨c, ?_⟩
    rw [coeff_smul, smul_eq_mul] at hc
    rw [map_mul, map_pow, hc, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ), one_mul]

/-- **The flat model and the `∇`-lattice** (N2-b at a lattice): `Θ_h F ∈ ∇(h·W^k)` iff `F` is integral. -/
theorem thetaB_mem_nab_iff (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 2 ≤ k) {d : Fin n' → ℕ}
    {h : Matrix (Fin k) (Fin k) Qq} (hh : IsUnit h.det) {F : LPol (Fin n') k Kf} (hF : F ∈ LHom Kf d) :
    thetaB ι σ d h F ∈ nab O ι σ (flatWt d) (colSpan W h) ↔ ∀ μ, F.coeff μ ∈ Oint O Kf := by
  have hC : ∀ b : Unit × Fin n', IsBasisOf (O := O) (blk ι σ b.2 (colSpan W h))
      ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix h) := fun b => isBasisOf_blk hU _ hh rfl
  have hCu : ∀ b : Unit × Fin n', IsUnit ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix h).det := fun b => (hC b).1
  rw [show nab O ι σ (flatWt d) (colSpan W h) = nablaB (wt1 (flatWt d)) fun b => blk ι σ b.2 (colSpan W h) from rfl,
    mem_nablaB_iff hC, thetaB, twist_twist_inv _ hCu, SetLike.mem_coe,
    ← theta0_mem_nablaInt_iff (A := Oint O Kf) hk hF]
  exact ⟨fun h => h.2, fun h => ⟨HermForms.twist_mem_nabla _ _ (theta0_mem_nabla hk hF), h⟩⟩

/-- **The flat model and the edge lattices** (N2-c): for the edge with adapted basis `h·g^{−T}` (source
`h g^{−T}W^k`, target `h g^{−T}D^{−1}W^k`, `D = diag(p on the plane)`, `g ∈ GL_k(W)`) and `F` of multidegree `d`,
`Θ_h F ∈ ϖ^i·𝓡(e)` iff `ord_g F ≥ i`, i.e. the lift substitution `ℓ_g F` has all coefficients in `ϖ^i·O`. The midpoint
blocks have the basis matrices `ι σ^s(h g^{−T}D^{−1})·diag(ϖ on the plane)` (`isBasisOf_midBlk`), so the condition is
`ϖ^{A_r − i}·twist_{G}(θ°F) ∈ ∇_O` with `G_s = σ^s(g⁻¹)ᵀ·diag(ϖ⁻¹ on the plane)`, that is
`ϖ^{−i}·θ°(ℓ_g F) ∈ ∇_O` (`twist_theta0_liftSub`), and N2-b concludes. -/
theorem thetaB_mem_edgeLat_iff (hU : Unram p n' W Qq O Kf ι σ j ϖ) (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r)
    (hrk : r < k) {d : Fin n' → ℕ} {h : Matrix (Fin k) (Fin k) Qq} (hh : IsUnit h.det)
    {g : Matrix (Fin k) (Fin k) W} (hg : IsUnit g.det) {F : LPol (Fin n') k Kf} (hF : F ∈ LHom Kf d) (i : ℕ) :
    thetaB ι σ d h F ∈ (algebraMap O Kf ϖ ^ i) • edgeLat ι σ ϖ r (flatWt d)
        (colSpan W (h * (g⁻¹)ᵀ.map (algebraMap W Qq)))
        (colSpan W (h * (g⁻¹)ᵀ.map (algebraMap W Qq) * planeDiag r (p : Qq)⁻¹)) ↔
      OrdGe ϖ i (liftSub ι σ ϖ r (vecF n') (fun s => s.val) g F) := by
  classical
  have hϖ := varpiK_ne_zero hU
  have hp : (p : Qq) ≠ 0 := hU.cast_ne_zero
  set gQ := (g⁻¹)ᵀ.map (algebraMap W Qq) with hgQ
  set B := h * gQ * planeDiag r (p : Qq)⁻¹ with hBdef
  set S : Finset (Fin k) := Finset.univ.filter fun i => i.val < r
  have hgQu : IsUnit gQ.det := by
    rw [hgQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det g hg).map _
  have hDu : IsUnit (planeDiag (k := k) r (p : Qq)⁻¹).det := by
    rw [planeDiag, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [hp])
  have hB : IsUnit B.det := by
    rw [hBdef, Matrix.det_mul, Matrix.det_mul]
    exact (hh.mul hgQu).mul hDu
  have hL'' : colSpan W (h * gQ) = Submodule.span W (Set.range fun l i =>
      (B * Matrix.diagonal fun i => if i ∈ S then (p : Qq) else 1) i l) := by
    rw [hBdef, Matrix.mul_assoc, planeDiag, Matrix.diagonal_mul_diagonal]
    have : (fun i : Fin k => (if i.val < r then (p : Qq)⁻¹ else 1) * if i ∈ S then (p : Qq) else 1) = fun _ => 1 :=
      funext fun i => by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; split_ifs <;> simp [hp]
    rw [this, Matrix.diagonal_one, Matrix.mul_one]
    rfl
  have hM : ∀ b : Unit × Fin n', IsBasisOf (midBlk ι σ ϖ b.2 (colSpan W (h * gQ)) (colSpan W B))
      ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix B * Matrix.diagonal fun i => if i ∈ S then algebraMap O Kf ϖ
        else 1) := fun b => isBasisOf_midBlk hU _ hB rfl hL''
  have hCu : ∀ b : Unit × Fin n', IsUnit ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix h).det := fun b => by
    rw [← RingHom.map_det]; exact hh.map _
  -- the twist relating `Θ_h` to the midpoint basis
  have hG : ∀ b : Unit × Fin n', ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix h)⁻¹ *
      ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix B * Matrix.diagonal fun i => if i ∈ S then algebraMap O Kf ϖ
        else 1) = (twK ι σ b.2.val g⁻¹)ᵀ * planeDiag r (algebraMap O Kf ϖ)⁻¹ := fun b => by
    rw [hBdef, map_mul, map_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hCu b)]
    congr 1
    rw [RingHom.mapMatrix_apply, planeDiag, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal,
      planeDiag]
    congr 1
    funext i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs
    · rw [map_inv₀, map_natCast, castK_eq_sq hU]
      field_simp
    · simp
  have hφ : liftSub ι σ ϖ r (vecF n') (fun s => s.val) g F ∈ LHom Kf d := by
    refine map_mem_LHom (fun v => ?_) hF
    rw [liftSub, aeval_X]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    simpa [rowW] using (isWeightedHomogeneous_X Kf (rowW (Fin n') k) (v.1, b)).C_mul _
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero _ hϖ), edgeLat, Set.mem_ofPred_eq, nabMid_eq,
    mem_nablaB_iff hM, thetaB]
  have key : twist (wt1 (flatWt d)) (fun b => (ι.comp (σ ^ b.2.val).toRingHom).mapMatrix B *
      Matrix.diagonal fun i => if i ∈ S then algebraMap O Kf ϖ else 1)
      (algebraMap O Kf ϖ ^ topA r (flatWt (k := k) d) • (algebraMap O Kf ϖ ^ i)⁻¹ •
        twist (wt1 (flatWt d)) (fun b => ((ι.comp (σ ^ b.2.val).toRingHom).mapMatrix h)⁻¹) (theta0 Kf F)) =
      theta0 Kf ((algebraMap O Kf ϖ ^ i)⁻¹ • liftSub ι σ ϖ r (vecF n') (fun s => s.val) g F) := by
    rw [HermForms.twist_smul, HermForms.twist_smul, HermForms.twist_twist, funext hG,
      twist_theta0_liftSub hU hk hr hrk hg hF, map_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_right_comm, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero, one_mul]
  rw [key, ordGe_iff hϖ, ← theta0_mem_nablaInt_iff hk (Submodule.smul_mem _ _ hφ)]
  exact ⟨fun h => h.2, fun h => ⟨Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (HermForms.twist_mem_nabla _ _ (theta0_mem_nabla hk hF))), h⟩⟩

end Edge

end Flat

end

end LetterFock
