import Mathlib

/-!
# Weights, dual Weyl modules, the Fock form and the lattices `Δ_N`

Layer L3 of the sharp frontier (`docs/rh-rebuild.md`): the coefficient systems of the forms of L4. Generic in the CM
field `E`, the coefficient field `L`, the CM type `Φ` and its embeddings `τ : Φ → (E →+* L)`.

**Weights** (`wt`, L3.1). For `τ ∈ Φ` and `0 ≤ j`, `λ_j(τ) ∈ ℤ^{k + j(t+1)}`, with
* `λ_j(τ)_i = u_i − (k−1)/2 + i − jh` for `i < k`;
* `λ_j(τ)_i = −e_B + k/2 + (2B+1)h − jh` for `i = k + B(t+1) + r`, `r ≤ t`;

where `h = (t+1)/2`. **Encoding of `u`.** The archive's `u_i` lie in `ℤ + ½` and `k` is even, so we store the
integer `u_i − ½` (`u`); then `λ_j(τ)_i = u_i + 1 − k/2 + i − jh`. The `e_B` are integers, indexed by `ℕ` (extend by
zero). Also `detShift λ = λ_{n−1}` and `natW λ = λ − λ_{n−1} ∈ ℕ^n`. (The spec's "equivalently" form via `ρ_{N_j}`
differs from the explicit one by a further `−jh` when `j > 0`; we follow the explicit formula. The sources use
only `j = 0`, where the two agree.)

**Polynomials** live in `MvPolynomial (Φ × Fin n × Fin n) L` (`Pol`); `X (τ, a, b)` is the entry in row `a`, column
`b` of block `τ`. Everything is defined **block-wise** at once: a single block is the case `Φ = Unit`. Invariance under
`U^Φ` is invariance under each factor, and the invariants of a product are the tensor product of the invariants, so
the block-wise `∇` is `⊗_τ ∇(ν_τ)`; the Fock form is multiplicative over blocks, so the block-wise Fock dual is
`⊗_τ Δ(ν_τ)`. This avoids tensor products.

**∇** (`nabla`, L3.2): the polynomials of degree `ν_{τ,b}` in column `(τ,b)` (Mathlib's
`weightedHomogeneousSubmodule`, with weights in `Φ → Fin n → ℕ`), invariant under `x_τ ↦ x_τ·u_τ` for upper
unitriangular `u_τ` (`rsub`). The highest-weight vector is `hw ν = ∏_τ ∏_s D_{τ,s}^{ν_{s−1}−ν_s}` (`hw`).

**Integral forms.** A bideterminant of shape `ν` (`bidet`) is a product, over `τ` and `s`, of `ν_{s−1} − ν_s` minors
on the first `s` columns of `x_τ`, with arbitrary rows (`rows`; repeated rows give `0`, harmless for spans). For a
subring `A ⊆ L`, `∇_A(ν)` is their `A`-span (`nablaInt`). We use only `A = O_L` and `A = O_{L,w}`.

**The Fock form** (`fockWith c`) is `Σ_α c(F_α)·F′_α·α!` for a ring endomorphism `c` of `L`: `fock` takes `c` the
star of `L` (`starRingEnd L`), normalised by `fock(hw, hw)`. `L` need not be CM: the frontier asks only that the star
be complex conjugation at one embedding `σ₀` (the archive's coefficient field contains `j(cc)`, so lies in no CM
field). **Δ** (`Delta A ν`) is the Fock dual of `∇_A(ν)` in `∇_L(ν)`: it is tested on the bideterminants, which span,
and with `c = id`: bideterminants have integer coefficients, so the hermitian pairing is the star of the bilinear one,
and `Δ` needs no star on `L`.

**The action and `Δ_N`** (L3.3). `VV λ = ∇_L(natW λ)` (`VV`). For `γ ∈ GL_n(E)`,
`ρ_λ(γ)F = ∏_τ τ(det γ)^{−λ_{τ,n−1}}·F((τ(γ)⁻¹x_τ)_τ)` (`rho`). For an `O_E`-lattice `N`, `F ∈ Δ_N(λ)` (`DeltaN`)
when at every finite place `w` of `L` some tuple `C_τ` of local bases of `O_{L,w}·τ(N)` (`IsLocalBasis`) has
`∏_τ det(C_τ)^{λ_{τ,n−1}}·F((C_τ x_τ)_τ) ∈ Δ_{O_{L,w}}` (`twist`); `∇_N` (`nablaN`) likewise with `∇`. The spec's
"one (equivalently every)" is taken as "some".

**Sanity theorems:** `hw_mem_nabla` (via `rsub_minor`, `minor_isWH`, `sum_mult`) and `DeltaOL_subset_DeltaN_std`.
-/

namespace WeylFock

open MvPolynomial NumberField IsDedekindDomain

/-! ## Weights (L3.1) -/

section Weights

/-- `detShift λ = λ_{n−1}`, the determinant twist of a weight (`0` for `n = 0`). Used by `rho`, `twist` (L4). -/
def detShift {n : ℕ} (w : Fin n → ℤ) : ℤ := if h : 0 < n then w ⟨n - 1, by omega⟩ else 0

/-- `natW λ = λ − λ_{n−1}`, the polynomial part of an antitone weight. Used by `VV`, `DeltaN` (L4, L6). -/
def natW {n : ℕ} (w : Fin n → ℤ) : Fin n → ℕ := fun i => (w i - detShift w).toNat

/-- The weights `λ_j(τ) ∈ ℤ^{k + j(t+1)}` of L3.1, with `h = (t+1)/2`; `u τ i` encodes `u_i − ½` and `e τ B` is
`e_B`. Meant for L4–L7 (`Forms_j(λ_j)`). -/
def wt {Φ : Type*} (k t j : ℕ) (u : Φ → Fin k → ℤ) (e : Φ → ℕ → ℤ) : Φ → Fin (k + j * (t + 1)) → ℤ :=
  fun τ i =>
    if hi : (i : ℕ) < k then u τ ⟨i, hi⟩ + 1 + i - (k / 2 : ℕ) - j * ((t + 1) / 2 : ℕ)
    else -e τ (((i : ℕ) - k) / (t + 1)) + (k / 2 : ℕ) + (2 * (((i : ℕ) - k) / (t + 1)) + 1) * ((t + 1) / 2 : ℕ)
      - j * ((t + 1) / 2 : ℕ)

end Weights

/-! ## Polynomials in the blocks, ∇ and the highest-weight vector (L3.2) -/

section Nabla

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

variable (Φ n L) in
/-- The polynomials in the entries `x_{τ,a,b}` of the blocks. -/
abbrev Pol := MvPolynomial (Φ × Fin n × Fin n) L

/-- The block `x_τ` as a matrix of variables. -/
noncomputable def xMat (τ : Φ) : Matrix (Fin n) (Fin n) (Pol Φ n L) := Matrix.of fun a b => X (τ, a, b)

variable (Φ n) in
/-- The column weight: `x_{τ,a,b}` counts once in column `(τ, b)`. -/
def colW : Φ × Fin n × Fin n → (Φ → Fin n → ℕ) := fun p => Pi.single p.1 (Pi.single p.2.2 1)

/-- Right substitution `x_τ ↦ x_τ·g_τ`, i.e. `F ↦ F(x·g)`. -/
noncomputable def rsub (g : Φ → Matrix (Fin n) (Fin n) L) : Pol Φ n L →ₐ[L] Pol Φ n L :=
  aeval fun p => ∑ c, X (p.1, p.2.1, c) * C (g p.1 c p.2.2)

/-- Left substitution `x_τ ↦ g_τ·x_τ`, i.e. `F ↦ F(g·x)`. -/
noncomputable def lsub (g : Φ → Matrix (Fin n) (Fin n) L) : Pol Φ n L →ₐ[L] Pol Φ n L :=
  aeval fun p => ∑ c, C (g p.1 p.2.1 c) * X (p.1, c, p.2.2)

/-- Upper unitriangular matrices. -/
def IsUni (u : Matrix (Fin n) (Fin n) L) : Prop := u.IsUpperTriangular ∧ ∀ i, u i i = 1

variable (L) in
/-- `∇_L(ν)` block-wise: degree `ν τ b` in column `(τ, b)`, invariant under `x_τ ↦ x_τ·u_τ`, `u_τ` upper
unitriangular. -/
noncomputable def nabla (ν : Φ → Fin n → ℕ) : Submodule L (Pol Φ n L) :=
  weightedHomogeneousSubmodule L (colW Φ n) ν ⊓
    ⨅ (u : Φ → Matrix (Fin n) (Fin n) L) (_ : ∀ τ, IsUni (u τ)),
      LinearMap.eqLocus (rsub u).toLinearMap LinearMap.id

/-- The multiplicity `ν_s − ν_{s+1}` (with `ν_n = 0`) of the leading `(s+1)`-minor. -/
def mult (ν : Fin n → ℕ) (s : Fin n) : ℕ := ν s - if h : (s : ℕ) + 1 < n then ν ⟨s + 1, h⟩ else 0

/-- The minor of `x_τ` on the rows `I` and the first `s + 1` columns. -/
noncomputable def minor (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) : Pol Φ n L :=
  ((xMat τ).submatrix I (Fin.castLE s.isLt)).det

variable (L) in
/-- The highest-weight vector `hw_ν = ∏_τ ∏_s D_{τ,s+1}^{ν_s − ν_{s+1}}`. -/
noncomputable def hw (ν : Φ → Fin n → ℕ) : Pol Φ n L :=
  ∏ τ, ∏ s : Fin n, minor τ s (Fin.castLE s.isLt) ^ mult (ν τ) s

variable (L) in
/-- The bideterminant of shape `ν` with rows `rows τ s c` for the `c`-th factor `D_{τ,s+1}`. -/
noncomputable def bidet (ν : Φ → Fin n → ℕ) (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) :
    Pol Φ n L :=
  ∏ τ, ∏ s : Fin n, ∏ c, minor τ s (rows τ s c)

/-- `∇_A(ν)`, the `A`-span of the bideterminants of shape `ν`, for a subring `A ⊆ L`. Used by `nablaN` (L6). -/
noncomputable def nablaInt (A : Subring L) (ν : Φ → Fin n → ℕ) : Submodule A (Pol Φ n L) :=
  Submodule.span A (Set.range (bidet L ν))

end Nabla

/-! ## The Fock form and Δ (L3.2) -/

section Fock

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

/-- The Fock form `Σ_α c(F_α)·G_α·α!`, for a ring endomorphism `c` of `L`. -/
noncomputable def fockWith (c : L →+* L) (F G : Pol Φ n L) : L :=
  ∑ d ∈ G.support, c (F.coeff d) * G.coeff d * d.prod fun _ k => (k.factorial : L)

/-- The normalised Fock form `⟨F, G⟩ = fock(F, G)/fock(hw_ν, hw_ν)`, with `c` the star of `L` (complex conjugation
at one embedding, in the frontier). Meant for the Petersson form `H_j` of L4.1. -/
noncomputable def fock [StarRing L] (ν : Φ → Fin n → ℕ) (F G : Pol Φ n L) : L :=
  fockWith (starRingEnd L) F G / fockWith (starRingEnd L) (hw L ν) (hw L ν)

/-- `Δ_A(ν)`: the `F ∈ ∇_L(ν)` whose normalised Fock pairing with every bideterminant of shape `ν` lies in `A`, the
Fock dual of `∇_A(ν)` (with `c = id`, see the module docstring). -/
def Delta (A : Subring L) (ν : Φ → Fin n → ℕ) : Set (Pol Φ n L) :=
  {F | F ∈ nabla L ν ∧ ∀ rows, fockWith (RingHom.id L) F (bidet L ν rows) /
    fockWith (RingHom.id L) (hw L ν) (hw L ν) ∈ A}

end Fock

/-! ## VV, the action and Δ_N (L3.3) -/

section Lattices

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type*} [Field E] [NumberField E]
  [Field L] [NumberField L] (τ : Φ → (E →+* L))

/-- `VV_L(λ) = ⊗_τ ∇_L(natW λ_τ)`, block-wise. Meant for `Forms_j` (L4.1). -/
noncomputable def VV (lam : Φ → Fin n → ℤ) : Submodule L (Pol Φ n L) := nabla L fun σ => natW (lam σ)

/-- The action `ρ_λ(γ)F = ∏_τ τ(det γ)^{−λ_{τ,n−1}}·F((τ(γ)⁻¹x_τ)_τ)` of `γ ∈ GL_n(E)`. Meant for L4.1. -/
noncomputable def rho (lam : Φ → Fin n → ℤ) (γ : GL (Fin n) E) (F : Pol Φ n L) : Pol Φ n L :=
  C (∏ σ, τ σ (γ : Matrix (Fin n) (Fin n) E).det ^ (-detShift (lam σ))) *
    lsub (fun σ => (τ σ).mapMatrix ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) F

/-- The local ring of integers `O_{L,w}` at a finite place `w` of `L`. -/
noncomputable abbrev Ow (w : HeightOneSpectrum (𝓞 L)) : Subring L := (w.valuation L).integer

/-- The columns of `C` are a basis of `O_{L,w}·σ(N)`: `C` is invertible and its columns span it. -/
def IsLocalBasis (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) (N : Submodule (𝓞 E) (Fin n → E))
    (C : Matrix (Fin n) (Fin n) L) : Prop :=
  C.det ≠ 0 ∧ Submodule.span (Ow w) ((fun v i => σ (v i)) '' (N : Set (Fin n → E))) =
    Submodule.span (Ow w) (Set.range fun j i => C i j)

/-- The twist `F ↦ ∏_τ det(C_τ)^{λ_{τ,n−1}}·F((C_τ x_τ)_τ)` that moves `F` to standard coordinates. -/
noncomputable def twist (lam : Φ → Fin n → ℤ) (C : Φ → Matrix (Fin n) (Fin n) L) (F : Pol Φ n L) : Pol Φ n L :=
  MvPolynomial.C (∏ σ, (C σ).det ^ detShift (lam σ)) * lsub C F

/-- `Δ_N(λ)`: the `F ∈ VV_L(λ)` that, at every finite place `w` of `L`, lie in `Δ_{O_{L,w}}` in the coordinates of
some local basis of `O_{L,w}·τ(N)`. Meant for the integral forms `M_j` (L4.1). -/
def DeltaN (lam : Φ → Fin n → ℤ) (N : Submodule (𝓞 E) (Fin n → E)) : Set (Pol Φ n L) :=
  {F | F ∈ VV lam ∧ ∀ w : HeightOneSpectrum (𝓞 L), ∃ C : Φ → Matrix (Fin n) (Fin n) L,
    (∀ σ, IsLocalBasis w (τ σ) N (C σ)) ∧ twist lam C F ∈ Delta (Ow w) fun σ => natW (lam σ)}

/-- `∇_N(λ)`, as `Δ_N(λ)` with `∇_{O_{L,w}}` for `Δ_{O_{L,w}}`. Meant for the rows (L6.2). -/
def nablaN (lam : Φ → Fin n → ℤ) (N : Submodule (𝓞 E) (Fin n → E)) : Set (Pol Φ n L) :=
  {F | F ∈ VV lam ∧ ∀ w : HeightOneSpectrum (𝓞 L), ∃ C : Φ → Matrix (Fin n) (Fin n) L,
    (∀ σ, IsLocalBasis w (τ σ) N (C σ)) ∧ twist lam C F ∈ nablaInt (Ow w) fun σ => natW (lam σ)}

end Lattices

/-! ## Sanity: the highest-weight vector lies in ∇ -/

section Sanity

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

omit [Fintype Φ] [DecidableEq Φ] in
/-- The leading minors are invariant under `x ↦ x·u`, `u` upper unitriangular: the leading block of `x·u` is the
leading block of `x` times that of `u`, of determinant `1`. -/
theorem rsub_minor {u : Φ → Matrix (Fin n) (Fin n) L} (hu : ∀ σ, IsUni (u σ)) (τ : Φ) (s : Fin n) :
    rsub u (minor τ s (Fin.castLE s.isLt)) = (minor τ s (Fin.castLE s.isLt) : Pol Φ n L) := by
  have key : (rsub u).mapMatrix ((xMat τ).submatrix (Fin.castLE s.isLt) (Fin.castLE s.isLt)) =
      (xMat τ).submatrix (Fin.castLE s.isLt) (Fin.castLE s.isLt) *
        ((u τ).submatrix (Fin.castLE s.isLt) (Fin.castLE s.isLt)).map C := by
    refine Matrix.ext fun a b => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, xMat, Matrix.of_apply, rsub,
      aeval_X, Matrix.mul_apply]
    symm
    apply Fintype.sum_of_injective (Fin.castLE s.isLt) (Fin.castLE_injective _)
    swap
    · exact fun _ => rfl
    intro c hc
    have hcs : s.1 + 1 ≤ c.1 := by
      by_contra h
      exact hc ⟨⟨c, by omega⟩, rfl⟩
    have h0 : u τ c (Fin.castLE s.isLt b) = 0 :=
      (hu τ).1 (show Fin.castLE s.isLt b < c from Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega))
    rw [h0, map_zero, mul_zero]
  unfold minor
  rw [AlgHom.map_det, key, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_of_isUpperTriangular (M := (u τ).submatrix (Fin.castLE s.isLt) (Fin.castLE s.isLt))
      (fun i j hij => (hu τ).1 (Fin.lt_def.2 (Fin.lt_def.1 hij)))]
  simp [(hu τ).2]

omit [Fintype Φ] in
/-- A minor on the first `s + 1` columns of `x_τ` has degree one in the columns `(τ, b)`, `b ≤ s`. -/
theorem minor_isWH (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) :
    IsWeightedHomogeneous (colW Φ n) (minor τ s I : Pol Φ n L)
      (Pi.single τ fun b => if (b : ℕ) ≤ s then 1 else 0) := by
  have hw : (Pi.single τ fun b : Fin n => if (b : ℕ) ≤ s then 1 else 0) =
      ∑ i : Fin (s + 1), colW Φ n (τ, I i, Fin.castLE s.isLt i) := by
    funext σ b
    simp only [colW, Finset.sum_apply]
    by_cases hσ : σ = τ
    · subst hσ
      simp only [Pi.single_eq_same, Pi.single_apply]
      split_ifs with hb
      · rw [Fintype.sum_eq_single ⟨b, by omega⟩ fun i hi => by
          rw [ite_eq_right_iff]; intro h; exact absurd (Fin.ext (by simp [h])) hi]
        simp
      · refine (Finset.sum_eq_zero fun i _ => ?_).symm
        rw [ite_eq_right_iff]; intro h; have := i.isLt; exact absurd (by rw [h, Fin.val_castLE]; omega) hb
    · simp [hσ]
  rw [hw, minor, Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  exact IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X L _ _

/-- The telescoping sum `Σ_{b ≤ s < m} (f_s − f_{s+1}) = f_b − f_{max m b}` for antitone `f : ℕ → ℕ`. -/
theorem sum_tele {f : ℕ → ℕ} (hf : Antitone f) (b m : ℕ) :
    ∑ i ∈ Finset.range m, (if b ≤ i then f i - f (i + 1) else 0) = f b - f (max m b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : f (m + 1) ≤ f m := hf (by omega)
    by_cases hb : b ≤ m
    · have h2 := hf hb
      rw [ite_eq_left_iff.2 (fun h => absurd hb h), max_eq_left hb, max_eq_left (by omega)]
      omega
    · rw [ite_eq_right_iff.2 (fun h => absurd h hb), max_eq_right (by omega), max_eq_right (by omega)]
      simp

/-- The degrees of `hw ν`: for antitone `ν`, column `b` of block `τ` meets `ν_b` leading minors. -/
theorem sum_mult {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    ∑ τ, ∑ s : Fin n, mult (ν τ) s • (Pi.single τ fun b : Fin n => if (b : ℕ) ≤ s then 1 else 0) = ν := by
  funext τ b
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single τ (fun σ _ h => by simp [Ne.symm h]) (by simp)]
  simp only [↓reduceIte]
  set f : ℕ → ℕ := fun i => if h : i < n then ν τ ⟨i, h⟩ else 0
  have hf : Antitone f := fun i j hij => by
    simp only [f]
    split_ifs with hj hi hi
    · exact hν τ (Fin.mk_le_mk.2 hij)
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have hm : ∀ s : Fin n, mult (ν τ) s = f s - f (s + 1) := fun s => by simp [mult, f, s.isLt]
  have := sum_tele hf b n
  rw [max_eq_left b.isLt.le, show f n = 0 by simp [f], Nat.sub_zero, show f b = ν τ b by simp [f, b.isLt],
    ← Fin.sum_univ_eq_sum_range (fun i => if (b : ℕ) ≤ i then f i - f (i + 1) else 0)] at this
  rw [← this]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hm]
  split_ifs <;> simp

/-- **Sanity.** For antitone `ν`, the highest-weight vector `hw_ν` lies in `∇_L(ν)`. -/
theorem hw_mem_nabla {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) : hw L ν ∈ nabla L ν := by
  rw [nabla, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · have key : IsWeightedHomogeneous (colW Φ n) (hw L ν)
        (∑ τ, ∑ s : Fin n, mult (ν τ) s • (Pi.single τ fun b : Fin n => if (b : ℕ) ≤ s then 1 else 0)) :=
      IsWeightedHomogeneous.prod _ _ _ fun τ _ => IsWeightedHomogeneous.prod _ _ _ fun s _ =>
        (minor_isWH τ s _).pow _
    rwa [sum_mult hν] at key
  · simp only [Submodule.mem_iInf]
    intro u hu
    simp [hw, map_prod, map_pow, rsub_minor hu]

end Sanity

/-! ## Sanity: the standard lattice -/

section Std

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type*} [Field E] [NumberField E]
  [Field L] [NumberField L] (τ : Φ → (E →+* L))

variable (E n) in
/-- The standard lattice `O_E^n`. -/
def stdLat : Submodule (𝓞 E) (Fin n → E) := Submodule.span (𝓞 E) (Set.range fun j => Pi.single j 1)

variable (L) in
/-- The global `Δ_{O_L}(ν)`, the Fock dual of `∇_{O_L}(ν)`. -/
def DeltaOL (ν : Φ → Fin n → ℕ) : Set (Pol Φ n L) := Delta (algebraMap (𝓞 L) L).range ν

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- Substituting the identity matrices changes nothing. -/
theorem lsub_one : lsub (fun _ => (1 : Matrix (Fin n) (Fin n) L)) = AlgHom.id L (Pol Φ n L) :=
  algHom_ext fun p => by simp [lsub, Matrix.one_apply]

omit [NumberField E] in
/-- An embedding maps `O_E` into every `O_{L,w}`. -/
theorem map_mem_Ow (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) (r : 𝓞 E) : σ r ∈ Ow w := by
  have h : IsIntegral ℤ (σ r) := (r.isIntegral_coe).map (σ.toIntAlgHom)
  have := w.valuation_le_one (K := L) (⟨σ r, h⟩ : 𝓞 L)
  exact this

/-- The identity matrix is a local basis of `O_{L,w}·σ(O_E^n)` at every `w`. -/
theorem isLocalBasis_one (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) :
    IsLocalBasis w σ (stdLat n E) (1 : Matrix (Fin n) (Fin n) L) := by
  have hcol : ∀ j : Fin n, (fun i => (1 : Matrix (Fin n) (Fin n) L) i j) =
      fun i => σ ((Pi.single j 1 : Fin n → E) i) := fun j => by
    funext i; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine ⟨by simp, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe]
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact Submodule.subset_span ⟨j, hcol j⟩
    | zero => convert (Submodule.span (Ow w) _).zero_mem using 1; funext i; simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1; funext i; simp
    | smul r x _ hx =>
      convert Submodule.smul_mem _ (⟨σ r, map_mem_Ow w σ r⟩ : Ow w) hx using 1
      funext i
      exact map_mul σ _ _
  · rintro _ ⟨j, rfl⟩
    show (fun i => (1 : Matrix (Fin n) (Fin n) L) i j) ∈ _
    rw [hcol j]
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

/-- **Sanity.** The global `Δ_{O_L}` lies in `Δ_N` for the standard lattice `N = O_E^n`, with the identity
matrices as local bases. -/
theorem DeltaOL_subset_DeltaN_std (lam : Φ → Fin n → ℤ) :
    DeltaOL L (fun σ => natW (lam σ)) ⊆ DeltaN τ lam (stdLat n E) := by
  rintro F ⟨hF, hA⟩
  refine ⟨hF, fun w => ⟨fun _ => 1, fun σ => isLocalBasis_one w (τ σ), ?_⟩⟩
  have ht : twist lam (fun _ => 1) F = F := by simp [twist, lsub_one]
  rw [ht]
  refine ⟨hF, fun rows => ?_⟩
  obtain ⟨x, hx⟩ := hA rows
  rw [← hx]
  exact w.valuation_le_one (K := L) x

end Std

end WeylFock
