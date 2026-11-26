import Mathlib
import HermClasses
import KLattice

/-!
# Finitely many classes of decorated unimodular lattices, finite stabilisers

The first piece of the proof of the sharp frontier (`SharpInputs.FiniteClasses`, C1): for a CM field `E`, the
decorated unimodular hermitian lattices of `HermClasses` fall into finitely many classes under
`𝒢 = U_n(E) × Λ_SG` (`finite_DCl`), and each class has a finite stabiliser (`finite_stab`). The hypotheses are those
of `FiniteClasses`, which a wrapper in `lib/pnt` discharges from the two theorems.

**The algebra.** `h` is definite (`herm_self_eq_zero`: at every complex embedding `σ h(x, x) = Σ |σ xᵢ|²`, as `E` is
CM), so a unimodular `N = N^#` spans `E^n` (`span_eq_top_of_unimodular`: a vector orthogonal to `N` lies in
`N^# = N`) and is finitely generated (`fg_of_unimodular`). For an `E`-basis `v` inside `N`, with Gram matrix
`G = (h(vᵢ, vⱼ))` (`hermGram`) and `P` the matrix of columns `vᵢ` (`colMat`), the coordinates `P⁻¹N` lie between
`O_E^n` and `(det G)⁻¹O_E^n` (`exists_den`), and there are finitely many such lattices (`finite_between`). Lattices
with the same `G` and the same coordinates are related by `P'P⁻¹ ∈ U` (`exists_U_of_inv`). So finitely many Gram
matrices give finitely many classes of lattices (`exists_finite_reps`); each lattice carries finitely many decorations,
linear maps to the finite `O_E/P` and `(O_E/w)^n` (`finite_deco`), whence `finite_DCl_of_reps`. A stabiliser embeds in
`Stab_U(N) × Λ`, with `Λ` finite (`finite_stab_of_lattice`).

**The geometry.** `N` is a lattice in `⊕_v ℂ^n` (`HermitianLattice.KLattice`, with the standard metric: `klat`),
through `ψ(x) = (σ_v(x))_v`, and `⟪ψ x, ψ y⟫ = Σ_v σ_v h(x, y)` (`inner_ψ_eq`): the real inner product is half the
trace form, `Tr h(x, y)/2` (`real_inner_ψ`, by `trace_eq_sum_places`, as `E` is totally complex).
* *Lengths are bounded below*: `2‖ψ x‖² = Tr h(x, x)` is a positive integer for `x ≠ 0` in `N`
  (`half_le_norm_ψ`).
* *Covolumes are bounded* (`det_gram_le`): for a `ℤ`-basis `ψ(v)` of `ψ(N)`, `2·Gram = T = (Tr h(vᵢ, vⱼ))` is an
  integer matrix, and `d_E·T⁻¹` is integral, since `N` is its own dual and the trace dual of `O_E` is
  `d_E⁻¹`-integral (`discr_div_smul_mem`, Mathlib's `isIntegral_discr_mul_of_mem_traceDual`). So `det T ∣ d_E^{rk}`,
  and the Haar measure of a fundamental domain is bounded independently of `N` (`exists_fund_le`).
* *Short bases* (`exists_short_basis`): Minkowski's theorem for the body `B(0, δ/2) + [-Kδ, Kδ]·â`
  (`exists_short_inner_ne_zero`) gives a vector of bounded length off any hyperplane `⟨a, ·⟩ = 0`. Off the hyperplane
  `⟨ψ u, ·⟩ = 0`, `u` orthogonal to `v₁, …, v_k`, it extends an independent family in `N` by a short vector.
* *Finitely many Gram matrices* (`exists_gram_cover`): the Gram entries of a short basis are algebraic integers with
  bounded conjugates (`norm_emb_herm_le`), finitely many (`NumberField.Embeddings.finite_of_norm_le`).
* *Finite stabilisers of lattices* (`finite_stabU`): `γ ∈ U` with `γN = N` is determined by the images of a basis
  in `N`, vectors of `ψ(N)` of fixed lengths, finitely many as `ψ(N)` is discrete (`finite_lattice_ball`).

No adelic compactness is used: the only analytic input is Minkowski's convex body theorem.
-/

namespace HermClasses

open NumberField IsDedekindDomain Matrix Module

noncomputable section

section Herm

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/-- `h(x, y) = conj h(y, x)`. -/
theorem herm_comm (x y : Fin n → E) : herm x y = IsCMField.complexConj E (herm y x) := by
  simp only [herm_def, map_sum, map_mul, IsCMField.complexConj_apply_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `h` is linear in its second argument. -/
theorem herm_smul_right (c : E) (y x : Fin n → E) : herm y (c • x) = c * herm y x :=
  (hermL y).map_smul c x

/-- `h` is conjugate-linear in its first argument. -/
theorem herm_smul_left (c : E) (y x : Fin n → E) :
    herm (c • y) x = IsCMField.complexConj E c * herm y x := by
  simp [herm_def, Finset.mul_sum, mul_assoc]

/-- `h` of a sum, in the second argument. -/
theorem herm_sum_right {ι : Type*} (s : Finset ι) (y : Fin n → E) (x : ι → Fin n → E) :
    herm y (∑ j ∈ s, x j) = ∑ j ∈ s, herm y (x j) :=
  map_sum (hermL y) x s

/-- `h` of a sum, in the first argument. -/
theorem herm_sum_left {ι : Type*} (s : Finset ι) (y : ι → Fin n → E) (x : Fin n → E) :
    herm (∑ i ∈ s, y i) x = ∑ i ∈ s, herm (y i) x := by
  rw [herm_comm, herm_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => (herm_comm _ _).symm

/-- `h` at a complex embedding: `σ h(y, x) = Σᵢ conj(σ yᵢ)·σ xᵢ`, as `σ ∘ conj = conj ∘ σ` on a CM field. -/
theorem emb_herm (φ : E →+* ℂ) (y x : Fin n → E) :
    φ (herm y x) = ∑ i, (starRingEnd ℂ) (φ (y i)) * φ (x i) := by
  simp [herm_def, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]

/-- `σ h(x, x) = Σᵢ |σ xᵢ|²`. -/
theorem emb_herm_self (φ : E →+* ℂ) (x : Fin n → E) :
    φ (herm x x) = ((∑ i, ‖φ (x i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [emb_herm]
  push_cast
  exact Finset.sum_congr rfl fun i _ => Complex.conj_mul' _

/-- **`h` is definite**: `h(x, x) = 0` only for `x = 0`. -/
theorem herm_self_eq_zero {x : Fin n → E} (h : herm x x = 0) : x = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := emb_herm_self φ x
  rw [h, map_zero, eq_comm, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => by positivity] at h1
  funext i
  have := h1 i (Finset.mem_univ _)
  rw [sq_eq_zero_iff, norm_eq_zero, map_eq_zero_iff _ φ.injective] at this
  exact this

end Herm

section Lattice

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {N : Submodule (𝓞 E) (Fin n → E)}

/-- A unimodular lattice is integral: `h(x, y) ∈ O_E` for `x, y ∈ N`. -/
theorem herm_mem_one (hN : IsUnimodular N) {x y : Fin n → E} (hx : x ∈ N) (hy : y ∈ N) :
    herm x y ∈ (1 : Submodule (𝓞 E) E) :=
  mem_dual.1 ((show dual N = N from hN).symm ▸ hy) x hx

/-- **A unimodular lattice spans `E^n`**: a vector `u` orthogonal to `N` lies in `N^# = N`, so `h(u, u) = 0`. -/
theorem span_eq_top_of_unimodular (hN : IsUnimodular N) : Submodule.span E (N : Set (Fin n → E)) = ⊤ := by
  by_contra h
  set V := Submodule.span E (N : Set (Fin n → E))
  let w := Module.finBasis E V
  let Φ : (Fin n → E) →ₗ[E] (Fin (finrank E V) → E) := LinearMap.pi fun i => hermL (w i : Fin n → E)
  have hker : LinearMap.ker Φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using Submodule.finrank_lt h)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hwu (i) : herm (w i : Fin n → E) u = 0 := congrFun (LinearMap.mem_ker.1 hu) i
  have hV {y : Fin n → E} (hy : y ∈ V) : herm y u = 0 := by
    have := congrArg Subtype.val (w.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [← this, herm_sum_left]
    exact Finset.sum_eq_zero fun i _ => by rw [herm_smul_left, hwu, mul_zero]
  have huN : u ∈ N := (show dual N = N from hN) ▸
    mem_dual.2 fun y hy => by rw [hV (Submodule.subset_span hy)]; exact zero_mem _
  exact hu0 (herm_self_eq_zero (hV (Submodule.subset_span huN)))

/-- The Gram matrix `(h(vᵢ, vⱼ))ᵢⱼ` of a family. -/
def hermGram {ι : Type*} (v : ι → Fin n → E) : Matrix ι ι E := Matrix.of fun i j => herm (v i) (v j)

/-- `h(vᵢ, Σⱼ cⱼ vⱼ) = (G c)ᵢ`. -/
theorem herm_sum_smul_right {ι : Type*} [Fintype ι] (v : ι → Fin n → E) (c : ι → E) (i : ι) :
    herm (v i) (∑ j, c j • v j) = (hermGram v *ᵥ c) i := by
  simp only [herm_sum_right, herm_smul_right, mulVec, dotProduct, hermGram, of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `h(Σᵢ cᵢ vᵢ, Σⱼ dⱼ vⱼ) = Σᵢ conj(cᵢ)·(G d)ᵢ`: `h` on the span of a family depends only on its Gram matrix. -/
theorem herm_sum_smul {ι : Type*} [Fintype ι] (v : ι → Fin n → E) (c d : ι → E) :
    herm (∑ i, c i • v i) (∑ j, d j • v j) =
      ∑ i, IsCMField.complexConj E (c i) * (hermGram v *ᵥ d) i := by
  simp only [herm_sum_left, herm_smul_left, herm_sum_smul_right]

/-- The Gram matrix of an independent family is nonsingular, as `h` is definite. -/
theorem det_gram_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → Fin n → E}
    (hv : LinearIndependent E v) : (hermGram v).det ≠ 0 := by
  intro h
  obtain ⟨d, hd0, hd⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h0 : herm (∑ j, d j • v j) (∑ j, d j • v j) = 0 := by
    rw [herm_sum_smul, hd]
    simp
  exact hd0 (funext (Fintype.linearIndependent_iff.1 hv d (herm_self_eq_zero h0)))

omit [NumberField E] [IsCMField E] in
/-- **Denominators**: for a nonsingular `G` with entries in `O_E`, there is `D ≠ 0` in `O_E` with `D·c` integral
whenever `G c` is (`D = det G`, by the adjugate). -/
theorem exists_den {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι E}
    (hG : ∀ i j, G i j ∈ (1 : Submodule (𝓞 E) E)) (hdet : G.det ≠ 0) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ c : ι → E, (∀ i, (G *ᵥ c) i ∈ (1 : Submodule (𝓞 E) E)) →
      ∀ j, (D : E) * c j ∈ (1 : Submodule (𝓞 E) E) := by
  choose G₀ hG₀ using fun i j => Submodule.mem_one.1 (hG i j)
  set G' : Matrix ι ι (𝓞 E) := Matrix.of G₀
  have hGm : G = G'.map (algebraMap (𝓞 E) E) := by ext i j; exact (hG₀ i j).symm
  refine ⟨G'.det, fun h => hdet ?_, fun c hc j => ?_⟩
  · rw [hGm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  choose a ha using fun i => Submodule.mem_one.1 (hc i)
  refine Submodule.mem_one.2 ⟨(G'.adjugate *ᵥ a) j, ?_⟩
  rw [RingHom.map_mulVec, show (algebraMap (𝓞 E) E ∘ a) = G *ᵥ c from funext ha, mulVec_mulVec, hGm,
    ← Matrix.map_mul, adjugate_mul, Matrix.map_smul', Matrix.map_one _ (map_zero _) (map_one _), smul_mulVec,
    one_mulVec, Pi.smul_apply, smul_eq_mul]
  exact fun _ _ => map_mul _ _ _

/-- **A unimodular lattice is finitely generated**: with `v` an `E`-basis of `E^n` inside `N`, the coordinates of
`x ∈ N` in `v` have denominator `D = det G` (`exists_den`), as `G c = (h(vᵢ, x))ᵢ` is integral. -/
theorem fg_of_unimodular (hN : IsUnimodular N) : N.FG := by
  classical
  obtain ⟨s, hsN, hspan, hli⟩ := exists_linearIndependent E (N : Set (Fin n → E))
  rw [span_eq_top_of_unimodular hN] at hspan
  have : Finite s := hli.finite
  let := Fintype.ofFinite s
  let b := Basis.mk hli (by rw [Subtype.range_coe]; exact hspan.ge)
  obtain ⟨D, hD, hden⟩ := exists_den (G := hermGram fun i : s => (i : Fin n → E))
    (fun i j => herm_mem_one hN (hsN i.2) (hsN j.2)) (det_gram_ne_zero hli)
  refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun i : s => (D : E)⁻¹ • (i : Fin n → E))) ?_
  intro x hx
  have hx' : ∑ i, b.repr x i • (i : Fin n → E) = x := by
    conv_rhs => rw [← b.sum_repr x]
    simp [b]
  choose a ha using fun j => Submodule.mem_one.1 (hden (b.repr x) (fun i => by
    rw [← herm_sum_smul_right, hx']; exact herm_mem_one hN (hsN i.2) hx) j)
  have hD' : (D : E) ≠ 0 := by simpa using hD
  rw [← hx']
  refine Submodule.sum_mem _ fun j _ => ?_
  have : b.repr x j • (j : Fin n → E) = a j • ((D : E)⁻¹ • (j : Fin n → E)) := by
    rw [← algebraMap_smul E (a j), smul_smul, ha, mul_comm, ← mul_assoc, inv_mul_cancel₀ hD', one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- A unimodular lattice is a lattice: finitely generated, spanning `E^n`. -/
theorem isLattice_of_unimodular (hN : IsUnimodular N) : N.IsLattice E :=
  ⟨fg_of_unimodular hN, span_eq_top_of_unimodular hN⟩

omit [NumberField E] [IsCMField E] in
variable (E n) in
/-- The lattice `O_E^n ⊂ E^n`. -/
def intVec : Submodule (𝓞 E) (Fin n → E) := Submodule.pi Set.univ fun _ => 1

omit [NumberField E] [IsCMField E] in
/-- Membership in `O_E^n`. -/
theorem mem_intVec {x : Fin n → E} : x ∈ intVec E n ↔ ∀ i, x i ∈ (1 : Submodule (𝓞 E) E) := by
  simp [intVec, Submodule.mem_pi]

omit [IsCMField E] in
/-- **Finitely many lattices between `O_E^n` and `D⁻¹O_E^n`**: each is determined by the reductions mod `D` of the
`D x`, `x` in it, a subset of the finite `(O_E/D)^n`. -/
theorem finite_between (D : 𝓞 E) (hD : D ≠ 0) :
    {M : Submodule (𝓞 E) (Fin n → E) | intVec E n ≤ M ∧
      ∀ x ∈ M, ∀ i, (D : E) * x i ∈ (1 : Submodule (𝓞 E) E)}.Finite := by
  have : Finite (𝓞 E ⧸ Ideal.span {D}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hD)
  let red : Submodule (𝓞 E) (Fin n → E) → Set (Fin n → 𝓞 E ⧸ Ideal.span {D}) := fun M =>
    {q | ∃ x ∈ M, ∃ a : Fin n → 𝓞 E, (∀ i, algebraMap (𝓞 E) E (a i) = D * x i) ∧
      q = fun i => Ideal.Quotient.mk _ (a i)}
  have hD' : (D : E) ≠ 0 := by simpa using hD
  have key : ∀ M₁ M₂ : Submodule (𝓞 E) (Fin n → E), intVec E n ≤ M₂ →
      (∀ x ∈ M₁, ∀ i, (D : E) * x i ∈ (1 : Submodule (𝓞 E) E)) → red M₁ ⊆ red M₂ → M₁ ≤ M₂ := by
    intro M₁ M₂ h₂ h₁ hred x hx
    choose a ha using fun i => Submodule.mem_one.1 (h₁ x hx i)
    obtain ⟨x', hx', a', ha', hq⟩ := hred ⟨x, hx, a, ha, rfl⟩
    have hz (i) : ∃ z, z * D = a i - a' i :=
      Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun hq i))
    choose z hz using hz
    have hxx' : x - x' ∈ intVec E n := mem_intVec.2 fun i => Submodule.mem_one.2 ⟨z i, by
      have := congrArg (algebraMap (𝓞 E) E) (hz i)
      rw [map_mul, map_sub, ha, ha'] at this
      refine mul_right_cancel₀ hD' ?_
      rw [this, Pi.sub_apply]
      ring⟩
    simpa using M₂.add_mem (h₂ hxx') hx'
  refine Set.Finite.of_finite_image (f := red) (Set.toFinite _) fun M₁ h₁ M₂ h₂ h => ?_
  exact le_antisymm (key _ _ h₂.1 h₁.2 h.le) (key _ _ h₁.1 h₂.2 h.ge)

omit [NumberField E] [IsCMField E] in
/-- The matrix with columns `vᵢ`. -/
def colMat (v : Fin n → Fin n → E) : Matrix (Fin n) (Fin n) E := Matrix.of fun r i => v i r

omit [NumberField E] [IsCMField E] in
/-- `P c = Σᵢ cᵢ vᵢ` for `P` with columns `vᵢ`. -/
theorem colMat_mulVec (v : Fin n → Fin n → E) (c : Fin n → E) : colMat v *ᵥ c = ∑ i, c i • v i := by
  funext r
  simp [colMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]

omit [NumberField E] [IsCMField E] in
/-- The matrix with columns an independent family is invertible. -/
theorem isUnit_colMat {v : Fin n → Fin n → E} (hv : LinearIndependent E v) : IsUnit (colMat v) :=
  Matrix.linearIndependent_cols_iff_isUnit.1 hv

/-- **Lattices with equal invariants are isometric**: if the columns of `P`, `P'` have equal Gram matrices, and `N`,
`N'` have equal coordinates (`P⁻¹N = P'⁻¹N'`), then `γ = P'P⁻¹ ∈ U` carries `N` to `N'`. -/
theorem exists_U_of_inv {v v' : Fin n → Fin n → E} (hv : IsUnit (colMat v)) (hv' : IsUnit (colMat v'))
    (hG : hermGram v = hermGram v') {N N' : Submodule (𝓞 E) (Fin n → E)}
    (hN : N.comap (act hv.unit) = N'.comap (act hv'.unit)) : ∃ γ ∈ U E n, N.map (act γ) = N' := by
  have key (c d : Fin n → E) : herm (act hv'.unit c) (act hv'.unit d) = herm (act hv.unit c) (act hv.unit d) := by
    simp only [act_apply, IsUnit.unit_spec, colMat_mulVec, herm_sum_smul, hG]
  refine ⟨hv'.unit * hv.unit⁻¹, fun x y => ?_, ?_⟩
  · rw [act_mul, act_mul, key, act_act_inv, act_act_inv]
  · ext x
    rw [mem_map_act, _root_.mul_inv_rev, inv_inv, act_mul]
    change act hv'.unit⁻¹ x ∈ N.comap (act hv.unit) ↔ _
    rw [hN, Submodule.mem_comap, act_act_inv]

end Lattice

/-! ### Classes -/

section Classes

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/-- **Finitely many classes of unimodular lattices, from finitely many Gram matrices**: if every unimodular `N`
contains an `E`-basis of `E^n` with Gram matrix in a finite set, then finitely many unimodular lattices represent
every unimodular lattice up to `U`. The invariant of `N` is the Gram matrix `G` of the basis and the coordinates
`P⁻¹N`, which lie between `O_E^n` and `(det G)⁻¹O_E^n`; equal invariants give isometric lattices. -/
theorem exists_finite_reps {𝒢 : Set (Matrix (Fin n) (Fin n) E)} (h𝒢 : 𝒢.Finite)
    (hcov : ∀ N : Submodule (𝓞 E) (Fin n → E), IsUnimodular N →
      ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ N) ∧ LinearIndependent E v ∧ hermGram v ∈ 𝒢) :
    ∃ S : Set (Submodule (𝓞 E) (Fin n → E)), S.Finite ∧ (∀ M ∈ S, IsUnimodular M) ∧
      ∀ N, IsUnimodular N → ∃ γ ∈ U E n, N.map (act γ) ∈ S := by
  classical
  choose v hvN hv hvG using hcov
  let inv (N : {N : Submodule (𝓞 E) (Fin n → E) // IsUnimodular N}) :
      Matrix (Fin n) (Fin n) E × Submodule (𝓞 E) (Fin n → E) :=
    (hermGram (v N.1 N.2), N.1.comap (act (isUnit_colMat (hv N.1 N.2)).unit))
  let FS (G : Matrix (Fin n) (Fin n) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
    {M | intVec E n ≤ M ∧ ∀ c ∈ M, ∀ i, (G *ᵥ c) i ∈ (1 : Submodule (𝓞 E) E)}
  let 𝒢₀ := {G ∈ 𝒢 | (∀ i j, G i j ∈ (1 : Submodule (𝓞 E) E)) ∧ G.det ≠ 0}
  have hFS : ∀ G ∈ 𝒢₀, (FS G).Finite := by
    rintro G ⟨-, hG, hdet⟩
    obtain ⟨D, hD, hden⟩ := exists_den hG hdet
    exact (finite_between D hD).subset fun M hM => ⟨hM.1, fun x hx => hden x (hM.2 x hx)⟩
  have hfin : (Set.range inv).Finite := by
    refine ((h𝒢.subset fun G hG => hG.1).biUnion fun G hG =>
      (Set.finite_singleton G).prod (hFS G hG)).subset ?_
    rintro _ ⟨⟨N, hN⟩, rfl⟩
    have hP (c : Fin n → E) : act (isUnit_colMat (hv N hN)).unit c = ∑ i, c i • v N hN i := by
      rw [act_apply, IsUnit.unit_spec, colMat_mulVec]
    refine Set.mem_biUnion (x := hermGram (v N hN)) ⟨hvG N hN, fun i j => herm_mem_one hN (hvN N hN i) (hvN N hN j),
      det_gram_ne_zero (hv N hN)⟩ ⟨rfl, fun c hc => ?_, fun c hc i => ?_⟩
    · rw [Submodule.mem_comap, hP]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (mem_intVec.1 hc i)
      rw [← ha, algebraMap_smul]
      exact N.smul_mem a (hvN N hN i)
    · have := Submodule.mem_comap.1 hc
      rw [hP] at this
      rw [← herm_sum_smul_right]
      exact herm_mem_one hN (hvN N hN i) this
  have hrep : ∀ p ∈ Set.range inv, ∃ N, inv N = p := fun p hp => hp
  choose rep hrep using hrep
  have := hfin.to_subtype
  refine ⟨Set.range fun p : Set.range inv => (rep p.1 p.2).1, Set.finite_range _, ?_, fun N hN => ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact (rep p.1 p.2).2
  · have h := hrep (inv ⟨N, hN⟩) ⟨_, rfl⟩
    obtain ⟨γ, hγ, hmap⟩ := exists_U_of_inv _ _ (congrArg Prod.fst h).symm (congrArg Prod.snd h).symm
    exact ⟨γ, hγ, hmap ▸ ⟨⟨_, ⟨_, rfl⟩⟩, rfl⟩⟩

omit [NumberField E] [IsCMField E] in
/-- Linear maps from a finitely generated module to a finite one are finitely many. -/
theorem finite_linearMap {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [Module.Finite R M] [Finite M'] : Finite (M →ₗ[R] M') := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  exact Finite.of_injective (fun f : M →ₗ[R] M' => fun i => f (s i)) fun f g h =>
    LinearMap.ext_on_range hs (congrFun h)

omit [IsCMField E] in
/-- The residue rings `O_E/P` are finite. -/
theorem finite_residue (P : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ P.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot

omit [IsCMField E] in
/-- **Finitely many decorations**: the decorated lattices on finitely many finitely generated lattices are finitely
many, as the `f_P` and `be_w` are linear maps to finite modules. -/
theorem finite_deco {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : Set (Submodule (𝓞 E) (Fin n → E))}
    (hS : S.Finite) (hfg : ∀ M ∈ S, M.FG) : {d : Deco E n ST SG | d.N ∈ S}.Finite := by
  have hM : ∀ M ∈ S, {d : Deco E n ST SG | d.N = M}.Finite := by
    intro M hM
    have : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 (hfg M hM)
    have := fun P : HeightOneSpectrum (𝓞 E) => finite_residue P
    have (P : ST) : Finite (M →ₗ[𝓞 E] 𝓞 E ⧸ P.1.asIdeal) := finite_linearMap
    have (w : SG) : Finite (M →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ w.1.asIdeal)) := finite_linearMap
    refine (Set.finite_range fun fb : (∀ P : ST, M →ₗ[𝓞 E] 𝓞 E ⧸ P.1.asIdeal) ×
      (∀ w : SG, M →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ w.1.asIdeal)) => (⟨M, fb.1, fb.2⟩ : Deco E n ST SG)).subset ?_
    rintro ⟨N, f, be⟩ rfl
    exact ⟨(f, be), rfl⟩
  exact (hS.biUnion hM).subset fun d hd => Set.mem_biUnion hd rfl

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}

/-- **Finitely many classes of decorated lattices, from finitely many lattice classes**: every point is in the
orbit of one whose lattice is a representative, and there are finitely many of those (`finite_deco`). -/
theorem finite_DCl_of_reps {S : Set (Submodule (𝓞 E) (Fin n → E))} (hS : S.Finite)
    (hSu : ∀ M ∈ S, IsUnimodular M) (hrep : ∀ N, IsUnimodular N → ∃ γ ∈ U E n, N.map (act γ) ∈ S) :
    Finite (DCl E n ST Λ) := by
  have hT := finite_deco (ST := ST) (SG := SG) hS fun M hM => fg_of_unimodular (hSu M hM)
  have : Finite {p : points (ST := ST) Λ | (p : Deco E n ST SG).N ∈ S} :=
    (hT.preimage Subtype.val_injective.injOn).to_subtype
  refine Finite.of_surjective (fun p : {p : points (ST := ST) Λ | (p : Deco E n ST SG).N ∈ S} =>
    (Quotient.mk _ p.1 : DCl E n ST Λ)) fun c => ?_
  obtain ⟨γ, hγ, hγS⟩ := hrep _ (show (c.out : Deco E n ST SG).Good from c.out.2).unimod
  let g : Grp E n SG Λ := (⟨γ, hγ⟩, 1)
  exact ⟨⟨g • c.out, hγS⟩, (Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ g))).trans
    (Quotient.out_eq c)⟩

/-- **Finite stabilisers, from finite stabilisers of lattices**: `Stab(c)` embeds in `Stab_U(N) × Λ`, and `Λ` is
finite. -/
theorem finite_stab_of_lattice (c : DCl E n ST Λ)
    (h : Finite {γ : U E n // (c.out : Deco E n ST SG).N.map (act γ.1) = (c.out : Deco E n ST SG).N}) :
    Finite (stab c) := by
  have := fun w : SG => finite_residue (E := E) w.1
  refine Finite.of_injective (fun g : stab c =>
    ((⟨g.1.1, congrArg (fun p : points (ST := ST) Λ => (p : Deco E n ST SG).N)
      (MulAction.mem_stabilizer_iff.1 g.2)⟩ :
        {γ : U E n // (c.out : Deco E n ST SG).N.map (act γ.1) = (c.out : Deco E n ST SG).N}), g.1.2))
    fun g g' hg => ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hg
  exact Subtype.ext (Prod.ext hg.1 hg.2)

end Classes

/-! ### The embedding in `⊕_v ℂ^n` -/

section Embed

open HermitianLattice KLattice InnerProductSpace

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/-- **The trace at the complex places**: `Tr_{E/ℚ}(a) = 2·Σ_v Re σ_v(a)`, as `E` is totally complex and the two
embeddings at `v` are `σ_v` and `conj ∘ σ_v`. -/
theorem trace_eq_sum_places (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℝ) = 2 * ∑ w : Pl E, (w.1.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ => φ a) (fun σ => σ a) (fun _ => rfl),
    ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ : E →+* ℂ => φ a)] at h
  have hfib (w : InfinitePlace E) : ∑ φ ∈ Finset.univ with InfinitePlace.mk φ = w, φ a =
      ((2 * (w.embedding a).re : ℝ) : ℂ) := by
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))
        (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
    have hs : (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff, ComplexEmbedding.conjugate,
        star_involutive.eq_iff]
    rw [hs, Finset.sum_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  simp_rw [hfib] at h
  rw [Finset.sum_subtype (p := fun w : InfinitePlace E => w.IsComplex) Finset.univ
    (fun w => by simp [IsTotallyComplex.isComplex w])] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h]
  push_cast
  rfl

/-- `⟪ψ₀ x, ψ₀ y⟫ = Σ_v σ_v h(x, y)`. -/
theorem inner_ψ₀_eq (x y : Fin n → E) :
    ⟪(ψ₀ x : Space E (Fin n)), ψ₀ y⟫_ℂ = ∑ w : Pl E, w.1.embedding (herm x y) := by
  rw [KLattice.inner_apply, Fintype.sum_prod_type_right]
  simp [coord_ψ₀, emb_herm]

open scoped ComplexOrder in
variable (E n) in
/-- `N` as a `KLattice`, with the standard metric at every place. -/
abbrev klat (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] : KLattice E (Fin n) :=
  ⟨N, fun _ => 1, fun _ => Matrix.PosDef.one⟩

variable (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E]

/-- `⟪ψ x, ψ y⟫ = Σ_v σ_v h(x, y)`. -/
theorem inner_ψ_eq (x y : Fin n → E) :
    ⟪(klat E n N).ψ x, (klat E n N).ψ y⟫_ℂ = ∑ w : Pl E, w.1.embedding (herm x y) := by
  have h1 : op (klat E n N).G (ψ₀ y : Space E (Fin n)) = ψ₀ y := by convert op_one (K := E) (ψ₀ y)
  rw [KLattice.inner_ψ, h1, inner_ψ₀_eq]

/-- **The real inner product is half the trace form**: `⟪ψ x, ψ y⟫_ℝ = Tr h(x, y)/2`. -/
theorem real_inner_ψ (x y : Fin n → E) :
    inner ℝ ((klat E n N).ψ x) ((klat E n N).ψ y) = ((Algebra.trace ℚ E (herm x y) : ℚ) : ℝ) / 2 := by
  rw [real_inner_eq_re_inner ℂ, inner_ψ_eq, trace_eq_sum_places, RCLike.re_to_complex, Complex.re_sum]
  ring

/-- `‖ψ x‖² = Σ_v Σᵢ |σ_v xᵢ|²`. -/
theorem norm_ψ_sq (x : Fin n → E) :
    ‖(klat E n N).ψ x‖ ^ 2 = ∑ w : Pl E, ∑ i, ‖w.1.embedding (x i)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq_re_inner ℂ, inner_ψ_eq, RCLike.re_to_complex, Complex.re_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [emb_herm_self, Complex.ofReal_re]

omit [IsCMField E] in
/-- The trace of an algebraic integer is an integer. -/
theorem trace_int {a : E} (ha : a ∈ (1 : Submodule (𝓞 E) E)) : ∃ z : ℤ, Algebra.trace ℚ E a = z := by
  obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
  exact ⟨Algebra.trace ℤ (𝓞 E) b, (Algebra.coe_trace_int b).symm⟩

/-- `ψ(N)` spans `⊕_v ℂ^n` over `ℝ` (`KLattice.span_lattice`). -/
instance : IsZLattice ℝ (klat E n N).lattice := ⟨span_lattice _⟩

/-- **Integrality bounds lengths below**: `‖ψ x‖ ≥ 1/2` for `x ≠ 0` in a unimodular `N`, as
`2‖ψ x‖² = Tr h(x, x)` is a positive integer. -/
theorem half_le_norm_ψ (hN : IsUnimodular N) {x : Fin n → E} (hx : x ∈ N) (hx0 : x ≠ 0) :
    1 / 2 ≤ ‖(klat E n N).ψ x‖ := by
  obtain ⟨z, hz⟩ := trace_int (herm_mem_one hN hx hx)
  have h2 := real_inner_ψ N x x
  rw [real_inner_self_eq_norm_sq, hz, Rat.cast_intCast] at h2
  have hpos : 0 < ‖(klat E n N).ψ x‖ :=
    norm_pos_iff.2 fun h => hx0 ((klat E n N).ψ_injective (h.trans (map_zero _).symm))
  have hz1 : (1 : ℝ) ≤ z := by
    have : (0 : ℝ) < z := by nlinarith
    exact_mod_cast (show (0 : ℤ) < z by exact_mod_cast this)
  nlinarith

/-- The points of `ψ(N)` in a ball are finitely many, as `ψ(N)` is discrete. -/
theorem finite_lattice_ball (r : ℝ) : {y | y ∈ (klat E n N).lattice ∧ ‖y‖ ≤ r}.Finite := by
  let b := Module.Free.chooseBasis ℤ (klat E n N).lattice
  have h := ZSpan.setFinite_inter (b.ofZLatticeBasis ℝ (klat E n N).lattice)
    (Metric.isBounded_closedBall (x := (0 : Space E (Fin n))) (r := r))
  rw [Basis.ofZLatticeBasis_span ℝ _ b] at h
  exact h.subset fun y hy => ⟨mem_closedBall_zero_iff.2 hy.2, hy.1⟩

/-- `‖ψ(γx)‖ = ‖ψ x‖` for `γ ∈ U`. -/
theorem norm_ψ_act {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (x : Fin n → E) :
    ‖(klat E n N).ψ (act γ x)‖ = ‖(klat E n N).ψ x‖ := by
  have h := real_inner_ψ N (act γ x) (act γ x)
  rw [herm_act hγ, ← real_inner_ψ N, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- **Finite stabilisers of lattices**: `γ ∈ U` with `γN = N` is determined by the images of an `E`-basis inside
`N`, vectors of `ψ(N)` of fixed lengths, which are finitely many. -/
theorem finite_stabU (hN : IsUnimodular N) : Finite {γ : U E n // N.map (act γ.1) = N} := by
  obtain ⟨s, hsN, hspan, hli⟩ := exists_linearIndependent E (N : Set (Fin n → E))
  rw [span_eq_top_of_unimodular hN] at hspan
  have : Finite s := hli.finite
  let b := Basis.mk hli (by rw [Subtype.range_coe]; exact hspan.ge)
  have := fun i : s => (finite_lattice_ball N ‖(klat E n N).ψ i‖).to_subtype
  have hmem (γ : {γ : U E n // N.map (act γ.1) = N}) {x : Fin n → E} (hx : x ∈ N) : act γ.1.1 x ∈ N := by
    have := Submodule.mem_map_of_mem (f := act γ.1.1) hx
    rwa [γ.2] at this
  let f (γ : {γ : U E n // N.map (act γ.1) = N}) (i : s) :
      {y | y ∈ (klat E n N).lattice ∧ ‖y‖ ≤ ‖(klat E n N).ψ i‖} :=
    ⟨(klat E n N).ψ (act γ.1.1 i), ⟨act γ.1.1 i, hmem γ (hsN i.2), rfl⟩,
      (norm_ψ_act N γ.1.2 i).le⟩
  refine Finite.of_injective f fun γ γ' h => ?_
  have hb (i : s) : act γ.1.1 (b i) = act γ'.1.1 (b i) := by
    rw [Basis.mk_apply]
    exact (klat E n N).ψ_injective (congrArg Subtype.val (congrFun h i))
  have hlin : Matrix.toLin' (γ.1.1 : Matrix (Fin n) (Fin n) E) =
      Matrix.toLin' (γ'.1.1 : Matrix (Fin n) (Fin n) E) :=
    b.ext fun i => by simpa [Matrix.toLin'_apply] using hb i
  exact Subtype.ext (Subtype.ext (Units.ext (Matrix.toLin'.injective hlin)))

omit [N.IsLattice E] in
/-- `Tr h(y, Σ aₗ vₗ) = Σ aₗ Tr h(y, vₗ)` for integers `aₗ`. -/
theorem trace_herm_sum_right {ι : Type*} [Fintype ι] (y : Fin n → E) (v : ι → Fin n → E) (a : ι → ℤ) :
    Algebra.trace ℚ E (herm y (∑ l, a l • v l)) = ∑ l, (a l : ℚ) * Algebra.trace ℚ E (herm y (v l)) := by
  simp only [herm_sum_right, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Int.cast_smul_eq_zsmul E, herm_smul_right, show ((a l : E) * herm y (v l)) = (a l : ℚ) • herm y (v l) by
    rw [Rat.smul_def]; push_cast; rfl, map_smul, smul_eq_mul]

omit [N.IsLattice E] in
/-- `Tr h(Σ zⱼ vⱼ, x) = Σ zⱼ Tr h(vⱼ, x)` for integers `zⱼ`. -/
theorem trace_herm_sum_left {ι : Type*} [Fintype ι] (v : ι → Fin n → E) (z : ι → ℤ) (x : Fin n → E) :
    Algebra.trace ℚ E (herm (∑ j, z j • v j) x) = ∑ j, (z j : ℚ) * Algebra.trace ℚ E (herm (v j) x) := by
  simp only [herm_sum_left, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Int.cast_smul_eq_zsmul E, herm_smul_left, map_intCast,
    show ((z j : E) * herm (v j) x) = (z j : ℚ) • herm (v j) x by rw [Rat.smul_def]; push_cast; rfl,
    map_smul, smul_eq_mul]

omit [N.IsLattice E] in
/-- **The different**: if `Tr h(y, x) ∈ tℤ` for every `y ∈ N`, then `(d_E/t)·x ∈ N^# = N`. Indeed `h(y, x)/t` lies in
the trace dual of `O_E` (`Tr(c·h(y, x)) = Tr h(conj(c)·y, x)`), which `d_E` carries into `O_E`. -/
theorem discr_div_smul_mem (hN : IsUnimodular N) {x : Fin n → E} {t : ℤ} (ht : t ≠ 0)
    (hx : ∀ y ∈ N, ∃ z : ℤ, Algebra.trace ℚ E (herm y x) = t * z) : ((discr E : ℚ) / t) • x ∈ N := by
  rw [← show dual N = N from hN]
  refine mem_dual.2 fun y hy => ?_
  have ht' : (t : E) ≠ 0 := Int.cast_ne_zero.2 ht
  have hw : herm y x / t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    refine Submodule.mem_traceDual.2 fun c hc => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hc
    have hcy : IsCMField.complexConj E (algebraMap (𝓞 E) E c) • y ∈ N := by
      rw [show IsCMField.complexConj E (algebraMap (𝓞 E) E c) =
        algebraMap (𝓞 E) E (IsCMField.ringOfIntegersComplexConj E c) from rfl, algebraMap_smul]
      exact N.smul_mem _ hy
    obtain ⟨z, hz⟩ := hx _ hcy
    rw [herm_smul_left, IsCMField.complexConj_apply_apply] at hz
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply, show herm y x / t * algebraMap (𝓞 E) E c =
      ((t : ℚ)⁻¹) • (algebraMap (𝓞 E) E c * herm y x) by rw [Rat.smul_def]; push_cast; field_simp,
      map_smul, hz, smul_eq_mul, eq_intCast]
    field_simp
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E) 1
    (b := integralBasis E) (fun i => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
    (Submodule.mem_one.2 ⟨1, map_one _⟩) hw
  rw [← coe_discr] at hint
  have key : (discr E : ℚ) • (1 : E) * (herm y x / t) = herm y (((discr E : ℚ) / t) • x) := by
    rw [← algebraMap_smul E ((discr E : ℚ) / t) x, herm_smul_right, Rat.smul_def, eq_ratCast]
    push_cast
    field_simp
  exact Submodule.mem_one.2 ⟨⟨_, hint⟩, key⟩

/-- `Tr h(y, q·x) = q·Tr h(y, x)` for `q ∈ ℚ`. -/
theorem trace_herm_qsmul (y x : Fin n → E) (q : ℚ) :
    Algebra.trace ℚ E (herm y (q • x)) = q * Algebra.trace ℚ E (herm y x) := by
  rw [← algebraMap_smul E q x, herm_smul_right, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- **Unimodularity bounds the covolume**: for a `ℤ`-basis `b = ψ(v)` of `ψ(N)`, `det Gram(b) ≤ (|d_E|/2)^{rk}`.
Here `2·Gram(b)` is the integer matrix `T = (Tr h(vᵢ, vⱼ))`. The vectors `xₖ = Σₗ adj(T)ₗₖ vₗ` have
`Tr h(y, xₖ) ∈ det(T)·ℤ` on `N`, so `uₖ = (d_E/det T)·xₖ ∈ N` (`discr_div_smul_mem`); their coordinates `W` in `v`
are integers with `T W = d_E`, so `det T` divides `d_E^{rk}`. -/
theorem det_gram_le (hN : IsUnimodular N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (klat E n N).lattice) :
    (Matrix.gram ℝ fun i => (b i : Space E (Fin n))).det ≤ (|(discr E : ℝ)| / 2) ^ Fintype.card ι := by
  have hb (i : ι) : ∃ v ∈ N, (klat E n N).ψ v = b i := (b i).2
  choose v hvN hv using hb
  have hcoord : ∀ y ∈ N, ∃ z : ι → ℤ, y = ∑ j, z j • v j := by
    intro y hy
    let yl : (klat E n N).lattice := ⟨(klat E n N).ψ y, y, hy, rfl⟩
    refine ⟨b.repr yl, (klat E n N).ψ_injective ?_⟩
    have := congrArg Subtype.val (b.sum_repr yl)
    rw [Submodule.coe_sum] at this
    rw [map_sum]
    simp only [map_zsmul, hv]
    exact this.symm.trans (Finset.sum_congr rfl fun i _ => by simp)
  have hT (i j : ι) := trace_int (herm_mem_one hN (hvN i) (hvN j))
  choose T hT using hT
  set Tm : Matrix ι ι ℤ := Matrix.of T
  have hgram : (Matrix.gram ℝ fun i => (b i : Space E (Fin n))) = (2⁻¹ : ℝ) • Tm.map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [Matrix.gram_apply, ← hv, ← hv, real_inner_ψ, hT]
    simp [Tm]
    ring
  have hdet : (Matrix.gram ℝ fun i => (b i : Space E (Fin n))).det = (2⁻¹ : ℝ) ^ Fintype.card ι * (Tm.det : ℝ) := by
    rw [hgram, Matrix.det_smul, Int.cast_det]
  have hpos : 0 < (Matrix.gram ℝ fun i => (b i : Space E (Fin n))).det := by
    rw [← GramVolume.vol_sq]
    exact pow_pos (GramVolume.vol_pos_iff.2 (EuclidLattice.linearIndependent_basis b)) 2
  have ht : Tm.det ≠ 0 := by
    intro h
    rw [hdet, h, Int.cast_zero, mul_zero] at hpos
    exact lt_irrefl _ hpos
  -- the columns of `d_E·T⁻¹` are integral
  have hTadj (j k : ι) : ∑ l, (T j l : ℚ) * Tm.adjugate l k = if j = k then (Tm.det : ℚ) else 0 := by
    have := congrFun (congrFun (Matrix.mul_adjugate Tm) j) k
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at this
    split_ifs at this ⊢ with hjk <;> simp only [smul_eq_mul, mul_one, mul_zero] at this <;> exact_mod_cast this
  have hW (k : ι) : ∃ w : ι → ℤ, ∀ j, ∑ l, (T j l : ℚ) * w l = if j = k then (discr E : ℚ) else 0 := by
    set x := ∑ l, Tm.adjugate l k • v l
    have hxj (j : ι) : Algebra.trace ℚ E (herm (v j) x) = if j = k then (Tm.det : ℚ) else 0 := by
      simp only [x, trace_herm_sum_right, hT]
      rw [← hTadj j k]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have hx : ∀ y ∈ N, ∃ z : ℤ, Algebra.trace ℚ E (herm y x) = Tm.det * z := by
      intro y hy
      obtain ⟨z, rfl⟩ := hcoord y hy
      refine ⟨z k, ?_⟩
      rw [trace_herm_sum_left]
      simp_rw [hxj]
      simp [mul_comm]
    obtain ⟨w, hw⟩ := hcoord _ (discr_div_smul_mem N hN ht hx)
    refine ⟨w, fun j => ?_⟩
    have h1 := trace_herm_sum_right (v j) v w
    rw [← hw, trace_herm_qsmul, hxj] at h1
    simp only [hT] at h1
    rw [Finset.sum_congr rfl fun l _ => mul_comm (T j l : ℚ) (w l), ← h1]
    have ht' : (Tm.det : ℚ) ≠ 0 := Int.cast_ne_zero.2 ht
    split_ifs
    · field_simp
    · simp
  choose W hW using hW
  have hTW : Tm * Matrix.of (fun l k => W k l) = (discr E) • 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    have := hW k j
    split_ifs at this ⊢ with hjk <;> simp only [smul_eq_mul, mul_one, mul_zero] <;> exact_mod_cast this
  have hD : (discr E) ≠ 0 := discr_ne_zero E
  have hdW := congrArg Matrix.det hTW
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hdW
  have hW0 : (Matrix.of fun l k => W k l).det ≠ 0 := fun h =>
    pow_ne_zero (Fintype.card ι) hD (by rw [← hdW, h, mul_zero])
  have hle : |Tm.det| ≤ |discr E| ^ Fintype.card ι := by
    rw [← abs_pow, ← hdW, abs_mul]
    exact le_mul_of_one_le_right (abs_nonneg _) (Int.one_le_abs hW0)
  have hle' : (Tm.det : ℝ) ≤ |(discr E : ℝ)| ^ Fintype.card ι := by
    have : ((|Tm.det| : ℤ) : ℝ) ≤ ((|discr E| ^ Fintype.card ι : ℤ) : ℝ) := by exact_mod_cast hle
    rw [Int.cast_abs, Int.cast_pow, Int.cast_abs] at this
    exact (le_abs_self _).trans this
  rw [hdet, div_pow, div_eq_inv_mul, inv_pow]
  exact mul_le_mul_of_nonneg_left hle' (by positivity)

end Embed

/-! ### Minkowski off a hyperplane -/

section Minkowski

open MeasureTheory

/-- **Minkowski off a hyperplane**: in a real inner product space with a Haar measure `μ`, given `δ > 0` and a bound
`c < ∞`, there is `R` such that every lattice with a fundamental domain of measure at most `c` and no nonzero vector
shorter than `δ` has, off every hyperplane `⟨a, ·⟩ = 0`, a vector of length at most `R`. Minkowski's theorem for the
body `B(0, δ/2) + [-Kδ, Kδ]·â`, which holds `2K + 1` disjoint balls `B(kδ·â, δ/2)` and meets the hyperplane only in
vectors shorter than `δ`. -/
theorem exists_short_inner_ne_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {δ : ℝ} (hδ : 0 < δ) {c : ENNReal} (hc : c ≠ ⊤) :
    ∃ R : ℝ, ∀ (L : AddSubgroup V) [Countable L] (F : Set V), IsAddFundamentalDomain L F μ → μ F ≤ c →
      (∀ x ∈ L, x ≠ 0 → δ ≤ ‖x‖) → ∀ a : V, a ≠ 0 → ∃ x ∈ L, inner ℝ a x ≠ 0 ∧ ‖x‖ ≤ R := by
  set B := μ (Metric.ball (0 : V) (δ / 2))
  have hB0 : B ≠ 0 := (Metric.measure_ball_pos μ _ (by positivity)).ne'
  have hBt : B ≠ ⊤ := measure_ball_lt_top.ne
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt
    (ENNReal.div_ne_top (ENNReal.mul_ne_top hc (ENNReal.pow_ne_top (ENNReal.ofNat_ne_top (n := 2)))) hB0)
  refine ⟨δ / 2 + K * δ, fun L _ F hF hFc hmin a ha => ?_⟩
  set u : V := (‖a‖⁻¹ : ℝ) • a
  have hu : ‖u‖ = 1 := norm_smul_inv_norm ha
  let s : Set V := {x | ∃ y ∈ Metric.ball (0 : V) (δ / 2), ∃ t ∈ Set.Icc (-(K * δ)) (K * δ), x = y + t • u}
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    rintro x ⟨y, hy, t, ht, rfl⟩
    exact ⟨-y, by simpa using hy, -t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by rw [neg_add, neg_smul]⟩
  have hconv : Convex ℝ s := by
    rintro x ⟨y, hy, t, ht, rfl⟩ x' ⟨y', hy', t', ht', rfl⟩ p q hp hq hpq
    refine ⟨p • y + q • y', convex_ball _ _ hy hy' hp hq hpq, p * t + q * t',
      convex_Icc _ _ ht ht' hp hq hpq, ?_⟩
    simp only [smul_add, smul_smul, add_smul]
    abel
  let cen (k : Fin (2 * K + 1)) : V := ((((k : ℕ) : ℝ) - K) * δ) • u
  have hsub : (⋃ k ∈ (Finset.univ : Finset (Fin (2 * K + 1))), Metric.ball (cen k) (δ / 2)) ⊆ s := by
    simp only [Finset.mem_univ, Set.iUnion_true, Set.iUnion_subset_iff]
    intro k z hz
    have hk : ((k : ℕ) : ℝ) ≤ 2 * K := by exact_mod_cast Nat.lt_succ_iff.1 k.2
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
    refine ⟨z - cen k, by rwa [mem_ball_zero_iff, ← dist_eq_norm], (((k : ℕ) : ℝ) - K) * δ,
      ⟨by nlinarith, by nlinarith⟩, by simp [cen]⟩
  have hdisj : ((Finset.univ : Finset (Fin (2 * K + 1))) : Set (Fin (2 * K + 1))).PairwiseDisjoint
      fun k => Metric.ball (cen k) (δ / 2) := by
    intro k _ k' _ hkk'
    refine Metric.ball_disjoint_ball ?_
    have h1 : (1 : ℝ) ≤ |((k : ℕ) : ℝ) - (k' : ℕ)| := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkk') with h | h
      · have : ((k : ℕ) : ℝ) + 1 ≤ (k' : ℕ) := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]
        linarith
      · have : ((k' : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]
        linarith
    rw [dist_eq_norm, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, ← sub_mul, abs_mul,
      abs_of_pos hδ]
    have : ((k : ℕ) : ℝ) - K - (((k' : ℕ) : ℝ) - K) = ((k : ℕ) : ℝ) - (k' : ℕ) := by ring
    rw [this]
    nlinarith
  have hvol : ((2 * K + 1 : ℕ) : ENNReal) * B ≤ μ s := by
    calc ((2 * K + 1 : ℕ) : ENNReal) * B = ∑ k : Fin (2 * K + 1), μ (Metric.ball (cen k) (δ / 2)) := by
          simp [Measure.addHaar_ball_center, B]
      _ = μ (⋃ k ∈ (Finset.univ : Finset (Fin (2 * K + 1))), Metric.ball (cen k) (δ / 2)) :=
          (measure_biUnion_finset hdisj fun _ _ => Metric.isOpen_ball.measurableSet).symm
      _ ≤ μ s := measure_mono hsub
  have hlt : μ F * 2 ^ finrank ℝ V < μ s := by
    calc μ F * 2 ^ finrank ℝ V ≤ c * 2 ^ finrank ℝ V := by gcongr
      _ < K * B := (ENNReal.div_lt_iff (Or.inl hB0) (Or.inl hBt)).1 hK
      _ ≤ ((2 * K + 1 : ℕ) : ENNReal) * B := by gcongr; exact_mod_cast (by omega : K ≤ 2 * K + 1)
      _ ≤ μ s := hvol
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hsymm hconv hlt
  obtain ⟨y, hy, t, ht, rfl⟩ := hxs
  have hx0' : y + t • u ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hy' : ‖y‖ < δ / 2 := mem_ball_zero_iff.1 hy
  have hnorm : ‖y + t • u‖ ≤ ‖y‖ + |t| :=
    (norm_add_le _ _).trans (by rw [norm_smul, hu, mul_one, Real.norm_eq_abs])
  refine ⟨y + t • u, hxL, fun hin => ?_, ?_⟩
  · have h1 : inner ℝ u (y + t • u) = 0 := by rw [real_inner_smul_left, hin, mul_zero]
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu] at h1
    have ht' : |t| ≤ ‖y‖ := by
      have : t = -inner ℝ u y := by linarith
      rw [this, abs_neg]
      exact (abs_real_inner_le_norm u y).trans (by rw [hu, one_mul])
    have := hmin _ hxL hx0'
    linarith
  · have := abs_le.2 ⟨ht.1, ht.2⟩
    linarith

end Minkowski

/-! ### Short bases -/

section Short

open HermitianLattice KLattice MeasureTheory

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
/-- The Borel σ-algebra on `⊕_v ℂ^n`. -/
abbrev spaceMeas : MeasurableSpace (Space E (Fin n)) := borel _

attribute [local instance] spaceMeas

omit [IsCMField E] in
/-- `⊕_v ℂ^n` with its Borel σ-algebra is a Borel space. -/
theorem spaceBorel : BorelSpace (Space E (Fin n)) := ⟨rfl⟩

attribute [local instance] spaceBorel

/-- **Bounded covolume**: a fundamental domain of `ψ(N)`, for any unimodular `N`, has Haar measure at most a bound
`C < ∞` independent of `N`. For a basis `b` of `ψ(N)` and a fixed basis `b₀`, `μ(F_b) = |det_{b₀} b|·μ(F_{b₀})` and
`|det_{b₀} b|·vol b₀ = vol b`, with `vol b² = det Gram(b) ≤ (|d_E|/2)^{rk}` (`det_gram_le`). -/
theorem exists_fund_le : ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E],
    IsUnimodular N → ∃ b : Basis (Fin (finrank ℝ (Space E (Fin n)))) ℝ (Space E (Fin n)),
      Submodule.span ℤ (Set.range b) = (klat E n N).lattice ∧
      (Measure.addHaar : Measure (Space E (Fin n))) (ZSpan.fundamentalDomain b) ≤ C := by
  let b₀ := Module.finBasis ℝ (Space E (Fin n))
  have hv0 : 0 < GramVolume.vol fun i => b₀ i := GramVolume.vol_pos_iff.2 b₀.linearIndependent
  refine ⟨ENNReal.ofReal (√((|(discr E : ℝ)| / 2) ^ finrank ℝ (Space E (Fin n))) /
      GramVolume.vol fun i => b₀ i) * Measure.addHaar (ZSpan.fundamentalDomain b₀),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne,
    fun N _ hN => ?_⟩
  let bL : Basis (Fin (finrank ℝ (Space E (Fin n)))) ℤ (klat E n N).lattice :=
    Module.finBasisOfFinrankEq ℤ _ (ZLattice.rank ℝ _)
  let b := bL.ofZLatticeBasis ℝ (klat E n N).lattice
  refine ⟨b, Basis.ofZLatticeBasis_span ℝ _ bL, ?_⟩
  rw [ZSpan.measure_fundamentalDomain b _ b₀]
  gcongr
  have hcomb := GramVolume.vol_comb (fun i => b₀ i) (b₀.toMatrix b)
  have hb : (fun j => ∑ i, b₀.toMatrix b i j • b₀ i) = fun j => b j :=
    funext fun j => by simp [Basis.toMatrix_apply, b₀.sum_repr]
  rw [hb, ← Basis.det_apply] at hcomb
  rw [le_div_iff₀ hv0, ← hcomb, GramVolume.vol]
  apply Real.sqrt_le_sqrt
  have := det_gram_le N hN bL
  simpa [b, Basis.ofZLatticeBasis_apply, Fintype.card_fin] using this

/-- **Short bases**: there is `R` such that every unimodular `N` contains an `E`-basis of `E^n` of vectors with
`‖ψ v‖ ≤ R`. Given independent `v₁, …, v_k ∈ N`, `k < n`, take `u ≠ 0` with `h(vᵢ, u) = 0`; Minkowski off the
hyperplane `⟨ψ u, ·⟩ = 0` (`exists_short_inner_ne_zero`, with the bounded covolume of `exists_fund_le` and the
minimum `1/2` of `half_le_norm_ψ`) gives `y ∈ N` with `‖ψ y‖ ≤ R` and `h(u, y) ≠ 0`, so `y ∉ Σ E vᵢ`. -/
theorem exists_short_basis : ∃ R : ℝ, ∀ (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E], IsUnimodular N →
    ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ N) ∧ LinearIndependent E v ∧ ∀ i, ‖(klat E n N).ψ (v i)‖ ≤ R := by
  obtain ⟨C, hC, hfund⟩ := exists_fund_le (E := E) (n := n)
  obtain ⟨R, hR⟩ := exists_short_inner_ne_zero (Measure.addHaar : Measure (Space E (Fin n)))
    (by norm_num : (0 : ℝ) < 1 / 2) hC
  refine ⟨R, fun N _ hN => ?_⟩
  obtain ⟨b, hbspan, hbC⟩ := hfund N hN
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b))
    infer_instance
  have hmem {x : Space E (Fin n)} (hx : x ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup) :
      ∃ y ∈ N, (klat E n N).ψ y = x := by
    rw [Submodule.mem_toAddSubgroup, hbspan] at hx
    exact hx
  have hstep := hR _ _ (ZSpan.isAddFundamentalDomain' b _) hbC fun x hx hx0 => by
    obtain ⟨y, hyN, rfl⟩ := hmem hx
    exact half_le_norm_ψ N hN hyN fun h => hx0 (by rw [h, map_zero])
  suffices h : ∀ k ≤ n, ∃ v : Fin k → Fin n → E, (∀ i, v i ∈ N) ∧ LinearIndependent E v ∧
      ∀ i, ‖(klat E n N).ψ (v i)‖ ≤ R from h n le_rfl
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hvN, hv, hvR⟩ := ih (by omega)
    let Φ : (Fin n → E) →ₗ[E] (Fin k → E) := LinearMap.pi fun i => hermL (v i)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) (by simp; omega))
    have hvu (i) : herm (v i) u = 0 := congrFun (LinearMap.mem_ker.1 hu) i
    obtain ⟨x, hxL, hxa, hxR⟩ := hstep ((klat E n N).ψ u)
      fun h => hu0 ((klat E n N).ψ_injective (h.trans (map_zero _).symm))
    obtain ⟨y, hyN, rfl⟩ := hmem hxL
    have hy : herm u y ≠ 0 := fun h => hxa (by rw [real_inner_ψ, h, map_zero]; simp)
    refine ⟨Fin.snoc v y, fun i => ?_, linearIndependent_finSnoc.2 ⟨hv, fun hspan => hy ?_⟩, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa using hyN
      | cast i => simpa using hvN i
    · have : Submodule.span E (Set.range v) ≤ LinearMap.ker (hermL u) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, rfl⟩
        change herm u (v i) = 0
        rw [herm_comm, hvu, map_zero]
      exact this hspan
    · induction i using Fin.lastCases with
      | last => simpa using hxR
      | cast i => simpa using hvR i

/-- `|σ h(x, y)| ≤ R²` at every complex embedding when `‖ψ x‖, ‖ψ y‖ ≤ R`: `|σ h(x, y)| ≤ Σᵢ |σ xᵢ||σ yᵢ|`, and
`Σᵢ |σ xᵢ|² ≤ ‖ψ x‖²`. -/
theorem norm_emb_herm_le (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] {x y : Fin n → E} {R : ℝ}
    (hx : ‖(klat E n N).ψ x‖ ≤ R) (hy : ‖(klat E n N).ψ y‖ ≤ R) (φ : E →+* ℂ) : ‖φ (herm x y)‖ ≤ R ^ 2 := by
  let w : Pl E := ⟨InfinitePlace.mk φ, IsTotallyComplex.isComplex _⟩
  have hS (z : Fin n → E) : ∑ i, ‖φ (z i)‖ ^ 2 ≤ ‖(klat E n N).ψ z‖ ^ 2 := by
    rw [norm_ψ_sq]
    have h1 (i : Fin n) : ‖φ (z i)‖ = ‖w.1.embedding (z i)‖ := by
      rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
    simp_rw [h1]
    exact Finset.single_le_sum (f := fun w : Pl E => ∑ i, ‖w.1.embedding (z i)‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ w)
  have h0 : 0 ≤ R := (norm_nonneg _).trans hx
  calc ‖φ (herm x y)‖ ≤ ∑ i, ‖φ (x i)‖ * ‖φ (y i)‖ := by
        rw [emb_herm]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, Complex.norm_conj]
    _ ≤ ∑ i, (‖φ (x i)‖ ^ 2 + ‖φ (y i)‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (‖φ (x i)‖ - ‖φ (y i)‖)]
    _ = (∑ i, ‖φ (x i)‖ ^ 2 + ∑ i, ‖φ (y i)‖ ^ 2) / 2 := by rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (R ^ 2 + R ^ 2) / 2 := by
        gcongr
        · exact (hS x).trans (pow_le_pow_left₀ (norm_nonneg _) hx 2)
        · exact (hS y).trans (pow_le_pow_left₀ (norm_nonneg _) hy 2)
    _ = R ^ 2 := by ring

/-- **Finitely many Gram matrices**: every unimodular `N` contains an `E`-basis of `E^n` whose Gram matrix lies in a
finite set: its entries are algebraic integers with all conjugates at most `R²` (`exists_short_basis`,
`norm_emb_herm_le`), finitely many (`NumberField.Embeddings.finite_of_norm_le`). -/
theorem exists_gram_cover : ∃ 𝒢 : Set (Matrix (Fin n) (Fin n) E), 𝒢.Finite ∧
    ∀ N : Submodule (𝓞 E) (Fin n → E), IsUnimodular N →
      ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ N) ∧ LinearIndependent E v ∧ hermGram v ∈ 𝒢 := by
  obtain ⟨R, hR⟩ := exists_short_basis (E := E) (n := n)
  refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ R ^ 2},
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Embeddings.finite_of_norm_le E ℂ (R ^ 2), fun N hN => ?_⟩
  have := isLattice_of_unimodular hN
  obtain ⟨v, hvN, hv, hvR⟩ := hR N hN
  refine ⟨v, hvN, hv, fun i _ j _ => ⟨?_, norm_emb_herm_le N (hvR i) (hvR j)⟩⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (herm_mem_one hN (hvN i) (hvN j))
  change IsIntegral ℤ (herm (v i) (v j))
  rw [← ha]
  exact RingOfIntegers.isIntegral_coe a

end Short

/-! ### The theorems -/

/-- **Finitely many classes** (C1, first half): the decorated unimodular lattices fall into finitely many classes
under `𝒢 = U_n(E) × Λ_SG`. Finitely many Gram matrices cover the unimodular lattices (`exists_gram_cover`), so
finitely many lattices represent them up to `U` (`exists_finite_reps`), and each carries finitely many decorations
(`finite_DCl_of_reps`). -/
theorem finite_DCl (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) :
    Finite (DCl E n ST Λ) := by
  obtain ⟨𝒢, h𝒢, hcov⟩ := exists_gram_cover (E := E) (n := n)
  obtain ⟨S, hS, hSu, hrep⟩ := exists_finite_reps h𝒢 hcov
  exact finite_DCl_of_reps hS hSu hrep

/-- **Finite stabilisers** (C1, second half): the stabiliser of every class of decorated unimodular lattices is
finite. It embeds in `Stab_U(N) × Λ` (`finite_stab_of_lattice`), and `Stab_U(N)` is finite (`finite_stabU`). -/
theorem finite_stab (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))
    (c : DCl E n ST Λ) : Finite (stab c) := by
  have hN : IsUnimodular (c.out : Deco E n ST SG).N := (show (c.out : Deco E n ST SG).Good from c.out.2).unimod
  have := isLattice_of_unimodular hN
  exact finite_stab_of_lattice c (finite_stabU _ hN)

end

end HermClasses
