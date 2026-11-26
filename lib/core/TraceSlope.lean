import Mathlib
import FrameRescale
import KLatticeVolume
import DeltaVolume

/-!
# The trace bound for the slope of a hermitian `O_K`-lattice, and duality

For the piece (G↑) of the sharp frontier (`docs/rh-rebuild.md`): a lower bound for the slope of a hermitian
`O_K`-lattice from finitely many of its vectors that span, the duality of slopes, and their monotonicity under
inclusion. Here `K` is totally complex and `X` a hermitian `O_K`-lattice in `K^κ` (`KLattice`).

**Units** (`slopeArch`). The slope in the archive's units is `μ_arch = 2·deg/rk + c_K`, with
`c_K = −log 2 + log|d_K|/[K:ℚ]` (`KLattice`, "The factor 2"). The constant is written out, as in `KLatticeVolume`: it
is the body of `archShift` (`lib/pnt/SharpBound.lean`), which `lib/core` does not import, so
`slopeArch X = 2·μ(X) + archShift K` by unfolding `archShift`.

**Pseudo-basis lattices** (`slopeArch_pseudo`). If `M = P·∏_i 𝔟_i` for a matrix `P` over `K` and nonzero fractional
ideals `𝔟_i`, then

  `μ_arch(X) = −mean_v log det(σ_v(P)ᴴ G_v σ_v(P))/|κ| − 2·Σ_i log N(𝔟_i)/([K:ℚ]·|κ|)`.

The map of `P` (`hom`) carries `ψ(∏_i 𝔟_i)`, with the metric `1`, onto `ψ(M)`, and its real determinant is
`∏_v det(σ_v(P)ᴴ G_v σ_v(P))` (`degK_mulVec`, through `EuclidLattice.covol_map` and `det_op_real`). K2 (`degK_pi`)
removes the ideals, and K3 (`degK_const`) gives the standard lattice `O_K^κ` with the metric `1` the archive slope `0`:
its library slope is `½ log 2 − ½ log|d_K|/[K:ℚ]`, and `2μ + c_K = 0`.

**The trace bound** (`slopeArch_ge_of_span`). For `x_i ∈ M` spanning `K^κ`,
`μ_arch(X) ≥ −mean_v log(Σ_i ‖x_i‖²_{G_v}/|κ|)`. A subfamily `x_b` is a basis (`exists_linearIndependent'`); its
`O_K`-span `N = P·O_K^κ` lies in `M`, so `μ(N) ≤ μ(M)` (`slopeArch_le_of_le`: the index only lowers the degree). With
`H_v = σ_v(P)ᴴ G_v σ_v(P)`, the Gram matrix of the `x_{b j}` at `v`, `μ_arch(N) = −mean_v log det H_v/|κ|`. AM–GM on
the eigenvalues (Jensen for `log`; `log_det_le`) gives `log det H_v ≤ |κ|·log(tr H_v/|κ|)`, and
`tr H_v = Σ_j ‖x_{b j}‖² ≤ Σ_i ‖x_i‖²` (`trace_re_eq_sum_sqLen`). The subfamily is compared with the whole family
through the trace, a sub-sum: no Loewner order and no Cauchy–Binet.

**Duality** (`dualK`, `slopeArch_dual`). The dual `X^∨` has the lattice `M^∨ = {w : w·x ∈ O_K for x ∈ M}`, the
coefficient vectors of `HermitianLattice.dual M` (`dualLat`), and the dual metrics `(G_v⁻¹)ᵀ`; then
`μ_arch(X^∨) = −μ_arch(X)`. An `O_K`-lattice need not be free, so the proof goes through pseudo-bases
(`HermClasses.exists_pseudo`, moved from `Fin n` to `κ` in `exists_pseudo_pi`): `M = P·∏_i 𝔟_i` has
`M^∨ = (P⁻¹)ᵀ·∏_i 𝔟_i⁻¹` (`dualLat_pseudo`); the determinants at each place are inverse (`log_re_det_dual`) and
`N(𝔟_i⁻¹) = N(𝔟_i)⁻¹`.

**The dual trace bound** (`slopeArch_le_of_dual_span`). For `c_i ∈ M^∨` spanning `K^κ`,
`μ_arch(X) ≤ mean_v log(Σ_i ‖c_i‖²_{(G_v⁻¹)ᵀ}/|κ|)`: the trace bound for `X^∨`, and duality. This is the form in which
(G↑) needs it: there the target lies in the dual of the span of the rows.
-/

namespace KLattice

open Module Submodule NumberField HermitianLattice Matrix

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical ComplexOrder InnerProductSpace nonZeroDivisors

/-- **The squared length** of `x ∈ K^κ` in the metric `G` at an embedding `σ`: `σ(x)ᴴ G σ(x)`. -/
noncomputable def sqLen {K : Type} [Field K] {κ : Type} [Fintype κ] (G : Matrix κ κ ℂ) (σ : K →+* ℂ)
    (x : κ → K) : ℝ :=
  (dotProduct (star fun i => σ (x i)) (G.mulVec fun i => σ (x i))).re

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {κ : Type} [Fintype κ]

/-- **The slope in the archive's units**, `μ_arch = 2·deg/rk + c_K` with `c_K = −log 2 + log|d_K|/[K:ℚ]`, the body of
`archShift K`. -/
noncomputable def slopeArch (X : KLattice K κ) : ℝ :=
  2 * (X.toPlaceLattice.slopeLattice.deg ⊤ / X.toPlaceLattice.slopeLattice.rk ⊤) +
    (-Real.log 2 + Real.log |(discr K : ℝ)| / finrank ℚ K)

/-! ### Pseudo-basis lattices -/

omit [Field K] [NumberField K] [IsTotallyComplex K] in
/-- **The squared modulus of a determinant**: `|det B|² = det(BᴴB)`. -/
theorem normSq_det (B : Matrix κ κ ℂ) : Complex.normSq B.det = (Bᴴ * B).det.re := by
  rw [det_mul, det_conjTranspose, ← Complex.ofReal_re (Complex.normSq B.det), Complex.normSq_eq_conj_mul_self]
  rfl

omit [NumberField K] [IsTotallyComplex K] in
/-- **The image of a lattice**: an invertible matrix carries an `O_K`-lattice to an `O_K`-lattice. -/
theorem isLattice_map_mulVec (N : Submodule (𝓞 K) (κ → K)) [N.IsLattice K] {P : Matrix κ κ K} (hP : IsUnit P) :
    (N.map ((mulVecLin P).restrictScalars (𝓞 K))).IsLattice K where
  fg := IsLattice.fg.map _
  span_eq_top := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, IsLattice.span_eq_top,
      Submodule.map_top, LinearMap.range_eq_top]
    exact mulVec_surjective_iff_isUnit.2 hP

/-- **A change of lattice and metric**: if `M_Y = P·M_X`, then
`deg Y = deg X − Σ_v (log det(σ_v(P)ᴴ G_{Y,v} σ_v(P)) − log det G_{X,v})`. The map `hom` of `P` carries `ψ_X(M_X)` onto
`ψ_Y(M_Y)` (`hom_ψ`) and is blockwise `A_{Y,v} σ_v(P) A_{X,v}⁻¹`, of real determinant
`∏_v |det(A_{Y,v} σ_v(P))|²/|det A_{X,v}|²` (`det_op_real`), which is the product of the ratios of determinants
(`normSq_det`, `factor_spec`); then `EuclidLattice.covol_map`. -/
theorem degK_mulVec (X Y : KLattice K κ) (P : Matrix κ κ K)
    (hM : Y.M = X.M.map ((mulVecLin P).restrictScalars (𝓞 K))) :
    degK Y = degK X - ∑ v : Pl K, (Real.log ((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re -
      Real.log (X.G v).det.re) := by
  set T := (X.hom Y (mulVecLin P) : Space K κ →ₗ[ℂ] Space K κ).restrictScalars ℝ with hT
  have hY : (Y.lattice : Set (Space K κ)) = T '' X.lattice := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ X.M.map ((mulVecLin P).restrictScalars (𝓞 K)) := by rw [← hM]; exact hz
      obtain ⟨x, hx, rfl⟩ := hz'
      exact ⟨X.ψ x, ⟨x, hx, rfl⟩, X.hom_ψ Y _ x⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hx' : P *ᵥ x ∈ Y.M := by rw [hM]; exact ⟨x, hx, rfl⟩
      change X.hom Y (mulVecLin P) (X.ψ x) ∈ Y.lattice
      rw [X.hom_ψ Y (mulVecLin P) x]
      exact ⟨P *ᵥ x, hx', rfl⟩
  have h := EuclidLattice.covol_map T X.span_lattice Y.span_lattice hY
  have hP : LinearMap.toMatrix' (mulVecLin P) = P := LinearMap.toMatrix'_toLin' P
  have hfac (v : Pl K) : Complex.normSq (Y.factor v * P.map v.1.embedding * (X.factor v)⁻¹).det =
      ((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re / (X.G v).det.re := by
    have hY' : (Y.factor v * P.map v.1.embedding)ᴴ * (Y.factor v * P.map v.1.embedding) =
        (P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding := by
      rw [conjTranspose_mul, ← Y.factor_spec v]
      simp only [Matrix.mul_assoc]
    rw [det_mul, map_mul, det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, ← div_eq_mul_inv, normSq_det, hY',
      normSq_det, factor_spec]
  have hdet : LinearMap.det T = ∏ v : Pl K,
      ((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re / (X.G v).det.re := by
    rw [hT, hom, det_op_real, hP]
    exact Finset.prod_congr rfl fun v _ => hfac v
  have hnn : 0 ≤ LinearMap.det T := by
    rw [hT, hom, det_op_real]
    exact Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _
  rw [abs_of_nonneg hnn, hdet] at h
  have hpos : 0 < ∏ v : Pl K, ((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re / (X.G v).det.re :=
    pos_of_mul_pos_left (h ▸ EuclidLattice.covol_pos _) (EuclidLattice.covol_pos _).le
  have hne (v : Pl K) : ((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re / (X.G v).det.re ≠ 0 :=
    Finset.prod_ne_zero_iff.1 hpos.ne' v (Finset.mem_univ v)
  show -Real.log (EuclidLattice.covol Y.lattice) = -Real.log (EuclidLattice.covol X.lattice) - _
  rw [h, Real.log_mul hpos.ne' (EuclidLattice.covol_pos _).ne', Real.log_prod fun v _ => hne v]
  have hsum : ∑ v : Pl K, Real.log (((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re /
      (X.G v).det.re) = ∑ v : Pl K, (Real.log ((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re -
        Real.log (X.G v).det.re) :=
    Finset.sum_congr rfl fun v _ => Real.log_div (div_ne_zero_iff.1 (hne v)).1
      (Complex.pos_iff.1 (X.posDef v).det_pos).1.ne'
  rw [hsum]
  ring

/-- **The degree of a pseudo-basis lattice**: if `M = P·∏_i 𝔟_i`, then
`deg X = −Σ_v log det(σ_v(P)ᴴ G_v σ_v(P)) − Σ_i log N(𝔟_i) − |κ|·([K:ℚ]/2)·(log|d_K|/[K:ℚ] − log 2)`: `degK_mulVec`
from `∏_i 𝔟_i` with the metric `1`, K2 (`degK_pi`) to `O_K^κ`, and K3 (`degK_const`) for `O_K^κ`. -/
theorem degK_pseudo (X : KLattice K κ) {𝔟 : κ → FractionalIdeal (𝓞 K)⁰ K} (h𝔟 : ∀ i, 𝔟 i ≠ 0)
    (P : Matrix κ κ K)
    (hM : X.M = (pi Set.univ fun i => (𝔟 i : Submodule (𝓞 K) K)).map ((mulVecLin P).restrictScalars (𝓞 K))) :
    degK X = -∑ v : Pl K, Real.log ((P.map v.1.embedding)ᴴ * X.G v * P.map v.1.embedding).det.re -
      ∑ i, Real.log (FractionalIdeal.absNorm (𝔟 i) : ℝ) -
      Fintype.card κ * (finrank ℚ K / 2 : ℝ) * (Real.log |(discr K : ℝ)| / finrank ℚ K - Real.log 2) := by
  have : (pi Set.univ fun i => (𝔟 i : Submodule (𝓞 K) K)).IsLattice K := HermForms.isLattice_pi h𝔟
  have : (pi Set.univ fun _ : κ => (1 : Submodule (𝓞 K) K)).IsLattice K := by
    have := HermForms.isLattice_pi (ι := κ) (𝔠 := fun _ => (1 : FractionalIdeal (𝓞 K)⁰ K)) fun _ => one_ne_zero
    rwa [FractionalIdeal.coe_one] at this
  let D : KLattice K κ := ⟨pi Set.univ fun i => (𝔟 i : Submodule (𝓞 K) K), fun _ => 1, fun _ => PosDef.one⟩
  let O : KLattice K κ := ⟨pi Set.univ fun _ => (1 : Submodule (𝓞 K) K), fun _ => 1, fun _ => PosDef.one⟩
  have h1 := degK_mulVec D X P hM
  have h2 := degK_pi D O 𝔟 rfl rfl rfl
  have h3 := degK_const O 1 rfl fun _ => (Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one).symm
  have hD (v : Pl K) : (D.G v).det.re = 1 := by simp [D]
  simp only [hD, Real.log_one, sub_zero] at h1
  rw [det_one, Real.log_one, mul_zero] at h3
  rw [h1, h2, h3]
  ring

/-- **The archive slope of a pseudo-basis lattice**: if `M = P·∏_i 𝔟_i`, then
`μ_arch(X) = −mean_v log det(σ_v(P)ᴴ G_v σ_v(P))/|κ| − 2·Σ_i log N(𝔟_i)/([K:ℚ]·|κ|)`, from `degK_pseudo`,
`rk = [K:ℚ]·|κ|` (`rk_top`) and `[K:ℚ] = 2·n_∞`: the field constant cancels. -/
theorem slopeArch_pseudo [Nonempty κ] (X : KLattice K κ) {𝔟 : κ → FractionalIdeal (𝓞 K)⁰ K}
    (h𝔟 : ∀ i, 𝔟 i ≠ 0) (P : Matrix κ κ K)
    (hM : X.M = (pi Set.univ fun i => (𝔟 i : Submodule (𝓞 K) K)).map ((mulVecLin P).restrictScalars (𝓞 K))) :
    slopeArch X = -((Fintype.card (Pl K) : ℝ)⁻¹ * ∑ v : Pl K,
        Real.log ((P.map v.1.embedding)ᴴ * X.G v * P.map v.1.embedding).det.re / Fintype.card κ) -
      2 * (∑ i, Real.log (FractionalIdeal.absNorm (𝔟 i) : ℝ)) / (finrank ℚ K * Fintype.card κ) := by
  have hK : (finrank ℚ K : ℝ) = 2 * Fintype.card (Pl K) := by
    rw [IsTotallyComplex.finrank]
    push_cast
    rfl
  have hc : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hp : (Fintype.card (Pl K) : ℝ) ≠ 0 := by
    have : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    rw [hK] at this
    exact right_ne_zero_of_mul this
  unfold slopeArch
  rw [show X.toPlaceLattice.slopeLattice.deg ⊤ = degK X from rfl, degK_pseudo X h𝔟 P hM, rk_top, ← Finset.sum_div]
  push_cast
  rw [hK]
  field_simp
  ring

/-! ### The trace bound -/

/-- **AM–GM on the eigenvalues**: `log det H ≤ |κ|·log(tr H/|κ|)` for a positive definite `H`. With `det H = ∏ λ_i`
and `tr H = Σ λ_i` (`IsHermitian.det_eq_prod_eigenvalues`, `IsHermitian.trace_eq_sum_eigenvalues`), this is Jensen's
inequality for the concave `log`. -/
theorem log_det_le [Nonempty κ] {H : Matrix κ κ ℂ} (hH : H.PosDef) :
    Real.log H.det.re ≤ Fintype.card κ * Real.log (H.trace.re / Fintype.card κ) := by
  have hev := hH.eigenvalues_pos
  have hdet : H.det.re = ∏ i, hH.1.eigenvalues i := by
    rw [hH.1.det_eq_prod_eigenvalues]
    simp [← Complex.ofReal_prod]
  have htr : H.trace.re = ∑ i, hH.1.eigenvalues i := by
    rw [hH.1.trace_eq_sum_eigenvalues]
    simp
  have hn : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Finset.univ)
    (w := fun _ => (Fintype.card κ : ℝ)⁻¹) (p := hH.1.eigenvalues) (fun _ _ => inv_nonneg.2 hn.le)
    (by simp [Finset.card_univ, hn.ne']) fun i _ => hev i
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  rw [hdet, htr, Real.log_prod fun i _ => (hev i).ne', div_eq_inv_mul]
  calc ∑ i, Real.log (hH.1.eigenvalues i)
      = Fintype.card κ * ((Fintype.card κ : ℝ)⁻¹ * ∑ i, Real.log (hH.1.eigenvalues i)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ hn.le

omit [NumberField K] [IsTotallyComplex K] in
/-- **The trace is a sum of squared lengths**: `tr(σ(P)ᴴ G σ(P)) = Σ_j ‖P e_j‖²_G`. -/
theorem trace_re_eq_sum_sqLen (G : Matrix κ κ ℂ) (σ : K →+* ℂ) (P : Matrix κ κ K) :
    ((P.map σ)ᴴ * G * P.map σ).trace.re = ∑ j, sqLen G σ fun i => P i j := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sqLen, diag_apply, mul_apply, conjTranspose_apply, map_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum, mul_assoc]

/-- **Monotonicity under inclusion**: for `M_X ⊆ M_Y` with the same metrics, `μ_arch(X) ≤ μ_arch(Y)`, as
`μ(M_X) = μ(M_Y) − log [M_Y : M_X]/rk` (`slope_withLattice`). -/
theorem slopeArch_le_of_le {X Y : KLattice K κ} (hM : X.M ≤ Y.M) (hG : X.G = Y.G) : slopeArch X ≤ slopeArch Y := by
  obtain ⟨M, G, hGp⟩ := X
  dsimp only at hM hG
  subst hG
  have h := Y.slope_withLattice hM
  have h0 : 0 ≤ Real.log (M.toAddSubgroup.relIndex Y.M.toAddSubgroup) / (Y.toPlaceLattice.slopeLattice.rk ⊤ : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  unfold slopeArch
  have : (⟨M, Y.G, hGp⟩ : KLattice K κ) = Y.withLattice M := rfl
  rw [this, h]
  linarith

omit [NumberField K] [IsTotallyComplex K] in
/-- **A basis subfamily**: a family spanning `K^κ` has a subfamily indexed by `κ` that is linearly independent. -/
theorem exists_linearIndependent_comp {ι : Type} [Fintype ι] (x : ι → κ → K)
    (hspan : Submodule.span K (Set.range x) = ⊤) : ∃ b : κ → ι, LinearIndependent K (x ∘ b) := by
  obtain ⟨κ', a, ha, hsp, hli⟩ := exists_linearIndependent' K x
  have : Fintype κ' := Fintype.ofInjective a ha
  let B := Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = Fintype.card κ' := by
    rw [← Module.finrank_fintype_fun_eq_card K, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hcard
  exact ⟨a ∘ e, hli.comp e e.injective⟩

/-- **The trace bound**: for vectors `x_i ∈ M` spanning `K^κ`,
`μ_arch(X) ≥ −mean_v log(Σ_i ‖x_i‖²_{G_v}/|κ|)`. A basis subfamily `x_b` spans `N = P·O_K^κ ⊆ M`
(`exists_linearIndependent_comp`), with `μ(N) ≤ μ(M)` (`slopeArch_le_of_le`) and
`μ_arch(N) = −mean_v log det H_v/|κ|` for the Gram matrices `H_v = σ_v(P)ᴴ G_v σ_v(P)` (`slopeArch_pseudo`); AM–GM
(`log_det_le`) and `tr H_v = Σ_j ‖x_{b j}‖² ≤ Σ_i ‖x_i‖²` (`trace_re_eq_sum_sqLen`). -/
theorem slopeArch_ge_of_span {ι : Type} [Nonempty κ] [Fintype ι] (X : KLattice K κ) (x : ι → κ → K)
    (hx : ∀ i, x i ∈ X.M) (hspan : Submodule.span K (Set.range x) = ⊤) :
    -((Fintype.card (Pl K) : ℝ)⁻¹ * ∑ v : Pl K,
        Real.log ((∑ i, sqLen (X.G v) v.1.embedding (x i)) / Fintype.card κ)) ≤ slopeArch X := by
  obtain ⟨b, hb⟩ := exists_linearIndependent_comp x hspan
  have hbinj : Function.Injective b := hb.injective.of_comp
  set P : Matrix κ κ K := Matrix.of fun i j => x (b j) i
  have hP : IsUnit P := linearIndependent_cols_iff_isUnit.1 hb
  set D := pi Set.univ fun _ : κ => ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  have : D.IsLattice K := HermForms.isLattice_pi fun _ => one_ne_zero
  set N := D.map ((mulVecLin P).restrictScalars (𝓞 K))
  have : N.IsLattice K := isLattice_map_mulVec D hP
  have hNM : N ≤ X.M := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' (j : κ) : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c j := by
      have : c j ∈ (1 : Submodule (𝓞 K) K) := by simpa using hc j (Set.mem_univ j)
      exact Submodule.mem_one.1 this
    choose a ha using hc'
    have hsum : P *ᵥ c = ∑ j, a j • x (b j) := by
      ext i
      simp only [P, mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, ← ha,
        Algebra.smul_def, mul_comm]
    show P *ᵥ c ∈ X.M
    rw [hsum]
    exact sum_mem fun j _ => X.M.smul_mem _ (hx _)
  have hle := slopeArch_le_of_le (X := X.withLattice N) (Y := X) hNM rfl
  rw [slopeArch_pseudo (X.withLattice N) (fun _ => one_ne_zero) P rfl] at hle
  simp only [map_one, Rat.cast_one, Real.log_one, Finset.sum_const_zero, mul_zero, zero_div, sub_zero] at hle
  refine le_trans ?_ hle
  rw [neg_le_neg_iff]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (inv_nonneg.2 (Nat.cast_nonneg _))
  have hn : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hσP : IsUnit (P.map v.1.embedding) := hP.map v.1.embedding.mapMatrix
  have hH : ((P.map v.1.embedding)ᴴ * X.G v * P.map v.1.embedding).PosDef :=
    (X.posDef v).conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.2 hσP)
  have htr := trace_re_eq_sum_sqLen (X.G v) v.1.embedding P
  have htrpos : 0 < ((P.map v.1.embedding)ᴴ * X.G v * P.map v.1.embedding).trace.re :=
    (Complex.pos_iff.1 hH.trace_pos).1
  have hsub : ∑ j, sqLen (X.G v) v.1.embedding (fun i => P i j) ≤ ∑ i, sqLen (X.G v) v.1.embedding (x i) := by
    change ∑ j, sqLen (X.G v) v.1.embedding (x (b j)) ≤ _
    rw [← Finset.sum_image (f := fun i => sqLen (X.G v) v.1.embedding (x i)) fun j _ j' _ h => hbinj h]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      (X.posDef v).posSemidef.re_dotProduct_nonneg _
  calc Real.log ((P.map v.1.embedding)ᴴ * (X.withLattice N).G v * P.map v.1.embedding).det.re / Fintype.card κ
      ≤ Real.log (((P.map v.1.embedding)ᴴ * X.G v * P.map v.1.embedding).trace.re / Fintype.card κ) := by
        rw [div_le_iff₀ hn, mul_comm]
        exact log_det_le hH
    _ ≤ _ := Real.log_le_log (div_pos htrpos hn) (div_le_div_of_nonneg_right (htr ▸ hsub) hn.le)

/-! ### Duality -/

omit [IsTotallyComplex K] in
/-- **Pseudo-bases in `K^κ`** (`HermClasses.exists_pseudo`, moved from `Fin n` by `κ ≃ Fin n`): every `O_K`-lattice
is `P·∏_i 𝔟_i` for an invertible `P` and nonzero fractional ideals `𝔟_i`. -/
theorem exists_pseudo_pi (M : Submodule (𝓞 K) (κ → K)) [M.IsLattice K] :
    ∃ (𝔟 : κ → FractionalIdeal (𝓞 K)⁰ K) (P : Matrix κ κ K), (∀ i, 𝔟 i ≠ 0) ∧ IsUnit P ∧
      M = (pi Set.univ fun i => (𝔟 i : Submodule (𝓞 K) K)).map ((mulVecLin P).restrictScalars (𝓞 K)) := by
  let e := Fintype.equivFin κ
  let L : (κ → K) ≃ₗ[K] (Fin (Fintype.card κ) → K) := LinearEquiv.funCongrLeft K K e.symm
  have hL (x : κ → K) : L x = x ∘ e.symm := rfl
  let N := M.map (L.toLinearMap.restrictScalars (𝓞 K))
  have : N.IsLattice K :=
    { fg := IsLattice.fg.map _
      span_eq_top := by
        rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, IsLattice.span_eq_top,
          Submodule.map_top, LinearEquiv.range] }
  obtain ⟨𝔞, γ, h𝔞, hN⟩ := HermClasses.exists_pseudo N
  refine ⟨𝔞 ∘ e, (γ : Matrix _ _ K).submatrix e e, fun i => h𝔞 _, ?_, ?_⟩
  · rw [isUnit_iff_isUnit_det, det_submatrix_equiv_self]
    exact (isUnit_iff_isUnit_det _).1 γ.isUnit
  · ext x
    have hx : x ∈ M ↔ L x ∈ N :=
      ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hxy⟩ => (L.injective hxy) ▸ hy⟩
    rw [hx, hN, Submodule.mem_map, Submodule.mem_map]
    constructor
    · rintro ⟨c, hc, hcx⟩
      refine ⟨c ∘ e, fun k _ => HermClasses.mem_diagLat.1 hc (e k), ?_⟩
      show (γ : Matrix _ _ K).submatrix e e *ᵥ (c ∘ e) = x
      have hc' : (c ∘ e) ∘ e.symm = c := by
        ext
        simp
      rw [submatrix_mulVec_equiv, hc', ← HermClasses.act_apply, hcx, hL]
      ext
      simp
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c ∘ e.symm, HermClasses.mem_diagLat.2 fun i => ?_, ?_⟩
      · have := hc (e.symm i) (Set.mem_univ _)
        simpa using this
      · rw [HermClasses.act_apply, hL]
        show _ = ((γ : Matrix _ _ K).submatrix e e *ᵥ c) ∘ e.symm
        rw [submatrix_mulVec_equiv]
        ext
        simp

/-- **The dual lattice in coordinates**: `M^∨ = {w : w·x ∈ O_K for all x ∈ M}`, the coefficient vectors of the
`O_K`-dual `HermitianLattice.dual M` of linear forms on `K^κ`. -/
noncomputable def dualLat (M : Submodule (𝓞 K) (κ → K)) : Submodule (𝓞 K) (κ → K) :=
  (HermitianLattice.dual M).comap
    ((LinearMap.mk₂ K dotProduct add_dotProduct smul_dotProduct dotProduct_add dotProduct_smul).restrictScalars (𝓞 K))

omit [NumberField K] [IsTotallyComplex K] in
/-- **Membership in the dual**: `w ∈ M^∨` iff `w·x ∈ O_K` for all `x ∈ M`. -/
theorem mem_dualLat {M : Submodule (𝓞 K) (κ → K)} {w : κ → K} :
    w ∈ dualLat M ↔ ∀ x ∈ M, w ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [dualLat, Submodule.mem_comap, HermitianLattice.mem_dual]
  rfl

omit [IsTotallyComplex K] in
/-- **The dual of `∏_i 𝔟_i` is `∏_i 𝔟_i⁻¹`**: `u·w ∈ O_K` for all `u ∈ ∏_i 𝔟_i` iff each `w_i ∈ 𝔟_i⁻¹` (test on
`u = a e_i`; `HermClasses.forall_dotProduct_mem_one` over `κ`). -/
theorem forall_dotProduct_mem_one_pi {𝔟 : κ → FractionalIdeal (𝓞 K)⁰ K} (h𝔟 : ∀ i, 𝔟 i ≠ 0) (w : κ → K) :
    (∀ u ∈ pi Set.univ (fun i => (𝔟 i : Submodule (𝓞 K) K)), u ⬝ᵥ w ∈ (1 : Submodule (𝓞 K) K)) ↔
      w ∈ pi Set.univ fun i => (((𝔟 i)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  have h1 (z : K) : z ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ z ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
  simp_rw [Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_inv_iff (h𝔟 _), h1]
  refine ⟨fun h i a ha => ?_, fun h u hu => ?_⟩
  · have := h (Pi.single i a) fun j => ?_
    · rwa [single_dotProduct, mul_comm] at this
    by_cases hj : j = i
    · subst hj
      simpa using ha
    · rw [Pi.single_eq_of_ne hj]
      exact (𝔟 j).zero_mem
  · exact sum_mem fun i _ => by rw [mul_comm]; exact h i _ (hu i)

omit [IsTotallyComplex K] in
/-- **The dual of a pseudo-basis lattice**: `(P·∏_i 𝔟_i)^∨ = (P⁻¹)ᵀ·∏_i 𝔟_i⁻¹`, as `w·(Pc) = c·(Pᵀw)`. -/
theorem dualLat_pseudo {𝔟 : κ → FractionalIdeal (𝓞 K)⁰ K} (h𝔟 : ∀ i, 𝔟 i ≠ 0) {P : Matrix κ κ K} (hP : IsUnit P) :
    dualLat ((pi Set.univ fun i => (𝔟 i : Submodule (𝓞 K) K)).map ((mulVecLin P).restrictScalars (𝓞 K))) =
      (pi Set.univ fun i => (((𝔟 i)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)).map
        ((mulVecLin (P⁻¹)ᵀ).restrictScalars (𝓞 K)) := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  have hPP' : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP)
  ext w
  rw [mem_dualLat]
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, mulVecLin_apply, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  have key : (∀ c ∈ pi Set.univ (fun i => (𝔟 i : Submodule (𝓞 K) K)), w ⬝ᵥ (P *ᵥ c) ∈ (1 : Submodule (𝓞 K) K)) ↔
      Pᵀ *ᵥ w ∈ pi Set.univ fun i => (((𝔟 i)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [← forall_dotProduct_mem_one_pi h𝔟]
    refine forall₂_congr fun c _ => ?_
    rw [dotProduct_mulVec, dotProduct_comm, mulVec_transpose]
  rw [key]
  constructor
  · intro h
    exact ⟨Pᵀ *ᵥ w, h, by rw [mulVec_mulVec, ← transpose_mul, hPP, transpose_one, one_mulVec]⟩
  · rintro ⟨u, hu, rfl⟩
    rwa [mulVec_mulVec, ← transpose_mul, hPP', transpose_one, one_mulVec]

omit [IsTotallyComplex K] in
/-- **The dual of a lattice is a lattice**, by pseudo-bases (`exists_pseudo_pi`, `dualLat_pseudo`). -/
instance isLattice_dualLat (M : Submodule (𝓞 K) (κ → K)) [M.IsLattice K] : (dualLat M).IsLattice K := by
  obtain ⟨𝔟, P, h𝔟, hP, rfl⟩ := exists_pseudo_pi M
  rw [dualLat_pseudo h𝔟 hP]
  have := HermForms.isLattice_pi fun i => inv_ne_zero (h𝔟 i)
  exact isLattice_map_mulVec _ ((isUnit_transpose _).2 (isUnit_nonsing_inv_iff.2 hP))

/-- **The dual hermitian `O_K`-lattice** `X^∨`: the dual lattice `M^∨` (`dualLat`) with the dual metrics `(G_v⁻¹)ᵀ`,
those of the linear forms `x ↦ w·x` (`‖w‖² = σ(w)ᵀ G_v⁻¹ conj σ(w)`). -/
noncomputable def dualK (X : KLattice K κ) : KLattice K κ :=
  ⟨dualLat X.M, fun v => ((X.G v)⁻¹)ᵀ, fun v => (X.posDef v).inv.transpose⟩

omit [NumberField K] [IsTotallyComplex K] in
/-- **The dual metric inverts the Gram determinant**: `det(σ(Q)ᴴ (G⁻¹)ᵀ σ(Q)) = det(σ(P)ᴴ G σ(P))⁻¹` for
`Q = (P⁻¹)ᵀ`, so their logarithms are opposite. -/
theorem log_re_det_dual {G : Matrix κ κ ℂ} (hG : G.PosDef) (σ : K →+* ℂ) {P : Matrix κ κ K} (hP : IsUnit P) :
    Real.log (((P⁻¹)ᵀ.map σ)ᴴ * (G⁻¹)ᵀ * (P⁻¹)ᵀ.map σ).det.re =
      -Real.log ((P.map σ)ᴴ * G * P.map σ).det.re := by
  have hm (A : Matrix κ κ K) : (A.map σ).det = σ A.det := (RingHom.map_det σ A).symm
  have hdP : σ P.det * σ P⁻¹.det = 1 := by
    rw [← map_mul, ← det_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).1 hP), det_one, map_one]
  have hdG : G.det * G⁻¹.det = 1 := by
    rw [← det_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det G).1 hG.isUnit), det_one]
  have hprod : ((P.map σ)ᴴ * G * P.map σ).det * (((P⁻¹)ᵀ.map σ)ᴴ * (G⁻¹)ᵀ * (P⁻¹)ᵀ.map σ).det = 1 := by
    simp only [det_mul, det_conjTranspose, hm, det_transpose]
    calc star (σ P.det) * G.det * σ P.det * (star (σ P⁻¹.det) * G⁻¹.det * σ P⁻¹.det)
        = star (σ P.det * σ P⁻¹.det) * (G.det * G⁻¹.det) * (σ P.det * σ P⁻¹.det) := by
          rw [star_mul']
          ring
      _ = 1 := by rw [hdP, hdG, star_one, one_mul, one_mul]
  have hH : ((P.map σ)ᴴ * G * P.map σ).PosDef :=
    hG.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.2 (hP.map σ.mapMatrix))
  have him : ((P.map σ)ᴴ * G * P.map σ).det.im = 0 := (Complex.pos_iff.1 hH.det_pos).2.symm
  have hre := congrArg Complex.re hprod
  rw [Complex.mul_re, him, zero_mul, sub_zero, Complex.one_re] at hre
  rw [eq_inv_of_mul_eq_one_right hre, Real.log_inv]

/-- **Duality**: `μ_arch(X^∨) = −μ_arch(X)`. With `M = P·∏_i 𝔟_i` (`exists_pseudo_pi`),
`M^∨ = (P⁻¹)ᵀ·∏_i 𝔟_i⁻¹` (`dualLat_pseudo`); in `slopeArch_pseudo` the Gram determinants at each place are inverse
(`log_re_det_dual`) and `N(𝔟_i⁻¹) = N(𝔟_i)⁻¹`. -/
theorem slopeArch_dual [Nonempty κ] (X : KLattice K κ) : slopeArch X.dualK = -slopeArch X := by
  obtain ⟨𝔟, P, h𝔟, hP, hM⟩ := exists_pseudo_pi X.M
  have hD : X.dualK.M = (pi Set.univ fun i => (((𝔟 i)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)).map
      ((mulVecLin (P⁻¹)ᵀ).restrictScalars (𝓞 K)) := by
    rw [show X.dualK.M = dualLat X.M from rfl, hM, dualLat_pseudo h𝔟 hP]
  rw [slopeArch_pseudo X.dualK (fun i => inv_ne_zero (h𝔟 i)) _ hD, slopeArch_pseudo X h𝔟 P hM]
  have hlog (v : Pl K) := log_re_det_dual (X.posDef v) v.1.embedding hP
  simp only [show ∀ v, X.dualK.G v = ((X.G v)⁻¹)ᵀ from fun _ => rfl, hlog, map_inv₀, Rat.cast_inv, Real.log_inv,
    neg_div, Finset.sum_neg_distrib]
  ring

/-- **The dual trace bound**: for vectors `c_i ∈ M^∨` spanning `K^κ` (the linear forms `x ↦ c_i·x`, integral on `M`),
`μ_arch(X) ≤ mean_v log(Σ_i ‖c_i‖²_{(G_v⁻¹)ᵀ}/|κ|)`: the trace bound (`slopeArch_ge_of_span`) for `X^∨`, and duality
(`slopeArch_dual`). -/
theorem slopeArch_le_of_dual_span {ι : Type} [Nonempty κ] [Fintype ι] (X : KLattice K κ) (c : ι → κ → K)
    (hc : ∀ i, c i ∈ dualLat X.M) (hspan : Submodule.span K (Set.range c) = ⊤) :
    slopeArch X ≤ (Fintype.card (Pl K) : ℝ)⁻¹ * ∑ v : Pl K,
      Real.log ((∑ i, sqLen ((X.G v)⁻¹)ᵀ v.1.embedding (c i)) / Fintype.card κ) := by
  have h : -((Fintype.card (Pl K) : ℝ)⁻¹ * ∑ v : Pl K,
      Real.log ((∑ i, sqLen ((X.G v)⁻¹)ᵀ v.1.embedding (c i)) / Fintype.card κ)) ≤ slopeArch X.dualK :=
    slopeArch_ge_of_span X.dualK c hc hspan
  rw [slopeArch_dual] at h
  linarith

end KLattice
