import WeylZForm

/-!
# The determinant of `ρ_λ` on `∇`

Part IV of the exact slope bound (F) (D1, D2), for a weight `λ` with shape `ν = natW λ`, embeddings
`τ : Φ → (E →+* L)` and `VV = ∇_L(ν)`. Recall `ρ_λ(γ)F = ∏_ρ τ_ρ(det γ)^{−s_ρ}·F((τ_ρ(γ)⁻¹x_ρ)_ρ)` with
`s_ρ = λ_{ρ,n−1}` (`WeylFock.rho`); it is the twist by `τ(γ⁻¹)` (`rho_eq_twist`).

**D1** (`rhoVV`). `ρ_λ(γ)` keeps `∇` (a twist does, `twist_mem_nabla`), so it restricts to an `L`-linear
endomorphism of `VV`; `ρ_λ(γδ) = ρ_λ(γ)ρ_λ(δ)` and `ρ_λ(1) = 1` (`rho_mul`, `rho_one`) make `rhoVV` a monoid hom
`GL_n(E) →* End_L(VV)`.

**D2** (`det_rhoVV`). With `r = dim VV = |ZIdx|` and `cExp ρ = r·s_ρ + wtMult ρ 0` (so `n·cExp ρ = r·Λ_ρ`,
`n_mul_cExp`):
`det ρ_λ(γ) = ∏_ρ τ_ρ(det γ)^{−cExp ρ}`, that is `∏_ρ τ_ρ(det γ)^{−r·Λ_ρ/n}`.
Both sides are multiplicative in `γ`, and invertible diagonal matrices and transvections generate `GL_n(E)`
(`Matrix.diagonal_transvection_induction_of_det_ne_zero`), so two cases remain.
* *Diagonals* (`det_rhoVV_diagonal`). For `γ = diag(D)`, `τ_ρ(γ⁻¹) = diag(τ_ρ(D_i)⁻¹)`, and on the row-homogeneous
  `zdual_j` (of row weight `zwt j`, `zdualK_isWH`) the twist is the scalar
  `∏_ρ τ_ρ(det γ)^{−s_ρ}·∏_{ρ,i} τ_ρ(D_i)^{−(zwt j)_{ρ,i}}` (`twist_diagonal_of_isWH`). So `ρ_λ(γ)` is diagonal in
  the basis `zdual`, and its determinant is `∏_ρ τ_ρ(det γ)^{−r s_ρ}·∏_{ρ,i} τ_ρ(D_i)^{−wtMult ρ i}`; the
  multiplicities do not depend on `i` (`wtMult_eq`), so the second product is `∏_ρ τ_ρ(det γ)^{−wtMult ρ 0}`.
* *Transvections* (`det_rhoVV_transvection`). With `d = diag(2 at i)`, `d·t_{ij}(c)·d⁻¹ = t_{ij}(2c) = t_{ij}(c)²`,
  so `x = det ρ_λ(t_{ij}(c))` has `x = x²` (the determinant is multiplicative and `L` is commutative); `x ≠ 0`, so
  `x = 1 = ∏_ρ τ_ρ(1)^{−cExp ρ}`.

The sign agrees with the spec: `rho` acts through `γ⁻¹` on the variables and through `det γ^{−s}` on the scalars,
and the diagonal case gives the exponent `−cExp ρ`.

**The matrix of `ρ_λ(γ)` in the coordinates of `Δ`** (`rhoMat`, for Part V). `R_γ = dcoord ∘ ρ_λ(γ) ∘ dcoord⁻¹`
is an automorphism of `L^{ZIdx}`, and `det R_γ = det ρ_λ(γ)` (`det_rhoMat`), the form in which
K1 (`KLattice.degK_map`) takes it.
-/

namespace HermForms

open WeylFock MvPolynomial

noncomputable section

variable {E : Type} [Field E] {n : ℕ} {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L]
  (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

/-! ## D1: `ρ_λ` on `∇` -/

/-- **D1.** `ρ_λ(γ)` on `VV = ∇_L(natW λ)` (it keeps `∇`: `rho_eq_twist`, `twist_mem_nabla`), as a monoid hom
from `GL_n(E)` to the `L`-linear endomorphisms of `VV` (`rho_mul`, `rho_one`). -/
def rhoVV : GL (Fin n) E →* Module.End L (nabla L fun ρ => natW (lam ρ)) where
  toFun γ :=
    { toFun := fun F => ⟨rho τ lam γ F, by rw [rho_eq_twist]; exact twist_mem_nabla lam _ F.2⟩
      map_add' := fun F G => Subtype.ext (rho_add τ lam γ F G)
      map_smul' := fun a F => Subtype.ext (rho_smul τ lam γ a F) }
  map_one' := LinearMap.ext fun F => Subtype.ext (rho_one τ lam F)
  map_mul' γ δ := LinearMap.ext fun F => Subtype.ext (rho_mul τ lam γ δ F)

/-- `rhoVV γ F = ρ_λ(γ) F`. -/
theorem rhoVV_apply (γ : GL (Fin n) E) (F : nabla L fun ρ => natW (lam ρ)) :
    (rhoVV τ lam γ F : Pol Φ n L) = rho τ lam γ F := rfl

/-! ## D2: the determinant -/

/-- **D2, transvections.** `det ρ_λ(t) = 1` for a transvection `t = t_{ij}(c)`: with `d = diag(2 at i)`,
`d·t_{ij}(c) = t_{ij}(2c)·d = t_{ij}(c)²·d`, so `x = det ρ_λ(t)` has `x = x²`, and `x ≠ 0`. -/
theorem det_rhoVV_transvection [CharZero E] (t : Matrix.TransvectionStruct (Fin n) E) (γ : GL (Fin n) E)
    (hγ : (γ : Matrix (Fin n) (Fin n) E) = t.toMatrix) : LinearMap.det (rhoVV τ lam γ) = 1 := by
  set f := (LinearMap.det : Module.End L (nabla L fun ρ => natW (lam ρ)) →* L).comp (rhoVV τ lam)
  obtain ⟨i, j, hij, c⟩ := t
  rw [Matrix.TransvectionStruct.toMatrix_mk] at hγ
  let dv : Fin n → E := fun k => if k = i then 2 else 1
  have hdv : (Matrix.diagonal dv).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    by_cases hk : k = i <;> simp [dv, hk]
  have hmat : Matrix.diagonal dv * Matrix.transvection i j c =
      Matrix.transvection i j c * Matrix.transvection i j c * Matrix.diagonal dv := by
    rw [Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, dv]
    rcases eq_or_ne a i with rfl | hai
    · rcases eq_or_ne b a with rfl | hba
      · simp [Ne.symm hij]
      · rcases eq_or_ne j b with rfl | hjb
        · simp [hba, hij]
          ring
        · simp [Ne.symm hba, hba, hjb]
    · rcases eq_or_ne b i with rfl | hbi
      · simp [hai, Ne.symm hai]
      · rcases eq_or_ne a b with rfl | hab
        · simp [hai, Ne.symm hai]
        · simp [hai, Ne.symm hai, hab, hbi]
  set d := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdv
  have hconj : d * γ = γ * γ * d := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hγ]
    exact hmat
  have h1 : f d * f γ = f γ * f γ * f d := by rw [← map_mul, ← map_mul, ← map_mul, hconj]
  have hu : ∀ g, f g * f g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hd : f d ≠ 0 := left_ne_zero_of_mul_eq_one (hu d)
  have hγ0 : f γ ≠ 0 := left_ne_zero_of_mul_eq_one (hu γ)
  have h2 : f γ * f γ = f γ * 1 := by
    rw [mul_one]
    refine mul_right_cancel₀ hd ?_
    rw [← h1, mul_comm]
  exact mul_left_cancel₀ hγ0 h2

/-- **D2, diagonals.** For `γ = diag(D)`, `ρ_λ(γ)` is diagonal in the basis `zdual` (`twist_diagonal_of_isWH`,
`zdualK_isWH`): `zdual_j ↦ ∏_ρ τ_ρ(det γ)^{−s_ρ}·∏_{ρ,i} τ_ρ(D_i)^{−(zwt j)_{ρ,i}}·zdual_j`. The product over `j`
is `∏_ρ τ_ρ(det γ)^{−r s_ρ}·∏_{ρ,i} τ_ρ(D_i)^{−wtMult ρ i}`, and `wtMult ρ i = wtMult ρ 0` (`wtMult_eq`). -/
theorem det_rhoVV_diagonal [CharZero L] (hlam : ∀ ρ, Antitone (lam ρ)) {D : Fin n → E} (hD : ∀ i, D i ≠ 0)
    (γ : GL (Fin n) E) (hγ : (γ : Matrix (Fin n) (Fin n) E) = Matrix.diagonal D) :
    LinearMap.det (rhoVV τ lam γ) = ∏ ρ, τ ρ (γ : Matrix (Fin n) (Fin n) E).det ^ (-cExp lam ρ) := by
  have hinv : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = Matrix.diagonal fun i => (D i)⁻¹ := by
    rw [Matrix.coe_units_inv, hγ]
    exact Matrix.inv_eq_right_inv (by rw [Matrix.diagonal_mul_diagonal]; simp [hD])
  set a : Φ → Fin n → L := fun σ i => τ σ (D i)⁻¹
  set e : ZIdx lam → L := fun j => ∏ σ, ((∏ i, a σ i) ^ detShift (lam σ) * ∏ i, a σ i ^ zwt lam j σ i)
  set b := zdualBasis L hlam
  have hb : ∀ j, rhoVV τ lam γ (b j) = e j • b j := fun j => by
    apply Subtype.ext
    rw [rhoVV_apply, rho_eq_twist, hinv, Submodule.coe_smul, zdualBasis_apply]
    have : (fun σ => (τ σ).mapMatrix (Matrix.diagonal fun i => (D i)⁻¹)) = fun σ => Matrix.diagonal (a σ) := by
      funext σ
      rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
    rw [this]
    exact twist_diagonal_of_isWH lam (zdualK_isWH L lam j) a
  have hmat : LinearMap.toMatrix b b (rhoVV τ lam γ) = Matrix.diagonal e := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Matrix.diagonal_apply]
    rcases eq_or_ne j i with rfl | hji
    · simp
    · simp [hji, Ne.symm hji]
  rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal, Finset.prod_comm]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have hy : ∏ i, a σ i = (τ σ (γ : Matrix (Fin n) (Fin n) E).det)⁻¹ := by
    rw [hγ, Matrix.det_diagonal, map_prod, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => map_inv₀ _ _
  have ht : τ σ (γ : Matrix (Fin n) (Fin n) E).det ≠ 0 :=
    (map_ne_zero _).2 ((Matrix.isUnits_det_units γ).ne_zero)
  have hw : ∏ i, a σ i ^ wtMult lam σ i =
      (∏ i, a σ i) ^ (if h : 0 < n then (wtMult lam σ ⟨0, h⟩ : ℤ) else 0) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · simp only [hn, ↓reduceDIte]
      rw [zpow_natCast, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [wtMult_eq lam σ i ⟨0, hn⟩]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_comm]
  simp only [Finset.prod_pow_eq_pow_sum]
  rw [show (fun i => a σ i ^ ∑ j, zwt lam j σ i) = fun i => a σ i ^ wtMult lam σ i from rfl, hw, hy,
    ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (inv_ne_zero ht), inv_zpow', cExp]
  ring_nf

/-- **D2.** `det ρ_λ(γ) = ∏_ρ τ_ρ(det γ)^{−cExp ρ}` on `VV`, that is `∏_ρ τ_ρ(det γ)^{−r·Λ_ρ/n}` (`n_mul_cExp`).
Both sides are multiplicative in `γ`, so it suffices to check invertible diagonal matrices
(`det_rhoVV_diagonal`) and transvections (`det_rhoVV_transvection`, where both sides are `1`), which generate
`GL_n(E)` (`Matrix.diagonal_transvection_induction_of_det_ne_zero`). -/
theorem det_rhoVV [CharZero E] [CharZero L] (hlam : ∀ ρ, Antitone (lam ρ)) (γ : GL (Fin n) E) :
    LinearMap.det (rhoVV τ lam γ) = ∏ ρ, τ ρ (γ : Matrix (Fin n) (Fin n) E).det ^ (-cExp lam ρ) := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E) = M →
      LinearMap.det (rhoVV τ lam γ) = ∏ ρ, τ ρ (γ : Matrix (Fin n) (Fin n) E).det ^ (-cExp lam ρ))
    (γ : Matrix (Fin n) (Fin n) E) (Matrix.isUnits_det_units γ).ne_zero ?_ ?_ ?_ γ rfl
  · intro D hD δ hδ
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
    exact det_rhoVV_diagonal τ lam hlam (fun i => hD i (Finset.mem_univ i)) δ hδ
  · intro t δ hδ
    rw [det_rhoVV_transvection τ lam t δ hδ, hδ, t.det]
    simp
  · intro A B hA hB IA IB δ hδ
    have hAB : δ = Matrix.GeneralLinearGroup.mkOfDetNeZero A hA * Matrix.GeneralLinearGroup.mkOfDetNeZero B hB :=
      Units.ext (by rw [hδ]; rfl)
    rw [hAB, map_mul (rhoVV τ lam), map_mul LinearMap.det, IA _ rfl, IB _ rfl, Units.val_mul, Matrix.det_mul]
    simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]

/-! ## The matrix of `ρ_λ` in the coordinates of `Δ` -/

variable {lam}

/-- **The matrix `R_γ` of `ρ_λ(γ)`** in the coordinates `dcoord` (the dual basis `zdual`):
`R_γ = dcoord ∘ ρ_λ(γ) ∘ dcoord⁻¹`, an automorphism of `L^{ZIdx}` with inverse `R_{γ⁻¹}`. Meant
for V4/V5, with K1 (`KLattice.degK_map`). -/
def rhoMat [CharZero L] (hlam : ∀ ρ, Antitone (lam ρ)) (γ : GL (Fin n) E) : (ZIdx lam → L) ≃ₗ[L] (ZIdx lam → L) :=
  (dcoord L hlam).symm ≪≫ₗ
    LinearEquiv.ofLinearMap (rhoVV τ lam γ) (rhoVV τ lam γ⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id]) ≪≫ₗ
    dcoord L hlam

/-- **D2 in coordinates.** `det R_γ = ∏_ρ τ_ρ(det γ)^{−cExp ρ}`: conjugating by `dcoord` keeps the determinant. -/
theorem det_rhoMat [CharZero E] [CharZero L] (hlam : ∀ ρ, Antitone (lam ρ)) (γ : GL (Fin n) E) :
    LinearMap.det (rhoMat τ hlam γ : (ZIdx lam → L) →ₗ[L] (ZIdx lam → L)) =
      ∏ ρ, τ ρ (γ : Matrix (Fin n) (Fin n) E).det ^ (-cExp lam ρ) := by
  rw [← det_rhoVV τ lam hlam γ, ← LinearMap.det_conj (rhoVV τ lam γ) (dcoord L hlam)]
  rfl

end

end HermForms
