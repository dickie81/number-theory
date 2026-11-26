import PeriodTarget
import WeylZForm

/-!
# The branching constant is nonzero, and the Fock projection exists

Two facts about the branching map `PeriodTarget.br` of layer L6.1, which the construction's period data needs: its
constant `c_Br = brConst λ σ` is nonzero when `σ` interlaces `λ`, and its projection `Π_σ` (`IsFockProj`) exists
when `σ` is antitone. Both are stated per block, for every CM type `Φ` and every field `L` of characteristic `0`.

**Interlacing** means `λ_{i+1} ≤ σ_i ≤ λ_i` for every `i < n`, with `λ` of rank `n + 1` and `σ` of rank `n`. It makes
both weights antitone (`antitone_of_interlace_left`, `antitone_of_interlace_right`).

**The integer factor** (`cBrZ_ne_zero`). A factor `(v − i − 1) − (σ_j − j − 1)` of `cBr(λ, σ)` has `v` in
`[λ_{i+1}, λ_i]` and `v ≠ σ_i`, so it vanishes only if `v = σ_j + i − j` with `j ≠ i`. For `j < i`,
`σ_j ≥ λ_{j+1} ≥ λ_i ≥ v`, so `σ_j + i − j > v`. For `j > i`, `σ_j ≤ λ_j ≤ λ_{i+1} ≤ v`, so `σ_j + i − j < v`.

**The Fock factor** (`brConst_ne_zero`). `brConst` is `∏_τ cBr(λ_τ, σ_τ)` times `pair λ ξ ξ`, the Fock norm of
`ξ = xiBr λ σ` divided by that of the highest-weight vector, which is nonzero (`fock_hw_hw_ne_zero`). Every minor
with distinct rows is a nonzero polynomial (`minor_ne_zero`): at the point whose `(I i, i)` entries are `1` and the
others `0`, it is `det 1 = 1`. So `ξ`, a product of powers of such minors, is nonzero over `ℚ` (`xiBr_ne_zero`). It
has rational coefficients (`map_xiBr`), and over `ℚ` the bilinear Fock form is definite (`fock_self_pos_rat`); so
its Fock norm over `L` is the image of a positive rational.

**The projection** (`exists_isFockProj`). For antitone `σ` the `ℤ`-form of `∇(natW σ)` gives two families spanning
`∇_L`, `zb` and `zdual`, with `⟨zdual_i, zb_j⟩ = κ·δ_{ij}` (`WeylZForm`). Then `Π F = Σ_j (⟨F, zb_j⟩/κ)·zdual_j`
lies in `∇_L`, and `⟨F − Π F, zb_i⟩ = 0` for every `i`; the `zb_j` span `∇_L`, so `F − Π F` is Fock-orthogonal to
it.
-/

namespace PeriodTarget

open MvPolynomial WeylFock HermForms

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ}

/-! ## Interlacing and the integer factor -/

section Interlace

variable {l : Fin (n + 1) → ℤ} {s : Fin n → ℤ}

/-- **Interlacing makes `λ` antitone**: `λ_{i+1} ≤ σ_i ≤ λ_i`. -/
theorem antitone_of_interlace_left (h : ∀ i : Fin n, l i.succ ≤ s i ∧ s i ≤ l i.castSucc) : Antitone l :=
  Fin.antitone_iff_succ_le.2 fun i => (h i).1.trans (h i).2

variable (l) in
/-- **Interlacing makes `σ` antitone**: for `i < j`, `σ_j ≤ λ_j ≤ λ_{i+1} ≤ σ_i`. (`λ` is explicit: the conclusion
does not determine it.) -/
theorem antitone_of_interlace_right (h : ∀ i : Fin n, l i.succ ≤ s i ∧ s i ≤ l i.castSucc) : Antitone s := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  have hlt' := Fin.lt_def.1 hlt
  have h1 := antitone_of_interlace_left h (show i.succ ≤ j.castSucc from
    Fin.le_def.2 (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
  exact (h j).2.trans (h1.trans (h i).1)

/-- **`cBr(λ, σ) ≠ 0` under interlacing**: a factor `(v − i − 1) − (σ_j − j − 1)` with `v ∈ [λ_{i+1}, λ_i]`,
`v ≠ σ_i`, vanishes only at `v = σ_j + i − j`, which is `> λ_i` for `j < i` and `< λ_{i+1}` for `j > i`. -/
theorem cBrZ_ne_zero (h : ∀ i : Fin n, l i.succ ≤ s i ∧ s i ≤ l i.castSucc) : cBrZ l s ≠ 0 := by
  have hl := antitone_of_interlace_left h
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun v hv =>
    Finset.prod_ne_zero_iff.2 fun j _ => ?_
  obtain ⟨hvs, hv⟩ := Finset.mem_erase.1 hv
  obtain ⟨hv1, hv2⟩ := Finset.mem_Icc.1 hv
  have hv3 := hv2.trans (min_le_left _ _)
  rcases lt_trichotomy (j : ℕ) i with hji | hji | hji
  · have h1 := hl (show j.succ ≤ i.castSucc from Fin.le_def.2 (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
    have h2 := (h j).1
    omega
  · obtain rfl : j = i := Fin.ext hji
    omega
  · have h1 := hl (show i.succ ≤ j.castSucc from Fin.le_def.2 (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
    have h2 := (h j).2
    omega

end Interlace

/-! ## The Fock factor -/

section Fock

variable {L : Type*} [Field L]

omit [Fintype Φ] [DecidableEq Φ] in
/-- **A minor with distinct rows is a nonzero polynomial**: at the point whose `(I i, i)` entries are `1` and the
others `0` it is `det 1 = 1`. -/
theorem minor_ne_zero (τ : Φ) (k : Fin n) {I : Fin (k + 1) → Fin n} (hI : Function.Injective I) :
    (minor τ k I : Pol Φ n L) ≠ 0 := by
  intro h0
  set x : Φ × Fin n × Fin n → L := fun p => if h : (p.2.2 : ℕ) < k + 1 then (if p.2.1 = I ⟨p.2.2, h⟩ then 1 else 0)
    else 0
  have key : (eval x).mapMatrix ((xMat τ).submatrix I (Fin.castLE k.isLt)) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, xMat, Matrix.of_apply, eval_X,
      Fin.val_castLE, x, b.isLt, ↓reduceDIte, Fin.eta, hI.eq_iff, Matrix.one_apply]
  have := congrArg (eval x) h0
  rw [minor, RingHom.map_det, key, Matrix.det_one, map_zero] at this
  exact one_ne_zero this

omit [Fintype Φ] [DecidableEq Φ] in
/-- **The rows of `Z_i`** (`0, …, i − 1, n`) are distinct. -/
theorem zRows_injective (i : Fin n) :
    Function.Injective fun r : Fin (i.castSucc + 1) =>
      if h : (r : ℕ) < i then (⟨r, by have := i.isLt; omega⟩ : Fin (n + 1)) else Fin.last n := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  have hi := i.isLt
  simp only [Fin.val_castSucc] at ha hb
  simp only at hab
  split_ifs at hab with h1 h2 h2 <;> simp only [Fin.ext_iff, Fin.val_last] at hab <;> exact Fin.ext (by omega)

omit [DecidableEq Φ] in
/-- **`ξ ≠ 0`**: it is a product of powers of minors with distinct rows. -/
theorem xiBr_ne_zero (lam : Φ → Fin (n + 1) → ℤ) (σ : Φ → Fin n → ℤ) : xiBr L lam σ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun ρ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (pow_ne_zero _ (minor_ne_zero ρ _ (Fin.castLE_injective _)))
      (pow_ne_zero _ (minor_ne_zero ρ _ (zRows_injective i)))

omit [DecidableEq Φ] in
/-- **`ξ` has rational coefficients**: it is the image of `ξ` over `ℚ`. -/
theorem map_xiBr [CharZero L] (lam : Φ → Fin (n + 1) → ℤ) (σ : Φ → Fin n → ℤ) :
    MvPolynomial.map (algebraMap ℚ L) (xiBr ℚ lam σ) = xiBr L lam σ := by
  simp only [xiBr, minor, map_prod, map_mul, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun ρ _ => Finset.prod_congr rfl fun i _ => ?_
  congr 3 <;> ext a b <;> simp [xMat]

omit [DecidableEq Φ] in
/-- **The branching constant is nonzero under interlacing**: `λ_{τ,i+1} ≤ σ_{τ,i} ≤ λ_{τ,i}` for every `τ` and
`i < n`. The integer factors are nonzero (`cBrZ_ne_zero`), and `pair λ ξ ξ` is a quotient of two nonzero Fock norms
(`xiBr_ne_zero`, `fock_hw_hw_ne_zero`). -/
theorem brConst_ne_zero [CharZero L] {lam : Φ → Fin (n + 1) → ℤ} {σ : Φ → Fin n → ℤ}
    (hint : ∀ ρ (i : Fin n), lam ρ i.succ ≤ σ ρ i ∧ σ ρ i ≤ lam ρ i.castSucc) : brConst L lam σ ≠ 0 := by
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun ρ _ => Int.cast_ne_zero.2 (cBrZ_ne_zero (hint ρ)))
    (div_ne_zero ?_ (fock_hw_hw_ne_zero _))
  rw [← map_xiBr, fock_map]
  exact (map_ne_zero_iff _ (algebraMap ℚ L).injective).2 (fock_self_pos_rat (xiBr_ne_zero lam σ)).ne'

end Fock

/-! ## The Fock projection -/

section Proj

variable {L : Type*} [Field L] [CharZero L]

variable (L) in
/-- **The Fock projection exists** for antitone `σ`: `Π F = Σ_j (⟨F, zb_j⟩/κ)·zdual_j` lies in `∇_L(natW σ)` and
`⟨F − Π F, zb_i⟩ = 0` for every `i` (`fock_zdualK_zbK`), and the `zb_i` span `∇_L(natW σ)` (`span_zbK`). -/
theorem exists_isFockProj {σ : Φ → Fin n → ℤ} (hσ : ∀ ρ, Antitone (σ ρ)) :
    ∃ P : Pol Φ n L →ₗ[L] Pol Φ n L, IsFockProj σ P := by
  have hκ : algebraMap ℚ L (kappa σ) ≠ 0 := (map_ne_zero_iff _ (algebraMap ℚ L).injective).2 (kappa_pos σ).ne'
  let P : Pol Φ n L →ₗ[L] Pol Φ n L :=
    { toFun := fun F => ∑ j, dc L σ j F • zdualK L σ j
      map_add' := fun F F' => by simp only [dc, fock_add_left, add_div, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a F => by
        simp only [dc, fock_smul_left, mul_div_assoc, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hP : ∀ F i, fockWith (RingHom.id L) (P F) (zbK L σ i) = fockWith (RingHom.id L) F (zbK L σ i) := by
    intro F i
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, fock_sum_left, fock_smul_left, fock_zdualK_zbK, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, dc]
    field_simp
  refine ⟨P, fun F => ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_, fun G hG => ?_⟩⟩
  · rw [← span_zdualK L hσ]
    exact Submodule.subset_span ⟨j, rfl⟩
  rw [← span_zbK L hσ] at hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [sub_eq_add_neg, ← neg_one_smul L (P F), fock_add_left, fock_smul_left, hP]
    ring
  | zero => exact fock_zero_right _
  | add x y _ _ hx hy => rw [fock_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [fock_smul_right, hx, mul_zero]

end Proj

end PeriodTarget
