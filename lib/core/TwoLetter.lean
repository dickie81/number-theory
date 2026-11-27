import HarmDecomp
import OffTop
import WeylSandwich

/-!
# The two-letter identification (Annex I's I4)

The identification of L5's tensor of polynomial pairs `H(A, B)` and of the flat weights `fl(α, β)` with letter
polynomials, two letters per position (`n′·2` letters): at position `s` the *vector letter* `2s` (`vL`) and the
*covector letter* `2s + 1` (`cL`), the flags of `LetterFock.theta0` on `Fin (n′·2)`.

**The two models.**
* *`H(A, B)`* (`psi = ρ∘θ°`): `θ°` on `n′·2` letters, then the renaming of the blocks `((), t)` to the blocks
  `(v, s)` of `FirstAssembly.lamH` (`eps`: `(true, s)` is the vector letter at even `s`, the covector letter at
  odd `s`), so that the weights agree (`blockWt_lamH`).
* *`fl(α, β)`* (`beta = δ∘θ°`): `θ°`, then merging the two blocks of a position (`delta`): the vector letter goes
  to the entries `x_{s,c,0}`, the covector letter to the cofactors `adj(x_s)_{k−1,c}` of the same block, so that the
  pairing `h_s` goes to `(adj(x_s)·x_s)_{k−1,0} = 0` (`beta_hP`).

**Main results.**
* *`H(A, B)`*: `ψ` is injective on the letter degree `dL` (`psi_injOn`), onto `∇` (`exists_psi`, `psi_mem_nabla`),
  `ψP ∈ ∇_A` iff `P` has coefficients in `A` (`psi_mem_nablaInt_iff`), and twisting by `C_s` at both blocks of every
  position is `tcst·ψ(P∘Alet)` (`twist_psi`), by renaming the blocks of `θ°` (`renB`, `renB_mem_nablaInt_iff`,
  `twist_renB`).
* *`fl(α, β)`*: the shape `(P + Q, Q, …, Q, 0)` is the sum of the shapes of the two letters (`shape_flatWt`); `β` of
  an `A`-integral letter polynomial is in `∇_A` and every element of `∇_A` is such (`beta_mem_nablaInt`,
  `exists_beta_of_mem_nablaInt`, by merging and splitting block factors, `delta_bidet`, `delta_bidet'`); `β` is onto
  `∇` (`exists_beta`); twists are `tcst·β(P∘Alet)` (`twist_beta`).
* *The kernel* (I4): `β` is injective on letter polynomials harmonic at every position (`eq_zero_of_beta`).

**The route to the kernel.** Evaluate the flat model at the test matrices `W_s = [x | y_{k−1}e_j − y_je_{k−1} | 0]`
(`Wm`, `ev`): `ev∘β` fixes the vector letters and sends `y_c` to the last cofactor row `Y_c` of `W_s`, which is
`Λ·y_c − [c = 0]·y_{k−1}^{k−3}·h`, `Λ = x_0·y_{k−1}^{k−3}` (`Yc_eq`: `Y` is orthogonal to the columns of `W`,
`Y_{k−1}` is a triangular determinant). So modulo the pairing the substitution at `s` is the scaling `y ↦ Λy`
(`chi_eq`), which multiplies by `Λ^{deg y}`; `x_0`, `y_{k−1}` are prime and do not divide `h`, so they cancel
(`mem_span_of_pow_mul`), and a harmonic multiple of `h` vanishes (`eq_zero_of_mem_span`, from
`HarmDecomp.eq_zero_of_lapP_hP` on homogeneous components). The positions are done one at a time (`phiS`,
`phiS_insert`), the substitution at `s` commuting with the Laplacians of the other positions (`lapP_phiS`).
-/

namespace TwoLetter

open MvPolynomial WeylFock InertModel LocalLattice LetterFock HarmDecomp OffTop Finset

open scoped Matrix

noncomputable section

/-! ## Block factors: merging and splitting shapes -/

section Bfac

variable {Φ : Type} {n : ℕ} {L : Type} [Field L]

/-- **The multiplicities add** for a sum of antitone shapes. -/
theorem mult_add {m₁ m₂ : Fin n → ℕ} (h₁ : Antitone m₁) (h₂ : Antitone m₂) (s : Fin n) :
    mult (m₁ + m₂) s = mult m₁ s + mult m₂ s := by
  simp only [mult, Pi.add_apply]
  split_ifs with h
  · have e₁ := h₁ (show s ≤ ⟨s + 1, h⟩ from Fin.le_def.2 (Nat.le_succ _))
    have e₂ := h₂ (show s ≤ ⟨s + 1, h⟩ from Fin.le_def.2 (Nat.le_succ _))
    omega
  · omega

/-- **Merging block factors**: a product of block factors of shapes `m₁`, `m₂` is a block factor of a shape `m` whose
multiplicities are the sums. -/
theorem bfac_merge (τ : Φ) {m₁ m₂ m : Fin n → ℕ} (h : ∀ s, mult m s = mult m₁ s + mult m₂ s)
    (r₁ : (s : Fin n) → Fin (mult m₁ s) → Fin (s + 1) → Fin n)
    (r₂ : (s : Fin n) → Fin (mult m₂ s) → Fin (s + 1) → Fin n) :
    ∃ r : (s : Fin n) → Fin (mult m s) → Fin (s + 1) → Fin n,
      (bfac τ m r : Pol Φ n L) = bfac τ m₁ r₁ * bfac τ m₂ r₂ := by
  refine ⟨fun s c => Fin.append (r₁ s) (r₂ s) (Fin.cast (h s) c), ?_⟩
  simp only [bfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Fin.prod_congr' (fun c => minor τ s (Fin.append (r₁ s) (r₂ s) c)) (h s), Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Splitting a block factor**: a block factor of a shape `m` whose multiplicities are those of `m₁` plus those of
`m₂` is a product of block factors of shapes `m₁`, `m₂`. -/
theorem bfac_split (τ : Φ) {m₁ m₂ m : Fin n → ℕ} (h : ∀ s, mult m s = mult m₁ s + mult m₂ s)
    (r : (s : Fin n) → Fin (mult m s) → Fin (s + 1) → Fin n) :
    ∃ (r₁ : (s : Fin n) → Fin (mult m₁ s) → Fin (s + 1) → Fin n)
      (r₂ : (s : Fin n) → Fin (mult m₂ s) → Fin (s + 1) → Fin n),
      (bfac τ m r : Pol Φ n L) = bfac τ m₁ r₁ * bfac τ m₂ r₂ := by
  refine ⟨fun s c => r s (Fin.cast (h s).symm (Fin.castAdd _ c)),
    fun s c => r s (Fin.cast (h s).symm (Fin.natAdd _ c)), ?_⟩
  simp only [bfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← Fin.prod_univ_add (fun c => minor τ s (r s (Fin.cast (h s).symm c))),
    Fin.prod_congr' (fun c => minor τ s (r s c)) (h s).symm]

end Bfac

/-! ## Letters, positions and the flat model of a pair -/

section Letters

variable {n' : ℕ}

/-- **The vector letter** `2s` of position `s`. -/
def vL (s : Fin n') : Fin (n' * 2) := finProdFinEquiv (s, 0)

/-- **The covector letter** `2s + 1` of position `s`. -/
def cL (s : Fin n') : Fin (n' * 2) := finProdFinEquiv (s, 1)

/-- **The position of a letter.** -/
def pos (t : Fin (n' * 2)) : Fin n' := (finProdFinEquiv.symm t).1

/-- **The vector letter is `2s`.** -/
theorem vL_val (s : Fin n') : (vL s).val = 2 * s.val := by simp [vL, finProdFinEquiv_apply_val]

/-- **The covector letter is `2s + 1`.** -/
theorem cL_val (s : Fin n') : (cL s).val = 2 * s.val + 1 := by
  simp [cL, finProdFinEquiv_apply_val]; ring

/-- **Vector letters are even.** -/
theorem even_vL (s : Fin n') : Even (vL s).val := by rw [vL_val]; exact even_two_mul _

/-- **Covector letters are odd.** -/
theorem not_even_cL (s : Fin n') : ¬ Even (cL s).val := by rw [cL_val]; exact Nat.not_even_two_mul_add_one _

/-- **The position of a vector letter.** -/
@[simp] theorem pos_vL (s : Fin n') : pos (vL s) = s := by simp [pos, vL]

/-- **The position of a covector letter.** -/
@[simp] theorem pos_cL (s : Fin n') : pos (cL s) = s := by simp [pos, cL]

/-- **Every letter is the vector or the covector letter of its position.** -/
theorem letter_cases (t : Fin (n' * 2)) : t = vL (pos t) ∨ t = cL (pos t) := by
  obtain ⟨⟨s, i⟩, rfl⟩ := finProdFinEquiv.surjective t
  fin_cases i
  · left; simp [vL, pos]
  · right; simp [cL, pos]

/-- **The vector and covector letters form disjoint pairs.** -/
theorem pairs : Pairs (vL (n' := n')) cL where
  ne s t h := by have := congrArg Fin.val h; rw [vL_val, cL_val] at this; omega
  inj_a s t h := by have := congrArg Fin.val h; rw [vL_val, vL_val] at this; exact Fin.ext (by omega)
  inj_b s t h := by have := congrArg Fin.val h; rw [cL_val, cL_val] at this; exact Fin.ext (by omega)

/-- **A letter is a vector letter iff it is even.** -/
theorem eq_vL_iff (t : Fin (n' * 2)) : t = vL (pos t) ↔ Even t.val := by
  rcases letter_cases t with h | h
  · exact ⟨fun _ => by rw [h]; exact even_vL _, fun _ => h⟩
  · refine ⟨fun h' => absurd (h'.symm.trans h) (pairs.ne (pos t) (pos t)), fun he => ?_⟩
    rw [h] at he
    exact absurd he (not_even_cL _)

variable {k : ℕ} [NeZero k] {Kf : Type} [Field Kf]

/-- **Merging the two blocks of a position**: `x_{((), t)} ↦ x_{((), pos t)}`. -/
def delta : Pol (Unit × Fin (n' * 2)) k Kf →ₐ[Kf] Pol (Unit × Fin n') k Kf :=
  rename fun x => (((), pos x.1.2), x.2)

variable (Kf) in
/-- **The flat model of a pair** `β = δ∘θ°`: the vector letter of `s` goes to the entries `x_{s,c,0}`, the covector
letter to the cofactors `adj(x_s)_{k−1,c}`. -/
def beta : LPol (Fin (n' * 2)) k Kf →ₐ[Kf] Pol (Unit × Fin n') k Kf := delta.comp (theta0 Kf)

omit [NeZero k] in
/-- **Merging blocks on a block matrix.** -/
theorem delta_xMat (t : Fin (n' * 2)) :
    (delta (k := k) (Kf := Kf)).mapMatrix (xMat ((), t)) = xMat ((), pos t) := by
  ext i j
  simp [delta, xMat]

/-- **`β` on a vector letter.** -/
theorem beta_vL (s : Fin n') (c : Fin k) : beta Kf (X (vL s, c)) = X (((), s), c, 0) := by
  simp [beta, theta0_X, even_vL, delta]

/-- **`β` on a covector letter.** -/
theorem beta_cL (s : Fin n') (c : Fin k) : beta Kf (X (cL s, c)) = (xMat ((), s)).adjugate (lastC k) c := by
  have e := congrFun (congrFun (AlgHom.map_adjugate (delta (k := k) (Kf := Kf)) (xMat ((), cL s))) (lastC k)) c
  rw [delta_xMat, pos_cL] at e
  simp only [beta, AlgHom.comp_apply, theta0_X, not_even_cL s, ite_false]
  rw [← e]
  rfl

/-- **`β` kills the pairings** (`k ≥ 2`): `Σ_c x_{s,c,0}·adj(x_s)_{k−1,c} = (adj(x_s)·x_s)_{k−1,0} = 0`. -/
theorem beta_hP (hk : 2 ≤ k) (s : Fin n') : beta (k := k) Kf (hP (vL s) (cL s)) = 0 := by
  have h0 : lastC k ≠ 0 := fun h => by
    have := congrArg Fin.val h; simp [lastC] at this; omega
  have e : ∑ c, (xMat ((), s)).adjugate (lastC k) c * (xMat ((), s)) c (0 : Fin k) =
      (0 : Pol (Unit × Fin n') k Kf) := by
    have := congrFun (congrFun (Matrix.adjugate_mul (xMat (Φ := Unit × Fin n') (L := Kf) ((), s))) (lastC k))
      (0 : Fin k)
    rwa [Matrix.smul_apply, Matrix.one_apply_ne h0, smul_zero, Matrix.mul_apply] at this
  simp only [hP, map_sum, map_mul, beta_vL, beta_cL]
  rw [← e]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm]; rfl

end Letters

/-! ## Renaming blocks -/

section Rename

variable {β₁ β₂ : Type} [Fintype β₁] [DecidableEq β₁] [Fintype β₂] [DecidableEq β₂] {k : ℕ} {Kf : Type}
  [Field Kf]

variable (k Kf) in
/-- **Renaming the blocks** along an equivalence `e`: `x_{b,i,j} ↦ x_{e b,i,j}`. -/
def renB (e : β₁ ≃ β₂) : Pol β₁ k Kf ≃ₐ[Kf] Pol β₂ k Kf :=
  renameEquiv Kf (Equiv.prodCongr e (Equiv.refl (Fin k × Fin k)))

omit [Fintype β₁] [DecidableEq β₁] [Fintype β₂] [DecidableEq β₂] in
/-- **Renaming blocks on a variable.** -/
theorem renB_X (e : β₁ ≃ β₂) (b : β₁) (i j : Fin k) : renB k Kf e (X (b, i, j)) = X (e b, i, j) := by
  simp [renB]

omit [Fintype β₁] [DecidableEq β₁] [Fintype β₂] [DecidableEq β₂] in
/-- **Renaming blocks on a constant.** -/
theorem renB_C (e : β₁ ≃ β₂) (a : Kf) : renB k Kf e (C a) = C a := by
  simp [renB]

omit [Fintype β₁] [DecidableEq β₁] [Fintype β₂] [DecidableEq β₂] in
/-- **Renaming blocks on a minor.** -/
theorem renB_minor (e : β₁ ≃ β₂) (τ : β₁) (s : Fin k) (I : Fin (s + 1) → Fin k) :
    renB k Kf e (minor τ s I) = minor (e τ) s I := by
  have h : (renB k Kf e).toAlgHom.mapMatrix ((xMat τ).submatrix I (Fin.castLE s.isLt)) =
      (xMat (e τ)).submatrix I (Fin.castLE s.isLt) := by
    ext i j; simp [xMat, renB_X]
  have := AlgHom.map_det (renB k Kf e).toAlgHom ((xMat τ).submatrix I (Fin.castLE s.isLt))
  rw [h] at this
  rw [minor, minor]
  exact this

omit [Fintype β₁] [DecidableEq β₁] [Fintype β₂] [DecidableEq β₂] in
/-- **Renaming blocks on a block factor.** -/
theorem renB_bfac (e : β₁ ≃ β₂) (τ : β₁) (m : Fin k → ℕ) (r : (s : Fin k) → Fin (mult m s) → Fin (s + 1) → Fin k) :
    renB k Kf e (bfac τ m r) = bfac (e τ) m r := by
  simp only [bfac, map_prod, renB_minor]

omit [DecidableEq β₁] [DecidableEq β₂] in
/-- **Renaming blocks on a bideterminant**: the bideterminants of shape `ν` are the renamed ones of `ν ∘ e`. -/
theorem renB_bidet (e : β₁ ≃ β₂) (ν : β₂ → Fin k → ℕ) (rows : BRows β₂ k ν) :
    renB k Kf e (bidet Kf (fun b => ν (e b)) fun b => rows (e b)) = bidet Kf ν rows := by
  show renB k Kf e (∏ τ, bfac τ (ν (e τ)) (rows (e τ))) = ∏ τ, bfac τ (ν τ) (rows τ)
  rw [map_prod]
  simp only [renB_bfac]
  exact e.prod_comp fun τ => bfac τ (ν τ) (rows τ)

omit [DecidableEq β₁] [DecidableEq β₂] in
/-- **Renamed bideterminants are bideterminants.** -/
theorem exists_renB_bidet (e : β₁ ≃ β₂) (ν : β₂ → Fin k → ℕ) (rows₁ : BRows β₁ k fun b => ν (e b)) :
    ∃ rows : BRows β₂ k ν, bidet Kf ν rows = renB k Kf e (bidet Kf (fun b => ν (e b)) rows₁) := by
  have key : ∀ τ : β₂, ∃ r : (s : Fin k) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin k,
      (bfac τ (ν τ) r : Pol β₂ k Kf) = bfac τ (ν (e (e.symm τ))) (rows₁ (e.symm τ)) :=
    fun τ => exists_bfac_eq (congrArg ν (e.apply_symm_apply τ)) _
  choose r hr using key
  refine ⟨r, ?_⟩
  show ∏ τ, bfac τ (ν τ) (r τ) = renB k Kf e (∏ τ, bfac τ (ν (e τ)) (rows₁ τ))
  rw [map_prod]
  simp only [renB_bfac, hr]
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have : ∀ τ₁ : β₁, τ₁ = τ → (bfac (e τ) (ν (e τ₁)) (rows₁ τ₁) : Pol β₂ k Kf) = bfac (e τ) (ν (e τ)) (rows₁ τ) := by
    rintro _ rfl; rfl
  exact this _ (e.symm_apply_apply τ)

omit [DecidableEq β₁] [DecidableEq β₂] in
/-- **Renaming blocks keeps the integral structures**: `ρF ∈ ∇_A(ν)` iff `F ∈ ∇_A(ν ∘ e)`. -/
theorem renB_mem_nablaInt_iff (e : β₁ ≃ β₂) (A : Subring Kf) (ν : β₂ → Fin k → ℕ) (F : Pol β₁ k Kf) :
    renB k Kf e F ∈ nablaInt A ν ↔ F ∈ nablaInt A fun b => ν (e b) := by
  constructor
  · intro h
    have key : ∀ G ∈ nablaInt A ν, (renB k Kf e).symm G ∈ nablaInt A fun b => ν (e b) := by
      intro G hG
      induction hG using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨rows, rfl⟩ := hx
        rw [← renB_bidet e ν rows, AlgEquiv.symm_apply_apply]
        exact Submodule.subset_span ⟨_, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [show a • x = (a : Kf) • x from rfl, map_smul]
        exact Submodule.smul_mem _ a hx
    simpa using key _ h
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨rows₁, rfl⟩ := hx
      obtain ⟨rows, hrows⟩ := exists_renB_bidet (Kf := Kf) e ν rows₁
      rw [← hrows]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : Kf) • x from rfl, map_smul]
      exact Submodule.smul_mem _ a hx

omit [DecidableEq β₁] [DecidableEq β₂] in
/-- **Renaming blocks commutes with twists.** -/
theorem twist_renB (e : β₁ ≃ β₂) (lam : β₂ → Fin k → ℤ) (Cm : β₂ → Matrix (Fin k) (Fin k) Kf) (F : Pol β₁ k Kf) :
    twist lam Cm (renB k Kf e F) = renB k Kf e (twist (fun b => lam (e b)) (fun b => Cm (e b)) F) := by
  have hl : (lsub Cm).comp (renB k Kf e).toAlgHom = (renB k Kf e).toAlgHom.comp (lsub fun b => Cm (e b)) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨b, i, j⟩ := v
    simp [renB_X, lsub_X, renB_C]
  have hl' := congrArg (fun φ => φ F) hl
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hl'
  rw [twist, twist, map_mul, hl', renB_C]
  congr 2
  exact (e.prod_comp fun b => (Cm b).det ^ detShift (lam b)).symm

end Rename

/-! ## The tensor of polynomial pairs as letter polynomials -/

section HModel

variable {n' : ℕ}

/-- **The block of a letter in `H(A, B)`**: `(true, s)` is the vector letter at even `s` and the covector letter at odd
`s` (`lamAt` dualises the odd positions). -/
def eps : Bool × Fin n' ≃ Fin (n' * 2) where
  toFun b := if b.1 = decide (Even b.2.val) then vL b.2 else cL b.2
  invFun t := (if Even t.val then decide (Even (pos t).val) else !decide (Even (pos t).val), pos t)
  left_inv := by
    rintro ⟨v, s⟩
    by_cases h : v = decide (Even s.val)
    · simp only [h, ite_true, even_vL, pos_vL]
    · simp only [h, ite_false, not_even_cL, pos_cL, Prod.mk.injEq, and_true]
      cases v <;> simp_all
  right_inv t := by
    rcases letter_cases t with h | h
    · rw [h]; simp [even_vL]
    · rw [h]; simp [not_even_cL]

/-- **`eps` keeps the position.** -/
@[simp] theorem pos_eps (b : Bool × Fin n') : pos (eps b) = b.2 := by
  simp only [eps, Equiv.coe_fn_mk]; split_ifs <;> simp

/-- **The position of `eps⁻¹`.** -/
@[simp] theorem eps_symm_snd (t : Fin (n' * 2)) : (eps.symm t).2 = pos t := rfl

/-- **The blocks of the letter model** `((), t)` as blocks `(v, s)` of `H(A, B)`. -/
def blkH : Unit × Fin (n' * 2) ≃ Bool × Fin n' := (Equiv.uniqueProd (Fin (n' * 2)) Unit).trans eps.symm

/-- **`blkH`**, unfolded. -/
@[simp] theorem blkH_apply (t : Unit × Fin (n' * 2)) : blkH t = eps.symm t.2 := rfl

/-- **Products over the letters** are products over the positions of the two letters. -/
theorem prod_letters {M : Type*} [CommMonoid M] (f : Fin (n' * 2) → M) :
    ∏ t, f t = ∏ s, (f (vL s) * f (cL s)) := by
  rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun s _ => Fin.prod_univ_two _

/-- **The degree of the vector letter**: `A_s` at even, `B_s` at odd `s`. -/
def degV (A B : Fin n' → ℕ) (s : Fin n') : ℕ := if Even s.val then A s else B s

/-- **The degree of the covector letter**: `B_s` at even, `A_s` at odd `s`. -/
def degC (A B : Fin n' → ℕ) (s : Fin n') : ℕ := if Even s.val then B s else A s

/-- **The letter degrees** of `H(A, B)` and of `fl(A, B)`. -/
def dL (A B : Fin n' → ℕ) (t : Fin (n' * 2)) : ℕ := if Even t.val then degV A B (pos t) else degC A B (pos t)

/-- **The letter degree of a vector letter.** -/
@[simp] theorem dL_vL (A B : Fin n' → ℕ) (s : Fin n') : dL A B (vL s) = degV A B s := by simp [dL, even_vL]

/-- **The letter degree of a covector letter.** -/
@[simp] theorem dL_cL (A B : Fin n' → ℕ) (s : Fin n') : dL A B (cL s) = degC A B s := by simp [dL, not_even_cL]

/-- **The twist constant** `∏_s det(C_s)^{−d(cL s)}`. -/
def tcst {k : ℕ} {Kf : Type} [Field Kf] (C₀ : Fin n' → Matrix (Fin k) (Fin k) Kf) (d : Fin (n' * 2) → ℕ) : Kf :=
  ∏ s, (C₀ s).det ^ (-(d (cL s) : ℤ))

/-- **The letter matrices of block matrices `C_s`**: `C_s` on the vector letter, `adj(C_s)ᵀ` on the covector
letter (`LetterFock.letMat`). -/
def Alet {k : ℕ} {Kf : Type} [Field Kf] (C₀ : Fin n' → Matrix (Fin k) (Fin k) Kf) (t : Fin (n' * 2)) :
    Matrix (Fin k) (Fin k) Kf :=
  if Even t.val then C₀ (pos t) else (C₀ (pos t)).adjugateᵀ

/-- **The letter matrices satisfy the pair conditions** with `γ_s = det(C_s)`. -/
theorem letCond_Alet {k : ℕ} {Kf : Type} [Field Kf] (C₀ : Fin n' → Matrix (Fin k) (Fin k) Kf) (s : Fin n') :
    LetCond (Alet C₀) (vL s) (cL s) (C₀ s).det := by
  simp only [LetCond, Alet, even_vL, not_even_cL, ite_true, ite_false, pos_vL, pos_cL, Matrix.transpose_transpose]
  refine ⟨?_, Matrix.mul_adjugate _⟩
  rw [← Matrix.transpose_mul, Matrix.adjugate_mul, Matrix.transpose_smul, Matrix.transpose_one]

variable {k : ℕ} [NeZero k] {Kf : Type} [Field Kf] {TT : Finset (Fin n')}

/-- **The weights of `H(A, B)` are those of the letter model**: the block `(v, s)` has the weight of the letter
`eps (v, s)` of degree `dL`, for `A, B ≥ 0` and `k ≥ 2`. -/
theorem blockWt_lamH (hk : 2 ≤ k) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    (b : Bool × Fin n') :
    blockWt (FirstAssembly.lamH (k := k) TT A B) b =
      wt1 (LetterFock.flatWt (dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat))
        ((), eps b) := by
  obtain ⟨v, s⟩ := b
  have hA' := FirstMeans.ext_nonneg hA s
  have hB' := FirstMeans.ext_nonneg hB s
  have hrev : ∀ i : Fin k, i.rev = 0 ↔ i.val + 1 = k := fun i => by
    simp only [Fin.ext_iff, Fin.val_rev, Fin.val_zero]; omega
  have hrev' : ∀ i : Fin k, (i.rev.val + 1 = k) ↔ i = 0 := fun i => by
    simp only [Fin.ext_iff, Fin.val_rev, Fin.val_zero]; omega
  have hev : ∀ v : Bool, eps (v, s) = if v = decide (Even s.val) then vL s else cL s := fun v => rfl
  have ht : ∀ i : Fin k, FirstAssembly.lamH (k := k) TT A B true s i = if i.val = 0 then FirstMeans.ext TT A s else 0 :=
    fun i => rfl
  have hf : ∀ i : Fin k, FirstAssembly.lamH (k := k) TT A B false s i =
      if i.val + 1 = k then -FirstMeans.ext TT B s else 0 := fun i => rfl
  funext i
  simp only [blockWt, lamAt, wt1, LetterFock.flatWt, hev]
  by_cases hs : Even s.val
  · cases v
    · simp only [hs, decide_true, Bool.false_eq_true, not_even_cL, dL_cL, degC, Pi.single_apply, ↓reduceIte, hf,
        hrev i]
      split_ifs <;> omega
    · simp only [hs, decide_true, even_vL, dL_vL, degV, Pi.single_apply, ↓reduceIte, ht, Fin.ext_iff,
        Fin.val_zero]
      split_ifs <;> omega
  · cases v
    · simp only [hs, decide_false, even_vL, dL_vL, degV, Pi.single_apply, ↓reduceIte, hf, hrev' i]
      split_ifs <;> omega
    · simp only [hs, decide_false, Bool.true_eq_false, not_even_cL, dL_cL, degC, Pi.single_apply, ↓reduceIte, ht,
        hrev i]
      split_ifs <;> (simp_all; try omega)

end HModel

/-! ## The identifications and their integral structures -/

section Ident

variable {n' k : ℕ} [NeZero k] {Kf : Type} [Field Kf] {TT : Finset (Fin n')}

variable (k Kf) in
/-- **The letter model of `H(A, B)`** `ψ = ρ∘θ°`. -/
def psi : LPol (Fin (n' * 2)) k Kf →ₐ[Kf] Pol (Bool × Fin n') k Kf := (renB k Kf blkH).toAlgHom.comp (theta0 Kf)

/-- **`ψ`**, unfolded. -/
theorem psi_apply (P : LPol (Fin (n' * 2)) k Kf) : psi k Kf P = renB k Kf blkH (theta0 Kf P) := rfl

/-- **The shapes of `H(A, B)`** are those of the letter model. -/
theorem shape_lamH (hk : 2 ≤ k) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s) :
    (fun b => natW (blockWt (FirstAssembly.lamH (k := k) TT A B) (blkH b))) =
      nu1 (LetterFock.flatWt (dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat)) := by
  funext b
  rw [blkH_apply, blockWt_lamH hk hA hB, Equiv.apply_symm_apply]

variable [CharZero Kf]

/-- **The integral structure of `H(A, B)`** (N2-b for two letters per position): for `P` of letter degree `dL`,
`ψP ∈ ∇_A(H(A, B))` iff the coefficients of `P` lie in `A`. -/
theorem psi_mem_nablaInt_iff (hk : 2 ≤ k) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    {Ar : Subring Kf} {P : LPol (Fin (n' * 2)) k Kf}
    (hP : P ∈ LHom Kf (dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat)) :
    psi k Kf P ∈ nablaInt Ar (fun b => natW (blockWt (FirstAssembly.lamH (k := k) TT A B) b)) ↔
      ∀ μ, P.coeff μ ∈ Ar := by
  rw [psi_apply, renB_mem_nablaInt_iff, shape_lamH hk hA hB]
  exact theta0_mem_nablaInt_iff hk hP

/-- **`ψ` is injective** on the letter degree `dL`. -/
theorem psi_injOn (hk : 2 ≤ k) (d : Fin (n' * 2) → ℕ) :
    Set.InjOn (psi k Kf) (LHom Kf (k := k) d : Set (LPol (Fin (n' * 2)) k Kf)) := fun _ hP _ hQ h =>
  theta0_injOn hk d hP hQ ((renB k Kf blkH).injective h)

/-- **The shapes of `H(A, B)` are antitone.** -/
theorem antitone_shape_lamH (hk : 2 ≤ k) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    (b : Bool × Fin n') : Antitone (natW (blockWt (FirstAssembly.lamH (k := k) TT A B) b)) := by
  rw [blockWt_lamH hk hA hB]
  exact antitone_nu1_flatWt hk _ ((), eps b)

/-- **`ψ` lands in `∇(H(A, B))`.** -/
theorem psi_mem_nabla (hk : 2 ≤ k) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    {P : LPol (Fin (n' * 2)) k Kf}
    (hP : P ∈ LHom Kf (dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat)) :
    psi k Kf P ∈ nabla Kf (fun b => natW (blockWt (FirstAssembly.lamH (k := k) TT A B) b)) :=
  WeylSandwich.nablaInt_subset_nabla ⊤ (antitone_shape_lamH hk hA hB)
    ((psi_mem_nablaInt_iff hk hA hB hP).2 fun _ => Subring.mem_top _)

/-- **`ψ` is onto `∇(H(A, B))`**: the bideterminants span, and each is a renamed bideterminant of the letter model. -/
theorem exists_psi (hk : 2 ≤ k) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    {F : Pol (Bool × Fin n') k Kf}
    (hF : F ∈ nabla Kf (fun b => natW (blockWt (FirstAssembly.lamH (k := k) TT A B) b))) :
    ∃ P ∈ LHom Kf (dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat),
      psi k Kf P = F := by
  rw [← span_bidet (antitone_shape_lamH hk hA hB)] at hF
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨rows, rfl⟩ := hy
    have hmem : bidet Kf (fun b => natW (blockWt (FirstAssembly.lamH (k := k) TT A B) (blkH b)))
        (fun b => rows (blkH b)) ∈ nablaInt (⊤ : Subring Kf) (nu1 (LetterFock.flatWt
          (dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat))) := by
      rw [← shape_lamH hk hA hB]
      exact Submodule.subset_span ⟨_, rfl⟩
    obtain ⟨Q, hQ, -, hQθ⟩ := exists_theta0_of_mem_nablaInt hk hmem
    refine ⟨Q, hQ, ?_⟩
    rw [psi_apply, hQθ]
    exact renB_bidet blkH (fun σ => natW (blockWt (FirstAssembly.lamH (k := k) TT A B) σ)) rows
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨_, hP, rfl⟩ := hx
    obtain ⟨_, hQ, rfl⟩ := hy
    exact ⟨_, add_mem hP hQ, map_add _ _ _⟩
  | smul a x _ hx =>
    obtain ⟨_, hP, rfl⟩ := hx
    exact ⟨_, Submodule.smul_mem _ a hP, map_smul _ _ _⟩

omit [CharZero Kf] in
/-- **The twists of `H(A, B)` in the letter model**: twisting `ψP` by `C_s` at both blocks of every position is
`tcst·ψ(P∘Alet)` (`LetterFock.lsub_theta0`). -/
theorem twist_psi (hk : 2 ≤ k) {A B : TT → ℤ} (hA : ∀ s, 0 ≤ A s) (hB : ∀ s, 0 ≤ B s)
    (C₀ : Fin n' → Matrix (Fin k) (Fin k) Kf) (P : LPol (Fin (n' * 2)) k Kf) :
    twist (blockWt (FirstAssembly.lamH (k := k) TT A B)) (fun b => C₀ b.2) (psi k Kf P) =
      tcst C₀ (dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat) •
        psi k Kf (linS k (Alet C₀) P) := by
  set d := dL (fun s => (FirstMeans.ext TT A s).toNat) fun s => (FirstMeans.ext TT B s).toNat
  have hlam : (fun b => blockWt (FirstAssembly.lamH (k := k) TT A B) (blkH b)) = wt1 (LetterFock.flatWt d) := by
    funext b
    rw [blkH_apply, blockWt_lamH hk hA hB, Equiv.apply_symm_apply]
  have hlet : letMat (fun b : Unit × Fin (n' * 2) => C₀ (blkH b).2) = Alet C₀ := by
    funext t
    simp [letMat, Alet]
  rw [psi_apply, twist_renB, hlam, twist, lsub_theta0, hlet, map_mul, renB_C, ← smul_eq_C_mul, psi_apply]
  congr 1
  rw [Fintype.prod_prod_type, Fintype.prod_unique, prod_letters, tcst]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [blkH_apply, eps_symm_snd, pos_vL, pos_cL, detShift_flatWt hk, even_vL, not_even_cL, ite_true,
    ite_false, zpow_zero, one_mul]

end Ident

/-! ## The flat model: shapes and bideterminants -/

section Flat

variable {n' k : ℕ} [NeZero k] {Kf : Type} [Field Kf] {TT : Finset (Fin n')}

/-- **The shape of a flat weight**: `(P + Q, Q, …, Q, 0)`, `P`, `Q` the degrees of the two letters. -/
theorem nu1_flatWtFM (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s) (s : Fin n')
    (i : Fin k) :
    nu1 (FirstMeans.flatWt (k := k) TT α β) ((), s) i =
      if i = 0 then degV (fun s => (FirstMeans.ext TT α s).toNat) (fun s => (FirstMeans.ext TT β s).toNat) s +
        degC (fun s => (FirstMeans.ext TT α s).toNat) (fun s => (FirstMeans.ext TT β s).toNat) s
      else if i = lastC k then 0
      else degC (fun s => (FirstMeans.ext TT α s).toNat) (fun s => (FirstMeans.ext TT β s).toNat) s := by
  have hα' := FirstMeans.ext_nonneg hα s
  have hβ' := FirstMeans.ext_nonneg hβ s
  have hl0 : (lastC k).val ≠ 0 := by simp [lastC]; omega
  have hlast : (lastC k).val + 1 = k := by simp [lastC]; omega
  have hd : ∀ w : Fin k → ℤ, detShift w = w (lastC k) := fun w => by
    simp only [detShift, dite_eq_left (NeZero.pos k)]; rfl
  have hfl : ∀ j : Fin k, FirstMeans.flatWt (k := k) TT α β s j =
      if j.val = 0 then FirstMeans.ext TT α s else if j.val + 1 = k then -FirstMeans.ext TT β s else 0 :=
    fun j => rfl
  have hrl : (lastC k).rev = 0 := Fin.ext (by simp [lastC]; omega)
  have hr0 : (0 : Fin k).rev = lastC k := Fin.ext (by simp [lastC])
  simp only [nu1, natW, wt1, blockWt, lamAt, hd, degV, degC]
  by_cases hs : Even s.val
  · simp only [hs, ite_true, hfl, hl0, hlast, ite_false]
    by_cases hi0 : i = 0
    · subst hi0; simp; omega
    · have h1 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      by_cases hil : i = lastC k
      · subst hil; simp [hl0, hlast, hi0]
      · have h2 : i.val + 1 ≠ k := fun h => hil (Fin.ext (by simp [lastC]; omega))
        simp only [hi0, hil, h1, h2, ite_false]; omega
  · simp only [hs, ite_false, hfl, hrl, Fin.val_zero, ite_true]
    by_cases hi0 : i = 0
    · subst hi0
      have : (0 : Fin k) ≠ lastC k := fun h => hl0 (by rw [← h]; rfl)
      simp only [hr0, hl0, hlast, ite_false, ite_true, this]; omega
    · have hi : i.val ≠ 0 := fun h => hi0 (Fin.ext (by simpa using h))
      have hik := i.isLt
      have h1 : i.rev.val + 1 ≠ k := by simp only [Fin.val_rev]; omega
      by_cases hil : i = lastC k
      · subst hil; simp [hrl, hi0]
      · have hil' : i.val ≠ k - 1 := fun h => hil (Fin.ext (by simp [lastC, h]))
        have h2 : i.rev.val ≠ 0 := by simp only [Fin.val_rev]; omega
        simp only [hi0, hil, h1, h2, ite_false]; omega

/-- **The shape of a flat weight** is the sum of the shapes of its two letters. -/
theorem shape_flatWt (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s) (s : Fin n') :
    nu1 (FirstMeans.flatWt (k := k) TT α β) ((), s) =
      nu1 (LetterFock.flatWt (dL (fun s => (FirstMeans.ext TT α s).toNat) fun s => (FirstMeans.ext TT β s).toNat))
          ((), vL s) +
        nu1 (LetterFock.flatWt (dL (fun s => (FirstMeans.ext TT α s).toNat)
          fun s => (FirstMeans.ext TT β s).toNat)) ((), cL s) := by
  have hl0 : (0 : Fin k) ≠ lastC k := fun h => by
    have := congrArg Fin.val h; simp [lastC] at this; omega
  funext i
  rw [Pi.add_apply, nu1_flatWtFM hk hα hβ, nu1_flatWt hk, nu1_flatWt hk]
  simp only [even_vL, not_even_cL, ite_true, ite_false, dL_vL, dL_cL]
  by_cases hi0 : i = 0
  · subst hi0; simp [hl0]
  · by_cases hil : i = lastC k
    · subst hil; simp [Ne.symm hl0]
    · simp [hi0, hil]

omit [NeZero k] in
/-- **The flat shapes are antitone.** -/
theorem antitone_shape_flatWt (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s)
    (b : Unit × Fin n') : Antitone (nu1 (FirstMeans.flatWt (k := k) TT α β) b) :=
  HermForms.natW_antitone (antitone_blockWt (fun _ s => FirstMeans.antitone_flatWt hk hα hβ s) b)

omit [NeZero k] in
/-- **Merging blocks on a block factor.** -/
theorem delta_bfac (t : Fin (n' * 2)) (m : Fin k → ℕ) (r : (s : Fin k) → Fin (mult m s) → Fin (s + 1) → Fin k) :
    delta (Kf := Kf) (bfac ((), t) m r) = bfac ((), pos t) m r := by
  simp only [bfac, map_prod]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun c _ => ?_
  rw [minor, minor, AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map, ← AlgHom.mapMatrix_apply,
    delta_xMat]

omit [NeZero k] in
/-- **Products over the blocks of one orbit** are products over the positions. -/
theorem prod_unit {M : Type*} [CommMonoid M] {β : Type*} [Fintype β] (f : Unit × β → M) :
    ∏ b, f b = ∏ t, f ((), t) := by
  rw [Fintype.prod_prod_type]; simp

omit [NeZero k] in
/-- **Merging the blocks of a bideterminant**: `δ` of a bideterminant of the letter model is a bideterminant of a
shape whose block `s` is the sum of the shapes of the two letters of `s`. -/
theorem delta_bidet {ν' : Unit × Fin (n' * 2) → Fin k → ℕ} {ν : Unit × Fin n' → Fin k → ℕ}
    (h' : ∀ b, Antitone (ν' b)) (hν : ∀ s, ν ((), s) = ν' ((), vL s) + ν' ((), cL s))
    (rows' : BRows (Unit × Fin (n' * 2)) k ν') :
    ∃ rows : BRows (Unit × Fin n') k ν, bidet Kf ν rows = delta (bidet Kf ν' rows') := by
  have key : ∀ s : Fin n', ∃ r : (i : Fin k) → Fin (mult (ν ((), s)) i) → Fin (i + 1) → Fin k,
      (bfac ((), s) (ν ((), s)) r : Pol (Unit × Fin n') k Kf) =
        bfac ((), s) (ν' ((), vL s)) (rows' ((), vL s)) * bfac ((), s) (ν' ((), cL s)) (rows' ((), cL s)) :=
    fun s => bfac_merge ((), s) (fun i => by rw [hν, mult_add (h' _) (h' _)]) _ _
  choose r hr using key
  refine ⟨fun b => r b.2, ?_⟩
  show ∏ b, bfac b (ν b) (r b.2) = delta (∏ b, bfac b (ν' b) (rows' b))
  rw [map_prod, prod_unit, prod_unit]
  simp only [delta_bfac]
  rw [prod_letters]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hr, pos_vL, pos_cL]

omit [NeZero k] in
/-- **Splitting the blocks of a bideterminant**: every bideterminant of a merged shape is `δ` of a bideterminant of
the letter model. -/
theorem delta_bidet' {ν' : Unit × Fin (n' * 2) → Fin k → ℕ} {ν : Unit × Fin n' → Fin k → ℕ}
    (h' : ∀ b, Antitone (ν' b)) (hν : ∀ s, ν ((), s) = ν' ((), vL s) + ν' ((), cL s))
    (rows : BRows (Unit × Fin n') k ν) :
    ∃ rows' : BRows (Unit × Fin (n' * 2)) k ν', bidet Kf ν rows = delta (bidet Kf ν' rows') := by
  have key : ∀ s : Fin n', ∃ (r₁ : (i : Fin k) → Fin (mult (ν' ((), vL s)) i) → Fin (i + 1) → Fin k)
      (r₂ : (i : Fin k) → Fin (mult (ν' ((), cL s)) i) → Fin (i + 1) → Fin k),
      (bfac ((), s) (ν ((), s)) (rows ((), s)) : Pol (Unit × Fin n') k Kf) =
        bfac ((), s) (ν' ((), vL s)) r₁ * bfac ((), s) (ν' ((), cL s)) r₂ :=
    fun s => bfac_split ((), s) (fun i => by rw [hν, mult_add (h' _) (h' _)]) _
  choose r₁ r₂ hr using key
  have key' : ∀ t : Fin (n' * 2), ∃ r : (i : Fin k) → Fin (mult (ν' ((), t)) i) → Fin (i + 1) → Fin k,
      (bfac ((), pos t) (ν' ((), t)) r : Pol (Unit × Fin n') k Kf) =
        if t = vL (pos t) then bfac ((), pos t) (ν' ((), vL (pos t))) (r₁ (pos t))
        else bfac ((), pos t) (ν' ((), cL (pos t))) (r₂ (pos t)) := by
    intro t
    by_cases ht : t = vL (pos t)
    · rw [ite_eq_left ht]
      exact exists_bfac_eq (congrArg (fun t => ν' ((), t)) ht.symm) _
    · rw [ite_eq_right ht]
      have hc := (letter_cases t).resolve_left ht
      exact exists_bfac_eq (congrArg (fun t => ν' ((), t)) hc.symm) _
  choose r' hr' using key'
  refine ⟨fun b => r' b.2, ?_⟩
  show ∏ b, bfac b (ν b) (rows b) = delta (∏ b, bfac b (ν' b) (r' b.2))
  rw [map_prod, prod_unit, prod_unit]
  simp only [delta_bfac, hr']
  rw [prod_letters]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hv : ∀ s₁ : Fin n', s₁ = s → (bfac ((), s₁) (ν' ((), vL s₁)) (r₁ s₁) : Pol (Unit × Fin n') k Kf) =
      bfac ((), s) (ν' ((), vL s)) (r₁ s) := by rintro _ rfl; rfl
  have hc : ∀ s₁ : Fin n', s₁ = s → (bfac ((), s₁) (ν' ((), cL s₁)) (r₂ s₁) : Pol (Unit × Fin n') k Kf) =
      bfac ((), s) (ν' ((), cL s)) (r₂ s) := by rintro _ rfl; rfl
  have hne : cL s ≠ vL (pos (cL s)) := by rw [pos_cL]; exact fun h => pairs.ne s s h.symm
  rw [hr, ite_eq_left (by rw [pos_vL]), ite_eq_right hne, hv _ (pos_vL s), hc _ (pos_cL s)]

variable [CharZero Kf]

/-- **`β` of an `A`-integral letter polynomial is `A`-integral** in the flat model (`θ°` and merging). -/
theorem beta_mem_nablaInt (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s) {Ar : Subring Kf}
    {P : LPol (Fin (n' * 2)) k Kf}
    (hP : P ∈ LHom Kf (dL (fun s => (FirstMeans.ext TT α s).toNat) fun s => (FirstMeans.ext TT β s).toNat))
    (hPA : ∀ μ, P.coeff μ ∈ Ar) : beta Kf P ∈ nablaInt Ar (nu1 (FirstMeans.flatWt (k := k) TT α β)) := by
  have key : ∀ G ∈ nablaInt Ar (nu1 (LetterFock.flatWt (k := k)
      (dL (fun s => (FirstMeans.ext TT α s).toNat) fun s => (FirstMeans.ext TT β s).toNat))),
      delta G ∈ nablaInt Ar (nu1 (FirstMeans.flatWt (k := k) TT α β)) := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨rows', rfl⟩ := hx
      obtain ⟨rows, hrows⟩ := delta_bidet (Kf := Kf) (antitone_nu1_flatWt hk _) (shape_flatWt hk hα hβ) rows'
      rw [← hrows]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : Kf) • x from rfl, map_smul]
      exact Submodule.smul_mem _ a hx
  exact key _ ((theta0_mem_nablaInt_iff hk hP).2 hPA)

omit [CharZero Kf] in
/-- **The `A`-integral flat polynomials are `β` of `A`-integral letter polynomials.** -/
theorem exists_beta_of_mem_nablaInt (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s)
    {Ar : Subring Kf} {G : Pol (Unit × Fin n') k Kf}
    (hG : G ∈ nablaInt Ar (nu1 (FirstMeans.flatWt (k := k) TT α β))) :
    ∃ Q ∈ LHom Kf (dL (fun s => (FirstMeans.ext TT α s).toNat) fun s => (FirstMeans.ext TT β s).toNat),
      (∀ μ, Q.coeff μ ∈ Ar) ∧ beta Kf Q = G := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨rows, rfl⟩ := hx
    obtain ⟨rows', hrows⟩ := delta_bidet' (Kf := Kf) (antitone_nu1_flatWt hk _) (shape_flatWt hk hα hβ) rows
    obtain ⟨Q, hQ, hQA, hQθ⟩ := exists_theta0_of_mem_nablaInt (A := Ar) hk (Submodule.subset_span ⟨rows', rfl⟩)
    exact ⟨Q, hQ, hQA, by rw [hrows, beta, AlgHom.comp_apply, hQθ]⟩
  | zero => exact ⟨0, zero_mem _, fun _ => by simp, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, hPA, rfl⟩ := hx
    obtain ⟨Q, hQ, hQA, rfl⟩ := hy
    exact ⟨P + Q, add_mem hP hQ, fun μ => by simpa using add_mem (hPA μ) (hQA μ), map_add _ _ _⟩
  | smul a x _ hx =>
    obtain ⟨P, hP, hPA, rfl⟩ := hx
    refine ⟨(a : Kf) • P, Submodule.smul_mem _ _ hP, fun μ => ?_, (map_smul _ _ _).trans rfl⟩
    rw [coeff_smul, smul_eq_mul]
    exact mul_mem a.2 (hPA μ)

/-- **`β` lands in `∇` of the flat weight.** -/
theorem beta_mem_nabla (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s)
    {P : LPol (Fin (n' * 2)) k Kf}
    (hP : P ∈ LHom Kf (dL (fun s => (FirstMeans.ext TT α s).toNat) fun s => (FirstMeans.ext TT β s).toNat)) :
    beta Kf P ∈ nabla Kf (nu1 (FirstMeans.flatWt (k := k) TT α β)) :=
  WeylSandwich.nablaInt_subset_nabla ⊤ (antitone_shape_flatWt hk hα hβ)
    (beta_mem_nablaInt hk hα hβ hP fun _ => Subring.mem_top _)

/-- **`β` is onto `∇` of the flat weight.** -/
theorem exists_beta (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s)
    {G : Pol (Unit × Fin n') k Kf} (hG : G ∈ nabla Kf (nu1 (FirstMeans.flatWt (k := k) TT α β))) :
    ∃ Q ∈ LHom Kf (dL (fun s => (FirstMeans.ext TT α s).toNat) fun s => (FirstMeans.ext TT β s).toNat),
      beta Kf Q = G := by
  rw [← span_bidet (antitone_shape_flatWt hk hα hβ)] at hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨rows, rfl⟩ := hx
    obtain ⟨Q, hQ, -, hQβ⟩ := exists_beta_of_mem_nablaInt (Ar := (⊤ : Subring Kf)) hk hα hβ
      (Submodule.subset_span ⟨rows, rfl⟩)
    exact ⟨Q, hQ, hQβ⟩
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨_, hP, rfl⟩ := hx
    obtain ⟨_, hQ, rfl⟩ := hy
    exact ⟨_, add_mem hP hQ, map_add _ _ _⟩
  | smul a x _ hx =>
    obtain ⟨_, hP, rfl⟩ := hx
    exact ⟨_, Submodule.smul_mem _ a hP, map_smul _ _ _⟩

omit [CharZero Kf] in
/-- **The determinant twist of a flat weight**: `−Q`, `Q` the degree of the covector letter. -/
theorem detShift_flatWtFM (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s) (s : Fin n') :
    detShift (wt1 (FirstMeans.flatWt (k := k) TT α β) ((), s)) =
      -(degC (fun s => (FirstMeans.ext TT α s).toNat) (fun s => (FirstMeans.ext TT β s).toNat) s : ℤ) := by
  have hα' := FirstMeans.ext_nonneg hα s
  have hβ' := FirstMeans.ext_nonneg hβ s
  have hl0 : (lastC k).val ≠ 0 := by simp [lastC]; omega
  have hlast : (lastC k).val + 1 = k := by simp [lastC]; omega
  have hrl : (lastC k).rev = 0 := Fin.ext (by simp [lastC]; omega)
  simp only [detShift, dite_eq_left (NeZero.pos k), wt1, blockWt, lamAt, degC]
  rw [show (⟨k - 1, _⟩ : Fin k) = lastC k from rfl]
  by_cases hs : Even s.val
  · simp only [hs, ite_true, FirstMeans.flatWt, hl0, hlast, ite_false]; omega
  · simp only [hs, ite_false, FirstMeans.flatWt, hrl, Fin.val_zero, ite_true]; omega

omit [CharZero Kf] in
/-- **The twists of the flat model**: twisting `βP` by `C_s` at every position is `tcst·β(P∘Alet)`. -/
theorem twist_beta (hk : 2 ≤ k) {α β : TT → ℤ} (hα : ∀ s, 0 ≤ α s) (hβ : ∀ s, 0 ≤ β s)
    (C₀ : Fin n' → Matrix (Fin k) (Fin k) Kf) (P : LPol (Fin (n' * 2)) k Kf) :
    twist (wt1 (FirstMeans.flatWt (k := k) TT α β)) (fun b => C₀ b.2) (beta Kf P) =
      tcst C₀ (dL (fun s => (FirstMeans.ext TT α s).toNat) fun s => (FirstMeans.ext TT β s).toNat) •
        beta Kf (linS k (Alet C₀) P) := by
  have hl : (lsub fun b : Unit × Fin n' => C₀ b.2).comp (delta (k := k) (Kf := Kf)) =
      (delta (k := k) (Kf := Kf)).comp (lsub fun b : Unit × Fin (n' * 2) => C₀ (pos b.2)) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨⟨⟨⟩, t⟩, i, j⟩ := v
    simp [delta, lsub_X]
  have hlet : letMat (fun b : Unit × Fin (n' * 2) => C₀ (pos b.2)) = Alet C₀ := by
    funext t; simp [letMat, Alet]
  have hl' := congrArg (fun φ => φ (theta0 Kf P)) hl
  simp only [AlgHom.comp_apply] at hl'
  rw [beta, AlgHom.comp_apply, twist, hl', lsub_theta0, hlet, ← smul_eq_C_mul, AlgHom.comp_apply]
  congr 1
  rw [prod_unit, tcst]
  exact Finset.prod_congr rfl fun s _ => by rw [detShift_flatWtFM hk hα hβ, dL_cL]

end Flat


/-! ## The kernel of the flat model on harmonic polynomials (I4) -/

section Kernel

variable {n' k : ℕ} [NeZero k] {Kf : Type} [Field Kf]

/-- **The test matrix of a position**: column `0` the vector letter `x`, columns `1 ≤ j ≤ k − 2` the vectors
`y_{k−1}e_j − y_je_{k−1}` of the covector letter `y`, column `k − 1` zero. -/
def Wm (s : Fin n') : Matrix (Fin k) (Fin k) (LPol (Fin (n' * 2)) k Kf) := fun i j =>
  if j = 0 then X (vL s, i) else if j = lastC k then 0
  else (if i = j then X (cL s, lastC k) else 0) - (if i = lastC k then X (cL s, j) else 0)

variable (Kf) in
/-- **Evaluating the flat model at the test matrices** `x_s ↦ W_s`. -/
def ev : Pol (Unit × Fin n') k Kf →ₐ[Kf] LPol (Fin (n' * 2)) k Kf := aeval fun v => Wm v.1.2 v.2.1 v.2.2

/-- **The last cofactor row of the test matrix**, `ev∘β` of the covector letter. -/
def Yc (s : Fin n') (c : Fin k) : LPol (Fin (n' * 2)) k Kf := (Wm (Kf := Kf) s).adjugate (lastC k) c

/-- **`ev∘β` on a vector letter** is the identity. -/
theorem ev_beta_vL (s : Fin n') (c : Fin k) : ev Kf (beta Kf (X (vL s, c))) = X (vL s, c) := by
  simp [beta_vL, ev, Wm]

/-- **`ev∘β` on a covector letter** is the last cofactor row of the test matrix. -/
theorem ev_beta_cL (s : Fin n') (c : Fin k) : ev Kf (beta Kf (X (cL s, c))) = Yc s c := by
  have h : (ev Kf).mapMatrix (xMat (Φ := Unit × Fin n') (n := k) (L := Kf) ((), s)) = Wm (Kf := Kf) s := by
    ext i j; simp [ev, xMat]
  rw [beta_cL, Yc, ← h, ← AlgHom.map_adjugate]
  rfl

/-- **The last entry of the cofactor row**: `Y_{k−1} = x_0·y_{k−1}^{k−2}`, a lower triangular determinant. -/
theorem Yc_last (hk : 3 ≤ k) (s : Fin n') :
    Yc (Kf := Kf) s (lastC k) = X (vL s, 0) * X (cL s, lastC k) ^ (k - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hl : lastC (m + 3) = Fin.last (m + 2) := lastC_succ (m + 2)
  rw [Yc, Matrix.adjugate_apply, Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc, hl]
    have hmid : ∀ j : Fin (m + 1), (Wm (Kf := Kf) (k := m + 3) s).updateRow (Fin.last (m + 2))
        (Pi.single (Fin.last (m + 2)) 1) j.castSucc.succ j.castSucc.succ = X (cL s, Fin.last (m + 2)) := by
      intro j
      have h1 : j.castSucc.succ ≠ Fin.last (m + 2) := by
        rw [Ne, Fin.ext_iff]; simp; omega
      rw [Matrix.updateRow_ne h1]
      simp [Wm, hl, h1, Fin.succ_ne_zero]
    simp only [hmid, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fin.succ_last,
      Matrix.updateRow_self, Pi.single_eq_same, mul_one]
    rw [Matrix.updateRow_ne (Fin.last_pos.ne : (0 : Fin (m + 3)) ≠ Fin.last (m + 2))]
    simp [Wm]
  · rw [hl]
    intro i j hij
    simp only [OrderDual.toDual_lt_toDual] at hij
    by_cases hi : i = Fin.last (m + 2)
    · subst hi; exact absurd hij (not_lt.2 (Fin.le_last j))
    · rw [Matrix.updateRow_ne hi]
      have hj0 : j ≠ 0 := fun h => by subst h; exact absurd hij (Fin.not_lt_zero i)
      have hij' : i ≠ j := ne_of_lt hij
      simp [Wm, hl, hj0, hij', hi]

/-- **The last coordinate is not the first** (`k ≥ 2`). -/
theorem lastC_ne_zero (hk : 2 ≤ k) : lastC k ≠ 0 := fun h => by
  have := congrArg Fin.val h; simp [lastC] at this; omega

/-- **The cofactor row is orthogonal to the columns** of the test matrix: `adj(W)·W = det W = 0`. -/
theorem Yc_orth (hk : 2 ≤ k) (s : Fin n') (j : Fin k) : ∑ c, Yc (Kf := Kf) s c * Wm s c j = 0 := by
  have hdet : (Wm (Kf := Kf) s).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero (lastC k) fun i => by simp [Wm, lastC_ne_zero hk]
  have := congrFun (congrFun (Matrix.adjugate_mul (Wm (Kf := Kf) s)) (lastC k)) j
  rw [hdet, zero_smul, Matrix.zero_apply, Matrix.mul_apply] at this
  exact this

/-- **The middle entries of the cofactor row**: `Y_j = Λ·y_j`, `Λ = x_0·y_{k−1}^{k−3}`, from the column `j`. -/
theorem Yc_mid (hk : 3 ≤ k) (s : Fin n') {j : Fin k} (hj0 : j ≠ 0) (hjl : j ≠ lastC k) :
    Yc (Kf := Kf) s j = X (vL s, 0) * X (cL s, lastC k) ^ (k - 3) * X (cL s, j) := by
  have h := Yc_orth (Kf := Kf) (by omega) s j
  have hW : ∀ c, Wm (Kf := Kf) s c j =
      (if c = j then X (cL s, lastC k) else 0) - (if c = lastC k then X (cL s, j) else 0) := fun c => by
    simp [Wm, hj0, hjl]
  simp only [hW, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Yc_last hk] at h
  have hX : (X (cL s, lastC k) : LPol (Fin (n' * 2)) k Kf) ≠ 0 := X_ne_zero _
  refine mul_right_cancel₀ hX ?_
  rw [sub_eq_zero] at h
  rw [h, show k - 2 = (k - 3) + 1 by omega, pow_succ]
  ring

/-- **The cofactor row** (`k ≥ 3`): `Y_c = Λ·y_c − [c = 0]·y_{k−1}^{k−3}·h`, `Λ = x_0·y_{k−1}^{k−3}`; the entry
`c = 0` from the orthogonality to the column `0`. -/
theorem Yc_eq (hk : 3 ≤ k) (s : Fin n') (c : Fin k) :
    Yc (Kf := Kf) s c = X (vL s, 0) * X (cL s, lastC k) ^ (k - 3) * X (cL s, c) -
      if c = 0 then X (cL s, lastC k) ^ (k - 3) * hP (vL s) (cL s) else 0 := by
  have hne : ∀ c : Fin k, c ≠ 0 → Yc (Kf := Kf) s c = X (vL s, 0) * X (cL s, lastC k) ^ (k - 3) * X (cL s, c) :=
    fun c hc => by
      by_cases hcl : c = lastC k
      · subst hcl
        rw [Yc_last hk, show k - 2 = (k - 3) + 1 by omega, pow_succ]
        ring
      · exact Yc_mid hk s hc hcl
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    have h := Yc_orth (Kf := Kf) (k := k) (by omega) s 0
    have hW : ∀ c, Wm (Kf := Kf) (k := k) s c 0 = X (vL s, c) := fun c => by simp [Wm]
    simp only [hW] at h
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0)] at h
    have e : ∑ c ∈ Finset.univ.erase 0, Yc (Kf := Kf) s c * X (vL s, c) =
        X (vL s, 0) * X (cL s, lastC k) ^ (k - 3) * (hP (vL s) (cL s) - X (vL s, 0) * X (cL s, 0)) := by
      rw [hP, ← Finset.sum_erase_add _ _ (Finset.mem_univ 0), add_sub_cancel_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [hne c (Finset.ne_of_mem_erase hc)]
      ring
    rw [e] at h
    have hX : (X (vL s, 0) : LPol (Fin (n' * 2)) k Kf) ≠ 0 := X_ne_zero _
    refine mul_left_cancel₀ hX ?_
    linear_combination h
  · rw [ite_eq_right hc, sub_zero]
    exact hne c hc

/-- **Substituting the cofactor rows** for the covector letters of the positions of `S`. -/
def phiS (S : Finset (Fin n')) : LPol (Fin (n' * 2)) k Kf →ₐ[Kf] LPol (Fin (n' * 2)) k Kf :=
  aeval fun v => if pos v.1 ∈ S ∧ v.1 = cL (pos v.1) then Yc (pos v.1) v.2 else X v

/-- **The substitution fixes the vector letters.** -/
theorem phiS_vL (S : Finset (Fin n')) (s : Fin n') (c : Fin k) :
    phiS (Kf := Kf) S (X (vL s, c)) = X (vL s, c) := by
  have : vL s ≠ cL s := pairs.ne s s
  simp [phiS, this]

/-- **The substitution on a covector letter of `S`.** -/
theorem phiS_cL_mem {S : Finset (Fin n')} {s : Fin n'} (hs : s ∈ S) (c : Fin k) :
    phiS (Kf := Kf) S (X (cL s, c)) = Yc s c := by
  simp [phiS, hs]

/-- **The substitution fixes the covector letters off `S`.** -/
theorem phiS_cL_not {S : Finset (Fin n')} {s : Fin n'} (hs : s ∉ S) (c : Fin k) :
    phiS (Kf := Kf) S (X (cL s, c)) = X (cL s, c) := by
  simp [phiS, hs]

/-- **Substituting at every position is `ev∘β`.** -/
theorem phiS_univ : phiS (Kf := Kf) (k := k) (n' := n') Finset.univ = (ev Kf).comp (beta Kf) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨t, c⟩ := v
  rcases letter_cases t with h | h <;> rw [h]
  · rw [phiS_vL, AlgHom.comp_apply, ev_beta_vL]
  · rw [phiS_cL_mem (Finset.mem_univ _), AlgHom.comp_apply, ev_beta_cL]

/-- **Substituting at no position is the identity.** -/
theorem phiS_empty : phiS (Kf := Kf) (k := k) (n' := n') ∅ = AlgHom.id Kf _ := by
  refine MvPolynomial.algHom_ext fun v => ?_
  simp [phiS]

/-- **The substitution fixes the pairings off `S`.** -/
theorem phiS_hP {S : Finset (Fin n')} {s : Fin n'} (hs : s ∉ S) :
    phiS (Kf := Kf) (k := k) S (hP (vL s) (cL s)) = hP (vL s) (cL s) := by
  simp only [hP, map_sum, map_mul, phiS_vL, phiS_cL_not hs]

/-- **The substitution fixes the cofactor rows off `S`.** -/
theorem phiS_Yc (hk : 3 ≤ k) {S : Finset (Fin n')} {s : Fin n'} (hs : s ∉ S) (c : Fin k) :
    phiS (Kf := Kf) S (Yc s c) = Yc s c := by
  rw [Yc_eq hk]
  split_ifs <;> simp only [map_sub, map_mul, map_pow, phiS_vL, phiS_cL_not hs, phiS_hP hs, map_zero]

/-- **Substituting at `insert s S`** is substituting at `s`, then at `S`. -/
theorem phiS_insert (hk : 3 ≤ k) {S : Finset (Fin n')} {s : Fin n'} (hs : s ∉ S) :
    phiS (Kf := Kf) (k := k) (insert s S) = (phiS S).comp (phiS {s}) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨t, c⟩ := v
  rcases letter_cases t with h | h <;> rw [h] <;> set t' := pos t
  · rw [phiS_vL, AlgHom.comp_apply, phiS_vL, phiS_vL]
  · rw [AlgHom.comp_apply]
    by_cases hts : t' = s
    · rw [hts, phiS_cL_mem (Finset.mem_insert_self s S), phiS_cL_mem (Finset.mem_singleton_self s),
        phiS_Yc hk hs]
    · have h1 : t' ∉ ({s} : Finset (Fin n')) := by simpa using hts
      rw [phiS_cL_not h1]
      by_cases htS : t' ∈ S
      · rw [phiS_cL_mem (Finset.mem_insert_of_mem htS), phiS_cL_mem htS]
      · have h2 : t' ∉ insert s S := by simp [hts, htS]
        rw [phiS_cL_not h2, phiS_cL_not htS]

/-- **The degree of a cofactor row**: `e_x + (k − 2)·e_y`. -/
def DY (s : Fin n') : Fin (n' * 2) → ℕ := Pi.single (vL s) 1 + (k - 2) • Pi.single (cL s) 1

omit [NeZero k] in
/-- **A letter variable has the degree of its letter.** -/
theorem isWH_X (t : Fin (n' * 2)) (c : Fin k) :
    IsWeightedHomogeneous (LetterFock.rowW (Fin (n' * 2)) k) (X (t, c) : LPol (Fin (n' * 2)) k Kf) (Pi.single t 1) :=
  isWeightedHomogeneous_X Kf (LetterFock.rowW _ k) (t, c)

/-- **The cofactor row has degree `e_x + (k − 2)·e_y`.** -/
theorem Yc_mem (hk : 3 ≤ k) (s : Fin n') (c : Fin k) : Yc (Kf := Kf) s c ∈ LHom Kf (DY (k := k) s) := by
  have hpow : (k - 3) • (Pi.single (cL s) 1 : Fin (n' * 2) → ℕ) + Pi.single (cL s) 1 =
      (k - 2) • Pi.single (cL s) 1 := by
    rw [← succ_nsmul]; congr 1; omega
  rw [Yc_eq hk]
  refine sub_mem ?_ ?_
  · rw [LHom, mem_weightedHomogeneousSubmodule]
    have := (((isWH_X (Kf := Kf) (vL s) 0).mul ((isWH_X (Kf := Kf) (cL s) (lastC k)).pow (k - 3))).mul
      (isWH_X (Kf := Kf) (cL s) c))
    rwa [add_assoc, hpow] at this
  · split_ifs
    · rw [LHom, mem_weightedHomogeneousSubmodule]
      have := ((isWH_X (Kf := Kf) (cL s) (lastC k)).pow (k - 3)).mul (hP_mem (K := Kf) (k := k) (vL s) (cL s))
      rwa [pe, add_left_comm, ← add_assoc, add_assoc, hpow] at this
    · exact zero_mem _

omit [NeZero k] in
/-- **Substitutions of homogeneous polynomials keep homogeneity**: letter `t` of degree `D_t`. -/
theorem aeval_mem_LHom {f : Fin (n' * 2) × Fin k → LPol (Fin (n' * 2)) k Kf} {D : Fin (n' * 2) → Fin (n' * 2) → ℕ}
    (hf : ∀ t c, f (t, c) ∈ LHom Kf (D t)) {d : Fin (n' * 2) → ℕ} {G : LPol (Fin (n' * 2)) k Kf}
    (hG : G ∈ LHom Kf d) : aeval f G ∈ LHom Kf (∑ t, d t • D t) := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hG
  rw [G.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hw := hG (mem_support_iff.1 hμ)
  rw [aeval_monomial, LHom, mem_weightedHomogeneousSubmodule, Finsupp.prod, MvPolynomial.algebraMap_eq]
  have hsum : ∑ v ∈ μ.support, μ v • D v.1 = ∑ t, d t • D t := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by rw [Finsupp.notMem_support_iff.1 hv, zero_smul]),
      Fintype.sum_prod_type, ← hw]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LetterFock.weight_rowW_apply, Finset.sum_smul]
  rw [← hsum]
  exact (IsWeightedHomogeneous.prod _ _ _ fun v _ => by
    have := hf v.1 v.2
    rw [LHom, mem_weightedHomogeneousSubmodule] at this
    exact this.pow (μ v)).C_mul _

/-- **The degrees of the letters after substituting at `s`.** -/
def Dt (s : Fin n') (t : Fin (n' * 2)) : Fin (n' * 2) → ℕ := if t = cL s then DY (k := k) s else Pi.single t 1

/-- **Substituting at one position keeps homogeneity.** -/
theorem phiS_single_mem (hk : 3 ≤ k) (s : Fin n') {d : Fin (n' * 2) → ℕ} {G : LPol (Fin (n' * 2)) k Kf}
    (hG : G ∈ LHom Kf d) : phiS {s} G ∈ LHom Kf (∑ t, d t • Dt (k := k) s t) := by
  refine aeval_mem_LHom (fun t c => ?_) hG
  rcases letter_cases t with h | h <;> rw [h]
  · have : vL (pos t) ≠ cL s := pairs.ne _ _
    simp only [Dt, this, ite_false]
    rw [show (if pos (vL (pos t)) ∈ ({s} : Finset (Fin n')) ∧ vL (pos t) = cL (pos (vL (pos t)))
        then Yc (pos (vL (pos t))) c else X (vL (pos t), c)) = X (vL (pos t), c) from by simp [pairs.ne]]
    rw [LHom, mem_weightedHomogeneousSubmodule]; exact isWH_X _ _
  · by_cases hts : pos t = s
    · rw [hts]
      simp only [Dt, ite_true, pos_cL, Finset.mem_singleton, and_self]
      exact Yc_mem hk s c
    · have : cL (pos t) ≠ cL s := fun e => hts (pairs.inj_b e)
      simp only [Dt, this, ite_false, pos_cL, Finset.mem_singleton, hts, false_and]
      rw [LHom, mem_weightedHomogeneousSubmodule]; exact isWH_X _ _

/-- **The derivatives in another position kill the cofactor rows.** -/
theorem pderiv_Yc (hk : 3 ≤ k) {s : Fin n'} {w : Fin (n' * 2) × Fin k} (hw1 : w.1 ≠ vL s) (hw2 : w.1 ≠ cL s)
    (c : Fin k) : pderiv w (Yc (Kf := Kf) s c) = 0 := by
  obtain ⟨l, e⟩ := w
  have h1 : ∀ c', (vL s, c') ≠ (l, e) := fun c' h => hw1 (congrArg Prod.fst h).symm
  have h2 : ∀ c', (cL s, c') ≠ (l, e) := fun c' h => hw2 (congrArg Prod.fst h).symm
  rw [Yc_eq hk]
  split_ifs <;> simp [pderiv_X_of_ne (h1 _), pderiv_X_of_ne (h2 _), pderiv_hP_other hw1 hw2]

/-- **Substituting at `s` commutes with the derivatives in another position.** -/
theorem pderiv_phiS (hk : 3 ≤ k) {s : Fin n'} {w : Fin (n' * 2) × Fin k} (hw1 : w.1 ≠ vL s) (hw2 : w.1 ≠ cL s)
    (G : LPol (Fin (n' * 2)) k Kf) : pderiv w (phiS {s} G) = phiS {s} (pderiv w G) := by
  refine derivation_comp (phiS {s}) (pderiv w) (pderiv w) (fun v => ?_) G
  obtain ⟨t, c⟩ := v
  have hconst : ∀ u : Fin (n' * 2) × Fin k, phiS (Kf := Kf) {s} (pderiv w (X u)) = pderiv w (X u) := fun u => by
    rw [pderiv_X]; by_cases h : w = u <;> simp [h]
  by_cases hts : t = cL s
  · subst hts
    rw [phiS_cL_mem (Finset.mem_singleton_self s), pderiv_Yc hk hw1 hw2, pderiv_X_of_ne, map_zero]
    exact fun h => hw2 (congrArg Prod.fst h).symm
  · have hX : phiS (Kf := Kf) {s} (X (t, c)) = X (t, c) := by
      rcases letter_cases t with h | h <;> rw [h]
      · exact phiS_vL _ _ _
      · exact phiS_cL_not (fun hm => hts (by rw [h, Finset.mem_singleton.1 hm])) _
    rw [hX, hconst]

/-- **Substituting at `s` commutes with the Laplacian of another position.** -/
theorem lapP_phiS (hk : 3 ≤ k) {s t : Fin n'} (hst : s ≠ t) (G : LPol (Fin (n' * 2)) k Kf) :
    lapP (vL t) (cL t) (phiS {s} G) = phiS {s} (lapP (vL t) (cL t) G) := by
  have a1 : vL t ≠ vL s := fun h => hst (pairs.inj_a h).symm
  have a2 : vL t ≠ cL s := pairs.ne t s
  have b1 : cL t ≠ vL s := fun h => pairs.ne s t h.symm
  have b2 : cL t ≠ cL s := fun h => hst (pairs.inj_b h).symm
  rw [lapP_apply, lapP_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [pderiv_phiS hk (w := (cL t, c)) b1 b2,
    pderiv_phiS hk (w := (vL t, c)) a1 a2]

omit [NeZero k] in
/-- **The homogeneous components of `H·q`**, `H` homogeneous of degree `e`: `(Hq)_{d+e} = H·q_d`. -/
theorem comp_mul_of_mem {α : Type*} [Fintype α] [DecidableEq α] {H : LPol α k Kf} {e : α → ℕ}
    (hH : H ∈ LHom Kf e) (d : α → ℕ) (q : LPol α k Kf) :
    weightedHomogeneousComponent (LetterFock.rowW α k) (d + e) (H * q) =
      H * weightedHomogeneousComponent (LetterFock.rowW α k) d q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : (monomial m a : LPol α k Kf) ∈ weightedHomogeneousSubmodule Kf (LetterFock.rowW α k)
        (Finsupp.weight (LetterFock.rowW α k) m) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hHm : H * monomial m a ∈ weightedHomogeneousSubmodule Kf (LetterFock.rowW α k)
        (e + Finsupp.weight (LetterFock.rowW α k) m) := by
      rw [LHom, mem_weightedHomogeneousSubmodule] at hH
      exact hH.mul hm
    rw [weightedHomogeneousComponent_of_mem hHm, weightedHomogeneousComponent_of_mem hm]
    by_cases h : d = Finsupp.weight (LetterFock.rowW α k) m
    · rw [ite_eq_left (by rw [h, add_comm]), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (by rw [add_comm] at h'; exact add_left_cancel h')), ite_eq_right h, mul_zero]
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]

omit [NeZero k] in
/-- **The homogeneous components of `H·q`** vanish below the degree of `H`. -/
theorem comp_mul_eq_zero {α : Type*} [Fintype α] [DecidableEq α] {H : LPol α k Kf} {e : α → ℕ}
    (hH : H ∈ LHom Kf e) {d : α → ℕ} (hd : ¬ e ≤ d) (q : LPol α k Kf) :
    weightedHomogeneousComponent (LetterFock.rowW α k) d (H * q) = 0 := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    have hHm : H * monomial m a ∈ weightedHomogeneousSubmodule Kf (LetterFock.rowW α k)
        (e + Finsupp.weight (LetterFock.rowW α k) m) := by
      rw [LHom, mem_weightedHomogeneousSubmodule] at hH
      exact hH.mul (isWeightedHomogeneous_monomial _ _ _ rfl)
    rw [weightedHomogeneousComponent_of_mem hHm, ite_eq_right]
    intro h
    exact hd (h ▸ le_self_add)
  | add p q hp hq => rw [mul_add, map_add, hp, hq, add_zero]

omit [NeZero k] in
/-- **Every degree is on a chain**: `D = d₀ + i·(e_a + e_b)` with `min(d₀_a, d₀_b) = 0`. -/
theorem chain_form {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) (D : α → ℕ) :
    ∃ d₀ : α → ℕ, ∃ i : ℕ, D = d₀ + i • pe a b ∧ (d₀ a = 0 ∨ d₀ b = 0) := by
  refine ⟨D - min (D a) (D b) • pe a b, min (D a) (D b), ?_, ?_⟩
  · funext l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pe, Pi.single_apply]
    by_cases ha : l = a
    · subst ha; simp [hab]
    · by_cases hb : l = b
      · subst hb; simp [ha]
      · simp [ha, hb]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pe_left hab, pe_right hab]
    omega

/-- **`x_0` and `y_{k−1}` do not divide the pairing** (evaluate at a point killing them). -/
theorem not_X_dvd_hP (hk : 2 ≤ k) (s : Fin n') {v : Fin (n' * 2) × Fin k}
    (hv : v = (vL s, 0) ∨ v = (cL s, lastC k)) : ¬ (X v ∣ (hP (vL s) (cL s) : LPol (Fin (n' * 2)) k Kf)) := by
  rintro ⟨r, hr⟩
  have hl0 := lastC_ne_zero (k := k) hk
  have hne := (pairs (n' := n')).ne s s
  -- evaluate at a point killing `X v` but not the pairing
  set c₁ : Fin k := if v = (vL s, 0) then lastC k else 0
  set f : Fin (n' * 2) × Fin k → Kf := fun u => if u = (vL s, c₁) ∨ u = (cL s, c₁) then 1 else 0
  have hfv : f v = 0 := by
    rcases hv with rfl | rfl
    · simp [f, c₁, hne, Ne.symm hl0]
    · have : (cL s, lastC k) ≠ (vL s, 0) := fun h => hne (congrArg Prod.fst h).symm
      simp [f, c₁, this, hl0]
  have hfh : eval f (hP (vL s) (cL s) : LPol (Fin (n' * 2)) k Kf) = 1 := by
    simp only [hP, map_sum, map_mul, eval_X, f, Prod.mk.injEq, hne, hne.symm, false_and, or_false, true_and,
      false_or]
    simp
  have := congrArg (eval f) hr
  rw [hfh, map_mul, eval_X, hfv, zero_mul] at this
  exact one_ne_zero this

omit [NeZero k] in
/-- **Cancelling `x_0` or `y_{k−1}` modulo the pairing**: they are prime and do not divide it. -/
theorem mem_span_of_X_mul {s : Fin n'} {v : Fin (n' * 2) × Fin k}
    (hv : ¬ (X v ∣ (hP (vL s) (cL s) : LPol (Fin (n' * 2)) k Kf))) {H : LPol (Fin (n' * 2)) k Kf}
    (h : X v * H ∈ Ideal.span {hP (vL s) (cL s)}) : H ∈ Ideal.span {(hP (vL s) (cL s) : LPol _ k Kf)} := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h
  have hdvd : X v ∣ q * hP (vL s) (cL s) := ⟨H, hq⟩
  rcases (X_prime (σ := Fin (n' * 2) × Fin k) (R := Kf) (i := v)).dvd_or_dvd hdvd with ⟨q', rfl⟩ | h'
  · refine Ideal.mem_span_singleton'.2 ⟨q', mul_left_cancel₀ (X_ne_zero v) ?_⟩
    rw [← hq]; ring
  · exact absurd h' hv

omit [NeZero k] in
/-- **Cancelling powers of `x_0` or `y_{k−1}` modulo the pairing.** -/
theorem mem_span_of_pow_mul {s : Fin n'} {v : Fin (n' * 2) × Fin k}
    (hv : ¬ (X v ∣ (hP (vL s) (cL s) : LPol (Fin (n' * 2)) k Kf))) (e : ℕ) {H : LPol (Fin (n' * 2)) k Kf}
    (h : X v ^ e * H ∈ Ideal.span {hP (vL s) (cL s)}) : H ∈ Ideal.span {(hP (vL s) (cL s) : LPol _ k Kf)} := by
  induction e with
  | zero => simpa using h
  | succ e ih => exact ih (mem_span_of_X_mul hv (by rw [← mul_assoc, ← pow_succ']; exact h))

omit [NeZero k] in
/-- **Scaling the covector letter of `s` by `Λ`** multiplies a polynomial of degree `d` by `Λ^{d_y}`. -/
theorem chi_eq (s : Fin n') (Λ : LPol (Fin (n' * 2)) k Kf) {d : Fin (n' * 2) → ℕ} {G : LPol (Fin (n' * 2)) k Kf}
    (hG : G ∈ LHom Kf d) : aeval (fun v : Fin (n' * 2) × Fin k => if v.1 = cL s then Λ * X v else X v) G =
      Λ ^ d (cL s) * G := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hG
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hw := hG (mem_support_iff.1 hμ)
  rw [aeval_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, MvPolynomial.algebraMap_eq]
  have e1 : ∀ v ∈ μ.support, (if v.1 = cL s then Λ * X v else X v) ^ μ v =
      (if v.1 = cL s then Λ ^ μ v else 1) * X v ^ μ v := fun v _ => by
    split_ifs <;> simp [mul_pow]
  rw [Finset.prod_congr rfl e1, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_pow_eq_pow_sum]
  have e2 : ∑ v ∈ μ.support with v.1 = cL s, μ v = d (cL s) := by
    rw [← hw, LetterFock.weight_rowW_apply, Finset.sum_filter,
      Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by rw [Finsupp.notMem_support_iff.1 hv]; simp),
      Fintype.sum_prod_type, Finset.sum_eq_single (cL s) (fun t _ ht => by simp [ht]) (by simp)]
    simp
  rw [e2]
  ring

variable [CharZero Kf]

omit [NeZero k] in
/-- **A harmonic multiple of the pairing vanishes** (homogeneous components, `eq_zero_of_lapP_hP`). -/
theorem eq_zero_of_mem_span (hk : 3 ≤ k) (s : Fin n') {d : Fin (n' * 2) → ℕ} {G : LPol (Fin (n' * 2)) k Kf}
    (hG : G ∈ LHom Kf d) (hh : lapP (vL s) (cL s) G = 0) (hI : G ∈ Ideal.span {hP (vL s) (cL s)}) : G = 0 := by
  classical
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hI
  have hpe := hP_mem (K := Kf) (k := k) (vL s) (cL s)
  have hGc : weightedHomogeneousComponent (LetterFock.rowW (Fin (n' * 2)) k) d (q * hP (vL s) (cL s)) =
      q * hP (vL s) (cL s) := by
    rw [LHom, mem_weightedHomogeneousSubmodule] at hG
    exact weightedHomogeneousComponent_eq_self hG
  rw [mul_comm q] at hGc hh ⊢
  by_cases hle : pe (vL s) (cL s) ≤ d
  · obtain ⟨D, rfl⟩ : ∃ D, d = D + pe (vL s) (cL s) := ⟨d - pe (vL s) (cL s), (tsub_add_cancel_of_le hle).symm⟩
    rw [comp_mul_of_mem hpe] at hGc
    set q' := weightedHomogeneousComponent (LetterFock.rowW (Fin (n' * 2)) k) D q
    have hq' : q' ∈ LHom Kf D := by
      rw [LHom, mem_weightedHomogeneousSubmodule]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    obtain ⟨d₀, i, rfl, h0⟩ := chain_form (pairs.ne s s) D
    rw [← hGc] at hh ⊢
    rw [eq_zero_of_lapP_hP (by omega) (pairs.ne s s) h0 hq' hh, mul_zero]
  · rw [comp_mul_eq_zero hpe hle] at hGc
    exact hGc.symm

/-- **The substitution at one position is injective on harmonic polynomials**: modulo the pairing it is
the scaling by `Λ`, `Λ` cancels, and harmonic multiples of the pairing vanish. -/
theorem eq_zero_of_phiS_single (hk : 3 ≤ k) (s : Fin n') {d : Fin (n' * 2) → ℕ} {G : LPol (Fin (n' * 2)) k Kf}
    (hG : G ∈ LHom Kf d) (hh : lapP (vL s) (cL s) G = 0) (hφ : phiS {s} G = 0) : G = 0 := by
  set I : Ideal (LPol (Fin (n' * 2)) k Kf) := Ideal.span {hP (vL s) (cL s)}
  set Λ : LPol (Fin (n' * 2)) k Kf := X (vL s, 0) * X (cL s, lastC k) ^ (k - 3)
  have hq : (Ideal.Quotient.mkₐ Kf I).comp (phiS {s}) = (Ideal.Quotient.mkₐ Kf I).comp
      (aeval fun v : Fin (n' * 2) × Fin k => if v.1 = cL s then Λ * X v else X v) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨t, c⟩ := v
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    by_cases hts : t = cL s
    · subst hts
      rw [phiS_cL_mem (Finset.mem_singleton_self s), ite_eq_left rfl, Ideal.Quotient.eq, Yc_eq hk]
      refine Ideal.mem_span_singleton'.2 ⟨-(if c = 0 then X (cL s, lastC k) ^ (k - 3) else 0), ?_⟩
      split_ifs <;> ring
    · rw [ite_eq_right hts]
      congr 1
      rcases letter_cases t with h | h <;> rw [h]
      · exact phiS_vL _ _ _
      · exact phiS_cL_not (fun hm => hts (by rw [h, Finset.mem_singleton.1 hm])) _
  have h1 := congrArg (fun φ => φ G) hq
  simp only [AlgHom.comp_apply, hφ, map_zero, chi_eq s Λ hG, Ideal.Quotient.mkₐ_eq_mk] at h1
  have h2 : Λ ^ d (cL s) * G ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
  have hv1 := not_X_dvd_hP (Kf := Kf) (k := k) (by omega) s (v := (vL s, 0)) (Or.inl rfl)
  have hv2 := not_X_dvd_hP (Kf := Kf) (k := k) (by omega) s (v := (cL s, lastC k)) (Or.inr rfl)
  rw [mul_pow, ← pow_mul, mul_assoc] at h2
  exact eq_zero_of_mem_span hk s hG hh (mem_span_of_pow_mul hv2 _ (mem_span_of_pow_mul hv1 _ h2))

/-- **The flat model is injective on polynomials harmonic at every position** (I4's kernel statement):
`ev∘β` is the substitution at every position, one position at a time. -/
theorem eq_zero_of_beta (hk : 3 ≤ k) {d : Fin (n' * 2) → ℕ} {G : LPol (Fin (n' * 2)) k Kf}
    (hG : G ∈ LHom Kf d) (hh : ∀ s, lapP (vL s) (cL s) G = 0) (hβ : beta Kf G = 0) : G = 0 := by
  have key : ∀ S : Finset (Fin n'), ∀ (d : Fin (n' * 2) → ℕ) (G : LPol (Fin (n' * 2)) k Kf), G ∈ LHom Kf d →
      (∀ s ∈ S, lapP (vL s) (cL s) G = 0) → phiS S G = 0 → G = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro d G _ _ h; rwa [phiS_empty] at h
    | insert s S hs ih =>
      intro d G hG hh h
      rw [phiS_insert hk hs, AlgHom.comp_apply] at h
      have hG' := phiS_single_mem hk s hG
      have hh' : ∀ t ∈ S, lapP (vL t) (cL t) (phiS {s} G) = 0 := fun t ht => by
        rw [lapP_phiS hk (fun e : s = t => hs (by rw [e]; exact ht)), hh t (Finset.mem_insert_of_mem ht),
          map_zero]
      exact eq_zero_of_phiS_single hk s hG (hh s (Finset.mem_insert_self s S)) (ih _ _ hG' hh' h)
  refine key Finset.univ d G hG (fun s _ => hh s) ?_
  rw [phiS_univ, AlgHom.comp_apply, hβ, map_zero]

end Kernel

end

end TwoLetter
