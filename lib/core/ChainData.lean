import SymbolData
import GlRep

/-!
# Chain data, the level map, the joint projectors and the membership condition

The shared definitions of the test side of the second local theorem (L6), written once for its pieces N13 (the flat
test), N14 (membership) and N15 (the chain Gram estimate): the `gl_n` action on letter polynomials as a `GlRep`, the
true and model letters of the chain model, the model map `φ`, the digit split `dig_ρ`, the chain, link and model sets,
the chain data with the conditions `𝒳`, `𝒴_{a,b}` and `H(C)` and its constants, the chain data tied to a frame system,
the level map, the joint projectors and the membership condition `Mem(σc, σL, L)`.

**Conventions** (those of `LetterFock`, `LocalOrbit` and `SymbolData`).
* *The action* (`letterRep`). On letter polynomials `LPol α n K` (`n` columns), `gl_n` acts through a finite set `S`
  of letters by `E_{ab} = Σ_{l ∈ S} letE vec l a b` (`letES`): `X_{l,a}∂_{l,b}` on vector letters, `−X_{l,b}∂_{l,a}` on
  covector letters. The weight of `X_v` is `e_c` for a vector letter `v = (l, c)`, `l ∈ S`, `−e_c` for a covector
  letter, `0` off `S` (`letWt`); the weight projections are the weighted homogeneous components. Each multidegree
  component `LHom K d` is finite-dimensional and stable (`finiteDimensional_LHom`, `letterRep_stable`), so
  `GlRep.typeProj` applies to it (`typeProjOn`).
* *Segments* are indexed by `ZMod J`; a segment `j` is read in the frame system through its representative
  `j.val ∈ [0, J)`, and the previous segment is `j − 1` in `ZMod J`.
* *True letters* (`TrueL J nL r = Σ j, Fin (nL j) ⊕ Fin r`): the loose letter `⟨j, inl l⟩` is the `l`-th loose letter
  of the segment `j` (`looseAt`), the frame row `⟨j, inr m⟩` sits at `f j (r − 1 − m)`: `m = 0` is the frame end
  `z j`. Its index in the chain order of the segment is `l`, resp. `nL j + (r − 1 − m)` (`chainIdx`), so the `u`-th
  late letter of `LocalOrbit` (`lateAt j u`) is the true letter of chain index `u`. Loose letters carry the flag of
  their parity, frame rows are vector letters (`trueVec`).
* *Model letters* (`ModelL`, T5's names): `loose j l`; for each frame row `t = (j, m)`: `dig t`, `crs t` (the row `t`
  as a W-letter of the segment `j + 1`) and `tan t` (`tan (j, 0)` unused). The model map `φ` (`modelMap`) sends
  `loose ↦ loose`, `dig t, tan t ↦ X_t` and `crs t ↦ X_t^{P_t}`, `P_t = p^{gP t}`.
* *Digit split* `dig_ρ` (`digSplit`): keep the monomials whose frame-row exponents are `≡ ρ (mod P_t)`; put the loose
  exponents on `loose` and `⌊e/P_t⌋` on `crs t`.
* *Sets.* `W(j) = {crs(j − 1, m)}` (`wSet`); chain sets `Ch(j, i) = W(j) ∪ {loose(j, l) : l < i}`, `i ≤ nL j`
  (`chSet`: the rows before the `i`-th late letter); model link sets
  `Y(j, m) = W(j) ∪ {loose of j} ∪ {tan(j, m′) : m′ > m}` (`ySet`); true link sets
  `T(j, m) = {loose of j} ∪ {(j, m′) : m′ > m}` (`tSet`: the late letters before `f j (r − 1 − m)`), `m ≤ r − 2`.
* *Thresholds* are real and read through `⌈θ⌉ ≤ val_S` (`SymbolData.valS`, plane columns `n = r`).

**Chain data** (`ChainData J r`: only what the conditions read): `nL`, the flags of the loose letters, the frame
jumps `gP`, the plane degrees `d`, the chain thresholds `th`, the chain slacks `sl`, the link thresholds `thl` and the
level `c`. The conditions: `IsX` (`𝒳`: multidegree `d`; `val_{Ch(j,i)}(dig_ρ F) ≥ th(j, i)` for all `ρ`, `j`,
`i ≤ nL j`; `val_{T(j,m)}(F) ≥ thl(j, m)` for `m ≤ r − 2`), `IsY a b` (`𝒴_{a,b}`: no `tan(j, 0)`;
`val_{Ch(j,i)} G ≥ th − sl − a·c`; `val_{Y(j,m)} G ≥ thl − b·c`), `HCond C` (`H(C)`:
`r·Σ_l d(j, l)/P_{(j,m)} + C·r·c ≤ sl(j + 1, i)`). The constants: `ℓ(n) = log_p(n + r) + 1` (`ell`),
`e₁ = r²ℓ(2Σd)`, `D_m = (Σ_j (nL j + 1))·e₁`, `D_l = J(r − 1)·e₁`, `κ_p = Σ_x r·ℓ(d x)`, `n₀ = v_p(∏_x d_x!)/2`, in
`p`-adic units (`v(p) = 1`).

**Tied chain data** (`ofFrames`): for a frame system, a joint normal type `κ`, plane degrees `dPl` and slacks
`(σc, σL, L)`: `J` frames, `nL j = #loose j`, flags = parity, `d = dPl`, `gP(j, m) = z_{j+1} − z_j`,
`th(j, i) = θ*(j, i) − σc·slack(j, x_i) − L` at the `i`-th late letter `x_i`,
`thl(j, m) = θ*(j, u) − σL·slack(j, x_u) − L` at `u = nL j + (r − 1 − m)` (the row `f j (r − 1 − m)`); `sl` and `c` are
free. The sub-spec's "tied" is `Mem(1/8, 3/8, 0)`.

**The level map** (`lev`, frame-free: letters `T` with positions `pos : T → Fin n′` and periods `P : T → ℕ`; `DigitFock`
should reuse it): the monomials `X^μ` with `μ(pos x, c) ≡ ρ(x, c) (mod P x)`, `Σ_{a<r} ⌊μ(pos x, a)/P x⌋ = dPl x` and
`Σ_{b<K} ⌊μ(pos x, r + b)/P x⌋ = dNo x` at every letter go to `Y^{q_pl} ⊗ Z^{q_no}`, a polynomial in the plane variables
with coefficients in the normal ring. `coeffPl ν e H` applies `e` to the coefficients and takes their `Z^ν`-coefficient.

**Joint projectors** (`jointProj`): for a joint normal type `κ_{j,u}` (`u ≤ nL j + r`), the product over `(j, u)` of
the type projectors `GlRep.typeProj` onto `{κ_{j,u}}` for the `GL_K`-actions through the first `u` late letters of the
segment `j` (`initSet`), taken on the multidegree component of each monomial and extended linearly. The factors are
composed in the order of `Finset.toList`; they commute (nested or disjoint letter sets, `GlRep.typeProj_comm_typeProj`),
which the membership piece proves. **Membership** (`Mem σc σL L G`): for every joint type `κ`, digit pattern `ρ`,
block degrees `dP`, `dN` and normal monomial `ν`, `coeffPl ν (jointProj κ) (lev ρ dP dN G)` satisfies `𝒳` of the chain
data tied with `(κ, dP, σc, σL, L)`; the sub-spec's six variants are `Mem` at different `(σc, σL, L)`.

**Readings of the planning statements.** Segments are `ZMod J` (the sub-spec's `ℤ/J`), with `[NeZero J]` where a
finite sum or a finite product over them is taken. The chain sets are fixed to "frame rows and the loose letters
`l < i`" (`nch j = nL j + 1`) as in every reader's use; `γ` (the digit units of the twisted form) is not read by the
conditions and is left to the Gram estimate. The constants are real (`ℓ` with the real `log_p`), the valuation unit is
`v(p) = 1`.
-/

namespace ChainData

open MvPolynomial Finset LetterFock LocalOrbit SymbolData

noncomputable section

/-! ## The `gl_n` action on letter polynomials -/

section LetterRep

variable {α K : Type*} [Field K] [DecidableEq α] {n : ℕ}

/-- **The weight of a variable** for the action through the letters of `S`: `e_c` at a vector letter, `−e_c` at a
covector letter, `0` off `S`. -/
def letWt (vec : α → Bool) (S : Finset α) (v : α × Fin n) : Fin n → ℤ :=
  if v.1 ∈ S then (if vec v.1 then Pi.single v.2 1 else -Pi.single v.2 1) else 0

variable (K) in
/-- **`E_{ab}` through the letters of `S`**: `Σ_{l ∈ S} letE vec l a b`. -/
def letES (vec : α → Bool) (S : Finset α) (a b : Fin n) : Derivation K (LPol α n K) (LPol α n K) :=
  ∑ l ∈ S, letE vec l a b

/-- **`E_{ab}` on a generator.** -/
theorem letES_X (vec : α → Bool) (S : Finset α) (a b : Fin n) (v : α × Fin n) :
    letES K vec S a b (X v) = if v.1 ∈ S then (if vec v.1 then (if v.2 = b then X (v.1, a) else 0)
      else -(if v.2 = a then X (v.1, b) else 0)) else 0 := by
  obtain ⟨l, e⟩ := v
  rw [letES, derivation_sum_apply]
  simp only [letE_X]
  by_cases hS : l ∈ S
  · rw [Finset.sum_eq_single l, ite_eq_left hS]
    · simp [Prod.ext_iff]
    · intro l' _ hl'
      simp [Prod.ext_iff, Ne.symm hl']
    · intro h
      exact absurd hS h
  · rw [ite_eq_right hS]
    refine Finset.sum_eq_zero fun l' hl' => ?_
    have : l ≠ l' := fun h => hS (h ▸ hl')
    simp [Prod.ext_iff, this]

/-- **The commutation relations** `[E_{ab}, E_{cd}] = δ_{bc}E_{ad} − δ_{da}E_{cb}`, checked on the generators. -/
theorem letES_comm (vec : α → Bool) (S : Finset α) (a b c d : Fin n) :
    ⁅letES K vec S a b, letES K vec S c d⁆ =
      (if b = c then letES K vec S a d else 0) - (if d = a then letES K vec S c b else 0) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply, Derivation.sub_apply]
  by_cases hS : l ∈ S
  · by_cases hv : vec l
    · simp only [letES_X, hS, hv, ite_true]
      split_ifs <;> simp_all [letES_X] <;> first | (intro h; simp_all) | (split_ifs <;> simp_all)
    · simp only [letES_X, hS, hv, ite_true, Bool.false_eq_true, ite_false]
      split_ifs <;> simp_all [letES_X]
  · simp only [letES_X, hS, ite_false]
    split_ifs <;> simp [letES_X, hS]

/-- **Derivations shifting weights**: if `D X_v` is weighted homogeneous of weight `w v + δ` for every `v`, `D` maps
weight `μ` to weight `μ + δ` (on monomials through `mkDerivation`). -/
theorem isWH_derivation {σ M : Type*} [AddCommMonoid M] {w : σ → M} {δ : M}
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (hD : ∀ v, IsWeightedHomogeneous w (D (X v)) (w v + δ)) {P : MvPolynomial σ K} {μ : M}
    (hP : IsWeightedHomogeneous w P μ) : IsWeightedHomogeneous w (D P) (μ + δ) := by
  have hDm : D = mkDerivation K fun v => D (X v) := derivation_ext fun v => by rw [mkDerivation_X]
  rw [P.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [hDm, mkDerivation_monomial, Finsupp.sum]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => ?_)
  rw [mem_weightedHomogeneousSubmodule, smul_eq_mul]
  have hw : Finsupp.weight w s = μ := hP (mem_support_iff.1 hs)
  have hsi : Finsupp.weight w (s - Finsupp.single i 1) + w i = μ := by
    rw [← hw]
    conv_rhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.2
      (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)))]
    rw [map_add, Finsupp.weight_single, one_smul]
  have h := (isWeightedHomogeneous_monomial w (s - Finsupp.single i 1) ((s i : ℕ) : K) rfl).mul (hD i)
  rwa [← add_assoc, hsi] at h

/-- **`E_{ab}` shifts the weight by `e_a − e_b`.** -/
theorem letES_X_isWH (vec : α → Bool) (S : Finset α) (a b : Fin n) (v : α × Fin n) :
    IsWeightedHomogeneous (letWt vec S) (letES K vec S a b (X v))
      (letWt vec S v + (Pi.single a 1 - Pi.single b 1)) := by
  obtain ⟨l, e⟩ := v
  rw [letES_X]
  by_cases hS : l ∈ S
  · by_cases hv : vec l
    · simp only [hS, hv, ite_true]
      split_ifs with he
      · subst he
        convert isWeightedHomogeneous_X K (letWt vec S) (l, a) using 1
        simp [letWt, hS, hv]
      · exact isWeightedHomogeneous_zero _ _ _
    · simp only [hS, hv, ite_true, Bool.false_eq_true, ite_false]
      split_ifs with he
      · subst he
        rw [← mem_weightedHomogeneousSubmodule]
        refine neg_mem ?_
        rw [mem_weightedHomogeneousSubmodule]
        convert isWeightedHomogeneous_X K (letWt vec S) (l, b) using 1
        simp only [letWt, hS, hv, ite_true, Bool.false_eq_true, ite_false]
        abel
      · rw [neg_zero]
        exact isWeightedHomogeneous_zero _ _ _
  · simp only [hS, ite_false]
    exact isWeightedHomogeneous_zero _ _ _

/-- **`E_{ab}` keeps the letter multidegree.** -/
theorem letES_X_isWH_row (vec : α → Bool) (S : Finset α) (a b : Fin n) (v : α × Fin n) :
    IsWeightedHomogeneous (rowW α n) (letES K vec S a b (X v)) (rowW α n v + 0) := by
  obtain ⟨l, e⟩ := v
  rw [letES_X, add_zero]
  have hX : ∀ c : Fin n, IsWeightedHomogeneous (rowW α n) (X (l, c) : LPol α n K) (rowW α n (l, e)) := fun c =>
    isWeightedHomogeneous_X K (rowW α n) (l, c)
  split_ifs
  all_goals first
    | exact hX _
    | exact isWeightedHomogeneous_zero _ _ _
    | (rw [← mem_weightedHomogeneousSubmodule]; exact neg_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (hX _)))
    | (rw [neg_zero]; exact isWeightedHomogeneous_zero _ _ _)

/-- **`E_{aa}` on a generator**: `letWt(v)_a·X_v`. -/
theorem letES_diag_X (vec : α → Bool) (S : Finset α) (a : Fin n) (v : α × Fin n) :
    letES K vec S a a (X v) = ((letWt vec S v a : ℤ) : K) • X v := by
  obtain ⟨l, e⟩ := v
  rw [letES_X, letWt]
  by_cases hS : l ∈ S <;> by_cases hv : vec l <;> rcases eq_or_ne e a with he | he <;>
    first | (subst he; simp [hS, hv]) | simp [hS, hv, he, he.symm]

/-- **`E_{aa}` on a weight vector** of weight `μ` is multiplication by `μ_a`. -/
theorem letES_diag_of_isWH (vec : α → Bool) (S : Finset α) (a : Fin n) {P : LPol α n K} {μ : Fin n → ℤ}
    (hP : IsWeightedHomogeneous (letWt vec S) P μ) : letES K vec S a a P = ((μ a : ℤ) : K) • P := by
  have hDm : letES K vec S a a = mkDerivation K fun v => ((letWt vec S v a : ℤ) : K) • X v :=
    derivation_ext fun v => by rw [mkDerivation_X, letES_diag_X]
  rw [hDm]
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw : Finsupp.weight (letWt vec S) s = μ := hP (mem_support_iff.1 hs)
  rw [mkDerivation_monomial, Finsupp.sum]
  have hterm : ∀ i ∈ s.support, monomial (s - Finsupp.single i 1) ((s i : ℕ) : K) •
      (((letWt vec S i a : ℤ) : K) • X i) = (((s i : ℕ) : K) * ((letWt vec S i a : ℤ) : K)) • monomial s (1 : K) := by
    intro i hi
    rw [smul_eq_mul, mul_smul_comm, X, monomial_mul_monomial, tsub_add_cancel_of_le (Finsupp.single_le_iff.2
      (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))), smul_monomial, smul_monomial]
    congr 1
    simp only [smul_eq_mul, mul_one]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ← hw, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
    smul_smul, smul_monomial, smul_monomial]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, mul_one, Int.cast_sum, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  ring

variable (K) in
/-- **The `gl_n` action on letter polynomials through the letters of `S`**, as a `GlRep`: the operators `letES`, the
weight projections the weighted homogeneous components for `letWt`. -/
def letterRep (vec : α → Bool) (S : Finset α) (n : ℕ) : GlRep K (LPol α n K) n where
  E a b := (letES K vec S a b : LPol α n K →ₗ[K] LPol α n K)
  comm a b c d := by
    refine LinearMap.ext fun F => ?_
    have h := congrArg (fun D : Derivation K (LPol α n K) (LPol α n K) => D F) (letES_comm vec S a b c d)
    simp only [Derivation.commutator_apply] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Derivation.coeFn_coe, h]
    split_ifs <;> simp
  comp μ := weightedHomogeneousComponent (letWt vec S) μ
  comp_mul μ ν := by
    refine LinearMap.ext fun F => ?_
    simp only [Module.End.mul_apply]
    split_ifs with h
    · subst h
      exact (weightedHomogeneousComponent_isWeightedHomogeneous _ _).weightedHomogeneousComponent_same
    · exact (weightedHomogeneousComponent_isWeightedHomogeneous _ _).weightedHomogeneousComponent_ne _ h
  exists_sum F := by
    classical
    refine ⟨F.support.image (Finsupp.weight (letWt vec S)), fun μ hμ => ?_, ?_⟩
    · ext s
      rw [coeff_weightedHomogeneousComponent, show (0 : LPol α n K).coeff s = 0 from rfl]
      split_ifs with h
      · by_contra hc
        exact hμ (mem_image.2 ⟨s, mem_support_iff.2 hc, h⟩)
      · rfl
    · ext s
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hc
        exact h (mem_image.2 ⟨s, mem_support_iff.2 fun h' => hc h'.symm, rfl⟩)
  diag_comp μ a := by
    refine LinearMap.ext fun F => ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
    exact letES_diag_of_isWH vec S a (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  comp_E μ a b := by
    refine LinearMap.ext fun F => ?_
    simp only [Module.End.mul_apply, Derivation.coeFn_coe]
    induction F using MvPolynomial.induction_on' with
    | add F G hF hG => simp only [map_add, hF, hG]
    | monomial s r =>
      have hm := isWeightedHomogeneous_monomial (letWt vec S) s r rfl
      have hE := isWH_derivation (letES K vec S a b) (letES_X_isWH vec S a b) hm
      by_cases h : Finsupp.weight (letWt vec S) s + (Pi.single a 1 - Pi.single b 1) = μ
      · rw [h] at hE
        rw [hE.weightedHomogeneousComponent_same,
          (isWeightedHomogeneous_monomial (letWt vec S) s r (eq_sub_of_add_eq h)).weightedHomogeneousComponent_same]
      · rw [hE.weightedHomogeneousComponent_ne _ (Ne.symm h),
          hm.weightedHomogeneousComponent_ne _ (fun h' => h (by rw [← h', sub_add_cancel])), map_zero]

variable [Fintype α]

/-- **The multidegree components are finite-dimensional**: inside the polynomials of degree `≤ Σ_l d_l` in each
variable. -/
instance finiteDimensional_LHom (d : α → ℕ) : FiniteDimensional K (LHom K d : Submodule K (LPol α n K)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := restrictDegree (α × Fin n) K (∑ l, d l)) fun F hF => ?_
  rw [mem_restrictDegree]
  intro s hs v
  rw [LHom, mem_weightedHomogeneousSubmodule] at hF
  have h := hF (mem_support_iff.1 hs)
  calc s v ≤ ∑ c, s (v.1, c) := Finset.single_le_sum (f := fun c => s (v.1, c)) (fun _ _ => Nat.zero_le _)
        (mem_univ v.2)
    _ = d v.1 := by rw [← weight_rowW_apply, h]
    _ ≤ ∑ l, d l := Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (mem_univ _)

omit [Fintype α] in
/-- **The multidegree components are stable** under the action through any set of letters. -/
theorem letterRep_stable (vec : α → Bool) (S : Finset α) (d : α → ℕ) :
    (letterRep K vec S n).Stable (LHom K d) := fun a b F hF => by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hF ⊢
  have h := isWH_derivation (letES K vec S a b) (letES_X_isWH_row vec S a b) hF
  rw [add_zero] at h
  exact h

variable [CharZero K]

/-- **The type projector on a multidegree component**: `GlRep.typeProj` onto the types `T` for the action through
`S`, on `LHom d` (along the other isotypic parts of `LHom d` and a complement). -/
def typeProjOn (vec : α → Bool) (S : Finset α) (d : α → ℕ) (T : Set (Fin n → ℤ)) : Module.End K (LPol α n K) :=
  (letterRep K vec S n).typeProj (W := LHom K d) (letterRep_stable vec S d) T

end LetterRep

/-! ## True and model letters -/

/-- **The true letters**: per segment `j`, the loose letters `inl l` and the frame rows `inr m`. -/
abbrev TrueL (J : ℕ) (nL : ZMod J → ℕ) (r : ℕ) := Σ j : ZMod J, Fin (nL j) ⊕ Fin r

/-- **The model letters**: the loose letters, and per frame row `(j, m)` the letters `dig`, `crs` (the row as a
W-letter of the segment `j + 1`) and `tan`. -/
inductive ModelL (J : ℕ) (nL : ZMod J → ℕ) (r : ℕ)
  /-- The loose letter `l` of the segment `j`. -/
  | loose (j : ZMod J) (l : Fin (nL j))
  /-- The digit copy of the frame row `(j, m)`. -/
  | dig (j : ZMod J) (m : Fin r)
  /-- The coarse copy of the frame row `(j, m)`. -/
  | crs (j : ZMod J) (m : Fin r)
  /-- The tangent copy of the frame row `(j, m)`. -/
  | tan (j : ZMod J) (m : Fin r)

section Letters

variable {J r : ℕ} {nL : ZMod J → ℕ}

/-- **The chain-order index** of a true letter in its segment: `l` for the loose letter `l`, `nL j + (r − 1 − m)` for
the frame row `m` (at `f j (r − 1 − m)`). -/
def chainIdx : TrueL J nL r → ℕ
  | ⟨_, .inl l⟩ => l.val
  | ⟨j, .inr m⟩ => nL j + (r - 1 - m.val)

/-- **The first `u` late letters of the segment `j`**, as true letters. -/
def initSet [NeZero J] (j : ZMod J) (u : ℕ) : Finset (TrueL J nL r) :=
  univ.filter fun x => x.1 = j ∧ chainIdx x < u

end Letters

end

end ChainData

/-! ## Chain data -/

open ChainData in
/-- **Chain data** of rank `r` with `J` segments: what the conditions `𝒳`, `𝒴` and `H` read. -/
structure ChainData (J r : ℕ) where
  /-- The number of loose letters of each segment. -/
  nL : ZMod J → ℕ
  /-- The flags of the loose letters (`true`: vector letter). -/
  vecL : (j : ZMod J) → Fin (nL j) → Bool
  /-- The frame jumps: `P_{(j,m)} = p^{gP j m}`. -/
  gP : ZMod J → Fin r → ℕ
  /-- The plane degrees of the true letters. -/
  d : TrueL J nL r → ℕ
  /-- The chain thresholds `th(j, i)`, `i ≤ nL j`. -/
  th : ZMod J → ℕ → ℝ
  /-- The chain slacks `sl(j, i)`. -/
  sl : ZMod J → ℕ → ℝ
  /-- The link thresholds `thl(j, m)`, `m ≤ r − 2`. -/
  thl : ZMod J → Fin r → ℝ
  /-- The level. -/
  c : ℕ

namespace ChainData

open MvPolynomial Finset LetterFock LocalOrbit SymbolData

noncomputable section

variable {J r : ℕ} (D : ChainData J r)

/-- **The flags of the true letters**: the loose letters by `vecL`, the frame rows vector letters. -/
def trueVec : TrueL J D.nL r → Bool
  | ⟨j, .inl l⟩ => D.vecL j l
  | ⟨_, .inr _⟩ => true

/-- **The flags of the model letters**: the loose letters by `vecL`, the copies of frame rows vector letters. -/
def modelVec : ModelL J D.nL r → Bool
  | .loose j l => D.vecL j l
  | _ => true

/-- **The period of a frame row** `P_{(j,m)} = p^{gP j m}`. -/
def P (p : ℕ) (j : ZMod J) (m : Fin r) : ℕ := p ^ D.gP j m

variable (R : Type*) [CommRing R]

/-- **The model map** `φ`: `loose ↦ loose`, `dig t, tan t ↦ X_t`, `crs t ↦ X_t^{P_t}`. -/
def modelMap (p : ℕ) : MvPolynomial (ModelL J D.nL r × Fin r) R →ₐ[R] MvPolynomial (TrueL J D.nL r × Fin r) R :=
  aeval fun v => match v.1 with
    | .loose j l => X (⟨j, .inl l⟩, v.2)
    | .dig j m => X (⟨j, .inr m⟩, v.2)
    | .crs j m => X (⟨j, .inr m⟩, v.2) ^ D.P p j m
    | .tan j m => X (⟨j, .inr m⟩, v.2)

/-- **The coarse model exponent** of a true exponent: the loose exponents on `loose`, `⌊e/P_t⌋` on `crs t`. -/
def liftExp (p : ℕ) (α : TrueL J D.nL r × Fin r →₀ ℕ) : ModelL J D.nL r × Fin r →₀ ℕ :=
  α.sum fun v e => match v.1 with
    | ⟨j, .inl l⟩ => Finsupp.single (.loose j l, v.2) e
    | ⟨j, .inr m⟩ => Finsupp.single (.crs j m, v.2) (e / D.P p j m)

/-- **The digit class `ρ`** of a true exponent: its frame-row exponents are `≡ ρ (mod P_t)`. -/
def DigitOK [NeZero J] (p : ℕ) (ρ : (ZMod J × Fin r) × Fin r → ℕ) (α : TrueL J D.nL r × Fin r →₀ ℕ) : Prop :=
  ∀ (j : ZMod J) (m a : Fin r), α (⟨j, .inr m⟩, a) % D.P p j m = ρ ((j, m), a)

open Classical in
/-- **The digit split** `dig_ρ`: the coarse part of `F` in the digit class `ρ`, in model letters. -/
def digSplit [NeZero J] (p : ℕ) (ρ : (ZMod J × Fin r) × Fin r → ℕ) (F : MvPolynomial (TrueL J D.nL r × Fin r) R) :
    MvPolynomial (ModelL J D.nL r × Fin r) R :=
  ∑ α ∈ F.support.filter (D.DigitOK p ρ), monomial (D.liftExp p α) (F.coeff α)

/-- **`W(j)`**: the coarse copies `crs(j − 1, m)` of the previous frame. -/
def wSet (j : ZMod J) : Set (ModelL J D.nL r) := {x | ∃ m, x = .crs (j - 1) m}

/-- **The chain set** `Ch(j, i) = W(j) ∪ {loose(j, l) : l < i}`. -/
def chSet (j : ZMod J) (i : ℕ) : Set (ModelL J D.nL r) :=
  D.wSet j ∪ {x | ∃ l : Fin (D.nL j), l.val < i ∧ x = .loose j l}

/-- **The model link set** `Y(j, m) = W(j) ∪ {loose of j} ∪ {tan(j, m′) : m′ > m}`. -/
def ySet (j : ZMod J) (m : Fin r) : Set (ModelL J D.nL r) :=
  D.wSet j ∪ {x | ∃ l, x = .loose j l} ∪ {x | ∃ m', m < m' ∧ x = .tan j m'}

/-- **The true link set** `T(j, m) = {loose of j} ∪ {(j, m′) : m′ > m}`. -/
def tSet (j : ZMod J) (m : Fin r) : Set (TrueL J D.nL r) :=
  {x | ∃ l, x = ⟨j, .inl l⟩} ∪ {x | ∃ m', m < m' ∧ x = ⟨j, .inr m'⟩}

variable [NeZero r]

/-- **`𝒳(F)`**: multidegree `d`; `val_{Ch(j,i)}(dig_ρ F) ≥ th(j, i)` for every digit class `ρ`, segment `j` and
`i ≤ nL j`; `val_{T(j,m)}(F) ≥ thl(j, m)` for `m ≤ r − 2`. -/
def IsX [NeZero J] (p : ℕ) (F : MvPolynomial (TrueL J D.nL r × Fin r) R) : Prop :=
  IsWeightedHomogeneous (rowW (TrueL J D.nL r) r) F D.d ∧
    (∀ ρ j (i : ℕ), i ≤ D.nL j → ((⌈D.th j i⌉ : ℤ) : WithTop ℤ) ≤ valS D.modelVec (D.chSet j i) (D.digSplit R p ρ F)) ∧
    ∀ j (m : Fin r), m.val + 2 ≤ r → ((⌈D.thl j m⌉ : ℤ) : WithTop ℤ) ≤ valS D.trueVec (D.tSet j m) F

/-- **`𝒴_{a,b}(G)`**: no `tan(j, 0)`; `val_{Ch(j,i)} G ≥ th − sl − a·c`; `val_{Y(j,m)} G ≥ thl − b·c` for
`m ≤ r − 2`. -/
def IsY (a b : ℝ) (G : MvPolynomial (ModelL J D.nL r × Fin r) R) : Prop :=
  (∀ μ ∈ G.support, ∀ j (a' : Fin r), μ (.tan j 0, a') = 0) ∧
    (∀ j (i : ℕ), i ≤ D.nL j →
      ((⌈D.th j i - D.sl j i - a * D.c⌉ : ℤ) : WithTop ℤ) ≤ valS D.modelVec (D.chSet j i) G) ∧
    ∀ j (m : Fin r), m.val + 2 ≤ r → ((⌈D.thl j m - b * D.c⌉ : ℤ) : WithTop ℤ) ≤ valS D.modelVec (D.ySet j m) G

/-- **`H(C)`**: `r·Σ_l d(j, l)/P_{(j,m)} + C·r·c ≤ sl(j + 1, i)` for every chain index `i ≤ nL (j + 1)`. -/
def HCond (p : ℕ) (C : ℝ) : Prop :=
  ∀ (j : ZMod J) (m : Fin r) (i : ℕ), i ≤ D.nL (j + 1) →
    r * (∑ l : Fin (D.nL j), (D.d ⟨j, .inl l⟩ : ℝ)) / D.P p j m + C * r * D.c ≤ D.sl (j + 1) i

/-- **`ℓ(n) = log_p(n + r) + 1`.** -/
def ell (p n : ℕ) : ℝ := Real.logb p (n + r) + 1

variable [NeZero J]

/-- **`e₁ = r²·ℓ(2Σ_x d_x)`**, one threshold projector's loss. -/
def e₁ (p : ℕ) : ℝ := (r : ℝ) ^ 2 * ell (r := r) p (2 * ∑ x, D.d x)

/-- **`D_m = (Σ_j (nL j + 1))·e₁`**, one projector per chain. -/
def Dm (p : ℕ) : ℝ := (∑ j, (D.nL j + 1 : ℝ)) * D.e₁ p

/-- **`D_l = J(r − 1)·e₁`**, one projector per link set. -/
def Dl (p : ℕ) : ℝ := J * ((r : ℝ) - 1) * D.e₁ p

/-- **`κ_p = Σ_x r·ℓ(d_x)`**, the bound of the multinomial valuations. -/
def κp (p : ℕ) : ℝ := ∑ x, (r : ℝ) * ell (r := r) p (D.d x)

/-- **`n₀ = v_p(∏_x d_x!)/2`.** -/
def n₀ (p : ℕ) : ℝ := (padicValNat p (∏ x, (D.d x).factorial) : ℝ) / 2

end

end ChainData

/-! ## Tied chain data, the level map, the joint projectors and membership -/

namespace LocalOrbit.FrameSys

open MvPolynomial Finset LetterFock SymbolData ChainData

noncomputable section

variable {n' r : ℕ} [NeZero n'] [NeZero r] (F : FrameSys n' r) (TT : Finset (Fin n'))

/-- **The true letters of a frame system**: `nL j = #loose j` for the segment `j.val`. -/
abbrev TrueLetter := TrueL F.J (fun j => F.nL TT j.val) r

/-- **The lifted position of a true letter**: the loose letter `l` at `looseAt j l`, the frame row `m` at
`f j (r − 1 − m)`. -/
def truePos : F.TrueLetter TT → ℤ
  | ⟨j, .inl l⟩ => F.looseAt TT j.val l
  | ⟨j, .inr m⟩ => F.f j.val ⟨r - 1 - m.val, by omega⟩

/-- **The chain data tied to the frames** for a joint normal type `κ`, plane degrees `dPl` and slacks
`(σc, σL, L)`: `th(j, i) = θ*(j, i) − σc·slack − L`, `thl(j, m) = θ*(j, nL j + r − 1 − m) − σL·slack − L`; `sl`, `c`
free. -/
def ofFrames {K : ℕ} [NeZero K] (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (mS : ℕ) (κ : ℤ → ℕ → Fin K → ℤ)
    (dPl : F.TrueLetter TT → ℕ) (σc σL L : ℝ) (sl : ZMod F.J → ℕ → ℝ) (c : ℕ) : ChainData F.J r where
  nL j := F.nL TT j.val
  vecL j l := decide (Even (F.looseAt TT j.val l))
  gP j _ := F.push (j.val + 1) (F.z j.val)
  d := dPl
  th j i := F.thrStar TT p deg (r + K) Y mS κ j.val i -
    σc * F.slack TT p deg (r + K) Y j.val (F.lateAt TT j.val i) - L
  sl := sl
  thl j m := F.thrStar TT p deg (r + K) Y mS κ j.val (F.nL TT j.val + (r - 1 - m.val)) -
    σL * F.slack TT p deg (r + K) Y j.val (F.lateAt TT j.val (F.nL TT j.val + (r - 1 - m.val))) - L
  c := c

end

end LocalOrbit.FrameSys

namespace ChainData

open MvPolynomial Finset LetterFock LocalOrbit SymbolData

noncomputable section

variable {n' r K : ℕ} (Kf : Type*) [Field Kf]

open Classical in
/-- **The level map** `lev_{ρ,dPl,dNo}` (frame-free: letters `T` at positions `pos` with periods `P`): the monomials of
`F` with digits `ρ` and coarse block degrees `(dPl, dNo)` at every letter, as plane monomials with coefficients in the
normal ring. -/
def lev {T : Type*} [Fintype T] (pos : T → Fin n') (P : T → ℕ) (ρ : T × Fin (r + K) → ℕ) (dPl dNo : T → ℕ)
    (F : MvPolynomial (Fin n' × Fin (r + K)) Kf) : MvPolynomial (T × Fin r) (MvPolynomial (T × Fin K) Kf) :=
  ∑ μ ∈ F.support.filter (fun μ => (∀ x c, μ (pos x, c) % P x = ρ (x, c)) ∧
      (∀ x, ∑ a : Fin r, μ (pos x, Fin.castAdd K a) / P x = dPl x) ∧
      ∀ x, ∑ b : Fin K, μ (pos x, Fin.natAdd r b) / P x = dNo x),
    monomial (Finsupp.equivFunOnFinite.symm fun v : T × Fin r => μ (pos v.1, Fin.castAdd K v.2) / P v.1)
      (monomial (Finsupp.equivFunOnFinite.symm fun v : T × Fin K => μ (pos v.1, Fin.natAdd r v.2) / P v.1)
        (F.coeff μ))

/-- **The plane coefficient** `coeff_ν(e·H) = Σ_β (e H_β)_ν·Y^β`. -/
def coeffPl {σ τ : Type*} (ν : τ →₀ ℕ) (e : Module.End Kf (MvPolynomial τ Kf))
    (H : MvPolynomial σ (MvPolynomial τ Kf)) : MvPolynomial σ Kf :=
  ∑ β ∈ H.support, monomial β ((e (H.coeff β)).coeff ν)

variable {J : ℕ} [NeZero J] {nL : ZMod J → ℕ} [CharZero Kf]

/-- **The index set of the joint projector**: `(j, u)` with `u ≤ nL j + r`. -/
abbrev JIdx (J : ℕ) (nL : ZMod J → ℕ) (r : ℕ) := Σ j : ZMod J, Fin (nL j + r + 1)

/-- **The joint projector on one multidegree component**: the product over `(j, u)` of the type projectors onto
`{κ_{j,u}}` for the `GL_K`-action through the first `u` late letters of `j`, on `LHom d`. -/
def projAt (vec : TrueL J nL r → Bool) (d : TrueL J nL r → ℕ) (κ : ZMod J → ℕ → Fin K → ℤ) :
    Module.End Kf (LPol (TrueL J nL r) K Kf) :=
  ((univ : Finset (JIdx J nL r)).toList).foldr (fun iu acc =>
    typeProjOn vec (initSet iu.1 iu.2) d {κ iu.1 iu.2} * acc) 1

/-- **The joint projector** `Π_κ`: `projAt` on the multidegree component of each monomial, extended linearly. -/
def jointProj (vec : TrueL J nL r → Bool) (κ : ZMod J → ℕ → Fin K → ℤ) : Module.End Kf (LPol (TrueL J nL r) K Kf) :=
  (basisMonomials (TrueL J nL r × Fin K) Kf).constr Kf fun s =>
    projAt Kf vec (Finsupp.weight (rowW (TrueL J nL r) K) s) κ (monomial s 1)

end

end ChainData

namespace LocalOrbit.FrameSys

open MvPolynomial Finset LetterFock SymbolData ChainData

noncomputable section

variable {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (F : FrameSys n' r) (TT : Finset (Fin n'))

/-- **Membership** `Mem(σc, σL, L)(G)`: for every joint normal type `κ`, digit pattern `ρ`, block degrees `dP`, `dN`
and normal monomial `ν`, the plane coefficient `coeff_ν(Π_κ·lev_{ρ,dP,dN}(G))` satisfies `𝒳` of the chain data tied
with `(κ, dP, σc, σL, L)`. -/
def Mem (Kf : Type*) [Field Kf] [CharZero Kf] [NeZero F.J] (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (mS : ℕ)
    (σc σL L : ℝ) (G : MvPolynomial (Fin n' × Fin (r + K)) Kf) : Prop :=
  ∀ (κ : ZMod F.J → ℕ → Fin K → ℤ) (ρ : F.TrueLetter TT × Fin (r + K) → ℕ) (dP dN : F.TrueLetter TT → ℕ)
    (ν : F.TrueLetter TT × Fin K →₀ ℕ),
    (F.ofFrames TT p deg Y mS (fun j u => κ (j : ZMod F.J) u) dP σc σL L 0 0).IsX Kf p
      (coeffPl Kf ν (jointProj Kf (F.ofFrames TT p deg Y mS (fun j u => κ (j : ZMod F.J) u) dP σc σL L 0 0).trueVec κ)
        (lev Kf (fun x => posOf n' (F.truePos TT x)) (fun x => p ^ F.push x.1.val (F.truePos TT x)) ρ dP dN G))

end

end LocalOrbit.FrameSys
