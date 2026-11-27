import SymbolData

/-!
# The generic translate and the twisted exponents (H1 of T3)

The weights of the generic twisted substitution `SymbolData.twistSub`: its `T`-exponents at the column `c` are the
`c`-th coordinates of the weights of the *generic translate* `gtr` (H1 of the T3 spec), so `val_S` and `top_S` are
read off the weights of one polynomial, `gtr F`.

**Conventions** (those of `SymbolData`). Letters `ι` with flags `vec` and `n` columns; polynomials in
`MvPolynomial (ι × Fin n) R`; `GenCoeff ι R n` the letter polynomials over `R[g]`, `g` the generic matrix (`genMat`).
The *weight* of a variable for the action through the letters of `S` (`twWt`) is `e_c` for a vector letter of `S`,
`−e_c` for a covector letter of `S` and `0` otherwise; a monomial has the sum of the weights of its variables
(`Finsupp.weight twWt`). The *generic translate* through `S` (`gtr`) substitutes `x_l ↦ x_l·adj(g)` (a vector letter
`l ∈ S`, a row) and `x_l ↦ g·x_l` (a covector letter, a column) and fixes the other letters; `gcomp ν F` is the
weight-`ν` component of `gtr F`.

**Main results.**
* *The factorisation* (`twistSub_eq_comp`): `twistSub_c = ρ ∘ δ_c ∘ gtr`, where `δ_c` (`tsc`) multiplies a monomial of
  weight `ν` by `T^{ν_c}` and `ρ` (`rho`) substitutes `x ↦ x·g`, `η ↦ adj(g)·η` on the letters of `S` (vector letters
  compose in order, `g·D_c·adj g`; covector letters in reverse order, `g·D_c⁻¹·adj g`). Hence the coefficient of `T^e`
  is `ρ` of the part of `gtr F` whose weights have `c`-th coordinate `e` (`coeff_twistSub`).
* *(H1)* Every twisted exponent at `c` is `ν_c` for a weight `ν` of `gtr F`, over every commutative ring
  (`twistExps_subset`); over a domain they are exactly these (`twistExps_eq`): `ρ'∘ρ` with `ρ'` the translate on
  `GenCoeff` multiplies each variable of a letter of `S` by `det g` (`rho'_comp_rho`), injective over a domain
  (`scal_injective`). So `θ ≤ val_S F` iff every weight `ν` of `gtr F` has `θ ≤ ν_{n−1}` (`le_valS_iff`), and
  `top_S F ≤ M` iff every weight has `ν_0 ≤ M` (`topS_le_iff`); one direction holds over every ring (`le_valS_of`,
  `topS_le_of`).
-/

namespace TwistWeights

open MvPolynomial Finset

noncomputable section

/-! ## Two generic substitutions: the `T`-scaling by a weight and a diagonal scaling -/

section Generic

variable {σ A : Type*} [CommRing A]

/-- **The `T`-scaling by a weight** `w`: `X_v ↦ T^{w v}·X_v`, a Laurent polynomial over the polynomials. -/
def tscale (w : σ → ℤ) : MvPolynomial σ A →+* LaurentPolynomial (MvPolynomial σ A) :=
  eval₂Hom (LaurentPolynomial.C.comp MvPolynomial.C) fun v => LaurentPolynomial.C (X v) * LaurentPolynomial.T (w v)

/-- **A product of powers of `T`** is the power of the sum. -/
theorem prod_T {B : Type*} [CommSemiring B] {τ : Type*} (s : Finset τ) (f : τ → ℤ) :
    ∏ v ∈ s, (LaurentPolynomial.T (f v) : LaurentPolynomial B) = LaurentPolynomial.T (∑ v ∈ s, f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LaurentPolynomial.T_zero]
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, LaurentPolynomial.T_add]

/-- **The `T`-scaling of a monomial**: `T^{weight}` times the monomial. -/
theorem tscale_monomial (w : σ → ℤ) (u : σ →₀ ℕ) (a : A) :
    tscale w (monomial u a) =
      LaurentPolynomial.C (monomial u a) * LaurentPolynomial.T (Finsupp.weight w u) := by
  rw [tscale, coe_eval₂Hom, eval₂_monomial, Finsupp.weight_apply, monomial_eq, map_mul, Finsupp.prod, Finsupp.prod,
    Finsupp.sum, map_prod, ← prod_T, mul_assoc, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun v _ => ?_
  rw [mul_pow, map_pow, LaurentPolynomial.T_pow, nsmul_eq_mul]

/-- **The coefficient of `T^e` of the `T`-scaling** is the weight-`e` component. -/
theorem coeff_tscale (w : σ → ℤ) (p : MvPolynomial σ A) (e : ℤ) :
    (tscale w p).coeff e = weightedHomogeneousComponent w e p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [tscale_monomial, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial w u a rfl)]
    simp only [eq_comm]
  | add p q hp hq => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, map_add]

/-- **The diagonal scaling** `X_v ↦ d_v·X_v` by constants `d_v`. -/
def scal (d : σ → A) : MvPolynomial σ A →+* MvPolynomial σ A :=
  eval₂Hom MvPolynomial.C fun v => MvPolynomial.C (d v) * X v

/-- **The coefficients of a diagonal scaling**: `coeff_u (scal d p) = coeff_u p · ∏_v d_v^{u_v}`. -/
theorem coeff_scal (d : σ → A) (p : MvPolynomial σ A) (u : σ →₀ ℕ) :
    (scal d p).coeff u = p.coeff u * u.prod fun v k => d v ^ k := by
  classical
  have hmono : ∀ (u' : σ →₀ ℕ) (a : A), scal d (monomial u' a) = monomial u' (a * u'.prod fun v k => d v ^ k) := by
    intro u' a
    rw [scal, coe_eval₂Hom, eval₂_monomial, monomial_eq, map_mul, mul_assoc]
    congr 1
    simp only [Finsupp.prod, mul_pow, prod_mul_distrib, map_prod, map_pow]
  induction p using MvPolynomial.induction_on' with
  | monomial u' a =>
    rw [hmono, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq,
      add_mul]

/-- **A diagonal scaling by non-zero constants is injective** over a domain. -/
theorem scal_injective [IsDomain A] {d : σ → A} (hd : ∀ v, d v ≠ 0) : Function.Injective (scal d) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  ext u
  have h := coeff_scal d p u
  have hu : (u.prod fun v k => d v ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hd v)
  rw [hp] at h
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h ⊢
  exact (mul_eq_zero.1 h.symm).resolve_right hu

/-- **A component is non-zero** iff some monomial of the support has that weight. -/
theorem weightedHomogeneousComponent_ne_zero_iff {M : Type*} [AddCommMonoid M] (w : σ → M) (m : M)
    (p : MvPolynomial σ A) :
    weightedHomogeneousComponent w m p ≠ 0 ↔ ∃ u ∈ p.support, Finsupp.weight w u = m := by
  classical
  rw [Ne, ← support_eq_empty, support_weightedHomogeneousComponent, ← Ne, ← nonempty_iff_ne_empty]
  simp only [Finset.Nonempty, mem_filter]

/-- **A coordinate of a vector weight** is the weight of the coordinate. -/
theorem weight_apply_coord {τ : Type*} (w : σ → τ → ℤ) (u : σ →₀ ℕ) (c : τ) :
    Finsupp.weight (fun v => w v c) u = Finsupp.weight w u c := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  rfl

end Generic

/-! ## The generic translate -/

section Translate

variable {ι R : Type*} [CommRing R] {n : ℕ}

open Classical in
/-- **The weight of a variable** for the action through the letters of `S`: `e_c` (vector letter of `S`), `−e_c`
(covector letter of `S`), `0` (other letters). The `Set` version of `ChainData.letWt`. -/
def twWt (vec : ι → Bool) (S : Set ι) (v : ι × Fin n) : Fin n → ℤ :=
  if v.1 ∈ S then (if vec v.1 then Pi.single v.2 1 else -Pi.single v.2 1) else 0

variable (R n) in
/-- **The generic matrix** `g` over `R[g]`. -/
def genMat : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) := Matrix.of fun a b => X (a, b)

open Classical in
/-- **The generic translate** through `S`: `x_l ↦ x_l·adj(g)` (vector letter of `S`), `x_l ↦ g·x_l` (covector letter
of `S`), other letters fixed. -/
def gtr (vec : ι → Bool) (S : Set ι) : MvPolynomial (ι × Fin n) R →+* SymbolData.GenCoeff ι R n :=
  eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun v =>
    if v.1 ∈ S then
      (if vec v.1 then ∑ b, X (v.1, b) * MvPolynomial.C ((genMat R n).adjugate b v.2)
       else ∑ b, MvPolynomial.C (genMat R n v.2 b) * X (v.1, b))
    else X v

/-- **The weight-`ν` component of the generic translate.** -/
def gcomp (vec : ι → Bool) (S : Set ι) (ν : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) :
    SymbolData.GenCoeff ι R n :=
  weightedHomogeneousComponent (twWt vec S) ν (gtr vec S F)

open Classical in
/-- **The back substitution** `ρ` on `GenCoeff`: `x_l ↦ x_l·g` (vector letter of `S`), `x_l ↦ adj(g)·x_l` (covector
letter of `S`), other letters fixed. -/
def rho (vec : ι → Bool) (S : Set ι) : SymbolData.GenCoeff ι R n →+* SymbolData.GenCoeff ι R n :=
  eval₂Hom MvPolynomial.C fun v =>
    if v.1 ∈ S then
      (if vec v.1 then ∑ b, X (v.1, b) * MvPolynomial.C (genMat R n b v.2)
       else ∑ b, MvPolynomial.C ((genMat R n).adjugate v.2 b) * X (v.1, b))
    else X v

open Classical in
/-- **The translate on `GenCoeff`**: `x_l ↦ x_l·adj(g)` (vector letter of `S`), `x_l ↦ g·x_l` (covector letter of
`S`), other letters fixed. -/
def rho' (vec : ι → Bool) (S : Set ι) : SymbolData.GenCoeff ι R n →+* SymbolData.GenCoeff ι R n :=
  eval₂Hom MvPolynomial.C fun v =>
    if v.1 ∈ S then
      (if vec v.1 then ∑ b, X (v.1, b) * MvPolynomial.C ((genMat R n).adjugate b v.2)
       else ∑ b, MvPolynomial.C (genMat R n v.2 b) * X (v.1, b))
    else X v

open Classical in
/-- **`ρ'∘ρ` multiplies the variables of the letters of `S` by `det g`.** -/
theorem rho'_comp_rho (vec : ι → Bool) (S : Set ι) :
    (rho' vec S).comp (rho vec S) =
      scal (fun v : ι × Fin n => if v.1 ∈ S then (genMat R n).det else 1) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun v => ?_
  · simp [rho, rho', scal]
  · obtain ⟨l, a⟩ := v
    have hC' : ∀ r, rho' (n := n) vec S (MvPolynomial.C r : SymbolData.GenCoeff ι R n) = MvPolynomial.C r :=
      fun r => by simp [rho']
    have hX' : ∀ b, rho' vec S (X (l, b) : SymbolData.GenCoeff ι R n) = if l ∈ S then
        (if vec l then ∑ b', X (l, b') * MvPolynomial.C ((genMat R n).adjugate b' b)
         else ∑ b', MvPolynomial.C (genMat R n b b') * X (l, b')) else X (l, b) := fun b => by simp [rho']
    simp only [RingHom.comp_apply, rho, scal, coe_eval₂Hom, eval₂_X]
    by_cases hS : l ∈ S
    · by_cases hv : vec l
      · simp only [hS, hv, ite_true]
        simp only [map_sum, map_mul, hX', hC', hS, hv, ite_true]
        simp only [Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [← map_mul, ← Finset.mul_sum, ← map_sum]
        have e : ∀ b', ∑ b, (genMat R n).adjugate b' b * genMat R n b a =
            if b' = a then (genMat R n).det else 0 := fun b' => by
          rw [← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
          split_ifs <;> simp
        simp only [e]
        rw [Finset.sum_eq_single a (fun b _ hb => by rw [ite_eq_right_iff.2 fun h => absurd h hb, map_zero, mul_zero])
          (by simp), ite_eq_left_iff.2 fun h => absurd rfl h, mul_comm]
      · simp only [hS, hv, Bool.false_eq_true, ite_true, ite_false]
        simp only [map_sum, map_mul, hX', hC', hS, hv, Bool.false_eq_true, ite_true, ite_false]
        simp only [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp only [← map_mul, ← Finset.sum_mul, ← map_sum]
        have e : ∀ b', ∑ b, (genMat R n).adjugate a b * genMat R n b b' =
            if a = b' then (genMat R n).det else 0 := fun b' => by
          rw [← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
          split_ifs <;> simp
        simp only [e]
        rw [Finset.sum_eq_single a (fun b _ hb => by
          rw [ite_eq_right_iff.2 fun h => absurd h.symm hb, map_zero, zero_mul]) (by simp),
          ite_eq_left_iff.2 fun h => absurd rfl h]
    · simp [hS, hX']

/-- **`ρ` is injective over a domain.** -/
theorem rho_injective [IsDomain R] (vec : ι → Bool) (S : Set ι) : Function.Injective (rho (n := n) (R := R) vec S) := by
  classical
  have h : Function.Injective ((rho' vec S).comp (rho (n := n) (R := R) vec S)) := by
    rw [rho'_comp_rho]
    refine scal_injective fun v => ?_
    split_ifs
    · exact Matrix.det_mvPolynomialX_ne_zero (Fin n) R
    · exact one_ne_zero
  exact fun a b hab => h (by rw [RingHom.comp_apply, RingHom.comp_apply, hab])

end Translate

/-! ## The factorisation of the twisted substitution and (H1) -/

section H1

variable {ι R : Type*} [CommRing R] {n : ℕ}

/-- **Mapping the coefficients of a constant Laurent polynomial.** -/
theorem mapRingHom_C {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C]
  ext k
  simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

/-- **Mapping the coefficients fixes the powers of `T`.** -/
theorem mapRingHom_T {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (k : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  ext j
  simp only [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- **The `T`-scaling of a variable.** -/
theorem tscale_X {σ A : Type*} [CommRing A] (w : σ → ℤ) (v : σ) :
    tscale (A := A) w (X v) = LaurentPolynomial.C (X v) * LaurentPolynomial.T (w v) := by
  simp [tscale]

/-- **The `T`-scaling of a constant.** -/
theorem tscale_C {σ A : Type*} [CommRing A] (w : σ → ℤ) (a : A) :
    tscale (σ := σ) w (C a) = LaurentPolynomial.C (C a) := by
  simp [tscale]

/-- **The adjugate of the generic matrix over the Laurent polynomials** is the image of the adjugate. -/
theorem gL_adj : (Matrix.of fun a b => LaurentPolynomial.C (MvPolynomial.C (X (a, b))) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial (SymbolData.GenCoeff ι R n))).adjugate =
      Matrix.of fun a b => LaurentPolynomial.C (MvPolynomial.C ((genMat R n).adjugate a b)) := by
  have h := RingHom.map_adjugate (R := MvPolynomial (Fin n × Fin n) R)
    (S := LaurentPolynomial (SymbolData.GenCoeff ι R n)) (LaurentPolynomial.C.comp MvPolynomial.C) (genMat R n)
  have e : (RingHom.mapMatrix (LaurentPolynomial.C.comp MvPolynomial.C) (genMat R n) :
      Matrix (Fin n) (Fin n) (LaurentPolynomial (SymbolData.GenCoeff ι R n))) =
        Matrix.of fun a b => LaurentPolynomial.C (MvPolynomial.C (X (a, b))) := by
    ext a b; simp [genMat]
  rw [e] at h
  rw [← h]
  ext a b; simp

/-- **The `T`-scaling at the column `c`** (`δ_c`): a monomial of weight `ν` times `T^{ν_c}`. -/
def tsc (vec : ι → Bool) (S : Set ι) (c : Fin n) :
    SymbolData.GenCoeff ι R n →+* LaurentPolynomial (SymbolData.GenCoeff ι R n) :=
  tscale fun v => twWt vec S v c

/-- **The factorisation** `twistSub_c = ρ ∘ δ_c ∘ gtr`. -/
theorem twistSub_eq_comp (vec : ι → Bool) (S : Set ι) (c : Fin n) :
    SymbolData.twistSub (R := R) vec S c =
      (AddMonoidAlgebra.mapRingHom ℤ (rho vec S)).comp ((tsc vec S c).comp (gtr vec S)) := by
  classical
  have hrC : ∀ r, rho (n := n) vec S (MvPolynomial.C r : SymbolData.GenCoeff ι R n) = MvPolynomial.C r :=
    fun r => by simp [rho]
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun v => ?_
  · simp [SymbolData.twistSub, gtr, tsc, tscale_C, mapRingHom_C, hrC]
  obtain ⟨l, a⟩ := v
  have hrX : ∀ b, rho (n := n) (R := R) vec S (X (l, b)) = if l ∈ S then
      (if vec l then ∑ b', X (l, b') * MvPolynomial.C (genMat R n b' b)
       else ∑ b', MvPolynomial.C ((genMat R n).adjugate b b') * X (l, b')) else X (l, b) := fun b => by simp [rho]
  simp only [SymbolData.twistSub, coe_eval₂Hom, eval₂_X, RingHom.comp_apply, gtr]
  by_cases hS : l ∈ S
  · by_cases hv : vec l
    · simp only [hS, hv, ite_true, map_sum, map_mul, tsc, tscale_X, tscale_C, mapRingHom_C, mapRingHom_T, hrX, hrC,
        gL_adj, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      have hD : (if b = c then LaurentPolynomial.T 1 else 1 : LaurentPolynomial (SymbolData.GenCoeff ι R n)) =
          LaurentPolynomial.T (twWt vec S (l, b) c) := by
        by_cases h : b = c
        · subst h; simp [twWt, hS, hv]
        · simp [twWt, hS, hv, h, Ne.symm h, LaurentPolynomial.T_zero]
      rw [Finset.sum_eq_single b (fun i _ hi => by rw [Matrix.diagonal_apply_ne _ hi]; ring) (by simp),
        Matrix.diagonal_apply_eq, hD]
      simp only [genMat, Matrix.of_apply]
      ring
    · simp only [hS, hv, Bool.false_eq_true, ite_true, ite_false, map_sum, map_mul, tsc, tscale_X, tscale_C,
        mapRingHom_C, mapRingHom_T, hrX, hrC, gL_adj, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      have hD : (if b = c then LaurentPolynomial.T (-1) else 1 : LaurentPolynomial (SymbolData.GenCoeff ι R n)) =
          LaurentPolynomial.T (twWt vec S (l, b) c) := by
        by_cases h : b = c
        · subst h; simp [twWt, hS, hv]
        · simp [twWt, hS, hv, h, Ne.symm h, LaurentPolynomial.T_zero]
      rw [Finset.sum_eq_single b (fun i _ hi => by rw [Matrix.diagonal_apply_ne _ hi]; ring) (by simp),
        Matrix.diagonal_apply_eq, hD]
      simp only [genMat, Matrix.of_apply]
      ring
  · simp [hS, tsc, tscale_X, mapRingHom_C, hrX, twWt, LaurentPolynomial.T_zero]

/-- **The coefficient of `T^e`** of the twisted substitution at `c`: `ρ` of the part of `gtr F` whose weights have
`c`-th coordinate `e`. -/
theorem coeff_twistSub (vec : ι → Bool) (S : Set ι) (c : Fin n) (F : MvPolynomial (ι × Fin n) R) (e : ℤ) :
    (SymbolData.twistSub vec S c F).coeff e =
      rho vec S (weightedHomogeneousComponent (fun v => twWt vec S v c) e (gtr vec S F)) := by
  rw [twistSub_eq_comp]
  simp only [RingHom.comp_apply, AddMonoidAlgebra.coeff_mapRingHom]
  rw [tsc, coeff_tscale]

/-- **The `c`-component is non-zero** iff some weight `ν` of `gtr F` with `ν_c = e` has a non-zero component. -/
theorem comp_coord_ne_zero_iff (vec : ι → Bool) (S : Set ι) (c : Fin n) (F : MvPolynomial (ι × Fin n) R) (e : ℤ) :
    weightedHomogeneousComponent (fun v => twWt vec S v c) e (gtr vec S F) ≠ 0 ↔
      ∃ ν : Fin n → ℤ, ν c = e ∧ gcomp vec S ν F ≠ 0 := by
  rw [weightedHomogeneousComponent_ne_zero_iff]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨Finsupp.weight (twWt vec S) u, by rw [← weight_apply_coord, he], ?_⟩
    exact (weightedHomogeneousComponent_ne_zero_iff _ _ _).2 ⟨u, hu, rfl⟩
  · rintro ⟨ν, hνc, hν⟩
    obtain ⟨u, hu, hw⟩ := (weightedHomogeneousComponent_ne_zero_iff _ _ _).1 hν
    exact ⟨u, hu, by rw [weight_apply_coord, hw, hνc]⟩

/-- **(H1, inclusion; any ring)** every twisted exponent at `c` is `ν_c` for a weight `ν` of the generic translate. -/
theorem twistExps_subset (vec : ι → Bool) (S : Set ι) (c : Fin n) (F : MvPolynomial (ι × Fin n) R) :
    (SymbolData.twistExps vec S c F : Set ℤ) ⊆ {e | ∃ ν : Fin n → ℤ, ν c = e ∧ gcomp vec S ν F ≠ 0} := by
  intro e he
  rw [Finset.mem_coe, SymbolData.twistExps, Finsupp.mem_support_iff, coeff_twistSub] at he
  exact (comp_coord_ne_zero_iff vec S c F e).1 fun h => he (by rw [h, map_zero])

/-- **(H1, equality; domains)** `ρ` is injective (`det g` is a non-zero-divisor). -/
theorem twistExps_eq [IsDomain R] (vec : ι → Bool) (S : Set ι) (c : Fin n)
    (F : MvPolynomial (ι × Fin n) R) :
    (SymbolData.twistExps vec S c F : Set ℤ) = {e | ∃ ν : Fin n → ℤ, ν c = e ∧ gcomp vec S ν F ≠ 0} := by
  refine (twistExps_subset vec S c F).antisymm fun e he => ?_
  rw [Finset.mem_coe, SymbolData.twistExps, Finsupp.mem_support_iff, coeff_twistSub]
  have h := (comp_coord_ne_zero_iff vec S c F e).2 he
  exact fun h' => h ((map_eq_zero_iff _ (rho_injective vec S)).1 h')

variable [NeZero n]

/-- **A lower bound for `val_S`** from the weights of `gtr F` (any ring). -/
theorem le_valS_of (vec : ι → Bool) (S : Set ι) (F : MvPolynomial (ι × Fin n) R) (θ : ℤ)
    (h : ∀ ν, gcomp vec S ν F ≠ 0 → θ ≤ ν (LetterFock.lastC n)) : (θ : WithTop ℤ) ≤ SymbolData.valS vec S F := by
  refine Finset.le_min fun e he => ?_
  obtain ⟨ν, hν, h0⟩ := twistExps_subset vec S _ F (Finset.mem_coe.2 he)
  exact WithTop.coe_le_coe.2 (hν ▸ h ν h0)

/-- **An upper bound for `top_S`** from the weights of `gtr F` (any ring). -/
theorem topS_le_of (vec : ι → Bool) (S : Set ι) (F : MvPolynomial (ι × Fin n) R) (M : ℤ)
    (h : ∀ ν, gcomp vec S ν F ≠ 0 → ν 0 ≤ M) : SymbolData.topS vec S F ≤ (M : WithBot ℤ) := by
  refine Finset.max_le fun e he => ?_
  obtain ⟨ν, hν, h0⟩ := twistExps_subset vec S _ F (Finset.mem_coe.2 he)
  exact WithBot.coe_le_coe.2 (hν ▸ h ν h0)

/-- **`θ ≤ val_S F`** iff every weight `ν` of `gtr F` has `θ ≤ ν_{n−1}` (domains). -/
theorem le_valS_iff [IsDomain R] (vec : ι → Bool) (S : Set ι) (F : MvPolynomial (ι × Fin n) R) (θ : ℤ) :
    (θ : WithTop ℤ) ≤ SymbolData.valS vec S F ↔ ∀ ν, gcomp vec S ν F ≠ 0 → θ ≤ ν (LetterFock.lastC n) := by
  refine ⟨fun h ν hν => ?_, le_valS_of vec S F θ⟩
  have he : ν (LetterFock.lastC n) ∈ SymbolData.twistExps vec S (LetterFock.lastC n) F := by
    rw [← Finset.mem_coe, twistExps_eq]
    exact ⟨ν, rfl, hν⟩
  exact WithTop.coe_le_coe.1 ((Finset.le_min_iff.1 h) _ he)

/-- **`top_S F ≤ M`** iff every weight `ν` of `gtr F` has `ν_0 ≤ M` (domains). -/
theorem topS_le_iff [IsDomain R] (vec : ι → Bool) (S : Set ι) (F : MvPolynomial (ι × Fin n) R) (M : ℤ) :
    SymbolData.topS vec S F ≤ (M : WithBot ℤ) ↔ ∀ ν, gcomp vec S ν F ≠ 0 → ν 0 ≤ M := by
  refine ⟨fun h ν hν => ?_, topS_le_of vec S F M⟩
  have he : ν 0 ∈ SymbolData.twistExps vec S 0 F := by
    rw [← Finset.mem_coe, twistExps_eq]
    exact ⟨ν, rfl, hν⟩
  exact WithBot.coe_le_coe.1 ((Finset.max_le_iff.1 h) _ he)

end H1

end

end TwistWeights
