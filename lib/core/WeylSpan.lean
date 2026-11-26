import WeylFock

/-!
# Bideterminants span the dual Weyl module

For antitone `ν` and a field `L` of characteristic `0`, the bideterminants of shape `ν` span `∇_L(ν)`
(`span_bidet`): `∇_L(ν)` is the `L`-span of the products of minors on the leading columns, with arbitrary rows.
This is the second piece of `FormsLattice` (`lib/pnt/SharpInputs.lean`).

**Route** (a reproducing formula for the Fock form, no straightening). Write `⟨P, Q⟩ = Σ_d P_d Q_d d!` for the
bilinear Fock form (`fockWith (RingHom.id L)`), and `κ = ⟨hw_ν, hw_ν⟩`.
* *Adjointness* (`fock_lsub`): `⟨P(gᵀx), Q⟩ = ⟨P, Q(gx)⟩`, from `⟨P·x_q, Q⟩ = ⟨P, ∂_q Q⟩` (`fock_mul_X`) and the
  chain rule (`pderiv_lsub`).
* *The extreme weight* (`fock_hw`): for `G ∈ ∇(ν)`, `⟨hw_ν, G⟩ = κ·G(1)`. The monomials of `hw_ν` have row
  weight `ν` (`hw_isWH_row`), and the coefficients of `G` in row weight `ν` are `G(1)` times those of `hw_ν`
  (`coeff_eq_zero_of_eval_one`): for `G` with `G(1) = 0`, a monomial of row weight `ν` with nonzero coefficient
  and largest trace is not diagonal, so it has an entry above the diagonal, and the polarisation
  `Σ_a x_{τ,a,k} ∂_{τ,a,j}` (`k < j`), which kills `G` (`polar_eq_zero`, the derivative of the invariance),
  would not kill it.
* *Cauchy–Binet* (`lsub_hw`): `hw_ν(gᵀx) = Σ_rows bidet_rows(g)·x^{γ(rows)}`, a sum over the rows of the
  bideterminants of monomials `x^{γ(rows)}` (`crow`).

Then for `F ∈ ∇(ν)` and every point `g`: `κ·F(g) = ⟨hw_ν, F(g·)⟩ = ⟨hw_ν(gᵀ·), F⟩ =
Σ_rows bidet_rows(g)·⟨x^{γ(rows)}, F⟩`, so `κ·F = Σ_rows ⟨x^{γ(rows)}, F⟩·bidet_rows` (`MvPolynomial.funext`),
and `κ ≠ 0` (`fock_hw_hw_ne_zero`: `hw_ν` has rational coefficients and `κ` is a positive rational). Everything
is block-wise; the one-block case is `Φ = Unit`. The inclusion `span ⊆ ∇` (`bidet_mem_nabla`) is the invariance of
leading minors (`rsub_minor_rows`) and the degree count of `hw_mem_nabla`.
-/

namespace WeylFock

open MvPolynomial

/-! ## The bilinear Fock form -/

section Fock

variable {Φ : Type*} [Fintype Φ] {n : ℕ} {L : Type*} [Field L]

/-- The factorial `d! = ∏_p (d_p)!` of an exponent. -/
noncomputable def fact (d : Φ × Fin n × Fin n →₀ ℕ) : L := ∏ p, ((d p).factorial : L)

theorem fact_add_single (d : Φ × Fin n × Fin n →₀ ℕ) (q : Φ × Fin n × Fin n) :
    (fact (d + Finsupp.single q 1) : L) = fact d * ((d q : L) + 1) := by
  classical
  unfold fact
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q),
    ← Finset.mul_prod_erase Finset.univ (fun p => ((d p).factorial : L)) (Finset.mem_univ q)]
  have h : ∀ p ∈ Finset.univ.erase q,
      ((((d + Finsupp.single q 1 : Φ × Fin n × Fin n →₀ ℕ)) p).factorial : L) = ((d p).factorial : L) :=
    fun p hp => by rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hp), add_zero]
  rw [Finset.prod_congr rfl h, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

theorem fact_zero : (fact (0 : Φ × Fin n × Fin n →₀ ℕ) : L) = 1 := by simp [fact]

theorem fact_ne_zero [CharZero L] (d : Φ × Fin n × Fin n →₀ ℕ) : (fact d : L) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

/-- The bilinear Fock form, summed over any finite set containing the support of the second argument. -/
theorem fock_eq_sum_right {P Q : Pol Φ n L} {S : Finset (Φ × Fin n × Fin n →₀ ℕ)} (hS : Q.support ⊆ S) :
    fockWith (RingHom.id L) P Q = ∑ d ∈ S, P.coeff d * Q.coeff d * fact d := by
  unfold fockWith
  calc ∑ d ∈ Q.support, (RingHom.id L) (P.coeff d) * Q.coeff d * d.prod (fun _ k => (k.factorial : L))
      = ∑ d ∈ Q.support, P.coeff d * Q.coeff d * fact d := Finset.sum_congr rfl fun d _ => by
        rw [RingHom.id_apply, Finsupp.prod_fintype _ _ (fun _ => by simp)]
        rfl
    _ = _ := Finset.sum_subset hS fun d _ hd => by rw [notMem_support_iff.1 hd]; ring

theorem fock_comm (P Q : Pol Φ n L) : fockWith (RingHom.id L) P Q = fockWith (RingHom.id L) Q P := by
  rw [fock_eq_sum_right (S := P.support ∪ Q.support) Finset.subset_union_right,
    fock_eq_sum_right (S := P.support ∪ Q.support) Finset.subset_union_left]
  exact Finset.sum_congr rfl fun d _ => by ring

theorem fock_eq_sum_left {P Q : Pol Φ n L} {S : Finset (Φ × Fin n × Fin n →₀ ℕ)} (hS : P.support ⊆ S) :
    fockWith (RingHom.id L) P Q = ∑ d ∈ S, P.coeff d * Q.coeff d * fact d := by
  rw [fock_comm, fock_eq_sum_right hS]
  exact Finset.sum_congr rfl fun d _ => by ring

theorem fock_add_left (P P' Q : Pol Φ n L) :
    fockWith (RingHom.id L) (P + P') Q = fockWith (RingHom.id L) P Q + fockWith (RingHom.id L) P' Q := by
  simp [fock_eq_sum_right (P := _) (subset_refl Q.support), add_mul, Finset.sum_add_distrib]

theorem fock_smul_left (a : L) (P Q : Pol Φ n L) :
    fockWith (RingHom.id L) (a • P) Q = a * fockWith (RingHom.id L) P Q := by
  simp only [fock_eq_sum_right (P := _) (subset_refl Q.support), coeff_smul, smul_eq_mul, Finset.mul_sum,
    mul_assoc]

variable (L) in
/-- The Fock form as a linear form in its first argument. -/
noncomputable def fockL (Q : Pol Φ n L) : Pol Φ n L →ₗ[L] L where
  toFun P := fockWith (RingHom.id L) P Q
  map_add' P P' := fock_add_left P P' Q
  map_smul' a P := fock_smul_left a P Q

theorem fock_sum_left {ι : Type*} (s : Finset ι) (P : ι → Pol Φ n L) (Q : Pol Φ n L) :
    fockWith (RingHom.id L) (∑ i ∈ s, P i) Q = ∑ i ∈ s, fockWith (RingHom.id L) (P i) Q :=
  map_sum (fockL L Q) P s

theorem fock_C_mul_left (a : L) (P Q : Pol Φ n L) :
    fockWith (RingHom.id L) (C a * P) Q = a * fockWith (RingHom.id L) P Q := by
  rw [C_mul', fock_smul_left]

theorem fock_sum_right {ι : Type*} (s : Finset ι) (P : Pol Φ n L) (Q : ι → Pol Φ n L) :
    fockWith (RingHom.id L) P (∑ i ∈ s, Q i) = ∑ i ∈ s, fockWith (RingHom.id L) P (Q i) := by
  rw [fock_comm, fock_sum_left]
  exact Finset.sum_congr rfl fun i _ => fock_comm _ _

theorem fock_C_mul_right (a : L) (P Q : Pol Φ n L) :
    fockWith (RingHom.id L) P (C a * Q) = a * fockWith (RingHom.id L) P Q := by
  rw [fock_comm, fock_C_mul_left, fock_comm]

theorem fock_monomial (d : Φ × Fin n × Fin n →₀ ℕ) (a : L) (Q : Pol Φ n L) :
    fockWith (RingHom.id L) (monomial d a) Q = a * Q.coeff d * fact d := by
  classical
  rw [fock_eq_sum_left (support_monomial_subset), Finset.sum_singleton, coeff_monomial]
  simp

theorem fock_C (a : L) (Q : Pol Φ n L) : fockWith (RingHom.id L) (C a) Q = a * Q.coeff 0 := by
  rw [← monomial_zero', fock_monomial, fact_zero, mul_one]

/-- Multiplication by `x_q` is adjoint to `∂/∂x_q`. -/
theorem fock_mul_X (P Q : Pol Φ n L) (q : Φ × Fin n × Fin n) :
    fockWith (RingHom.id L) (P * X q) Q = fockWith (RingHom.id L) P (pderiv q Q) := by
  induction P using MvPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_mul, fock_add_left, fock_add_left, hp, hp']
  | monomial d a =>
    rw [X, monomial_mul_monomial, mul_one, fock_monomial, fock_monomial, coeff_pderiv, fact_add_single]
    ring

theorem fock_X_mul (P Q : Pol Φ n L) (q : Φ × Fin n × Fin n) :
    fockWith (RingHom.id L) P (X q * Q) = fockWith (RingHom.id L) (pderiv q P) Q := by
  rw [fock_comm, mul_comm, fock_mul_X, fock_comm]

theorem fock_add_right (P Q Q' : Pol Φ n L) :
    fockWith (RingHom.id L) P (Q + Q') = fockWith (RingHom.id L) P Q + fockWith (RingHom.id L) P Q' := by
  rw [fock_comm, fock_add_left, fock_comm, fock_comm Q']

end Fock

/-! ## Left substitution: the chain rule and the adjoint -/

section Subst

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

omit [Fintype Φ] in
/-- Membership in `∇(ν)`: column degrees `ν` and invariance under `x ↦ x·u`, `u` upper unitriangular. -/
theorem mem_nabla_iff {ν : Φ → Fin n → ℕ} {F : Pol Φ n L} :
    F ∈ nabla L ν ↔ IsWeightedHomogeneous (colW Φ n) F ν ∧
      ∀ u : Φ → Matrix (Fin n) (Fin n) L, (∀ σ, IsUni (u σ)) → rsub u F = F := by
  simp only [nabla, Submodule.mem_inf, mem_weightedHomogeneousSubmodule, Submodule.mem_iInf,
    LinearMap.mem_eqLocus, AlgHom.toLinearMap_apply, LinearMap.id_apply]

omit [Fintype Φ] [DecidableEq Φ] in
theorem lsub_X (g : Φ → Matrix (Fin n) (Fin n) L) (p : Φ × Fin n × Fin n) :
    lsub g (X p) = ∑ c, C (g p.1 p.2.1 c) * X (p.1, c, p.2.2) := by
  simp [lsub]

omit [Fintype Φ] [DecidableEq Φ] in
theorem rsub_X (u : Φ → Matrix (Fin n) (Fin n) L) (p : Φ × Fin n × Fin n) :
    rsub u (X p) = ∑ c, X (p.1, p.2.1, c) * C (u p.1 c p.2.2) := by
  simp [rsub]

omit [Fintype Φ] [DecidableEq Φ] in
theorem lsub_C (g : Φ → Matrix (Fin n) (Fin n) L) (a : L) : lsub g (C a) = C a := by
  simp [lsub]

omit [Fintype Φ] in
theorem pderiv_lsub_X (g : Φ → Matrix (Fin n) (Fin n) L) (τ : Φ) (a b : Fin n) (q : Φ × Fin n × Fin n) :
    pderiv (τ, a, b) (lsub g (X q)) = ∑ c, C (g τ c a) * lsub g (pderiv (τ, c, b) (X q)) := by
  obtain ⟨σ, a', b'⟩ := q
  rw [lsub_X]
  simp only [map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases hσ : σ = τ
  · subst hσ
    by_cases hb : b' = b
    · subst hb
      simp
    · simp [hb]
  · simp [hσ]

omit [Fintype Φ] in
/-- **The chain rule** for `F ↦ F(g·x)`: `∂_{τ,a,b}(F(g·x)) = Σ_c g_{τ,c,a} (∂_{τ,c,b}F)(g·x)`. -/
theorem pderiv_lsub (g : Φ → Matrix (Fin n) (Fin n) L) (τ : Φ) (a b : Fin n) (Q : Pol Φ n L) :
    pderiv (τ, a, b) (lsub g Q) = ∑ c, C (g τ c a) * lsub g (pderiv (τ, c, b) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p q hp =>
    rw [map_mul, pderiv_mul, hp, pderiv_lsub_X]
    simp only [pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring

omit [Fintype Φ] [DecidableEq Φ] in
theorem constantCoeff_lsub (g : Φ → Matrix (Fin n) (Fin n) L) (Q : Pol Φ n L) :
    constantCoeff (lsub g Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C x => rw [lsub_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p q hp => simp [hp, lsub_X]

/-- **Adjointness.** For the Fock form, `F ↦ F(gᵀ·x)` is adjoint to `F ↦ F(g·x)`. -/
theorem fock_lsub (g : Φ → Matrix (Fin n) (Fin n) L) (P Q : Pol Φ n L) :
    fockWith (RingHom.id L) (lsub (fun τ => (g τ).transpose) P) Q = fockWith (RingHom.id L) P (lsub g Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C x => rw [lsub_C, fock_C, fock_C, ← constantCoeff_eq, ← constantCoeff_eq, constantCoeff_lsub]
  | add p p' hp hp' => rw [map_add, fock_add_left, fock_add_left, hp, hp']
  | mul_X p q hp =>
    obtain ⟨τ, a, b⟩ := q
    rw [map_mul, lsub_X, Finset.mul_sum, fock_sum_left, fock_mul_X, pderiv_lsub, fock_sum_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_left_comm, fock_C_mul_left, fock_mul_X, hp, fock_C_mul_right, Matrix.transpose_apply]

omit [Fintype Φ] [DecidableEq Φ] in
/-- Left and right substitutions commute. -/
theorem rsub_lsub (u g : Φ → Matrix (Fin n) (Fin n) L) (P : Pol Φ n L) :
    rsub u (lsub g P) = lsub g (rsub u P) := by
  have h : (rsub u).comp (lsub g) = (lsub g).comp (rsub u) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp only [AlgHom.comp_apply, lsub_X, map_sum, map_mul, lsub_C, rsub, aeval_C, algebraMap_eq,
      aeval_X, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  exact DFunLike.congr_fun h P

omit [Fintype Φ] in
/-- `F ↦ F(g·x)` preserves the column degrees. -/
theorem lsub_isWH (g : Φ → Matrix (Fin n) (Fin n) L) {P : Pol Φ n L} {m : Φ → Fin n → ℕ}
    (hP : IsWeightedHomogeneous (colW Φ n) P m) : IsWeightedHomogeneous (colW Φ n) (lsub g P) m := by
  rw [P.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hX : ∀ p, IsWeightedHomogeneous (colW Φ n) (lsub g (X p)) (colW Φ n p) := fun p => by
    rw [lsub_X]
    exact IsWeightedHomogeneous.sum _ _ _ fun c _ =>
      (isWeightedHomogeneous_X L (colW Φ n) (p.1, c, p.2.2)).C_mul (g p.1 p.2.1 c)
  rw [← hP (mem_support_iff.1 hd), Finsupp.weight_apply, Finsupp.sum]
  have := (IsWeightedHomogeneous.prod d.support (fun p => lsub g (X p) ^ d p) _ fun p _ => (hX p).pow (d p)).C_mul
    (P.coeff d)
  convert this using 1
  rw [lsub, aeval_monomial, algebraMap_eq, Finsupp.prod]
  simp only [aeval_X]

omit [Fintype Φ] in
/-- `F ↦ F(g·x)` preserves `∇`. -/
theorem lsub_mem_nabla (g : Φ → Matrix (Fin n) (Fin n) L) {ν : Φ → Fin n → ℕ} {F : Pol Φ n L}
    (hF : F ∈ nabla L ν) : lsub g F ∈ nabla L ν := by
  rw [mem_nabla_iff] at hF ⊢
  exact ⟨lsub_isWH g hF.1, fun u hu => by rw [rsub_lsub, hF.2 u hu]⟩

variable (Φ n L) in
/-- The identity point: `x_τ = 1` for every `τ`. -/
def onePt : Φ × Fin n × Fin n → L := fun p => if p.2.1 = p.2.2 then 1 else 0

omit [Fintype Φ] [DecidableEq Φ] in
theorem eval_lsub (g : Φ → Matrix (Fin n) (Fin n) L) (P : Pol Φ n L) :
    eval (onePt Φ n L) (lsub g P) = eval (fun p => g p.1 p.2.1 p.2.2) P := by
  induction P using MvPolynomial.induction_on with
  | C x => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp => simp [hp, lsub_X, onePt]

end Subst

/-! ## Row and column weights, the diagonal monomial -/

section Weights

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

variable (Φ n) in
/-- The row weight: `x_{τ,a,b}` counts once in row `(τ, a)`. -/
def rowW : Φ × Fin n × Fin n → (Φ → Fin n → ℕ) := fun p => Pi.single p.1 (Pi.single p.2.1 1)

variable (Φ n) in
/-- The trace weight: `x_{τ,a,b}` counts once if `a = b`. -/
def trW : Φ × Fin n × Fin n → ℕ := fun p => if p.2.1 = p.2.2 then 1 else 0

theorem weight_colW_apply (d : Φ × Fin n × Fin n →₀ ℕ) (τ : Φ) (b : Fin n) :
    Finsupp.weight (colW Φ n) d τ b = ∑ a, d (τ, a, b) := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single τ (fun σ _ hσ => by simp [colW, Ne.symm hσ]) (by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single b (fun c _ hc => by simp [colW, Ne.symm hc]) (by simp)]
  simp [colW]

theorem weight_rowW_apply (d : Φ × Fin n × Fin n →₀ ℕ) (τ : Φ) (a : Fin n) :
    Finsupp.weight (rowW Φ n) d τ a = ∑ b, d (τ, a, b) := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single τ (fun σ _ hσ => by simp [rowW, Ne.symm hσ]) (by simp),
    Fintype.sum_prod_type, Finset.sum_eq_single a (fun c _ hc => by simp [rowW, Ne.symm hc])
      (by simp)]
  simp [rowW]

variable (Φ n) in
/-- The exponent of the diagonal monomial `∏_τ ∏_b x_{τ,b,b}^{ν_{τ,b}}`. -/
noncomputable def diagExp (ν : Φ → Fin n → ℕ) : Φ × Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if p.2.1 = p.2.2 then ν p.1 p.2.1 else 0

omit [DecidableEq Φ] in
theorem diagExp_apply (ν : Φ → Fin n → ℕ) (p : Φ × Fin n × Fin n) :
    diagExp Φ n ν p = if p.2.1 = p.2.2 then ν p.1 p.2.1 else 0 := rfl

/-- An exponent supported on the diagonal, of column weight `ν`, is the diagonal one. -/
theorem eq_diagExp_of_diag {ν : Φ → Fin n → ℕ} {d : Φ × Fin n × Fin n →₀ ℕ}
    (hd : ∀ p : Φ × Fin n × Fin n, p.2.1 ≠ p.2.2 → d p = 0) (hc : Finsupp.weight (colW Φ n) d = ν) :
    d = diagExp Φ n ν := by
  ext ⟨τ, a, b⟩
  rw [diagExp_apply]
  dsimp only
  split_ifs with hab
  · subst hab
    have := congrFun (congrFun hc τ) a
    rw [weight_colW_apply, Finset.sum_eq_single a (fun c _ hc => hd _ hc) (by simp)] at this
    exact this
  · exact hd _ hab

/-- An exponent of row and column weight `ν` with nothing above the diagonal is the diagonal one: the row
index and the column index have the same weighted sum `Σ_{τ,a} a·ν_{τ,a}`. -/
theorem eq_diagExp {ν : Φ → Fin n → ℕ} {d : Φ × Fin n × Fin n →₀ ℕ}
    (hr : Finsupp.weight (rowW Φ n) d = ν) (hc : Finsupp.weight (colW Φ n) d = ν)
    (hu : ∀ τ k j, k < j → d (τ, k, j) = 0) : d = diagExp Φ n ν := by
  have hsum : ∑ p : Φ × Fin n × Fin n, d p * (p.2.2 : ℕ) = ∑ p : Φ × Fin n × Fin n, d p * (p.2.1 : ℕ) := by
    have e1 : ∑ p : Φ × Fin n × Fin n, d p * (p.2.1 : ℕ) = ∑ τ, ∑ a : Fin n, (a : ℕ) * ν τ a := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hr, weight_rowW_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    have e2 : ∑ p : Φ × Fin n × Fin n, d p * (p.2.2 : ℕ) = ∑ τ, ∑ b : Fin n, (b : ℕ) * ν τ b := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hc, weight_colW_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [e1, e2]
  have hle : ∀ p ∈ (Finset.univ : Finset (Φ × Fin n × Fin n)), d p * (p.2.2 : ℕ) ≤ d p * (p.2.1 : ℕ) := by
    rintro ⟨τ, a, b⟩ _
    by_cases hab : a < b
    · simp [hu τ a b hab]
    · exact Nat.mul_le_mul_left _ (Fin.not_lt.1 hab)
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  refine eq_diagExp_of_diag (fun p hp => ?_) hc
  have := heq p (Finset.mem_univ _)
  rcases mul_eq_mul_left_iff.1 this with h | h
  · exact absurd (Fin.ext h.symm) hp
  · exact h

omit [DecidableEq Φ] in
theorem prod_onePt_eq_zero {d : Φ × Fin n × Fin n →₀ ℕ} {p : Φ × Fin n × Fin n} (hp : p.2.1 ≠ p.2.2)
    (hd : d p ≠ 0) : ∏ q, onePt Φ n L q ^ d q = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ p) (by simp [onePt, hp, hd])

/-- At the identity point, a polynomial of column weight `ν` takes the value of its diagonal coefficient. -/
theorem eval_one_eq_coeff {ν : Φ → Fin n → ℕ} {H : Pol Φ n L} (hH : IsWeightedHomogeneous (colW Φ n) H ν) :
    eval (onePt Φ n L) H = H.coeff (diagExp Φ n ν) := by
  rw [eval_eq', Finset.sum_eq_single (diagExp Φ n ν)]
  · rw [Finset.prod_eq_one fun p _ => ?_, mul_one]
    rw [diagExp_apply]
    split_ifs with h <;> simp [onePt, h]
  · intro d hd hne
    obtain ⟨p, hp, hdp⟩ : ∃ p : Φ × Fin n × Fin n, p.2.1 ≠ p.2.2 ∧ d p ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (eq_diagExp_of_diag (fun p hp => h p hp) (hH (mem_support_iff.1 hd)))
    rw [prod_onePt_eq_zero hp hdp, mul_zero]
  · intro h
    rw [notMem_support_iff.1 h, zero_mul]

omit [Fintype Φ] in
/-- `Σ_{i ≤ s} e_{castLE i} = 1_{≤ s}` in block `τ`. -/
theorem sum_single_castLE (τ : Φ) (s : Fin n) :
    (Pi.single τ fun b : Fin n => if (b : ℕ) ≤ s then 1 else 0) =
      ∑ i : Fin (s + 1), (Pi.single τ (Pi.single (Fin.castLE s.isLt i) 1) : Φ → Fin n → ℕ) := by
  funext σ b
  simp only [Finset.sum_apply]
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

omit [Fintype Φ] in
/-- A leading principal minor has degree one in the rows `(τ, a)`, `a ≤ s`. -/
theorem minor_isWH_row (τ : Φ) (s : Fin n) :
    IsWeightedHomogeneous (rowW Φ n) (minor τ s (Fin.castLE s.isLt) : Pol Φ n L)
      (Pi.single τ fun a => if (a : ℕ) ≤ s then 1 else 0) := by
  rw [minor, Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have h := IsWeightedHomogeneous.prod (R := L) (w := rowW Φ n) Finset.univ
    (fun i => (xMat τ).submatrix (Fin.castLE s.isLt) (Fin.castLE s.isLt) (σ i) i) _
    fun i _ => isWeightedHomogeneous_X L _ _
  convert h using 1
  rw [sum_single_castLE]
  exact (Equiv.sum_comp σ (fun i => (Pi.single τ (Pi.single (Fin.castLE s.isLt i) 1) : Φ → Fin n → ℕ))).symm

/-- The monomials of `hw_ν` have row weight `ν`. -/
theorem hw_isWH_row {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    IsWeightedHomogeneous (rowW Φ n) (hw L ν) ν := by
  have key : IsWeightedHomogeneous (rowW Φ n) (hw L ν)
      (∑ τ, ∑ s : Fin n, mult (ν τ) s • (Pi.single τ fun b : Fin n => if (b : ℕ) ≤ s then 1 else 0)) :=
    IsWeightedHomogeneous.prod _ _ _ fun τ _ => IsWeightedHomogeneous.prod _ _ _ fun s _ =>
      (minor_isWH_row τ s).pow _
  rwa [sum_mult hν] at key

omit [Fintype Φ] [DecidableEq Φ] in
theorem eval_one_minor (τ : Φ) (s : Fin n) : eval (onePt Φ n L) (minor τ s (Fin.castLE s.isLt)) = 1 := by
  rw [minor, RingHom.map_det]
  convert Matrix.det_one (R := L) (n := Fin (s + 1))
  ext i j
  simp [xMat, onePt, Matrix.one_apply, Fin.castLE_inj]

omit [DecidableEq Φ] in
/-- `hw_ν(1) = 1`. -/
theorem eval_one_hw (ν : Φ → Fin n → ℕ) : eval (onePt Φ n L) (hw L ν) = 1 := by
  simp [hw, map_prod, map_pow, eval_one_minor]

end Weights

/-! ## The derivative of the invariance: polarisations kill `∇` -/

section Polar

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

/-- The transvection `1 + t·e_{k,j}` in block `τ`, the identity in the others. -/
noncomputable def elem (τ : Φ) (k j : Fin n) (t : L) : Φ → Matrix (Fin n) (Fin n) L :=
  fun σ => if σ = τ then Matrix.transvection k j t else 1

omit [Fintype Φ] in
theorem isUni_elem (τ : Φ) {k j : Fin n} (hkj : k < j) (t : L) (σ : Φ) : IsUni (elem τ k j t σ) := by
  unfold elem
  split_ifs
  · refine ⟨Matrix.blockTriangular_transvection hkj.le t, fun a => ?_⟩
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
    split_ifs with h
    · exact absurd (h.1.trans h.2.symm) hkj.ne
    · exact add_zero 1
  · exact ⟨Matrix.blockTriangular_one, fun a => Matrix.one_apply_eq a⟩

/-- The coefficient of `T` in `x_q(x·(1 + T e_{k,j}))`, `1 + T e_{k,j}` in block `τ`: column `j` gains column `k`. -/
noncomputable def linT (τ : Φ) (k j : Fin n) (q : Φ × Fin n × Fin n) : Pol Φ n L :=
  if q.1 = τ ∧ q.2.2 = j then X (q.1, q.2.1, k) else 0

/-- The substitution `x ↦ x·(1 + T e_{k,j})` in block `τ`, with values in `Pol[T]`. -/
noncomputable def psi (τ : Φ) (k j : Fin n) : Pol Φ n L →ₐ[L] Polynomial (Pol Φ n L) :=
  aeval fun q => Polynomial.C (X q) + Polynomial.C (linT τ k j q) * Polynomial.X

omit [Fintype Φ] in
theorem rsub_elem_X (τ : Φ) (k j : Fin n) (t : L) (q : Φ × Fin n × Fin n) :
    rsub (elem τ k j t) (X q) = X q + linT τ k j q * C t := by
  obtain ⟨σ, a, b⟩ := q
  rw [rsub_X]
  simp only [elem, linT]
  by_cases hσ : σ = τ
  · subst hσ
    simp only [↓reduceIte, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add,
      mul_add, Finset.sum_add_distrib, true_and]
    by_cases hb : b = j
    · subst hb
      simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_ite, mul_one, mul_zero, map_one,
        map_zero, apply_ite C]
      rw [Finset.sum_eq_single k (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
      simp
    · simp [hb, Ne.symm hb]
  · simp [hσ, Matrix.one_apply]

omit [Fintype Φ] in
theorem eval_psi (τ : Φ) (k j : Fin n) (t : L) (P : Pol Φ n L) :
    (psi τ k j P).eval (C t) = rsub (elem τ k j t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [psi, rsub, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, rsub_elem_X]
    simp [psi]

omit [Fintype Φ] in
theorem psi_coeff_zero (τ : Φ) (k j : Fin n) (P : Pol Φ n L) : (psi τ k j P).coeff 0 = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [psi, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    simp [psi]

omit [Fintype Φ] in
theorem psi_X_coeff_one (τ : Φ) (k j : Fin n) (q : Φ × Fin n × Fin n) :
    (psi τ k j (X q : Pol Φ n L)).coeff 1 = linT τ k j q := by
  simp [psi, Polynomial.coeff_C]

omit [Fintype Φ] in
theorem sum_pderiv_X (τ : Φ) (k j : Fin n) (q : Φ × Fin n × Fin n) :
    ∑ a, X (τ, a, k) * pderiv (τ, a, j) (X q : Pol Φ n L) = linT τ k j q := by
  obtain ⟨σ, a', b'⟩ := q
  simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq, linT]
  by_cases hσ : σ = τ
  · subst hσ
    by_cases hb : b' = j
    · subst hb
      simp
    · simp [hb]
  · simp [hσ]

omit [Fintype Φ] in
/-- The coefficient of `T` in `F(x·(1 + T e_{k,j}))` is the polarisation `Σ_a x_{τ,a,k} ∂_{τ,a,j} F`. -/
theorem psi_coeff_one (τ : Φ) (k j : Fin n) (P : Pol Φ n L) :
    (psi τ k j P).coeff 1 = ∑ a, X (τ, a, k) * pderiv (τ, a, j) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [psi, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p q hp =>
    rw [map_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
      psi_coeff_zero, hp, psi_X_coeff_one, ← sum_pderiv_X τ k j q]
    simp only [pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun a _ => by ring

omit [Fintype Φ] in
/-- **Polarisations kill `∇`**: for `k < j` and `F ∈ ∇(ν)`, `Σ_a x_{τ,a,k} ∂_{τ,a,j} F = 0`, the derivative at
`t = 0` of `F(x·(1 + t e_{k,j})) = F(x)` (`L` is infinite). -/
theorem polar_eq_zero [CharZero L] {ν : Φ → Fin n → ℕ} {H : Pol Φ n L} (hH : H ∈ nabla L ν) (τ : Φ)
    {k j : Fin n} (hkj : k < j) : ∑ a, X (τ, a, k) * pderiv (τ, a, j) H = 0 := by
  have hinv : ∀ t : L, rsub (elem τ k j t) H = H := fun t => (mem_nabla_iff.1 hH).2 _ (isUni_elem τ hkj t)
  have h2 : psi τ k j H = Polynomial.C H := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (C_injective (Φ × Fin n × Fin n) L))
    rintro _ ⟨t, rfl⟩
    show Polynomial.eval (C t) (psi τ k j H) = Polynomial.eval (C t) (Polynomial.C H)
    rw [eval_psi, hinv, Polynomial.eval_C]
  rw [← psi_coeff_one, h2, Polynomial.coeff_C]
  simp

end Polar

/-! ## The extreme weight: `⟨hw_ν, G⟩ = κ·G(1)` -/

section Extreme

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

omit [Fintype Φ] [DecidableEq Φ] in
theorem fock_zero_right (P : Pol Φ n L) : fockWith (RingHom.id L) P 0 = 0 := by simp [fockWith]

/-- **The coefficients of row weight `ν`.** If `G ∈ ∇(ν)` vanishes at the identity, so do its coefficients of
row weight `ν`: a monomial of row weight `ν` in `G` of largest trace has an entry `(τ, k, j)` above the diagonal,
and the polarisation `Σ_a x_{τ,a,k} ∂_{τ,a,j}` of `G` would see it. -/
theorem coeff_eq_zero_of_eval_one [CharZero L] {ν : Φ → Fin n → ℕ} {H : Pol Φ n L} (hH : H ∈ nabla L ν)
    (h1 : eval (onePt Φ n L) H = 0) {d : Φ × Fin n × Fin n →₀ ℕ} (hd : Finsupp.weight (rowW Φ n) d = ν) :
    H.coeff d = 0 := by
  have hWH := (mem_nabla_iff.1 hH).1
  by_contra hne
  obtain ⟨d, hdT, hmax⟩ := Finset.exists_max_image (H.support.filter fun d => Finsupp.weight (rowW Φ n) d = ν)
    (Finsupp.weight (trW Φ n)) ⟨d, Finset.mem_filter.2 ⟨mem_support_iff.2 hne, hd⟩⟩
  rw [Finset.mem_filter, mem_support_iff] at hdT
  obtain ⟨hdH, hdr⟩ := hdT
  have hdiag : d ≠ diagExp Φ n ν := fun h => hdH (by rw [h, ← eval_one_eq_coeff hWH, h1])
  obtain ⟨τ, k, j, hkj, hdkj⟩ : ∃ τ k j, k < j ∧ d (τ, k, j) ≠ 0 := by
    by_contra h
    push Not at h
    exact hdiag (eq_diagExp hdr (hWH hdH) h)
  set d₀ := d - Finsupp.single (τ, k, j) 1
  have hd₀ : d₀ + Finsupp.single (τ, k, j) 1 = d := Finsupp.sub_add_single_one_cancel hdkj
  set β := d₀ + Finsupp.single (τ, k, k) 1 with hβ
  have hterm : ∀ a, fockWith (RingHom.id L) (monomial β 1) (X (τ, a, k) * pderiv (τ, a, j) H) =
      (β (τ, a, k) : L) * H.coeff (β - Finsupp.single (τ, a, k) 1 + Finsupp.single (τ, a, j) 1) *
        fact (β - Finsupp.single (τ, a, k) 1 + Finsupp.single (τ, a, j) 1) := fun a => by
    rw [fock_X_mul, ← fock_mul_X, pderiv_monomial, X, monomial_mul_monomial, fock_monomial]
    ring
  have key := congrArg (fockWith (RingHom.id L) (monomial β 1)) (polar_eq_zero hH τ hkj)
  rw [fock_sum_right, Finset.sum_congr rfl (fun a _ => hterm a), fock_zero_right] at key
  rw [Finset.sum_eq_single k ?_ (by simp)] at key
  · have hβk : β - Finsupp.single (τ, k, k) 1 + Finsupp.single (τ, k, j) 1 = d := by
      rw [hβ, add_tsub_cancel_right, hd₀]
    rw [hβk] at key
    have hβ0 : (β (τ, k, k) : L) ≠ 0 := Nat.cast_ne_zero.2 (by simp [hβ])
    exact mul_ne_zero (mul_ne_zero hβ0 hdH) (fact_ne_zero d) key
  · intro a _ hak
    by_cases hb : β (τ, a, k) = 0
    · simp [hb]
    set α := β - Finsupp.single (τ, a, k) 1 + Finsupp.single (τ, a, j) 1
    have hα : α + Finsupp.single (τ, a, k) 1 = β + Finsupp.single (τ, a, j) 1 := by
      rw [add_right_comm, Finsupp.sub_add_single_one_cancel hb]
    suffices H.coeff α = 0 by simp [this]
    by_contra hα0
    have hαr : Finsupp.weight (rowW Φ n) α = ν := by
      have h1 := congrArg (Finsupp.weight (rowW Φ n)) hα
      have h2 := congrArg (Finsupp.weight (rowW Φ n)) hd₀
      simp only [map_add, Finsupp.weight_single, one_smul] at h1 h2
      have e1 : rowW Φ n (τ, a, k) = rowW Φ n (τ, a, j) := rfl
      have e2 : rowW Φ n (τ, k, k) = rowW Φ n (τ, k, j) := rfl
      rw [e1] at h1
      rw [add_right_cancel h1, hβ, map_add, Finsupp.weight_single, one_smul, e2, h2, hdr]
    have htr : Finsupp.weight (trW Φ n) d < Finsupp.weight (trW Φ n) α := by
      have h1 := congrArg (Finsupp.weight (trW Φ n)) hα
      have h2 := congrArg (Finsupp.weight (trW Φ n)) hd₀
      have h3 := congrArg (Finsupp.weight (trW Φ n)) hβ
      simp only [map_add, Finsupp.weight_single, smul_eq_mul, one_mul, trW, hak, hkj.ne, ↓reduceIte] at h1 h2 h3
      omega
    exact absurd (hmax α (Finset.mem_filter.2 ⟨mem_support_iff.2 hα0, hαr⟩)) (not_le.2 htr)

/-- **The extreme weight.** For `G ∈ ∇(ν)`, `⟨hw_ν, G⟩ = G(1)·⟨hw_ν, hw_ν⟩`. -/
theorem fock_hw [CharZero L] {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) {G : Pol Φ n L}
    (hG : G ∈ nabla L ν) :
    fockWith (RingHom.id L) (hw L ν) G = eval (onePt Φ n L) G * fockWith (RingHom.id L) (hw L ν) (hw L ν) := by
  set c := eval (onePt Φ n L) G with hc
  have hH : G - C c * hw L ν ∈ nabla L ν :=
    Submodule.sub_mem _ hG (by rw [C_mul']; exact Submodule.smul_mem _ _ (hw_mem_nabla hν))
  have h1 : eval (onePt Φ n L) (G - C c * hw L ν) = 0 := by simp [hc, eval_one_hw]
  have h0 : fockWith (RingHom.id L) (hw L ν) (G - C c * hw L ν) = 0 := by
    rw [fock_eq_sum_left (subset_refl _)]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [coeff_eq_zero_of_eval_one hH h1 (hw_isWH_row hν (mem_support_iff.1 hd)), mul_zero, zero_mul]
  have e : G = (G - C c * hw L ν) + C c * hw L ν := by ring
  conv_lhs => rw [e]
  rw [fock_add_right, h0, fock_C_mul_right, zero_add]

omit [DecidableEq Φ] in
theorem map_hw (ν : Φ → Fin n → ℕ) [CharZero L] : MvPolynomial.map (algebraMap ℚ L) (hw ℚ ν) = hw L ν := by
  simp only [hw, minor, map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext i j
  simp [xMat]

omit [DecidableEq Φ] in
/-- `κ = ⟨hw_ν, hw_ν⟩ ≠ 0`: `hw_ν` has rational coefficients and `κ` is a positive rational. -/
theorem fock_hw_hw_ne_zero [CharZero L] (ν : Φ → Fin n → ℕ) :
    fockWith (RingHom.id L) (hw L ν) (hw L ν) ≠ 0 := by
  have hP : hw ℚ ν ≠ (0 : Pol Φ n ℚ) := fun h => by
    have := eval_one_hw (L := ℚ) (Φ := Φ) ν
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hpos : 0 < fockWith (RingHom.id ℚ) (hw ℚ ν) (hw ℚ ν) := by
    rw [fock_eq_sum_left (subset_refl _)]
    refine Finset.sum_pos (fun d hd => mul_pos (mul_self_pos.2 (mem_support_iff.1 hd)) ?_)
      (support_nonempty.2 hP)
    exact Finset.prod_pos fun p _ => Nat.cast_pos.2 (Nat.factorial_pos _)
  have hmap : fockWith (RingHom.id L) (hw L ν) (hw L ν) =
      algebraMap ℚ L (fockWith (RingHom.id ℚ) (hw ℚ ν) (hw ℚ ν)) := by
    rw [← map_hw, fock_eq_sum_left (support_map_subset _ _), fock_eq_sum_left (subset_refl (hw ℚ ν).support)]
    simp [coeff_map, fact]
  rw [hmap]
  exact (map_ne_zero_iff _ (algebraMap ℚ L).injective).2 hpos.ne'

end Extreme

/-! ## Cauchy–Binet, and the span -/

section Span

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {L : Type*} [Field L]

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Cauchy–Binet** for a leading minor of `gᵀx`, `g_τ = (x_{τ,a,b})`: a sum over all row maps `f` of the minor
of `g` on the rows `f` times the monomial `∏_i x_{τ, f i, i}`. -/
theorem lsub_minor (x : Φ × Fin n × Fin n → L) (τ : Φ) (s : Fin n) :
    lsub (fun σ => (Matrix.of fun a b => x (σ, a, b)).transpose) (minor τ s (Fin.castLE s.isLt)) =
      ∑ f : Fin (s + 1) → Fin n, C (eval x (minor τ s f)) * ∏ i, X (τ, f i, Fin.castLE s.isLt i) := by
  rw [minor, AlgHom.map_det, Matrix.det_apply']
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, xMat, Matrix.of_apply, lsub_X,
    Matrix.transpose_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  rw [minor, RingHom.map_det, ← Matrix.det_transpose, Matrix.det_apply', map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [xMat, map_prod]

/-- The monomial `∏_{τ,s,c,i} x_{τ, rows τ s c i, i}` paired with the bideterminant `bidet_rows`. -/
noncomputable def crow (ν : Φ → Fin n → ℕ)
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) : Pol Φ n L :=
  ∏ τ, ∏ s : Fin n, ∏ c, ∏ i, X (τ, rows τ s c i, Fin.castLE s.isLt i)

/-- **Cauchy–Binet for `hw_ν`**: `hw_ν(gᵀx) = Σ_rows bidet_rows(g)·x^{γ(rows)}`, `g_τ = (x_{τ,a,b})`. -/
theorem lsub_hw (x : Φ × Fin n × Fin n → L) (ν : Φ → Fin n → ℕ) :
    lsub (fun σ => (Matrix.of fun a b => x (σ, a, b)).transpose) (hw L ν) =
      ∑ rows, C (eval x (bidet L ν rows)) * crow ν rows := by
  rw [hw, map_prod]
  simp only [map_prod, lsub_minor, ← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun rows _ => ?_
  simp only [bidet, crow, map_prod, Finset.prod_mul_distrib]

omit [Fintype Φ] [DecidableEq Φ] in
/-- A minor with rows `I` is the leading principal minor at `g·x`, for `g` sending row `i ≤ s` to row `I i`. -/
theorem lsub_minor_rows (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) :
    lsub (fun _ => Matrix.of fun a c => if h : (a : ℕ) < s + 1 then (if c = I ⟨a, h⟩ then (1 : L) else 0) else 0)
      (minor τ s (Fin.castLE s.isLt)) = minor τ s I := by
  rw [minor, minor, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  have hi : Fin.castLE s.isLt i ≤ s := Fin.le_def.2 (by simp only [Fin.val_castLE]; omega)
  simp [xMat, lsub_X, hi]

omit [Fintype Φ] [DecidableEq Φ] in
/-- The leading minors with arbitrary rows are invariant under `x ↦ x·u`, `u` upper unitriangular: `rsub_minor`
at `g·x`. -/
theorem rsub_minor_rows {u : Φ → Matrix (Fin n) (Fin n) L} (hu : ∀ σ, IsUni (u σ)) (τ : Φ) (s : Fin n)
    (I : Fin (s + 1) → Fin n) : rsub u (minor τ s I) = (minor τ s I : Pol Φ n L) := by
  rw [← lsub_minor_rows, rsub_lsub, rsub_minor hu]

/-- **`⊆`.** For antitone `ν`, every bideterminant of shape `ν` lies in `∇_L(ν)`. -/
theorem bidet_mem_nabla {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ))
    (rows : (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n) : bidet L ν rows ∈ nabla L ν := by
  refine mem_nabla_iff.2 ⟨?_, fun u hu => by simp [bidet, map_prod, rsub_minor_rows hu]⟩
  have key : IsWeightedHomogeneous (colW Φ n) (bidet L ν rows)
        (∑ τ, ∑ s : Fin n, mult (ν τ) s • (Pi.single τ fun b : Fin n => if (b : ℕ) ≤ s then 1 else 0)) := by
    refine IsWeightedHomogeneous.prod _ _ _ fun τ _ => IsWeightedHomogeneous.prod _ _ _ fun s _ => ?_
    have h := IsWeightedHomogeneous.prod (R := L) (w := colW Φ n) Finset.univ
      (fun c => minor τ s (rows τ s c)) _ fun c _ => minor_isWH τ s (rows τ s c)
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  rwa [sum_mult hν] at key

/-- **Bideterminants span the dual Weyl module.** For antitone `ν` and `L` of characteristic `0`, the
bideterminants of shape `ν` span `∇_L(ν)`: for `F ∈ ∇_L(ν)`,
`⟨hw_ν, hw_ν⟩·F = Σ_rows ⟨x^{γ(rows)}, F⟩·bidet_rows` (the module docstring). -/
theorem span_bidet [CharZero L] {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    Submodule.span L (Set.range (bidet L ν)) = nabla L ν := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun F hF => ?_
  · rintro _ ⟨rows, rfl⟩
    exact bidet_mem_nabla hν rows
  set κ := fockWith (RingHom.id L) (hw L ν) (hw L ν) with hκdef
  have key : C κ * F = ∑ rows, C (fockWith (RingHom.id L) (crow ν rows) F) * bidet L ν rows := by
    refine MvPolynomial.funext fun x => ?_
    have h := fock_hw hν (lsub_mem_nabla (fun σ => Matrix.of fun a b => x (σ, a, b)) hF)
    rw [eval_lsub, ← fock_lsub, lsub_hw, fock_sum_left] at h
    simp only [fock_C_mul_left] at h
    have hx : (fun p : Φ × Fin n × Fin n => Matrix.of (fun a b => x (p.1, a, b)) p.2.1 p.2.2) = x :=
      funext fun _ => rfl
    rw [hx, ← hκdef] at h
    simp only [map_mul, eval_C, map_sum]
    rw [mul_comm, ← h]
    exact Finset.sum_congr rfl fun rows _ => mul_comm _ _
  have hκ : κ ≠ 0 := fock_hw_hw_ne_zero ν
  have hF' : F = κ⁻¹ • ∑ rows, fockWith (RingHom.id L) (crow ν rows) F • bidet L ν rows := by
    simp only [← C_mul']
    rw [← key, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hκ, C_1, one_mul]
  rw [hF']
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun rows _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨rows, rfl⟩))

end Span

end WeylFock
