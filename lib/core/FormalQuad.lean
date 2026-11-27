import CMEquiv

/-!
# Rational combinations in the Lubin–Tate group and the quadratic transfer

D1b-4 of the D1b plan. On the Lubin–Tate group (`L = log_LT`, `e = expLT`, `A ⊕ B = CMFormalBiadd.addP`) the Gaussian
exponent `ph` (`CMFormalInert.ph`) is a quadratic form up to the Gaussian equivalence `≃` (`CMFormalInert.Simeq`),
with polar form the pairing `B(x, y) = ph(x ⊕ y) − ph(x) − ph(y)` (`CMFormalBiadd.bP`, `be` at the variables).

**Rational combinations.** `⊕_i [a_i]X_i = e(Σ_i a_i·L(X_i))` (`linLT`) is integral for `ℓ`-integral rational `a`
(`isIntK_linLT_rat`): Hazewinkel's lemma over `ℚ_ℓ` with `φ = id`, as `g − ℓ⁻¹g(X^{ℓ²}) = Σ_i a_iX_i`. At integral
points `A_i` the combination is `linP a A = linLT(a)(A)` (`linP_eq_subst`).

**Multiples of `≃`.** Integer multiples keep `≃`, and `m·f ≃ 0` gives `f ≃ 0` for `ℓ ∤ m` (`exp f` is an `m`-th root
of an integral unit series, `isIntK_of_pow_eq`): so `ℓ`-integral rational multiples keep `≃` (`simeq_ratCast_mul`).
Scalars `γ` with `φγ = −γ` do not, and nothing here multiplies a `≃` by one.

**Bilinearity.** From `bP_add`, `bP_odd` and induction, `B(⊕_i [n_i]A_i, y) ≃ Σ_i n_i·B(A_i, y)` for integers
(`bP_linP_int`), and with a common denominator `m`, `m·B(P, y) ≃ B([m]P, y)`, also for `ℓ`-integral rationals
(`bP_linP_rat`). The parallelogram law at `(A, A)` with `A ⊖ A = 0` gives `B(A, A) ≃ 2·ph(A)` (`bP_self`).

**The transfer** (`quad_transfer`): `Σ_k ph(⊕_i [M_ki]X_i) ≃ Σ_i G_ii·ph(X_i) + Σ_{i<j} G_ij·be(X_i, X_j)`,
`G = MᵀM` (`quadPh`), for `ℓ`-integral rational `M`: twice either side is `Σ_{i,j} G_ij·B(X_j, X_i)`. No CM is used.
And `ph ≃ (γ/2)·serAB(X, X)` once `be ≃ γ·serAB` (`ph_simeq_serAB_diag`: `be(X, X) ≃ 2·ph`, then halve).

**Main declarations:** `linLT`, `isIntK_linLT_rat`, `linP`, `simeq_ratCast_mul`, `bP_linP_rat`, `bP_self`, `quadPh`,
`quad_transfer`, `ph_simeq_serAB_diag`.
-/

namespace FormalQuad

open PowerSeries CMFormalInert CMFormalBiadd

noncomputable section

/-! ## Rational combinations of points -/

section Lin

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`⊕_i [a_i] X_i = e(Σ_i a_i·L(X_i))`** over any field (`L = log_LT`, `e = expLT`). -/
def linLTK (K : Type) [Field K] (ℓ : ℕ) {ι : Type} [Fintype ι] (a : ι → K) : MvPowerSeries ι K :=
  PowerSeries.subst (∑ i, MvPowerSeries.C (a i) * PowerSeries.subst (MvPowerSeries.X i) (logLT K ℓ)) (expLT K ℓ)

/-- **`⊕_i [a_i] X_i = e(Σ_i a_i·L(X_i))`**, the formal group's linear combination, via logarithms. -/
def linLT {ι : Type} [Fintype ι] (a : ι → ℂ_[ℓ]) : MvPowerSeries ι ℂ_[ℓ] :=
  PowerSeries.subst (∑ i, MvPowerSeries.C (a i) * PowerSeries.subst (MvPowerSeries.X i) (logLT ℂ_[ℓ] ℓ))
    (expLT ℂ_[ℓ] ℓ)

variable {ι : Type} [Fintype ι]

/-- **The exponent `Σ_i a_i·L(X_i)` has no constant term.** -/
theorem constantCoeff_sum_logLT {K : Type} [Field K] (a : ι → K) :
    MvPowerSeries.constantCoeff (∑ i, MvPowerSeries.C (a i) *
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K) (logLT K ℓ)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _
    (constantCoeff_logLT K hℓp.out.one_lt), mul_zero]

/-- **The combination is defined over `ℚ`**: field maps carry it to itself. -/
theorem map_linLTK {K L : Type} [Field K] [Field L] (f : K →+* L) (a : ι → K) :
    MvPowerSeries.map f (linLTK K ℓ a) = linLTK L ℓ (fun i => f (a i)) := by
  have hX : ∀ i : ι, HasSubst (MvPowerSeries.X i : MvPowerSeries ι K) := fun i => HasSubst.X i
  rw [linLTK, PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (constantCoeff_sum_logLT a)),
    map_expLT f hℓp.out.one_lt, map_sum]
  simp only [map_mul, MvPowerSeries.map_C, PowerSeries.map_subst (hX _), map_logLT, MvPowerSeries.map_X]
  rfl

/-- **A sum of integral series is integral.** -/
theorem isIntK_sum {K : Type} [NormedField K] [IsUltrametricDist K] {σ κ : Type} (s : Finset κ)
    {f : κ → MvPowerSeries σ K} (hf : ∀ i ∈ s, IsIntK (f i)) : IsIntK (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun n => by simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Integrality over `ℚ_ℓ`** (Hazewinkel's lemma with `φ = id`, for `g = Σ_i a_i·L(X_i)`, where
`g − ℓ⁻¹g(X^{ℓ²}) = Σ_i a_i X_i`, as for `isIntK_ltAdd_padic`). -/
theorem isIntK_linLTK_padic (a : ι → ℚ_[ℓ]) (ha : ∀ i, ‖a i‖ ≤ 1) : IsIntK (linLTK ℚ_[ℓ] ℓ a) := by
  have hℓ := hℓp.out
  set L := logLT ℚ_[ℓ] ℓ
  have hX0 : ∀ i : ι, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι ℚ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hfX : ∀ f : MvPowerSeries ι ℚ_[ℓ], frobS ℓ (RingHom.id ℚ_[ℓ]) f = MvPowerSeries.expand ℓ hℓ.ne_zero f :=
    fun f => by simp [frobS, MvPowerSeries.map_id]
  have hfr : ∀ i : ι, frobS ℓ (RingHom.id ℚ_[ℓ]) (frobS ℓ (RingHom.id ℚ_[ℓ]) (L.subst (MvPowerSeries.X i))) =
      L.subst ((MvPowerSeries.X i : MvPowerSeries ι ℚ_[ℓ]) ^ (ℓ ^ 2)) := fun i => by
    rw [frobS_logLT_subst _ (hX0 i), frobS_logLT_subst _ (by rw [constantCoeff_frobS, hX0, map_zero]), hfX, hfX,
      MvPowerSeries.expand_X, map_pow, MvPowerSeries.expand_X, ← pow_mul, ← sq]
  have hfC : ∀ c : ℚ_[ℓ], frobS ℓ (RingHom.id ℚ_[ℓ]) (MvPowerSeries.C c : MvPowerSeries ι ℚ_[ℓ]) =
      MvPowerSeries.C c := fun c => by simp [frobS, MvPowerSeries.expand_C]
  apply isIntK_expLT_subst norm_sub_pow_le_padic (constantCoeff_sum_logLT a)
  have e : ∀ i : ι, L.subst (MvPowerSeries.X i : MvPowerSeries ι ℚ_[ℓ]) =
      MvPowerSeries.X i + (ℓ : ℚ_[ℓ])⁻¹ • L.subst ((MvPowerSeries.X i : MvPowerSeries ι ℚ_[ℓ]) ^ (ℓ ^ 2)) :=
    fun i => logLT_subst_eq hℓ.one_lt (HasSubst.X i)
  have key : (∑ i, MvPowerSeries.C (a i) * L.subst (MvPowerSeries.X i : MvPowerSeries ι ℚ_[ℓ])) -
      (ℓ : ℚ_[ℓ])⁻¹ • frobS ℓ (RingHom.id ℚ_[ℓ]) (frobS ℓ (RingHom.id ℚ_[ℓ])
        (∑ i, MvPowerSeries.C (a i) * L.subst (MvPowerSeries.X i : MvPowerSeries ι ℚ_[ℓ]))) =
      ∑ i, MvPowerSeries.C (a i) * MvPowerSeries.X i := by
    simp only [map_sum, map_mul, hfC, hfr]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e i, mul_add, mul_smul_comm, add_sub_cancel_right]
  rw [key]
  exact isIntK_sum _ fun i _ => (isIntK_C (ha i)).mul (isIntK_X i)

/-- **`⊕_i [a_i]X_i` is integral for `ℓ`-integral rational `a`** (Hazewinkel over `ℚ_ℓ` with `φ = id`,
`isIntK_expLT_subst`). -/
theorem isIntK_linLT_rat (a : ι → ℚ) (ha : ∀ i, ‖(a i : ℚ_[ℓ])‖ ≤ 1) :
    IsIntK (linLT (ℓ := ℓ) fun i => (a i : ℂ_[ℓ])) := fun n => by
  have e : (linLT (ℓ := ℓ) fun i => (a i : ℂ_[ℓ])) =
      MvPowerSeries.map (algebraMap ℚ_[ℓ] ℂ_[ℓ]) (linLTK ℚ_[ℓ] ℓ fun i => (a i : ℚ_[ℓ])) := by
    rw [map_linLTK]
    simp only [map_ratCast]
    rfl
  rw [e, MvPowerSeries.coeff_map]
  exact (PadicComplex.norm_extends' ℓ _).trans_le (isIntK_linLTK_padic _ ha n)

end Lin


/-! ## Points with prescribed logarithms -/

section Points

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {σ : Type}

/-- **`log_LT(e(g)) = g`** for `g` without constant term. -/
theorem lgP_exP {g : MvPowerSeries σ ℂ_[ℓ]} (hg : MvPowerSeries.constantCoeff g = 0) : lgP ℓ (exP ℓ g) = g := by
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero hg
  rw [lgP, exP, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (constantCoeff_expLT _ _)) hgs,
    logLT_subst_expLT _ hℓp.out.one_lt, subst_X hgs]

/-- **`e(g)` has no constant term.** -/
theorem constantCoeff_exP {g : MvPowerSeries σ ℂ_[ℓ]} (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (exP ℓ g) = 0 :=
  constantCoeff_subst_eq_zero hg _ (constantCoeff_expLT _ _)

/-- **`e(0) = 0`.** -/
theorem exP_zero : exP ℓ (0 : MvPowerSeries σ ℂ_[ℓ]) = 0 :=
  subst_zero_eq_zero (constantCoeff_expLT _ _)

/-- **The constant term of a scalar multiple.** -/
theorem constantCoeff_smul (c : ℂ_[ℓ]) (f : MvPowerSeries σ ℂ_[ℓ]) :
    MvPowerSeries.constantCoeff (c • f) = c * MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_C]

variable {ι : Type} [Fintype ι]

/-- **The linear combination of points** `⊕_i [a_i] A_i = e(Σ_i a_i·L(A_i))`. -/
def linP (a : ι → ℂ_[ℓ]) (A : ι → MvPowerSeries σ ℂ_[ℓ]) : MvPowerSeries σ ℂ_[ℓ] :=
  exP ℓ (∑ i, a i • lgP ℓ (A i))

/-- **The exponent of `linP` has no constant term.** -/
theorem constantCoeff_sum_smul_lgP (a : ι → ℂ_[ℓ]) {A : ι → MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) :
    MvPowerSeries.constantCoeff (∑ i, a i • lgP ℓ (A i)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [constantCoeff_smul, constantCoeff_lgP hℓp.out.one_lt (hA0 i), mul_zero]

/-- **`L(⊕_i [a_i] A_i) = Σ_i a_i·L(A_i)`.** -/
theorem lgP_linP (a : ι → ℂ_[ℓ]) {A : ι → MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) : lgP ℓ (linP a A) = ∑ i, a i • lgP ℓ (A i) :=
  lgP_exP (constantCoeff_sum_smul_lgP a hA0)

/-- **`⊕_i [a_i] A_i` has no constant term.** -/
theorem constantCoeff_linP (a : ι → ℂ_[ℓ]) {A : ι → MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) : MvPowerSeries.constantCoeff (linP a A) = 0 :=
  constantCoeff_exP (constantCoeff_sum_smul_lgP a hA0)

/-- **`linLT` is the combination of the variables.** -/
theorem linLT_eq_linP (a : ι → ℂ_[ℓ]) : linLT a = linP a (MvPowerSeries.X : ι → MvPowerSeries ι ℂ_[ℓ]) := by
  simp only [linLT, linP, exP, lgP, MvPowerSeries.smul_eq_C_mul]

/-- **`⊕_i [a_i] A_i` is `linLT a` evaluated at the points `A`.** -/
theorem linP_eq_subst (a : ι → ℂ_[ℓ]) {A : ι → MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) : linP a A = (linLT a).subst A := by
  have hℓ := hℓp.out.one_lt
  have hA : MvPowerSeries.HasSubst A := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
  rw [linLT, subst_subst _ (constantCoeff_sum_logLT a) hA, linP, exP]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hA, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom hA, MvPowerSeries.subst_C,
    subst_subst _ (MvPowerSeries.constantCoeff_X i) hA, MvPowerSeries.subst_X hA, ← MvPowerSeries.smul_eq_C_mul, lgP]

/-- **`⊕_i [a_i] A_i` is integral** for `ℓ`-integral rational `a` and integral points `A` (`isIntK_linLT_rat`). -/
theorem isIntK_linP_rat (a : ι → ℚ) (ha : ∀ i, ‖(a i : ℚ_[ℓ])‖ ≤ 1) {A : ι → MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) (hAi : ∀ i, IsIntK (A i)) :
    IsIntK (linP (fun i => (a i : ℂ_[ℓ])) A) := by
  rw [linP_eq_subst _ hA0]
  exact (isIntK_linLT_rat a ha).subst hAi hA0

end Points

/-! ## Multiples of Gaussian equivalences -/

section SimeqMul

variable {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`exp(n·f) = exp(f)^n`.** -/
theorem expMv_natCast_mul {f : MvPowerSeries σ ℂ_[ℓ]} (hf : MvPowerSeries.constantCoeff f = 0) (n : ℕ) :
    expMv (MvPowerSeries.C (n : ℂ_[ℓ]) * f) = expMv f ^ n := by
  induction n with
  | zero => simp [expMv_zero]
  | succ n ih =>
    rw [Nat.cast_succ, map_add, map_one, add_mul, one_mul,
      expMv_add (by rw [map_mul, hf, mul_zero]) hf, ih, pow_succ]

/-- **Division by a prime-to-`ℓ` integer**: `m·f ≃ 0` implies `f ≃ 0` for `‖m‖ = 1` (`exp(f)` is an `m`-th root
of the integral `exp(m·f)` with constant term `1`, `isIntK_of_pow_eq`). -/
theorem simeq_zero_of_natCast_mul [Finite σ] {m : ℕ} (hm : ‖(m : ℂ_[ℓ])‖ = 1) {f : MvPowerSeries σ ℂ_[ℓ]}
    (hf : Simeq (MvPowerSeries.C (m : ℂ_[ℓ]) * f) 0) : Simeq f 0 := by
  have hm0 : (m : ℂ_[ℓ]) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm
    exact zero_ne_one hm
  have h0 : MvPowerSeries.constantCoeff f = 0 := by
    have := hf.1
    rw [sub_zero, map_mul, MvPowerSeries.constantCoeff_C] at this
    exact (mul_eq_zero.mp this).resolve_left hm0
  refine ⟨by rw [sub_zero, h0], ?_⟩
  have hU := hf.2
  rw [sub_zero, expMv_natCast_mul h0] at hU
  rw [sub_zero]
  exact isIntK_of_pow_eq hm hU (by rw [constantCoeff_expMv h0, norm_one]) rfl

/-- **`≃` is stable under multiplication by integers.** -/
theorem simeq_intCast_mul {f g : MvPowerSeries σ ℂ_[ℓ]} (h : Simeq f g) (n : ℤ) :
    Simeq (MvPowerSeries.C (n : ℂ_[ℓ]) * f) (MvPowerSeries.C (n : ℂ_[ℓ]) * g) := by
  cases n with
  | ofNat k => simpa using h.natCast_mul k
  | negSucc k =>
    rw [Int.cast_negSucc, map_neg, neg_mul, neg_mul]
    exact (h.natCast_mul (k + 1)).neg

/-- **The denominator of an `ℓ`-integral rational is an `ℓ`-adic unit.** -/
theorem norm_den_eq_one {q : ℚ} (hq : ‖(q : ℚ_[ℓ])‖ ≤ 1) : ‖(q.den : ℂ_[ℓ])‖ = 1 := by
  have h := PadicInt.isUnit_iff.mp (PadicInt.isUnit_den q hq)
  have e := PadicComplex.norm_extends' ℓ (q.den : ℚ_[ℓ])
  rw [map_natCast, PadicComplex.coe_natCast] at e
  rw [e]
  simpa using h

/-- **`≃` is stable under multiplication by `ℓ`-integral rationals** (`q = n/m`: `m·(qf − qg) = n·(f − g)`, and
`simeq_zero_of_natCast_mul`). -/
theorem simeq_ratCast_mul [Finite σ] {f g : MvPowerSeries σ ℂ_[ℓ]} (h : Simeq f g) {q : ℚ}
    (hq : ‖(q : ℚ_[ℓ])‖ ≤ 1) :
    Simeq (MvPowerSeries.C (q : ℂ_[ℓ]) * f) (MvPowerSeries.C (q : ℂ_[ℓ]) * g) := by
  rw [simeq_iff_sub] at h ⊢
  refine simeq_zero_of_natCast_mul (norm_den_eq_one hq) ?_
  have e : MvPowerSeries.C (q.den : ℂ_[ℓ]) * (MvPowerSeries.C (q : ℂ_[ℓ]) * f - MvPowerSeries.C (q : ℂ_[ℓ]) * g) =
      MvPowerSeries.C (q.num : ℂ_[ℓ]) * (f - g) := by
    rw [← mul_sub, ← mul_assoc, ← map_mul]
    congr 2
    exact_mod_cast (mul_comm (q : ℚ) q.den ▸ Rat.mul_den_eq_num q)
  rw [e]
  simpa using simeq_intCast_mul h q.num

/-- **`≃` is stable under finite sums.** -/
theorem simeq_sum {κ : Type*} (t : Finset κ) {f g : κ → MvPowerSeries σ ℂ_[ℓ]} (h : ∀ i ∈ t, Simeq (f i) (g i)) :
    Simeq (∑ i ∈ t, f i) (∑ i ∈ t, g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Simeq.refl (0 : MvPowerSeries σ ℂ_[ℓ])
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Equal series are equivalent.** -/
theorem simeq_of_eq {f g : MvPowerSeries σ ℂ_[ℓ]} (h : f = g) : Simeq f g :=
  h ▸ Simeq.refl f

end SimeqMul

/-! ## The pairing is `ℤ_(ℓ)`-bilinear up to `≃` -/

section Bilin

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {σ : Type}

/-- **The hypotheses of the parallelogram law** (`CMFormalBiadd.parallelogram`) for `(a, b, s)` at the unit `ε`. -/
structure IsCurve (ℓ : ℕ) [Fact ℓ.Prime] (a b s ε : ℂ_[ℓ]) : Prop where
  /-- `ℓ ≠ 2`. -/
  two : ℓ ≠ 2
  /-- `a` is integral. -/
  ha : ‖a‖ ≤ 1
  /-- `b` is integral. -/
  hb : ‖b‖ ≤ 1
  /-- `ε` is a unit. -/
  hε : ‖ε‖ = 1
  /-- The formal addition law of `σ*`. -/
  add : AddLaw a b s
  /-- The differential equation of `℘`. -/
  ode : WeierODE a b
  /-- The CM-b integrality of `t(ε·log_LT(T))`. -/
  t : IsInt ((tSer a b).subst (zLT ℓ ε))

/-- **`B(0, y) = 0`.** -/
theorem bP_zero_left (a b s ε : ℂ_[ℓ]) {y : MvPowerSeries σ ℂ_[ℓ]} (hy : MvPowerSeries.constantCoeff y = 0) :
    bP (ph ℓ a b s ε) 0 y = 0 := by
  have hℓ := hℓp.out.one_lt
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries σ ℂ_[ℓ]) = 0 := map_zero _
  have e : addP 0 y = y := eq_of_lgP_eq hℓ (constantCoeff_addP h0 hy) hy (by
    rw [lgP_addP h0 hy, lgP_zero hℓ, zero_add])
  rw [bP, e, subst_zero_eq_zero (constantCoeff_ph hℓ a b s ε)]
  ring

/-- **The pairing is symmetric**: `B(x, y) = B(y, x)`. -/
theorem bP_comm (p : ℂ_[ℓ]⟦X⟧) {x y : MvPowerSeries σ ℂ_[ℓ]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) : bP p x y = bP p y x := by
  rw [bP, bP, addP_comm hx hy]
  ring

variable [Finite σ] {a b s ε : ℂ_[ℓ]}

/-- **The pairing is odd**: `B(−v, y) ≃ −B(v, y)` (`bP_odd`). -/
theorem bP_neg_left (H : IsCurve ℓ a b s ε) {v y : MvPowerSeries σ ℂ_[ℓ]} (hv : MvPowerSeries.constantCoeff v = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (hvi : IsIntK v) (hyi : IsIntK y) :
    Simeq (bP (ph ℓ a b s ε) (-v) y) (-bP (ph ℓ a b s ε) v y) := by
  rw [simeq_iff_sub, sub_neg_eq_add, add_comm]
  exact bP_odd H.two H.ha H.hb H.hε H.add H.ode H.t hv hy hvi hyi

/-- **Additivity over a finite sum of points**: `B(⊕_{i ∈ t} B_i, y) ≃ Σ_{i ∈ t} B(B_i, y)`, and the sum is
integral (induction with `bP_add`). -/
theorem bP_exP_sum (H : IsCurve ℓ a b s ε) {κ : Type} (t : Finset κ) {B : κ → MvPowerSeries σ ℂ_[ℓ]}
    (hB0 : ∀ i, MvPowerSeries.constantCoeff (B i) = 0) (hBi : ∀ i, IsIntK (B i)) {y : MvPowerSeries σ ℂ_[ℓ]}
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hyi : IsIntK y) :
    IsIntK (exP ℓ (∑ i ∈ t, lgP ℓ (B i))) ∧
      Simeq (bP (ph ℓ a b s ε) (exP ℓ (∑ i ∈ t, lgP ℓ (B i))) y) (∑ i ∈ t, bP (ph ℓ a b s ε) (B i) y) := by
  classical
  have hℓ := hℓp.out.one_lt
  have hL0 : ∀ t : Finset κ, MvPowerSeries.constantCoeff (∑ i ∈ t, lgP ℓ (B i)) = 0 := fun t => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => constantCoeff_lgP hℓ (hB0 i)
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, exP_zero, bP_zero_left a b s ε hy0]
    exact ⟨fun n => by simp, Simeq.refl 0⟩
  | insert j t hj ih =>
    obtain ⟨hPi, hP⟩ := ih
    have hP0 := constantCoeff_exP (hL0 t)
    have e : exP ℓ (∑ i ∈ insert j t, lgP ℓ (B i)) = addP (B j) (exP ℓ (∑ i ∈ t, lgP ℓ (B i))) := by
      refine eq_of_lgP_eq hℓ (constantCoeff_exP (hL0 _)) (constantCoeff_addP (hB0 j) hP0) ?_
      rw [lgP_exP (hL0 _), lgP_addP (hB0 j) hP0, lgP_exP (hL0 t), Finset.sum_insert hj]
    rw [e, Finset.sum_insert hj]
    exact ⟨isIntK_addP (hB0 j) hP0 (hBi j) hPi,
      (bP_add H.two H.ha H.hb H.hε H.add H.ode H.t (hB0 j) hP0 hy0 (hBi j) hPi hyi).trans
        ((Simeq.refl _).add hP)⟩

/-- **Integer multiples**: `B([n]A, y) ≃ n·B(A, y)`, `[n]A = e(n·L(A))` integral. -/
theorem bP_zsmul (H : IsCurve ℓ a b s ε) (n : ℤ) {A : MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : MvPowerSeries.constantCoeff A = 0) (hAi : IsIntK A) {y : MvPowerSeries σ ℂ_[ℓ]}
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hyi : IsIntK y) :
    IsIntK (exP ℓ ((n : ℂ_[ℓ]) • lgP ℓ A)) ∧
      Simeq (bP (ph ℓ a b s ε) (exP ℓ ((n : ℂ_[ℓ]) • lgP ℓ A)) y)
        (MvPowerSeries.C (n : ℂ_[ℓ]) * bP (ph ℓ a b s ε) A y) := by
  have hℓ := hℓp.out.one_lt
  have hodd : Odd ℓ := hℓp.out.odd_of_ne_two H.two
  have hg0 : ∀ c : ℂ_[ℓ], MvPowerSeries.constantCoeff (c • lgP ℓ A) = 0 := fun c => by
    rw [constantCoeff_smul, constantCoeff_lgP hℓ hA0, mul_zero]
  have hnat : ∀ k : ℕ, IsIntK (exP ℓ ((k : ℂ_[ℓ]) • lgP ℓ A)) ∧
      Simeq (bP (ph ℓ a b s ε) (exP ℓ ((k : ℂ_[ℓ]) • lgP ℓ A)) y)
        (MvPowerSeries.C (k : ℂ_[ℓ]) * bP (ph ℓ a b s ε) A y) := by
    intro k
    have e : (k : ℂ_[ℓ]) • lgP ℓ A = ∑ _i ∈ Finset.range k, lgP ℓ A := by
      rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
    have e2 : MvPowerSeries.C (k : ℂ_[ℓ]) * bP (ph ℓ a b s ε) A y = ∑ _i ∈ Finset.range k, bP (ph ℓ a b s ε) A y := by
      rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ_[ℓ], MvPowerSeries.smul_eq_C_mul]
    rw [e, e2]
    exact bP_exP_sum H (Finset.range k) (fun _ => hA0) (fun _ => hAi) hy0 hyi
  cases n with
  | ofNat k => simpa using hnat k
  | negSucc k =>
    obtain ⟨hPi, hP⟩ := hnat (k + 1)
    have hP0 := constantCoeff_exP (hg0 ((k + 1 : ℕ) : ℂ_[ℓ]))
    have e : exP ℓ (((Int.negSucc k : ℤ) : ℂ_[ℓ]) • lgP ℓ A) = -exP ℓ (((k + 1 : ℕ) : ℂ_[ℓ]) • lgP ℓ A) := by
      refine eq_of_lgP_eq hℓ (constantCoeff_exP (hg0 _)) (by rw [map_neg, hP0, neg_zero]) ?_
      rw [lgP_exP (hg0 _), lgP_neg hodd hP0, lgP_exP (hg0 _), Int.cast_negSucc, neg_smul]
    rw [e, Int.cast_negSucc, map_neg, neg_mul]
    exact ⟨hPi.neg, (bP_neg_left H hP0 hy0 hPi hyi).trans hP.neg⟩

/-- **Integer combinations**: `B(⊕_i [n_i] A_i, y) ≃ Σ_i n_i·B(A_i, y)`. -/
theorem bP_linP_int (H : IsCurve ℓ a b s ε) {κ : Type} [Fintype κ] (n : κ → ℤ) {A : κ → MvPowerSeries σ ℂ_[ℓ]}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) (hAi : ∀ i, IsIntK (A i)) {y : MvPowerSeries σ ℂ_[ℓ]}
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hyi : IsIntK y) :
    Simeq (bP (ph ℓ a b s ε) (linP (fun i => (n i : ℂ_[ℓ])) A) y)
      (∑ i, MvPowerSeries.C (n i : ℂ_[ℓ]) * bP (ph ℓ a b s ε) (A i) y) := by
  have hℓ := hℓp.out.one_lt
  have hB := fun i => bP_zsmul H (n i) (hA0 i) (hAi i) hy0 hyi
  have hg0 : ∀ i, MvPowerSeries.constantCoeff ((n i : ℂ_[ℓ]) • lgP ℓ (A i)) = 0 := fun i => by
    rw [constantCoeff_smul, constantCoeff_lgP hℓ (hA0 i), mul_zero]
  have e : linP (fun i => (n i : ℂ_[ℓ])) A = exP ℓ (∑ i, lgP ℓ (exP ℓ ((n i : ℂ_[ℓ]) • lgP ℓ (A i)))) := by
    rw [linP]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (lgP_exP (hg0 i)).symm
  rw [e]
  exact (bP_exP_sum H Finset.univ (fun i => constantCoeff_exP (hg0 i)) (fun i => (hB i).1) hy0 hyi).2.trans
    (simeq_sum _ fun i _ => (hB i).2)

/-- **`ℓ`-integral rational combinations**: `B(⊕_i [q_i] A_i, y) ≃ Σ_i q_i·B(A_i, y)` (with `m = Π den q_i`,
`m·B(P, y) ≃ B([m]P, y) = B(⊕_i [mq_i] A_i, y) ≃ Σ_i mq_i·B(A_i, y)`, and division by `m`). -/
theorem bP_linP_rat (H : IsCurve ℓ a b s ε) {κ : Type} [Fintype κ] (q : κ → ℚ) (hq : ∀ i, ‖(q i : ℚ_[ℓ])‖ ≤ 1)
    {A : κ → MvPowerSeries σ ℂ_[ℓ]} (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) (hAi : ∀ i, IsIntK (A i))
    {y : MvPowerSeries σ ℂ_[ℓ]} (hy0 : MvPowerSeries.constantCoeff y = 0) (hyi : IsIntK y) :
    Simeq (bP (ph ℓ a b s ε) (linP (fun i => (q i : ℂ_[ℓ])) A) y)
      (∑ i, MvPowerSeries.C (q i : ℂ_[ℓ]) * bP (ph ℓ a b s ε) (A i) y) := by
  classical
  set m : ℕ := ∏ i, (q i).den with hmdef
  have hm : ‖(m : ℂ_[ℓ])‖ = 1 := by
    rw [hmdef, Nat.cast_prod, norm_prod]
    exact Finset.prod_eq_one fun i _ => norm_den_eq_one (hq i)
  set n : κ → ℤ := fun i => (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ) with hndef
  have hnq : ∀ i, (n i : ℚ) = (m : ℚ) * q i := fun i => by
    simp only [hndef, hmdef]
    push_cast
    rw [← Rat.mul_den_eq_num, ← Finset.mul_prod_erase Finset.univ (fun j => ((q j).den : ℚ)) (Finset.mem_univ i)]
    ring
  have hn : ∀ i, (n i : ℂ_[ℓ]) = (m : ℂ_[ℓ]) * (q i : ℂ_[ℓ]) := fun i => by
    have := congrArg (fun r : ℚ => (r : ℂ_[ℓ])) (hnq i)
    push_cast at this
    exact this
  set P := linP (fun i => (q i : ℂ_[ℓ])) A with hPdef
  have hPi : IsIntK P := isIntK_linP_rat q hq hA0 hAi
  have hP0 : MvPowerSeries.constantCoeff P = 0 := constantCoeff_linP _ hA0
  have h1 := (bP_zsmul H (m : ℤ) hP0 hPi hy0 hyi).2
  have e : exP ℓ (((m : ℤ) : ℂ_[ℓ]) • lgP ℓ P) = linP (fun i => (n i : ℂ_[ℓ])) A := by
    rw [hPdef, lgP_linP _ hA0, Finset.smul_sum, linP]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hn i]
    push_cast
    rfl
  rw [e] at h1
  have h2 := bP_linP_int H n hA0 hAi hy0 hyi
  have h3 : Simeq (MvPowerSeries.C (m : ℂ_[ℓ]) * bP (ph ℓ a b s ε) P y)
      (MvPowerSeries.C (m : ℂ_[ℓ]) * ∑ i, MvPowerSeries.C (q i : ℂ_[ℓ]) * bP (ph ℓ a b s ε) (A i) y) := by
    have h := h1.symm.trans h2
    rw [Int.cast_natCast] at h
    convert h using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hn i, map_mul, mul_assoc]
  rw [simeq_iff_sub]
  refine simeq_zero_of_natCast_mul hm ?_
  rw [mul_sub]
  exact simeq_iff_sub.mp h3

omit [Finite σ] in
/-- **The diagonal of the pairing**: `B(A, A) ≃ 2·ph(A)` (the parallelogram law at `(A, A)`, with `A ⊖ A = 0`). -/
theorem bP_self (H : IsCurve ℓ a b s ε) {A : MvPowerSeries σ ℂ_[ℓ]} (hA0 : MvPowerSeries.constantCoeff A = 0)
    (hAi : IsIntK A) : Simeq (bP (ph ℓ a b s ε) A A) (2 * (ph ℓ a b s ε).subst A) := by
  have hℓ := hℓp.out.one_lt
  have hodd : Odd ℓ := hℓp.out.odd_of_ne_two H.two
  have hA0' : MvPowerSeries.constantCoeff (-A) = 0 := by rw [map_neg, hA0, neg_zero]
  have h := parallelogram_pt H.two H.ha H.hb H.hε H.add H.ode H.t hA0 hA0 hAi hAi
  have e0 : addP A (-A) = 0 := eq_of_lgP_eq hℓ (constantCoeff_addP hA0 hA0') (map_zero _) (by
    rw [lgP_addP hA0 hA0', lgP_neg hodd hA0, lgP_zero hℓ, add_neg_cancel])
  rw [e0, subst_zero_eq_zero (constantCoeff_ph hℓ a b s ε), add_zero] at h
  have h' := h.symm.sub (Simeq.refl (2 * (ph ℓ a b s ε).subst A))
  rw [bP]
  convert h' using 1 <;> ring

end Bilin

/-! ## The quadratic transfer -/

section Transfer

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {ι κ : Type} [Fintype ι] [Fintype κ]

/-- **The formal quadratic form with Gram matrix `G`**: `Σ_i G_ii·p(X_i) + Σ_{i<j} G_ij·B(X_i, X_j)`. -/
def quadPh [LinearOrder ι] (p : ℂ_[ℓ]⟦X⟧) (B : MvPowerSeries (Fin 2) ℂ_[ℓ]) (G : Matrix ι ι ℂ_[ℓ]) :
    MvPowerSeries ι ℂ_[ℓ] :=
  ∑ i, MvPowerSeries.C (G i i) * PowerSeries.subst (MvPowerSeries.X i) p +
    ∑ i, ∑ j, if i < j then MvPowerSeries.C (G i j) *
      MvPowerSeries.subst ![(MvPowerSeries.X i : MvPowerSeries ι ℂ_[ℓ]), MvPowerSeries.X j] B else 0

omit [Fintype ι] in
/-- **A symmetric double sum** is its diagonal plus twice its strict upper triangle. -/
theorem sum_sum_symm [Fintype ι] {R : Type*} [CommRing R] [LinearOrder ι] (f : ι → ι → R)
    (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
  have h1 : ∀ i j, f i j =
      ((if i < j then f i j else 0) + if i = j then f i j else 0) + if j < i then f j i else 0 := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp
    · simp [h, h.ne', not_lt.mpr h.le, hf i j]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
  ring

/-- **The rational quadratic transfer**: `Σ_k ph(⊕_i [M_ki] X_i) ≃ Q_{MᵀM}(X)` for `ℓ`-integral rational `M`
(only the cube relation and biadditivity, no CM). Twice the left side is `Σ_k B(Y_k, Y_k)` (`bP_self`), which by
rational bilinearity (`bP_linP_rat`, twice) is `Σ_{i,j} (MᵀM)_ij·B(X_j, X_i)`; so is twice the right side
(`bP_self`, `sum_sum_symm`); halve. -/
theorem quad_transfer [LinearOrder ι] (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hε : ‖ε‖ = 1) (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε)))
    (M : Matrix κ ι ℚ) (hM : ∀ k i, ‖(M k i : ℚ_[ℓ])‖ ≤ 1) :
    Simeq (∑ k, PowerSeries.subst (linLT fun i => (M k i : ℂ_[ℓ])) (ph ℓ a b s ε))
      (quadPh (ph ℓ a b s ε) (be ℓ a b s ε) ((M.transpose * M).map fun q => (q : ℂ_[ℓ]))) := by
  have H : IsCurve ℓ a b s ε := ⟨hℓ2, ha, hb, hε, hAdd, hODE, ht⟩
  set p := ph ℓ a b s ε with hp
  set X : ι → MvPowerSeries ι ℂ_[ℓ] := MvPowerSeries.X with hX
  have hX0 : ∀ i, MvPowerSeries.constantCoeff (X i) = 0 := fun i => MvPowerSeries.constantCoeff_X i
  have hXi : ∀ i, IsIntK (X i) := fun i => isIntK_X i
  set Y : κ → MvPowerSeries ι ℂ_[ℓ] := fun k => linLT fun i => (M k i : ℂ_[ℓ]) with hY
  have hYP : ∀ k, Y k = linP (fun i => (M k i : ℂ_[ℓ])) X := fun k => linLT_eq_linP _
  have hYi : ∀ k, IsIntK (Y k) := fun k => isIntK_linLT_rat _ (hM k)
  have hY0 : ∀ k, MvPowerSeries.constantCoeff (Y k) = 0 := fun k => by
    rw [hYP]
    exact constantCoeff_linP _ hX0
  set G : ι → ι → ℚ := fun i j => ∑ k, M k i * M k j with hG
  have hGM : ∀ i j, ((M.transpose * M).map fun q => (q : ℂ_[ℓ])) i j = (G i j : ℂ_[ℓ]) := fun i j => by
    simp [hG, Matrix.mul_apply]
  have hGn : ∀ i j, ‖(G i j : ℚ_[ℓ])‖ ≤ 1 := fun i j => by
    rw [hG]
    push_cast
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => by
      rw [norm_mul]
      exact (mul_le_mul (hM k i) (hM k j) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1))
  have hBsym : ∀ i j, bP p (X i) (X j) = bP p (X j) (X i) := fun i j => bP_comm p (hX0 i) (hX0 j)
  -- `2·ph(Y_k) ≃ Σ_{i,j} M_ki M_kj·B(X_j, X_i)`
  have hk : ∀ k, Simeq (2 * p.subst (Y k))
      (∑ i, ∑ j, MvPowerSeries.C ((M k i * M k j : ℚ) : ℂ_[ℓ]) * bP p (X j) (X i)) := by
    intro k
    have s2 : Simeq (bP p (Y k) (Y k)) (∑ i, MvPowerSeries.C (M k i : ℂ_[ℓ]) * bP p (X i) (Y k)) := by
      have := bP_linP_rat H (fun i => M k i) (hM k) hX0 hXi (hY0 k) (hYi k)
      rwa [← hYP k] at this
    have s3 : ∀ i, Simeq (MvPowerSeries.C (M k i : ℂ_[ℓ]) * bP p (X i) (Y k))
        (MvPowerSeries.C (M k i : ℂ_[ℓ]) * ∑ j, MvPowerSeries.C (M k j : ℂ_[ℓ]) * bP p (X j) (X i)) := by
      intro i
      refine simeq_ratCast_mul ?_ (hM k i)
      rw [bP_comm p (hX0 i) (hY0 k)]
      have := bP_linP_rat H (fun j => M k j) (hM k) hX0 hXi (hX0 i) (hXi i)
      rwa [← hYP k] at this
    refine (bP_self H (hY0 k) (hYi k)).symm.trans (s2.trans ((simeq_sum _ fun i _ => s3 i).trans
      (simeq_of_eq ?_)))
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← map_mul]
    push_cast
    rfl
  -- the left side
  have hL : Simeq (2 * ∑ k, p.subst (Y k)) (∑ i, ∑ j, MvPowerSeries.C (G i j : ℂ_[ℓ]) * bP p (X j) (X i)) := by
    rw [Finset.mul_sum]
    refine (simeq_sum _ fun k _ => hk k).trans (simeq_of_eq ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, hG]
    push_cast
    rfl
  -- the right side
  have hR : Simeq (2 * quadPh p (be ℓ a b s ε) ((M.transpose * M).map fun q => (q : ℂ_[ℓ])))
      (∑ i, ∑ j, MvPowerSeries.C (G i j : ℂ_[ℓ]) * bP p (X j) (X i)) := by
    have hGs : ∀ i j, G i j = G j i := fun i j => Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [sum_sum_symm (fun i j => MvPowerSeries.C (G i j : ℂ_[ℓ]) * bP p (X j) (X i))
      (fun i j => by rw [hGs, hBsym])]
    unfold quadPh
    rw [mul_add]
    refine Simeq.add ?_ (simeq_of_eq ?_)
    · rw [Finset.mul_sum]
      refine simeq_sum _ fun i _ => ?_
      rw [hGM, mul_left_comm]
      exact simeq_ratCast_mul (bP_self H (hX0 i) (hXi i)).symm (hGn i i)
    · congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [hGM, subst_be a b s ε (hX0 i) (hX0 j), hBsym]
      · rfl
  rw [simeq_iff_sub]
  refine simeq_zero_of_two_mul hℓ2 ?_
  rw [mul_sub]
  exact simeq_iff_sub.mp (hL.trans hR.symm)

/-- **`ph ≃ (γ/2)·serAB(X, X)`** once `be ≃ γ·serAB`: `be(X, X) = B(X, X) ≃ 2·ph(X)` (`bP_self`) and halving
(`simeq_zero_of_two_mul`). Nothing multiplies a `≃` by `γ`. -/
theorem ph_simeq_serAB_diag (hℓ2 : ℓ ≠ 2) {a b s ε γ : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε)))
    (hbe : Simeq (be ℓ a b s ε) (MvPowerSeries.C γ * serAB ℓ)) :
    Simeq (ph ℓ a b s ε : MvPowerSeries Unit ℂ_[ℓ])
      (MvPowerSeries.C (γ / 2) * MvPowerSeries.subst ![(MvPowerSeries.X () : MvPowerSeries Unit ℂ_[ℓ]),
        MvPowerSeries.X ()] (serAB ℓ)) := by
  have H : IsCurve ℓ a b s ε := ⟨hℓ2, ha, hb, hε, hAdd, hODE, ht⟩
  set T : MvPowerSeries Unit ℂ_[ℓ] := MvPowerSeries.X () with hTdef
  have hT0 : MvPowerSeries.constantCoeff T = 0 := MvPowerSeries.constantCoeff_X ()
  have hψ : MvPowerSeries.HasSubst ![T, T] := hasSubst_pair hT0 hT0
  have hpT : (ph ℓ a b s ε : MvPowerSeries Unit ℂ_[ℓ]) = (ph ℓ a b s ε).subst T := by
    have e : (fun _ : Unit => T) = MvPowerSeries.X := by
      funext u
      rfl
    rw [PowerSeries.subst, e, MvPowerSeries.subst_self]
    rfl
  have h1 := hbe.subst (ψ := ![T, T]) (fun i => by fin_cases i <;> exact isIntK_X ())
    (fun i => by fin_cases i <;> exact hT0)
  rw [subst_be a b s ε hT0 hT0, MvPowerSeries.subst_mul hψ, MvPowerSeries.subst_C] at h1
  have h2 := (bP_self H hT0 (isIntK_X ())).symm.trans h1
  rw [hpT, simeq_iff_sub]
  refine simeq_zero_of_two_mul hℓ2 ?_
  have e2 : (2 : MvPowerSeries Unit ℂ_[ℓ]) * MvPowerSeries.C (γ / 2) = MvPowerSeries.C γ := by
    rw [← map_ofNat MvPowerSeries.C 2, ← map_mul, mul_div_cancel₀ γ two_ne_zero]
  rw [mul_sub, ← mul_assoc, e2]
  exact simeq_iff_sub.mp h2

end Transfer
end

end FormalQuad
