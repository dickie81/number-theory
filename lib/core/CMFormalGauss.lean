import CMFormalBiadd

/-!
# The uniqueness half of the formal-Gaussian classification

D1a′ of the D1 plan, item 5 completed: the uniqueness statement `CMFormalBiadd.GaussClass` holds for every closed
subfield `k` of `ℂ_ℓ` with a Frobenius lift that contains a Teichmüller `ζ` with `‖ζ − ζ^ℓ‖ = 1`
(`gaussClass_of_isClosed`), in particular for `unramC ℓ` (`gaussClass_unramC`), so the classification `be ≃ c·serAB`
of the CM curve needs only the hermitian input (`be_classification_cm'`), or the boundedness of the coefficients of
`X·Y^{ℓ^{2j}}` in `be` in its place (`be_classification_cm_bdd`). Closedness is needed: over `ℚ(√ν)` a series
`≃ c·serAB` with `c ∈ ℤ_ℓ√ν` outside the field satisfies every hypothesis of `GaussClass` and is `≃ c′·serAB` for no
`c′` in the field. Notation: `L = log_LT`, `L^F = log_LT(T^ℓ)`, `F = X ⊕ Y` (`ltAdd`), `O` the unit ball.

**Dwork in `T`-form.** With `φ` extended by `0` off `k` (`phiC`), a series with coefficients in `k` and no constant
term is `≃ 0` iff `T f = f − ℓ⁻¹·f^φ(X^ℓ)` is integral (`simeq_zero_iff_isIntK_tOpC`, from `simeq_zero_iff_dwork`);
at an exponent prime to `ℓ`, `T f` and `f` agree (`norm_coeff_le_one_of_simeq_zero`).

**The coefficients of the group law.** `F(0, Y) = Y` and `F(Y, X) = F(X, Y)`, so `F = X + Y·H` with `H(0) = 1`
(`ltAdd_eq_X_add_X_mul_grpH`); the `Y`-linear part of `F^{m+1}` is `(m + 1)X^mY·H` (`fc_succ_one`), and
`F^N ≡ (X + Y)^N` in degree `N` (`fc_top`). The additivity defect `deltaX B = B(X ⊕ X′, Y) − B(X, Y) − B(X′, Y)` has
at `X^iX′^jY^n` the defect coefficient `dC` of the column `B_{·,n}` (the `Y`-separation formula
`coeff_subst_pair_X2`, `coeff_deltaX`); `L` is additive (`dC_logLT`), `L^F` additive mod `ℓ` (`norm_dC_lcF_le`).

**The structure theorem** (`gauss_structure`, no hermitian hypothesis): a symmetric series `B` over a closed `k`,
biadditive up to `≃`, is `≃ α·L(X)L(Y) + γ·serAB` with `α, γ ∈ k`, `φ(γ) = −γ`, `‖γ‖ ≤ 1`.
* S1 (`isXDp_of_biadd`): the coefficients of `deltaX B` at `X^pX′Y^n` are integral (Dwork), and they are
  `Σ_{t ≤ p}(t + 1)·β_{t+1}·H_{p−t}` for `β = B_{·,n} − B_{1,n}·L`; so `P = B − L(X)u(Y)`, `u = B_{1,·}`, is of
  divided-power type in `X`: `‖m·P_{m,n}‖ ≤ 1`.
* S2 (`isIntK_deltaX_tOpC`): for such `P`, `deltaX (T P) = T (deltaX P) + ℓ⁻¹·(Q(X^ℓ ⊕ X′^ℓ, Y^ℓ) − Q((X ⊕ X′)^ℓ, Y^ℓ))`
  with `Q = P^φ`, integral by Dwork and the divided-power congruence (`isDivK_subst_sub_dp`: lifting the exponent,
  `A^m ≡ A′^m (mod ℓ·m)`).
* S3 (`quasiLog_col`): a column with integral defect coefficients is `a·L + b·ℓ⁻¹L^F` modulo `O`, `a, b ∈ O`: models
  by induction on the degree (Lucas and Kummer: `C(N, ℓ^{v(N)})` is a unit off the powers of `ℓ`, `C(ℓ^{c+1}, ℓ^c)` has
  valuation `1`), then limits in `ℂ_ℓ`.
* S4 (`quasiBilin`): `T B ≡ L(X)U(Y) + ℓ⁻¹L^F(X)V(Y)`; S5 (`bilin_of_symm`): symmetry forces `U = αL + γℓ⁻¹L^F`,
  `V = γL + δL^F` exactly (the exactness trick `eq_of_norm_sub_le_pow`).
* Closedness puts `α, γ` in `k` (`mem_of_approx`); integrality of `b` gives `δ = −φ(α)`, `φ(γ) = −γ`; then
  `T(B − αL(X)L(Y) − γ·serAB)` is integral by the Frobenius defect of `serAB` (`serAB_frob`).

**The hermitian condition** only kills `α`: `α = 0` iff the coefficients of `X·Y^{ℓ^{2j}}` in `B` are bounded
(`alpha_eq_zero_iff`), and the hermitian property bounds them by `1` when `ζ ∈ k` (`bdd_of_isHerm`). For `unramC`:
it is a topological closure (`isClosed_unramC`), and a primitive `(ℓ² − 1)`-th root of unity is a Teichmüller `ζ`
with `‖ζ − ζ^ℓ‖ = 1` (`exists_teich_unramC`, `norm_one_sub_eq_one`).

**Main results:** `simeq_zero_iff_isIntK_tOpC`, `gauss_structure`, `alpha_eq_zero_iff`, `bdd_of_isHerm`,
`gauss_class_of_bdd`, `gaussClass_of_isClosed`, `gaussClass_unramC`, `be_classification_cm'`,
`be_classification_cm_bdd`.
-/

namespace CMFormalGauss

open PowerSeries CMFormalInert CMFormalBiadd

noncomputable section

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-! ## Frobenius on coefficients and Dwork's criterion in `T`-form -/

section Frob

variable (k : Subfield ℂ_[ℓ]) (φ : k →+* k)

open Classical in
/-- **Frobenius on coefficients**: `φ` on `k`, extended by `0` off `k`. -/
def phiC (x : ℂ_[ℓ]) : ℂ_[ℓ] := if h : x ∈ k then (φ ⟨x, h⟩ : ℂ_[ℓ]) else 0

variable {k φ}

/-- **`phiC` on `k` is `φ`.** -/
theorem phiC_of_mem {x : ℂ_[ℓ]} (hx : x ∈ k) : phiC k φ x = (φ ⟨x, hx⟩ : ℂ_[ℓ]) := by
  simp [phiC, hx]

/-- **`phiC` is additive on `k`.** -/
theorem phiC_add {x y : ℂ_[ℓ]} (hx : x ∈ k) (hy : y ∈ k) : phiC k φ (x + y) = phiC k φ x + phiC k φ y := by
  rw [phiC_of_mem hx, phiC_of_mem hy, phiC_of_mem (k.add_mem hx hy)]
  rw [show (⟨x + y, k.add_mem hx hy⟩ : k) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]
  rfl

/-- **`phiC` is multiplicative on `k`.** -/
theorem phiC_mul {x y : ℂ_[ℓ]} (hx : x ∈ k) (hy : y ∈ k) : phiC k φ (x * y) = phiC k φ x * phiC k φ y := by
  rw [phiC_of_mem hx, phiC_of_mem hy, phiC_of_mem (k.mul_mem hx hy)]
  rw [show (⟨x * y, k.mul_mem hx hy⟩ : k) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
  rfl

/-- **`phiC` commutes with negation on `k`.** -/
theorem phiC_neg {x : ℂ_[ℓ]} (hx : x ∈ k) : phiC k φ (-x) = -phiC k φ x := by
  rw [phiC_of_mem hx, phiC_of_mem (k.neg_mem hx)]
  rw [show (⟨-x, k.neg_mem hx⟩ : k) = -⟨x, hx⟩ from rfl, map_neg]
  rfl

/-- **`phiC` commutes with subtraction on `k`.** -/
theorem phiC_sub {x y : ℂ_[ℓ]} (hx : x ∈ k) (hy : y ∈ k) : phiC k φ (x - y) = phiC k φ x - phiC k φ y := by
  rw [sub_eq_add_neg, phiC_add hx (k.neg_mem hy), phiC_neg hy, sub_eq_add_neg]

/-- **`phiC` fixes the rationals.** -/
theorem phiC_ratCast (q : ℚ) : phiC k φ (q : ℂ_[ℓ]) = q := by
  have hq : (q : ℂ_[ℓ]) ∈ k := SubfieldClass.ratCast_mem k q
  rw [phiC_of_mem hq, show (⟨(q : ℂ_[ℓ]), hq⟩ : k) = (q : k) from Subtype.ext (by simp), map_ratCast]
  simp

/-- **`phiC` fixes the naturals.** -/
theorem phiC_natCast (n : ℕ) : phiC k φ (n : ℂ_[ℓ]) = n := by
  simpa using phiC_ratCast (k := k) (φ := φ) (n : ℚ)

/-- **`phiC 0 = 0`.** -/
theorem phiC_zero : phiC k φ 0 = 0 := by simpa using phiC_natCast (k := k) (φ := φ) 0

/-- **`phiC` is additive on finite sums in `k`.** -/
theorem phiC_sum {ι : Type} (s : Finset ι) {f : ι → ℂ_[ℓ]} (hf : ∀ i ∈ s, f i ∈ k) :
    phiC k φ (∑ i ∈ s, f i) = ∑ i ∈ s, phiC k φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phiC_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, phiC_add (hf a (Finset.mem_insert_self _ _))
      (k.sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **A Frobenius lift keeps the unit ball**, for `phiC`. -/
theorem norm_phiC_le_one (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {x : ℂ_[ℓ]} (hx : x ∈ k)
    (h1 : ‖x‖ ≤ 1) : ‖phiC k φ x‖ ≤ 1 := by
  rw [phiC_of_mem hx]
  exact norm_map_le_one hφ (x := ⟨x, hx⟩) h1

variable (k φ)

/-- **Frobenius on the coefficients of a series** (`phiC` coefficientwise). -/
def phiS {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) : MvPowerSeries σ ℂ_[ℓ] :=
  fun e => phiC k φ (MvPowerSeries.coeff e f)

/-- **The Dwork operator** `T f = f − ℓ⁻¹·f^φ(X^ℓ)`, for series with coefficients in `k`. -/
def tOpC {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) : MvPowerSeries σ ℂ_[ℓ] :=
  f - MvPowerSeries.C (ℓ : ℂ_[ℓ])⁻¹ * MvPowerSeries.expand ℓ hℓp.out.ne_zero (phiS k φ f)

variable {k φ}

/-- **The coefficients of `phiS`.** -/
theorem coeff_phiS {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (phiS k φ f) = phiC k φ (MvPowerSeries.coeff e f) := rfl

/-- **The coefficients of `T f` at `ℓ`-multiples**: `(T f)_{ℓβ} = f_{ℓβ} − ℓ⁻¹·φ(f_β)`. -/
theorem coeff_tOpC_smul {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) (β : σ →₀ ℕ) :
    MvPowerSeries.coeff (ℓ • β) (tOpC k φ f) =
      MvPowerSeries.coeff (ℓ • β) f - (ℓ : ℂ_[ℓ])⁻¹ * phiC k φ (MvPowerSeries.coeff β f) := by
  rw [tOpC, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_expand_smul, coeff_phiS]

/-- **The coefficients of `T f` off the `ℓ`-multiples** are those of `f`. -/
theorem coeff_tOpC_of_not_dvd {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) {e : σ →₀ ℕ} {i : σ} (h : ¬ ℓ ∣ e i) :
    MvPowerSeries.coeff e (tOpC k φ f) = MvPowerSeries.coeff e f := by
  rw [tOpC, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_expand_of_not_dvd _ _ _ h, mul_zero,
    sub_zero]

/-- **The lift of a series with coefficients in `k`** to a series over `k`. -/
def liftK {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) (hf : ∀ e, MvPowerSeries.coeff e f ∈ k) :
    MvPowerSeries σ k :=
  fun e => ⟨MvPowerSeries.coeff e f, hf e⟩

/-- **The lift maps back to the series.** -/
theorem map_liftK {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) (hf : ∀ e, MvPowerSeries.coeff e f ∈ k) :
    MvPowerSeries.map k.subtype (liftK f hf) = f := by
  ext e
  rfl

/-- **The Frobenius of the lift** is `f^φ(X^ℓ)` in `ℂ_ℓ`. -/
theorem map_frobS_liftK {σ : Type} (f : MvPowerSeries σ ℂ_[ℓ]) (hf : ∀ e, MvPowerSeries.coeff e f ∈ k) :
    MvPowerSeries.map k.subtype (frobS ℓ φ (liftK f hf)) =
      MvPowerSeries.expand ℓ hℓp.out.ne_zero (phiS k φ f) := by
  change MvPowerSeries.map k.subtype (MvPowerSeries.expand ℓ hℓp.out.ne_zero
    (MvPowerSeries.map φ (liftK f hf))) = _
  rw [MvPowerSeries.map_expand]
  congr 1
  ext e
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, coeff_phiS, phiC_of_mem (hf e)]
  rfl

/-- **Dwork's criterion in `T`-form**: a series with coefficients in `k` and no constant term is `≃ 0` iff
`T f = f − ℓ⁻¹·f^φ(X^ℓ)` is integral (`simeq_zero_iff_dwork`, divided by `−ℓ`). -/
theorem simeq_zero_iff_isIntK_tOpC {σ : Type} [Finite σ] (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    {f : MvPowerSeries σ ℂ_[ℓ]} (hf : ∀ e, MvPowerSeries.coeff e f ∈ k)
    (hf0 : MvPowerSeries.constantCoeff f = 0) : Simeq f 0 ↔ IsIntK (tOpC k φ f) := by
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓp.out.ne_zero
  have hn0 : 0 < ‖(ℓ : ℂ_[ℓ])‖ := norm_pos_iff.2 hℓ0
  have hk0 : MvPowerSeries.constantCoeff (liftK f hf) = 0 := Subtype.ext (by
    change MvPowerSeries.coeff 0 f = 0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0])
  have h := simeq_zero_iff_dwork k hφ hk0
  rw [map_liftK] at h
  rw [h]
  have key : ∀ e, ‖((MvPowerSeries.coeff e (frobS ℓ φ (liftK f hf) - ℓ • liftK f hf) : k) : ℂ_[ℓ])‖ =
      ‖(ℓ : ℂ_[ℓ])‖ * ‖MvPowerSeries.coeff e (tOpC k φ f)‖ := fun e => by
    have h1 := congrArg (MvPowerSeries.coeff e) (map_frobS_liftK (φ := φ) f hf)
    rw [MvPowerSeries.coeff_map] at h1
    change ‖k.subtype (MvPowerSeries.coeff e (frobS ℓ φ (liftK f hf) - ℓ • liftK f hf))‖ = _
    rw [map_sub, map_sub, map_nsmul, h1, tOpC, map_sub, MvPowerSeries.coeff_C_mul]
    change ‖_ - ℓ • MvPowerSeries.coeff e f‖ = _
    rw [← norm_mul, nsmul_eq_mul, ← norm_neg]
    congr 1
    field_simp
    ring
  constructor
  · intro hD e
    have h2 := hD e
    change ‖((MvPowerSeries.coeff e (frobS ℓ φ (liftK f hf) - ℓ • liftK f hf) : k) : ℂ_[ℓ])‖ ≤
      ‖((ℓ : k) : ℂ_[ℓ])‖ at h2
    rw [key, show ((ℓ : k) : ℂ_[ℓ]) = (ℓ : ℂ_[ℓ]) from map_natCast k.subtype ℓ] at h2
    exact le_of_mul_le_mul_left (by rwa [mul_one]) hn0
  · intro hT e
    change ‖((MvPowerSeries.coeff e (frobS ℓ φ (liftK f hf) - ℓ • liftK f hf) : k) : ℂ_[ℓ])‖ ≤
      ‖((ℓ : k) : ℂ_[ℓ])‖
    rw [key, show ((ℓ : k) : ℂ_[ℓ]) = (ℓ : ℂ_[ℓ]) from map_natCast k.subtype ℓ]
    exact mul_le_of_le_one_right hn0.le (hT e)

/-- **Dwork, the easy coefficients**: a series with coefficients in `k`, no constant term and `≃ 0` has integral
coefficients at every exponent not divisible by `ℓ` (there `T f` and `f` agree). -/
theorem norm_coeff_le_one_of_simeq_zero {σ : Type} [Finite σ]
    (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {f : MvPowerSeries σ ℂ_[ℓ]}
    (hf : ∀ e, MvPowerSeries.coeff e f ∈ k) (hf0 : MvPowerSeries.constantCoeff f = 0) (hs : Simeq f 0)
    {e : σ →₀ ℕ} {i : σ} (hi : ¬ ℓ ∣ e i) : ‖MvPowerSeries.coeff e f‖ ≤ 1 := by
  have h := ((simeq_zero_iff_isIntK_tOpC hφ hf hf0).1 hs) e
  rwa [coeff_tOpC_of_not_dvd f hi] at h

end Frob

/-! ## Exponents, and the coefficients of the group law -/

section GroupLaw

/-- **Two-variable exponents** `X^m Y^n`. -/
abbrev ex2 (m n : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 m + Finsupp.single 1 n

/-- **Three-variable exponents** `X^i X′^j Y^n`. -/
abbrev ex3 (i j n : ℕ) : Fin 3 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 n

/-- **Every two-variable exponent is an `ex2`.** -/
theorem eq_ex2 (e : Fin 2 →₀ ℕ) : e = ex2 (e 0) (e 1) := eq_single_add_single e

/-- **Every three-variable exponent is an `ex3`.** -/
theorem eq_ex3 (e : Fin 3 →₀ ℕ) : e = ex3 (e 0) (e 1) (e 2) := by
  ext i
  fin_cases i <;> simp

/-- **`ex2` is injective.** -/
theorem ex2_inj {a b c d : ℕ} : ex2 a b = ex2 c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The order on `ex2`** is componentwise. -/
theorem ex2_le_ex2 {a b c d : ℕ} : ex2 a b ≤ ex2 c d ↔ a ≤ c ∧ b ≤ d := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i <;> simpa

/-- **Subtraction of `ex2`** is componentwise. -/
theorem ex2_sub_ex2 (a b c d : ℕ) : ex2 c d - ex2 a b = ex2 (c - a) (d - b) := by
  ext i
  fin_cases i <;> simp

/-- **The total degree of `ex2`.** -/
theorem degree_ex2 (m n : ℕ) : (ex2 m n).degree = m + n := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- **The coordinate sum of `ex2`.** -/
theorem sum_ex2 (m n : ℕ) : ((ex2 m n).sum fun _ e => e) = m + n := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
    Finsupp.sum_single_index rfl]

/-- **Monomials in two variables**: `X^a Y^b = monomial (a, b)`. -/
theorem X_pow_mul_X_pow (a b : ℕ) :
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) ^ a * MvPowerSeries.X 1 ^ b =
      MvPowerSeries.monomial (ex2 a b) 1 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]

/-- **The coefficients of `X`.** -/
theorem coeff_X0_ex2 (a b : ℕ) : MvPowerSeries.coeff (ex2 a b) (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) =
    if a = 1 ∧ b = 0 then 1 else 0 := by
  rw [MvPowerSeries.coeff_X, show Finsupp.single (0 : Fin 2) 1 = ex2 1 0 by simp [ex2]]
  simp only [ex2_inj]

/-- **The coefficients of `Y`.** -/
theorem coeff_X1_ex2 (a b : ℕ) : MvPowerSeries.coeff (ex2 a b) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) =
    if a = 0 ∧ b = 1 then 1 else 0 := by
  rw [MvPowerSeries.coeff_X, show Finsupp.single (1 : Fin 2) 1 = ex2 0 1 by simp [ex2]]
  simp only [ex2_inj]

variable (ℓ) in
/-- **The coefficients of the powers of the group law**: `[X^iY^j](X ⊕ Y)^m`. -/
def fc (m i j : ℕ) : ℂ_[ℓ] := MvPowerSeries.coeff (ex2 i j) (ltAdd ℂ_[ℓ] ℓ ^ m)

/-- **The group law is integral.** -/
theorem norm_fc_le_one (m i j : ℕ) : ‖fc ℓ m i j‖ ≤ 1 := (isIntK_ltAdd.pow m) _

/-- **The group law has rational coefficients.** -/
theorem exists_ratCast_fc (m i j : ℕ) : ∃ q : ℚ, fc ℓ m i j = q := by
  refine ⟨MvPowerSeries.coeff (ex2 i j) (ltAdd ℚ ℓ ^ m), ?_⟩
  rw [fc, ← map_ltAdd (algebraMap ℚ ℂ_[ℓ]) hℓp.out.one_lt, ← map_pow, MvPowerSeries.coeff_map]
  exact eq_ratCast _ _

/-- **The coefficients of the group law lie in every subfield.** -/
theorem fc_mem (k : Subfield ℂ_[ℓ]) (m i j : ℕ) : fc ℓ m i j ∈ k := by
  obtain ⟨q, hq⟩ := exists_ratCast_fc (ℓ := ℓ) m i j
  rw [hq]
  exact SubfieldClass.ratCast_mem k q

/-- **Frobenius fixes the coefficients of the group law.** -/
theorem phiC_fc {k : Subfield ℂ_[ℓ]} {φ : k →+* k} (m i j : ℕ) : phiC k φ (fc ℓ m i j) = fc ℓ m i j := by
  obtain ⟨q, hq⟩ := exists_ratCast_fc (ℓ := ℓ) m i j
  rw [hq, phiC_ratCast]

/-- **The coefficients of `F(Y, X)`**: `[X^mY^n] F(Y, X) = [X^nY^m] F`. -/
theorem coeff_subst_swap (G : MvPowerSeries (Fin 2) ℂ_[ℓ]) (m n : ℕ) :
    MvPowerSeries.coeff (ex2 m n) (MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] G) =
      MvPowerSeries.coeff (ex2 n m) G := by
  set e : Fin 2 ↪ Fin 2 := (Equiv.swap (0 : Fin 2) 1).toEmbedding
  have he : (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) =
      MvPowerSeries.X ∘ e := by
    funext i
    fin_cases i <;> simp [e]
  rw [he, ← MvPowerSeries.rename_eq_subst]
  have h : ex2 m n = Finsupp.embDomain e (ex2 n m) := by
    rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single, add_comm]
    simp [e]
  rw [h, MvPowerSeries.coeff_embDomain_rename]

/-- **The group law is commutative**: `F(Y, X) = F(X, Y)`. -/
theorem subst_swap_ltAdd :
    MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (ltAdd ℂ_[ℓ] ℓ) = ltAdd ℂ_[ℓ] ℓ := by
  have c0 := MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (0 : Fin 2)
  have c1 := MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (1 : Fin 2)
  have hid : MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] (ltAdd ℂ_[ℓ] ℓ) = ltAdd ℂ_[ℓ] ℓ := by
    have : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) = MvPowerSeries.X := by
      funext i
      fin_cases i <;> rfl
    rw [this, MvPowerSeries.subst_self]
    rfl
  have h := addP_comm (ℓ := ℓ) c1 c0
  rw [addP, addP, hid] at h
  exact h

/-- **The group law is symmetric in its coefficients.** -/
theorem coeff_ltAdd_swap (a b : ℕ) :
    MvPowerSeries.coeff (ex2 a b) (ltAdd ℂ_[ℓ] ℓ) = MvPowerSeries.coeff (ex2 b a) (ltAdd ℂ_[ℓ] ℓ) := by
  rw [← coeff_subst_swap, subst_swap_ltAdd]

/-- **`F(0, Y) = Y`**, in coefficients: `[Y^a] F = [a = 1]`. -/
theorem coeff_ltAdd_zero_left (a : ℕ) :
    MvPowerSeries.coeff (ex2 0 a) (ltAdd ℂ_[ℓ] ℓ) = if a = 1 then 1 else 0 := by
  have hℓ := hℓp.out.one_lt
  have hψ0 : ∀ i, MvPowerSeries.constantCoeff
      ((![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) i) = 0 := fun i => by
    fin_cases i <;> simp
  have hY : MvPowerSeries.subst (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ])
      (ltAdd ℂ_[ℓ] ℓ) = MvPowerSeries.X 1 := by
    refine eq_of_lgP_eq hℓ (MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0) hψ0 (constantCoeff_ltAdd hℓ))
      (MvPowerSeries.constantCoeff_X 1) ?_
    rw [lgP_subst_ltAdd hℓ hψ0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [lgP_zero hℓ, zero_add]
  have h := coeff_subst_zero_X (ltAdd ℂ_[ℓ] ℓ) (Finsupp.single 1 a)
  rw [hY, ite_eq_left (by simp), Finsupp.single_eq_same] at h
  have e : ex2 0 a = Finsupp.single 1 a := by simp
  rw [e, ← h, MvPowerSeries.coeff_X]
  by_cases ha : a = 1
  · subst ha
    simp
  · rw [ite_eq_right ha, ite_eq_right fun h' => ha (Finsupp.single_injective 1 h')]

/-- **`F(X, 0) = X`**, in coefficients: `[X^a] F = [a = 1]`. -/
theorem coeff_ltAdd_zero_right (a : ℕ) :
    MvPowerSeries.coeff (ex2 a 0) (ltAdd ℂ_[ℓ] ℓ) = if a = 1 then 1 else 0 := by
  rw [coeff_ltAdd_swap, coeff_ltAdd_zero_left]

variable (ℓ) in
/-- **The group law divided by `Y` off the `X`-axis**: `F = X + Y·H`. -/
def grpH : MvPowerSeries (Fin 2) ℂ_[ℓ] :=
  fun e => MvPowerSeries.coeff (e + Finsupp.single 1 1) (ltAdd ℂ_[ℓ] ℓ)

/-- **The coefficients of `H`.** -/
theorem coeff_grpH (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (grpH ℓ) = MvPowerSeries.coeff (e + Finsupp.single 1 1) (ltAdd ℂ_[ℓ] ℓ) := rfl

/-- **`H` is integral.** -/
theorem norm_coeff_grpH_le_one (e : Fin 2 →₀ ℕ) : ‖MvPowerSeries.coeff e (grpH ℓ)‖ ≤ 1 := isIntK_ltAdd _

/-- **`H(0) = 1`.** -/
theorem coeff_zero_grpH : MvPowerSeries.coeff (ex2 0 0) (grpH ℓ) = 1 := by
  rw [coeff_grpH, show ex2 0 0 + Finsupp.single 1 1 = ex2 0 1 by simp, coeff_ltAdd_zero_left, ite_eq_left rfl]

/-- **`Y` as a monomial.** -/
theorem X_one_eq_monomial :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) = MvPowerSeries.monomial (ex2 0 1) 1 := by
  rw [← pow_one (MvPowerSeries.X 1), MvPowerSeries.X_pow_eq]
  simp [ex2]

/-- **`F = X + Y·H`** (from `F(X, 0) = X`). -/
theorem ltAdd_eq_X_add_X_mul_grpH :
    ltAdd ℂ_[ℓ] ℓ = MvPowerSeries.X 0 + MvPowerSeries.X 1 * grpH ℓ := by
  ext e
  obtain ⟨a, b, rfl⟩ : ∃ a b, e = ex2 a b := ⟨e 0, e 1, eq_ex2 e⟩
  have h1 := coeff_X0_ex2 (ℓ := ℓ) a b
  have h2 : MvPowerSeries.coeff (ex2 a b) (MvPowerSeries.X 1 * grpH ℓ) =
      if 1 ≤ b then MvPowerSeries.coeff (ex2 a b) (ltAdd ℂ_[ℓ] ℓ) else 0 := by
    rw [X_one_eq_monomial, MvPowerSeries.coeff_monomial_mul]
    by_cases hb : 1 ≤ b
    · rw [ite_eq_left (ex2_le_ex2.2 ⟨Nat.zero_le _, hb⟩), ite_eq_left hb, one_mul, ex2_sub_ex2, coeff_grpH,
        show ex2 (a - 0) (b - 1) + Finsupp.single 1 1 = ex2 a b by ext i; fin_cases i <;> simp [ex2]; omega]
    · rw [ite_eq_right (fun h => hb (ex2_le_ex2.1 h).2), ite_eq_right hb]
  rw [map_add, h1, h2]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [coeff_ltAdd_zero_right, ite_eq_right (by omega : ¬ 1 ≤ 0), add_zero]
    simp
  · rw [ite_eq_right (fun h => absurd h.2 hb.ne'), ite_eq_left (show 1 ≤ b from hb), zero_add]

/-- **The `Y`-linear part of the powers of the group law**: `F^{m+1} = X^{m+1} + (m+1)X^mY·H + Y²·W`. -/
theorem exists_ltAdd_pow (m : ℕ) : ∃ W : MvPowerSeries (Fin 2) ℂ_[ℓ], ltAdd ℂ_[ℓ] ℓ ^ (m + 1) =
    MvPowerSeries.X 0 ^ (m + 1) + ((m + 1 : ℕ) : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
      (MvPowerSeries.X 0 ^ m * MvPowerSeries.X 1 * grpH ℓ) + MvPowerSeries.X 1 ^ 2 * W := by
  induction m with
  | zero =>
    refine ⟨0, ?_⟩
    rw [zero_add, pow_one, ltAdd_eq_X_add_X_mul_grpH]
    push_cast
    ring
  | succ m ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨((m + 1 : ℕ) : MvPowerSeries (Fin 2) ℂ_[ℓ]) * MvPowerSeries.X 0 ^ m * grpH ℓ ^ 2 +
      W * (MvPowerSeries.X 0 + MvPowerSeries.X 1 * grpH ℓ), ?_⟩
    rw [pow_succ, hW, ltAdd_eq_X_add_X_mul_grpH]
    push_cast
    ring

/-- **The `Y`-linear coefficients of the powers of the group law**: `[X^pY](F^{m+1}) = (m+1)·H_{p−m}`. -/
theorem fc_succ_one (m p : ℕ) :
    fc ℓ (m + 1) p 1 = (m + 1 : ℂ_[ℓ]) *
      (if m ≤ p then MvPowerSeries.coeff (ex2 (p - m) 0) (grpH ℓ) else 0) := by
  obtain ⟨W, hW⟩ := exists_ltAdd_pow (ℓ := ℓ) m
  have hA : MvPowerSeries.coeff (ex2 p 1) (MvPowerSeries.X 0 ^ (m + 1) : MvPowerSeries (Fin 2) ℂ_[ℓ]) = 0 := by
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, ite_eq_right]
    intro h
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp [ex2] at this
  have hB : MvPowerSeries.coeff (ex2 p 1) (MvPowerSeries.X 0 ^ m * MvPowerSeries.X 1 * grpH ℓ) =
      if m ≤ p then MvPowerSeries.coeff (ex2 (p - m) 0) (grpH ℓ) else 0 := by
    rw [show (MvPowerSeries.X 0 ^ m * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) =
        MvPowerSeries.monomial (ex2 m 1) 1 by
      rw [X_one_eq_monomial, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]
      congr 1
      simp [ex2], MvPowerSeries.coeff_monomial_mul]
    by_cases hm : m ≤ p
    · rw [ite_eq_left (ex2_le_ex2.2 ⟨hm, le_rfl⟩), ite_eq_left hm, one_mul, ex2_sub_ex2]
    · rw [ite_eq_right fun h => hm (ex2_le_ex2.1 h).1, ite_eq_right hm]
  have hC : MvPowerSeries.coeff (ex2 p 1) (MvPowerSeries.X 1 ^ 2 * W) = 0 := by
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, ite_eq_right]
    intro h
    have := (Finsupp.le_def.1 h) 1
    simp [ex2] at this
  rw [fc, hW, map_add, map_add, hA, hC, ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := ℂ_[ℓ])),
    MvPowerSeries.coeff_C_mul, hB]
  push_cast
  ring

/-- **`[X^pY]F^0 = 0`.** -/
theorem fc_zero_one (p : ℕ) : fc ℓ 0 p 1 = 0 := by
  rw [fc, pow_zero, MvPowerSeries.coeff_one, ite_eq_right fun h => by
    simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h]

/-- **The coefficients of `(X + Y)^N`**: `[X^iY^{N−i}](X + Y)^N = C(N, i)`. -/
theorem coeff_X_add_X_pow {N i : ℕ} (hi : i ≤ N) :
    MvPowerSeries.coeff (ex2 i (N - i))
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) ^ N) = (N.choose i : ℂ_[ℓ]) := by
  rw [add_pow, map_sum, Finset.sum_eq_single i]
  · rw [← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := ℂ_[ℓ])), MvPowerSeries.coeff_mul_C, X_pow_mul_X_pow,
      MvPowerSeries.coeff_monomial, ite_eq_left rfl, one_mul]
  · intro t ht hti
    rw [← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := ℂ_[ℓ])), MvPowerSeries.coeff_mul_C, X_pow_mul_X_pow,
      MvPowerSeries.coeff_monomial, ite_eq_right fun h => hti (ex2_inj.1 h).1.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- **The lowest-degree part of the powers of the group law**: `[X^iY^{N−i}]F^N = C(N, i)` (as
`F ≡ X + Y` modulo degree `2`). -/
theorem fc_top {N i : ℕ} (hi : i ≤ N) : fc ℓ N i (N - i) = (N.choose i : ℂ_[ℓ]) := by
  have hℓ := hℓp.out.one_lt
  set F := ltAdd ℂ_[ℓ] ℓ
  set S : MvPowerSeries (Fin 2) ℂ_[ℓ] := MvPowerSeries.X 0 + MvPowerSeries.X 1
  have hF0 : MvPowerSeries.constantCoeff F = 0 := constantCoeff_ltAdd hℓ
  have hS0 : MvPowerSeries.constantCoeff S = 0 := by simp [S]
  -- `F − S` has order at least `2`
  have hR : ((2 : ℕ) : ℕ∞) ≤ (F - S).order := by
    refine MvPowerSeries.nat_le_order fun d hd => ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b, d = ex2 a b := ⟨d 0, d 1, eq_ex2 d⟩
    rw [degree_ex2] at hd
    rw [map_sub, map_add, coeff_X0_ex2, coeff_X1_ex2]
    rcases (by omega : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [coeff_ltAdd_zero_left]
      simp
    · rw [coeff_ltAdd_zero_right]
      simp
    · rw [coeff_ltAdd_zero_left]
      simp
  -- the geometric sum has order at least `N − 1`
  set G := ∑ t ∈ Finset.range N, F ^ t * S ^ (N - 1 - t)
  have hG : ((N - 1 : ℕ) : ℕ∞) ≤ G.order := by
    refine MvPowerSeries.nat_le_order fun d hd => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun t ht => MvPowerSeries.coeff_of_lt_order ?_
    rw [Finset.mem_range] at ht
    refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_mul)
    refine lt_of_lt_of_le ?_ (add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero t hF0)
      (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (N - 1 - t) hS0))
    exact_mod_cast (by omega : d.degree < t + (N - 1 - t))
  have hGR : ((N + 1 : ℕ) : ℕ∞) ≤ (G * (F - S)).order := by
    refine le_trans ?_ MvPowerSeries.le_order_mul
    refine le_trans ?_ (add_le_add hG hR)
    exact_mod_cast (by omega : N + 1 ≤ N - 1 + 2)
  have h := MvPowerSeries.coeff_of_lt_order (d := ex2 i (N - i)) (lt_of_lt_of_le
    (by rw [degree_ex2]; exact_mod_cast (by omega : i + (N - i) < N + 1)) hGR)
  rw [geom_sum₂_mul, map_sub, sub_eq_zero] at h
  rw [fc, h, coeff_X_add_X_pow hi]

end GroupLaw

/-! ## The additivity defect and its coefficients -/

section Defect

/-- **The ultrametric inequality for differences.** -/
theorem norm_sub_le_max' (x y : ℂ_[ℓ]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

/-- **Differences of integral elements are integral.** -/
theorem norm_sub_le_one {x y : ℂ_[ℓ]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 :=
  (norm_sub_le_max' x y).trans (max_le hx hy)

/-- **Sums of integral elements are integral.** -/
theorem norm_add_le_one {x y : ℂ_[ℓ]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

/-- **The additivity defect in `X`**: `B(X ⊕ X′, Y) − B(X, Y) − B(X′, Y)` (variables `X, X′, Y` = `0, 1, 2`). -/
def deltaX (B : MvPowerSeries (Fin 2) ℂ_[ℓ]) : MvPowerSeries (Fin 3) ℂ_[ℓ] :=
  MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2] B -
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2] B -
    MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2] B

/-- **`GaussClass`'s biadditivity hypothesis is `deltaX B ≃ 0`.** -/
theorem biadd_iff_deltaX (B : MvPowerSeries (Fin 2) ℂ_[ℓ]) :
    Simeq (MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2] B)
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2] B +
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2] B) ↔
      Simeq (deltaX B) 0 := by
  rw [simeq_iff_sub, deltaX, sub_sub]

variable (ℓ) in
/-- **The defect coefficients** of a column `g`: `[X^iX′^j](g(X ⊕ X′) − g(X) − g(X′))`. -/
def dC (g : ℕ → ℂ_[ℓ]) (i j : ℕ) : ℂ_[ℓ] :=
  ∑ m ∈ Finset.range (i + j + 1), g m * fc ℓ m i j - (if j = 0 then g i else 0) - (if i = 0 then g j else 0)

/-- **The coefficients of `Q(X, X′)` in three variables.** -/
theorem coeff_subst_X0_X1 (Q : MvPowerSeries (Fin 2) ℂ_[ℓ]) (i j n : ℕ) :
    MvPowerSeries.coeff (ex3 i j n)
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 1] Q) =
      if n = 0 then MvPowerSeries.coeff (ex2 i j) Q else 0 := by
  set e : Fin 2 ↪ Fin 3 := Fin.castSuccEmb
  have he : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[ℓ]) =
      MvPowerSeries.X ∘ e := by
    funext i
    fin_cases i <;> rfl
  rw [he, ← MvPowerSeries.rename_eq_subst]
  split_ifs with hn
  · subst hn
    have h : ex3 i j 0 = Finsupp.embDomain e (ex2 i j) := by
      rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]
      simp [e, ex3]
    rw [h, MvPowerSeries.coeff_embDomain_rename]
  · refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨d, hd⟩
    have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) hd
    rw [Finsupp.mapDomain_of_notMem_range] at h2
    · apply hn
      simp at h2
      omega
    · rintro ⟨x, hx⟩
      fin_cases x <;> simp [e] at hx

/-- **The `Y`-separation formula**: in `B(G(X, X′), Y)` only the `Y`-exponent `n` of `B` meets `Y^n`. -/
theorem coeff_subst_pair_X2 (G B : MvPowerSeries (Fin 2) ℂ_[ℓ]) (hG : MvPowerSeries.constantCoeff G = 0)
    (i j n : ℕ) :
    MvPowerSeries.coeff (ex3 i j n) (MvPowerSeries.subst
      ![MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 1] G,
        MvPowerSeries.X 2] B) =
      ∑ m ∈ Finset.range (i + j + 1), MvPowerSeries.coeff (ex2 m n) B * MvPowerSeries.coeff (ex2 i j) (G ^ m) := by
  classical
  have h01 : ∀ s, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[ℓ]) s) = 0 := fun s => by
    fin_cases s <;> simp
  have hs01 := MvPowerSeries.hasSubst_of_constantCoeff_zero h01
  set A := MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 1] G
  have hA0 : MvPowerSeries.constantCoeff A = 0 := MvPowerSeries.constantCoeff_subst_eq_zero hs01 h01 hG
  have hs := hasSubst_pair hA0 (MvPowerSeries.constantCoeff_X 2)
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e =>
      (![A, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[ℓ]) s ^ e) = A ^ d 0 * MvPowerSeries.X 2 ^ d 1 :=
    fun d => by
      rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
      rfl
  have hterm : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d B •
      MvPowerSeries.coeff (ex3 i j n) (A ^ d 0 * MvPowerSeries.X 2 ^ d 1) =
      if d 1 = n then MvPowerSeries.coeff d B * MvPowerSeries.coeff (ex2 i j) (G ^ d 0) else 0 := by
    intro d
    rw [smul_eq_mul, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial, ← MvPowerSeries.subst_pow hs01]
    by_cases h : d 1 ≤ n
    · rw [ite_eq_left (by rw [Finsupp.single_le_iff]; simpa using h),
        show ex3 i j n - Finsupp.single 2 (d 1) = ex3 i j (n - d 1) by ext s; fin_cases s <;> simp,
        coeff_subst_X0_X1, mul_one]
      by_cases h' : d 1 = n
      · rw [ite_eq_left (by omega), ite_eq_left h']
      · rw [ite_eq_right (by omega), ite_eq_right h', mul_zero]
    · rw [ite_eq_right (by rw [Finsupp.single_le_iff]; simpa using h), ite_eq_right (by omega), mul_zero]
  rw [MvPowerSeries.coeff_subst hs]
  simp_rw [hprod, hterm]
  have hinj : Set.InjOn (fun m => ex2 m n) ↑(Finset.range (i + j + 1)) := fun a _ b _ hab => (ex2_inj.1 hab).1
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (i + j + 1)).image fun m => ex2 m n),
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [ite_eq_left (by simp)]
    simp
  · intro d hd
    rw [Function.mem_support] at hd
    by_cases h1 : d 1 = n
    · rw [ite_eq_left h1] at hd
      have hle : d 0 ≤ i + j := by
        by_contra hlt
        exact hd (by rw [coeff_pow_eq_zero hG (by rw [sum_ex2]; omega), mul_zero])
      rw [Finset.coe_image]
      refine ⟨d 0, Finset.mem_coe.2 (Finset.mem_range.2 (by omega)), ?_⟩
      show ex2 (d 0) n = d
      rw [← h1]
      exact (eq_ex2 d).symm
    · exact absurd (ite_eq_right h1) hd

/-- **The coefficients of `X^m`.** -/
theorem coeff_X0_pow_ex2 (m a b : ℕ) :
    MvPowerSeries.coeff (ex2 a b) ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) ^ m) =
      if a = m ∧ b = 0 then 1 else 0 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, show Finsupp.single (0 : Fin 2) m = ex2 m 0 by
    simp [ex2]]
  simp only [ex2_inj]

/-- **The coefficients of `Y^m`.** -/
theorem coeff_X1_pow_ex2 (m a b : ℕ) :
    MvPowerSeries.coeff (ex2 a b) ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) ^ m) =
      if a = 0 ∧ b = m then 1 else 0 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, show Finsupp.single (1 : Fin 2) m = ex2 0 m by
    simp [ex2]]
  simp only [ex2_inj]

/-- **The coefficients of the additivity defect**: `[X^iX′^jY^n] deltaX B = dC (B_{·,n}) i j`. -/
theorem coeff_deltaX (B : MvPowerSeries (Fin 2) ℂ_[ℓ]) (i j n : ℕ) :
    MvPowerSeries.coeff (ex3 i j n) (deltaX B) = dC ℓ (fun m => MvPowerSeries.coeff (ex2 m n) B) i j := by
  have h01 : ∀ s, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[ℓ]) s) = 0 := fun s => by
    fin_cases s <;> simp
  have hs01 := MvPowerSeries.hasSubst_of_constantCoeff_zero h01
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]) = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 1] (MvPowerSeries.X 0 :
        MvPowerSeries (Fin 2) ℂ_[ℓ]) := by rw [MvPowerSeries.subst_X hs01]; rfl
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]) = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 1] (MvPowerSeries.X 1 :
        MvPowerSeries (Fin 2) ℂ_[ℓ]) := by rw [MvPowerSeries.subst_X hs01]; rfl
  rw [deltaX, map_sub, map_sub]
  conv_lhs =>
    arg 1; arg 2
    rw [hX0]
  conv_lhs =>
    arg 2
    rw [hX1]
  rw [addP, coeff_subst_pair_X2 _ _ (constantCoeff_ltAdd hℓp.out.one_lt),
    coeff_subst_pair_X2 _ _ (MvPowerSeries.constantCoeff_X 0),
    coeff_subst_pair_X2 _ _ (MvPowerSeries.constantCoeff_X 1), dC]
  congr 1
  · congr 1
    rw [Finset.sum_eq_single i]
    · rw [coeff_X0_pow_ex2]
      by_cases hj : j = 0
      · rw [ite_eq_left ⟨rfl, hj⟩, ite_eq_left hj, mul_one]
      · rw [ite_eq_right fun h => hj h.2, ite_eq_right hj, mul_zero]
    · intro m _ hm
      rw [coeff_X0_pow_ex2, ite_eq_right fun h => hm h.1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [Finset.sum_eq_single j]
    · rw [coeff_X1_pow_ex2]
      by_cases hi : i = 0
      · rw [ite_eq_left ⟨hi, rfl⟩, ite_eq_left hi, mul_one]
      · rw [ite_eq_right fun h => hi h.1, ite_eq_right hi, mul_zero]
    · intro m _ hm
      rw [coeff_X1_pow_ex2, ite_eq_right fun h => hm h.2.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h

/-- **`X ⊕ Y` in two variables is the group law.** -/
theorem addP_X0_X1 :
    addP (MvPowerSeries.X 0) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) = ltAdd ℂ_[ℓ] ℓ := by
  have : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) = MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [addP, this, MvPowerSeries.subst_self]
  rfl

/-- **The coefficients of `g(X ⊕ X′)`.** -/
theorem coeff_subst_ltAdd (g : ℂ_[ℓ]⟦X⟧) (i j : ℕ) :
    MvPowerSeries.coeff (ex2 i j) (g.subst (ltAdd ℂ_[ℓ] ℓ)) =
      ∑ m ∈ Finset.range (i + j + 1), coeff m g * fc ℓ m i j := by
  have hF0 := constantCoeff_ltAdd (K := ℂ_[ℓ]) hℓp.out.one_lt
  rw [PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hF0),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (i + j + 1))]
  · rfl
  · intro m hm
    rw [Function.mem_support] at hm
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hm (by rw [coeff_pow_eq_zero hF0 (by rw [sum_ex2]; omega), smul_zero])

/-- **The coefficients of `g(X)` in two variables.** -/
theorem coeff_subst_X0 (g : ℂ_[ℓ]⟦X⟧) (i j : ℕ) :
    MvPowerSeries.coeff (ex2 i j) (g.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ])) =
      if j = 0 then coeff i g else 0 := by
  classical
  rw [PowerSeries.coeff_subst_single]
  by_cases hj : j = 0
  · subst hj
    rw [ite_eq_left (by simp [ex2]), ite_eq_left rfl]
    simp
  · rw [ite_eq_right fun h => hj (by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h), ite_eq_right hj]

/-- **The coefficients of `g(Y)` in two variables.** -/
theorem coeff_subst_X1 (g : ℂ_[ℓ]⟦X⟧) (i j : ℕ) :
    MvPowerSeries.coeff (ex2 i j) (g.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ])) =
      if i = 0 then coeff j g else 0 := by
  classical
  rw [PowerSeries.coeff_subst_single]
  by_cases hi : i = 0
  · subst hi
    rw [ite_eq_left (by simp [ex2]), ite_eq_left rfl]
    simp
  · rw [ite_eq_right fun h => hi (by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h), ite_eq_right hi]

/-- **The defect coefficients of a one-variable series**: `[X^iX′^j](g(X ⊕ X′) − g(X) − g(X′)) = dC g i j`. -/
theorem coeff_defect (g : ℂ_[ℓ]⟦X⟧) (i j : ℕ) :
    MvPowerSeries.coeff (ex2 i j) (g.subst (ltAdd ℂ_[ℓ] ℓ) - g.subst (MvPowerSeries.X 0) -
      g.subst (MvPowerSeries.X 1)) = dC ℓ (fun m => coeff m g) i j := by
  rw [map_sub, map_sub, coeff_subst_ltAdd, coeff_subst_X0, coeff_subst_X1, dC]

/-- **`log_LT` is additive**: its defect coefficients vanish. -/
theorem dC_logLT (i j : ℕ) : dC ℓ (fun m => coeff m (logLT ℂ_[ℓ] ℓ)) i j = 0 := by
  rw [← coeff_defect]
  have h := lgP_ltAdd (K := ℂ_[ℓ]) hℓp.out.one_lt
  rw [lgP, lgP, lgP] at h
  rw [h]
  simp

/-- **`log_LT(T^ℓ)` is additive mod `ℓ`**: its defect coefficients are `ℓ`-divisible. -/
theorem norm_dC_lcF_le (i j : ℕ) : ‖dC ℓ (lcF ℓ) i j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ := by
  have hℓ0 := hℓp.out.ne_zero
  have c0 := MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (0 : Fin 2)
  have c1 := MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (1 : Fin 2)
  have cp : ∀ U : MvPowerSeries (Fin 2) ℂ_[ℓ], MvPowerSeries.constantCoeff U = 0 →
      MvPowerSeries.constantCoeff (U ^ ℓ) = 0 := fun U hU => by rw [map_pow, hU, zero_pow hℓ0]
  have hF0 := constantCoeff_ltAdd (K := ℂ_[ℓ]) hℓp.out.one_lt
  have hsub : ∀ A : MvPowerSeries (Fin 2) ℂ_[ℓ], MvPowerSeries.constantCoeff A = 0 →
      (logLTF ℓ).subst A = (logLT ℂ_[ℓ] ℓ).subst (A ^ ℓ) := fun A hA => by
    have hAs := HasSubst.of_constantCoeff_zero hA
    rw [logLTF, PowerSeries.subst_comp_subst_apply (HasSubst.X_pow hℓ0) hAs, PowerSeries.subst_pow hAs,
      PowerSeries.subst_X hAs]
  have e : dC ℓ (lcF ℓ) i j = dC ℓ (fun m => coeff m (logLTF ℓ)) i j := by
    simp only [coeff_logLTF]
  rw [e, ← coeff_defect, hsub _ hF0, hsub _ c0, hsub _ c1]
  have hA := lgP_addP (ℓ := ℓ) (cp _ c0) (cp _ c1)
  rw [lgP, lgP, lgP] at hA
  rw [sub_sub, ← hA]
  have hD := (isDivK_addP_pow_sub c0 c1 (isIntK_X 0) (isIntK_X 1)).neg
  rw [neg_sub, addP_X0_X1] at hD
  exact isDivK_logLT_subst_sub (isIntK_ltAdd.pow ℓ)
    (isIntK_addP (cp _ c0) (cp _ c1) ((isIntK_X 0).pow ℓ) ((isIntK_X 1).pow ℓ)) (cp _ hF0)
    (constantCoeff_addP (cp _ c0) (cp _ c1)) hD (ex2 i j)

/-- **`dC` is linear.** -/
theorem dC_smul (c : ℂ_[ℓ]) (g : ℕ → ℂ_[ℓ]) (i j : ℕ) : dC ℓ (fun m => c * g m) i j = c * dC ℓ g i j := by
  simp only [dC, mul_assoc, ← Finset.mul_sum]
  split_ifs <;> ring

/-- **`dC` is linear.** -/
theorem dC_sub (g h : ℕ → ℂ_[ℓ]) (i j : ℕ) : dC ℓ (fun m => g m - h m) i j = dC ℓ g i j - dC ℓ h i j := by
  simp only [dC, sub_mul, Finset.sum_sub_distrib]
  split_ifs <;> ring

/-- **`dC` of a column in `k` lies in `k`.** -/
theorem dC_mem (k : Subfield ℂ_[ℓ]) {g : ℕ → ℂ_[ℓ]} (hg : ∀ m, g m ∈ k) (i j : ℕ) : dC ℓ g i j ∈ k := by
  rw [dC]
  refine k.sub_mem (k.sub_mem (k.sum_mem fun m _ => k.mul_mem (hg m) (fc_mem k m i j)) ?_) ?_ <;>
    split_ifs <;> simp [hg, k.zero_mem]

/-- **Frobenius commutes with `dC`** on columns in `k`. -/
theorem phiC_dC {k : Subfield ℂ_[ℓ]} {φ : k →+* k} {g : ℕ → ℂ_[ℓ]} (hg : ∀ m, g m ∈ k) (i j : ℕ) :
    phiC k φ (dC ℓ g i j) = dC ℓ (fun m => phiC k φ (g m)) i j := by
  have hsum : ∑ m ∈ Finset.range (i + j + 1), g m * fc ℓ m i j ∈ k :=
    k.sum_mem fun m _ => k.mul_mem (hg m) (fc_mem k m i j)
  have hi1 : (if j = 0 then g i else 0) ∈ k := by split_ifs <;> simp [hg, k.zero_mem]
  have hi2 : (if i = 0 then g j else 0) ∈ k := by split_ifs <;> simp [hg, k.zero_mem]
  rw [dC, phiC_sub (k.sub_mem hsum hi1) hi2, phiC_sub hsum hi1,
    phiC_sum _ fun m _ => k.mul_mem (hg m) (fc_mem k m i j), dC]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [phiC_mul (hg m) (fc_mem k m i j), phiC_fc]
    · split_ifs <;> simp [phiC_zero]
  · split_ifs <;> simp [phiC_zero]

/-- **The top coefficient in the defect**: for `0 < i < N` and a column integral below `N`,
`‖C(N, i)·g_N‖ ≤ max(1, ‖dC g i (N − i)‖)` (as `[X^iX′^{N−i}]F^N = C(N, i)`). -/
theorem norm_choose_mul_le {g : ℕ → ℂ_[ℓ]} {N i : ℕ} (hi0 : 0 < i) (hiN : i < N) (hlow : ∀ m < N, ‖g m‖ ≤ 1)
    (hd : ‖dC ℓ g i (N - i)‖ ≤ 1) : ‖(N.choose i : ℂ_[ℓ]) * g N‖ ≤ 1 := by
  have hlow' : ‖∑ m ∈ Finset.range N, g m * fc ℓ m i (N - i)‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m hm => by
      rw [norm_mul]
      exact mul_le_one_of_le (hlow m (Finset.mem_range.1 hm)) (norm_fc_le_one m i (N - i))
  have e : (N.choose i : ℂ_[ℓ]) * g N = dC ℓ g i (N - i) - ∑ m ∈ Finset.range N, g m * fc ℓ m i (N - i) := by
    rw [dC, ite_eq_right (by omega), ite_eq_right (by omega), sub_zero, sub_zero,
      show i + (N - i) + 1 = N + 1 by omega, Finset.sum_range_succ, fc_top hiN.le]
    ring
  rw [e]
  exact (norm_sub_le_max' _ _).trans (max_le hd hlow')

/-- **The coefficients of `deltaX B` lie in `k`** when those of `B` do. -/
theorem coeff_deltaX_mem (k : Subfield ℂ_[ℓ]) {B : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hk : ∀ e, MvPowerSeries.coeff e B ∈ k) (e : Fin 3 →₀ ℕ) : MvPowerSeries.coeff e (deltaX B) ∈ k := by
  rw [eq_ex3 e, coeff_deltaX]
  exact dC_mem k (fun m => hk _) _ _

end Defect

/-! ## S1: biadditivity makes `B − L(X)·B_{1,·}(Y)` of divided-power type in `X` -/

section S1

/-- **Divided-power type in `X`**: `‖e₀·B_e‖ ≤ 1` for every exponent `e`. -/
def IsXDp (P : MvPowerSeries (Fin 2) ℂ_[ℓ]) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, ‖((e 0 : ℕ) : ℂ_[ℓ]) * MvPowerSeries.coeff e P‖ ≤ 1

variable {k : Subfield ℂ_[ℓ]} {φ : k →+* k}

/-- **S1, coefficientwise**: if `deltaX B ≃ 0` then `‖m·(B_{m,n} − L_m·B_{1,n})‖ ≤ 1`. The coefficients of
`deltaX B` at `X^pX′Y^n` are integral (Dwork: the exponent `1` is prime to `ℓ`), and they are
`Σ_{t ≤ p} (t + 1)·β_{t+1}·H_{p−t}` for `β = B_{·,n} − B_{1,n}·L` (`F = X + X′·H`, `log_LT` additive), with
`H_0 = 1`. -/
theorem norm_mul_coeff_sub_le_of_biadd (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    {B : MvPowerSeries (Fin 2) ℂ_[ℓ]} (hk : ∀ e, MvPowerSeries.coeff e B ∈ k) (hB : Simeq (deltaX B) 0)
    (m n : ℕ) : ‖(m : ℂ_[ℓ]) * (MvPowerSeries.coeff (ex2 m n) B -
      coeff m (logLT ℂ_[ℓ] ℓ) * MvPowerSeries.coeff (ex2 1 n) B)‖ ≤ 1 := by
  set u := MvPowerSeries.coeff (ex2 1 n) B
  set β : ℕ → ℂ_[ℓ] := fun m => MvPowerSeries.coeff (ex2 m n) B - u * coeff m (logLT ℂ_[ℓ] ℓ) with hβ
  have h0 : MvPowerSeries.constantCoeff (deltaX B) = 0 := by
    have := hB.1
    rwa [sub_zero] at this
  have hd : ∀ p, ‖dC ℓ β p 1‖ ≤ 1 := fun p => by
    have h := norm_coeff_le_one_of_simeq_zero hφ (coeff_deltaX_mem k hk) h0 hB (e := ex3 p 1 n) (i := 1)
      (by simpa using hℓp.out.not_dvd_one)
    rw [coeff_deltaX] at h
    rw [hβ, dC_sub, dC_smul, dC_logLT, mul_zero, sub_zero]
    exact h
  have hβ1 : β 1 = 0 := by simp [hβ, u, coeff_one_logLT]
  have key : ∀ p, dC ℓ β p 1 = ∑ t ∈ Finset.range (p + 1),
      ((t : ℂ_[ℓ]) + 1) * β (t + 1) * MvPowerSeries.coeff (ex2 (p - t) 0) (grpH ℓ) := fun p => by
    have hz : (if p = 0 then β 1 else 0) = 0 := by split_ifs <;> simp [hβ1]
    rw [dC, ite_eq_right one_ne_zero, hz, sub_zero, sub_zero, Finset.sum_range_succ', fc_zero_one, mul_zero,
      add_zero]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [fc_succ_one, ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht))]
    ring
  have hc : ∀ p : ℕ, ‖((p : ℂ_[ℓ]) + 1) * β (p + 1)‖ ≤ 1 := fun p => by
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      have e : ((p : ℂ_[ℓ]) + 1) * β (p + 1) = dC ℓ β p 1 - ∑ t ∈ Finset.range p,
          ((t : ℂ_[ℓ]) + 1) * β (t + 1) * MvPowerSeries.coeff (ex2 (p - t) 0) (grpH ℓ) := by
        rw [key p, Finset.sum_range_succ, Nat.sub_self, coeff_zero_grpH, mul_one]
        ring
      rw [e]
      refine norm_sub_le_one (hd p) (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
        fun t ht => ?_)
      rw [norm_mul]
      exact mul_le_one_of_le (ih t (Finset.mem_range.1 ht)) (norm_coeff_grpH_le_one _)
  rcases m with _ | p
  · simp
  · convert hc p using 2
    simp only [hβ]
    push_cast
    ring

/-- **S1**: `B − L(X)·u(Y)`, `u = B_{1,·}`, is of divided-power type in `X` when `deltaX B ≃ 0`. -/
theorem isXDp_of_biadd (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    {B : MvPowerSeries (Fin 2) ℂ_[ℓ]} (hk : ∀ e, MvPowerSeries.coeff e B ∈ k) (hB : Simeq (deltaX B) 0) :
    IsXDp (B - (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
      (PowerSeries.mk fun n => MvPowerSeries.coeff (ex2 1 n) B).subst
        (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ])) := by
  intro e
  obtain ⟨m, n, rfl⟩ : ∃ m n, e = ex2 m n := ⟨e 0, e 1, eq_ex2 e⟩
  rw [map_sub, coeff_subst_X0_mul_subst_X1, PowerSeries.coeff_mk]
  simpa using norm_mul_coeff_sub_le_of_biadd hφ hk hB m n

end S1

/-! ## S2: Frobenius commutes with `deltaX` modulo `ℓ` on divided-power series -/

section S2

/-- **Integral substitution pairs**: the three pairs of `deltaX` substitute. -/
theorem hasSubst_X_X (i j : Fin 3) :
    MvPowerSeries.HasSubst (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[ℓ]) :=
  hasSubst_pair (MvPowerSeries.constantCoeff_X i) (MvPowerSeries.constantCoeff_X j)

/-- **`X ⊕ X′` has no constant term.** -/
theorem constantCoeff_addP_X0_X1 :
    MvPowerSeries.constantCoeff (addP (MvPowerSeries.X 0) (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ])) = 0 :=
  constantCoeff_addP (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1)

/-- **`deltaX` is additive.** -/
theorem deltaX_sub (P Q : MvPowerSeries (Fin 2) ℂ_[ℓ]) : deltaX (P - Q) = deltaX P - deltaX Q := by
  have h1 := hasSubst_pair constantCoeff_addP_X0_X1 (MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (2 : Fin 3))
  rw [deltaX, deltaX, deltaX, MvPowerSeries.subst_sub h1, MvPowerSeries.subst_sub (hasSubst_X_X 0 2),
    MvPowerSeries.subst_sub (hasSubst_X_X 1 2)]
  ring

/-- **`deltaX` is linear over constants.** -/
theorem deltaX_C_mul (c : ℂ_[ℓ]) (Q : MvPowerSeries (Fin 2) ℂ_[ℓ]) :
    deltaX (MvPowerSeries.C c * Q) = MvPowerSeries.C c * deltaX Q := by
  have h1 := hasSubst_pair constantCoeff_addP_X0_X1 (MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (2 : Fin 3))
  rw [deltaX, deltaX, MvPowerSeries.subst_mul h1, MvPowerSeries.subst_mul (hasSubst_X_X 0 2),
    MvPowerSeries.subst_mul (hasSubst_X_X 1 2), MvPowerSeries.subst_C, MvPowerSeries.subst_C, MvPowerSeries.subst_C]
  ring

/-- **Frobenius on coefficients commutes with `deltaX`** (the group law is rational). -/
theorem phiS_deltaX {k : Subfield ℂ_[ℓ]} {φ : k →+* k} {P : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hk : ∀ e, MvPowerSeries.coeff e P ∈ k) : phiS k φ (deltaX P) = deltaX (phiS k φ P) := by
  ext e
  rw [eq_ex3 e, coeff_phiS, coeff_deltaX, coeff_deltaX, phiC_dC fun m => hk _]
  rfl

/-- **Substitution into an expanded series**: `(Q(X^ℓ, Y^ℓ))(U, V) = Q(U^ℓ, V^ℓ)`. -/
theorem subst_pair_expand {σ : Type} {U V : MvPowerSeries σ ℂ_[ℓ]} (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (Q : MvPowerSeries (Fin 2) ℂ_[ℓ]) :
    MvPowerSeries.subst ![U, V] (MvPowerSeries.expand ℓ hℓp.out.ne_zero Q) = MvPowerSeries.subst ![U ^ ℓ, V ^ ℓ] Q := by
  have hψ := hasSubst_pair hU hV
  rw [expand_eq_subst, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_pow hℓp.out.ne_zero) hψ]
  congr 1
  funext i
  fin_cases i <;> simp [MvPowerSeries.subst_pow hψ, MvPowerSeries.subst_X hψ]

/-- **`deltaX` of an expanded series**: `Q((X ⊕ X′)^ℓ, Y^ℓ) − Q(X^ℓ, Y^ℓ) − Q(X′^ℓ, Y^ℓ)`. -/
theorem deltaX_expand (Q : MvPowerSeries (Fin 2) ℂ_[ℓ]) :
    deltaX (MvPowerSeries.expand ℓ hℓp.out.ne_zero Q) =
      MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1) ^ ℓ, MvPowerSeries.X 2 ^ ℓ] Q -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]) ^ ℓ, MvPowerSeries.X 2 ^ ℓ] Q -
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]) ^ ℓ, MvPowerSeries.X 2 ^ ℓ] Q := by
  rw [deltaX, subst_pair_expand constantCoeff_addP_X0_X1 (MvPowerSeries.constantCoeff_X 2),
    subst_pair_expand (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 2),
    subst_pair_expand (MvPowerSeries.constantCoeff_X 1) (MvPowerSeries.constantCoeff_X 2)]

/-- **The expansion of `deltaX`**: `Q(X^ℓ ⊕ X′^ℓ, Y^ℓ) − Q(X^ℓ, Y^ℓ) − Q(X′^ℓ, Y^ℓ)`. -/
theorem expand_deltaX (Q : MvPowerSeries (Fin 2) ℂ_[ℓ]) :
    MvPowerSeries.expand ℓ hℓp.out.ne_zero (deltaX Q) =
      MvPowerSeries.subst ![addP (MvPowerSeries.X 0 ^ ℓ) (MvPowerSeries.X 1 ^ ℓ), MvPowerSeries.X 2 ^ ℓ] Q -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]) ^ ℓ, MvPowerSeries.X 2 ^ ℓ] Q -
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]) ^ ℓ, MvPowerSeries.X 2 ^ ℓ] Q := by
  have hℓ0 := hℓp.out.ne_zero
  have c : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hX : ∀ i : Fin 3, MvPowerSeries.expand ℓ hℓ0 (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) =
      MvPowerSeries.X i ^ ℓ := fun i => MvPowerSeries.expand_X ℓ hℓ0 i
  have hpair : ∀ {U V U' V' : MvPowerSeries (Fin 3) ℂ_[ℓ]}, MvPowerSeries.expand ℓ hℓ0 U = U' →
      MvPowerSeries.expand ℓ hℓ0 V = V' →
      (fun i => MvPowerSeries.expand ℓ hℓ0 ((![U, V] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[ℓ]) i)) = ![U', V'] := by
    intro U V U' V' hU hV
    funext i
    fin_cases i
    · exact hU
    · exact hV
  have hP : MvPowerSeries.expand ℓ hℓ0 (addP (MvPowerSeries.X 0) (MvPowerSeries.X 1)) =
      addP (MvPowerSeries.X 0 ^ ℓ) (MvPowerSeries.X 1 ^ ℓ : MvPowerSeries (Fin 3) ℂ_[ℓ]) := by
    rw [addP, MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair (c 0) (c 1)), hpair (hX 0) (hX 1)]
    rfl
  rw [deltaX, map_sub, map_sub, MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair constantCoeff_addP_X0_X1 (c 2)),
    MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair (c 0) (c 2)),
    MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair (c 1) (c 2)), hpair hP (hX 2), hpair (hX 0) (hX 2),
    hpair (hX 1) (hX 2)]

/-- **Lifting the exponent**: for integral `A ≡ A′ (mod ℓ)`, `A^m ≡ A′^m (mod ℓ·m)`. -/
theorem norm_coeff_pow_sub_pow_le_mul {σ : Type} {A A' : MvPowerSeries σ ℂ_[ℓ]} (hA : IsIntK A) (hA' : IsIntK A')
    (hAA : IsDivK ℓ (A - A')) (m : ℕ) (α : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff α (A ^ m - A' ^ m)‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ * ‖(m : ℂ_[ℓ])‖ := by
  classical
  have hℓ := hℓp.out
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.ne_one
  have hu1 : ‖(u : ℂ_[ℓ])‖ = 1 :=
    CMThetaOne.norm_natCast_padicComplex ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hu)
  have e : A ^ (ℓ ^ v * u) - A' ^ (ℓ ^ v * u) = (A ^ ℓ ^ v - A' ^ ℓ ^ v) *
      ∑ i ∈ Finset.range u, (A ^ ℓ ^ v) ^ i * (A' ^ ℓ ^ v) ^ (u - 1 - i) := by
    rw [pow_mul, pow_mul, mul_comm, geom_sum₂_mul]
  have hG : IsIntK (∑ i ∈ Finset.range u, (A ^ ℓ ^ v) ^ i * (A' ^ ℓ ^ v) ^ (u - 1 - i)) := fun β => by
    rw [map_sum]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ =>
      (((hA.pow _).pow i).mul ((hA'.pow _).pow _)) β
  rw [e, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hu1, mul_one, ← pow_succ']
  exact norm_coeff_mul_le (by positivity) (norm_coeff_pow_sub_pow_le hℓ0 hA hA' hAA v) hG α

/-- **Divided-power congruence** (generalises `isDivK_subst_sub` from `ℓ`-power supports to `IsXDp`): for `M` of
divided-power type in `X` and integral `A ≡ A′ (mod ℓ)`, `M(A, Y) ≡ M(A′, Y) (mod ℓ)`. -/
theorem isDivK_subst_sub_dp {σ : Type} {M : MvPowerSeries (Fin 2) ℂ_[ℓ]} (hM : IsXDp M)
    {A A' Y : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hA' : MvPowerSeries.constantCoeff A' = 0) (hY : MvPowerSeries.constantCoeff Y = 0) (hAi : IsIntK A)
    (hA'i : IsIntK A') (hYi : IsIntK Y) (hAA : IsDivK ℓ (A - A')) :
    IsDivK ℓ (MvPowerSeries.subst ![A, Y] M - MvPowerSeries.subst ![A', Y] M) := by
  classical
  have hs := hasSubst_pair hA hY
  have hs' := hasSubst_pair hA' hY
  have hprod : ∀ (B : MvPowerSeries σ ℂ_[ℓ]) (d : Fin 2 →₀ ℕ),
      (d.prod fun s e => (![B, Y] : Fin 2 → MvPowerSeries σ ℂ_[ℓ]) s ^ e) = B ^ d 0 * Y ^ d 1 := fun B d => by
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    rfl
  intro α
  have f1 := MvPowerSeries.coeff_subst_finite hs M α
  have f2 := MvPowerSeries.coeff_subst_finite hs' M α
  set t := f1.toFinset ∪ f2.toFinset
  rw [map_sub, MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs',
    finsum_eq_sum_of_support_subset _ (s := t) (fun x hx => Finset.mem_union_left _ (f1.mem_toFinset.2 hx)),
    finsum_eq_sum_of_support_subset _ (s := t) (fun x hx => Finset.mem_union_right _ (f2.mem_toFinset.2 hx)),
    ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun e _ => ?_
  rw [hprod, hprod, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← sub_mul, norm_mul]
  have h1 := norm_coeff_mul_le (by positivity) (norm_coeff_pow_sub_pow_le_mul hAi hA'i hAA (e 0))
    (hYi.pow (e 1)) α
  calc ‖MvPowerSeries.coeff e M‖ * ‖MvPowerSeries.coeff α ((A ^ e 0 - A' ^ e 0) * Y ^ e 1)‖
      ≤ ‖MvPowerSeries.coeff e M‖ * (‖(ℓ : ℂ_[ℓ])‖ * ‖((e 0 : ℕ) : ℂ_[ℓ])‖) := by gcongr
    _ = ‖(ℓ : ℂ_[ℓ])‖ * ‖((e 0 : ℕ) : ℂ_[ℓ]) * MvPowerSeries.coeff e M‖ := by rw [norm_mul]; ring
    _ ≤ ‖(ℓ : ℂ_[ℓ])‖ * 1 := by gcongr; exact hM e
    _ = ‖(ℓ : ℂ_[ℓ])‖ := mul_one _

/-- **Frobenius keeps the divided-power type.** -/
theorem isXDp_phiS {k : Subfield ℂ_[ℓ]} {φ : k →+* k} (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    {P : MvPowerSeries (Fin 2) ℂ_[ℓ]} (hk : ∀ e, MvPowerSeries.coeff e P ∈ k) (hdp : IsXDp P) :
    IsXDp (phiS k φ P) := fun e => by
  have hn : ((e 0 : ℕ) : ℂ_[ℓ]) ∈ k := natCast_mem k _
  rw [coeff_phiS, ← phiC_natCast (k := k) (φ := φ), ← phiC_mul hn (hk e)]
  exact norm_phiC_le_one hφ (k.mul_mem hn (hk e)) (hdp e)

/-- **S2**: for `P` with coefficients in `k`, of divided-power type in `X`, with `deltaX P ≃ 0`, the defect
`deltaX (T P)` is integral. Indeed `deltaX (T P) = T (deltaX P) + ℓ⁻¹·(Q(X^ℓ ⊕ X′^ℓ, Y^ℓ) − Q((X ⊕ X′)^ℓ, Y^ℓ))`
with `Q = P^φ`, the first term integral by Dwork, the second by the divided-power congruence. -/
theorem isIntK_deltaX_tOpC {k : Subfield ℂ_[ℓ]} {φ : k →+* k}
    (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {P : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hk : ∀ e, MvPowerSeries.coeff e P ∈ k) (hdp : IsXDp P) (hP : Simeq (deltaX P) 0) :
    IsIntK (deltaX (tOpC k φ P)) := by
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓp.out.ne_zero
  have c : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have cp : ∀ U : MvPowerSeries (Fin 3) ℂ_[ℓ], MvPowerSeries.constantCoeff U = 0 →
      MvPowerSeries.constantCoeff (U ^ ℓ) = 0 := fun U hU => by rw [map_pow, hU, zero_pow hℓp.out.ne_zero]
  have h0 : MvPowerSeries.constantCoeff (deltaX P) = 0 := by
    have := hP.1
    rwa [sub_zero] at this
  have hT := (simeq_zero_iff_isIntK_tOpC hφ (coeff_deltaX_mem k hk) h0).1 hP
  set Q := phiS k φ P
  have hD : IsDivK ℓ (MvPowerSeries.expand ℓ hℓp.out.ne_zero (deltaX Q) -
      deltaX (MvPowerSeries.expand ℓ hℓp.out.ne_zero Q)) := by
    rw [expand_deltaX, deltaX_expand]
    have e : ∀ a b c d : MvPowerSeries (Fin 3) ℂ_[ℓ], a - b - c - (d - b - c) = a - d := fun _ _ _ _ => by ring
    rw [e]
    exact isDivK_subst_sub_dp (isXDp_phiS hφ hk hdp) (constantCoeff_addP (cp _ (c 0)) (cp _ (c 1)))
      (cp _ constantCoeff_addP_X0_X1) (cp _ (c 2))
      (isIntK_addP (cp _ (c 0)) (cp _ (c 1)) ((isIntK_X 0).pow ℓ) ((isIntK_X 1).pow ℓ))
      ((isIntK_addP (c 0) (c 1) (isIntK_X 0) (isIntK_X 1)).pow ℓ) ((isIntK_X 2).pow ℓ)
      (isDivK_addP_pow_sub (c 0) (c 1) (isIntK_X 0) (isIntK_X 1))
  have e : deltaX (tOpC k φ P) = tOpC k φ (deltaX P) + MvPowerSeries.C (ℓ : ℂ_[ℓ])⁻¹ *
      (MvPowerSeries.expand ℓ hℓp.out.ne_zero (deltaX Q) - deltaX (MvPowerSeries.expand ℓ hℓp.out.ne_zero Q)) := by
    rw [tOpC, tOpC, deltaX_sub, deltaX_C_mul, phiS_deltaX hk]
    ring
  rw [e]
  refine hT.add fun β => ?_
  rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_inv]
  exact inv_mul_le_one_of_le₀ (hD β) (norm_nonneg _)

end S2

/-! ## S3: divided-power quasi-logarithms, one column at a time -/

section S3

/-- **Lucas**: for `N ≥ 2` not a power of `ℓ`, some `C(N, i)`, `0 < i < N`, is prime to `ℓ` (`i = ℓ^{v(N)}`). -/
theorem exists_norm_choose_eq_one {N : ℕ} (h2 : 2 ≤ N) (hN : ∀ c, N ≠ ℓ ^ c) :
    ∃ i, 0 < i ∧ i < N ∧ ‖(N.choose i : ℂ_[ℓ])‖ = 1 := by
  have hℓ := hℓp.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) ℓ hℓ.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; simp at h2
  have hu1 : u ≠ 1 := by rintro rfl; exact hN v (mul_one _)
  have hpos : 0 < ℓ ^ v := pow_pos hℓ.pos v
  refine ⟨ℓ ^ v, hpos, by nlinarith [show 2 ≤ u by omega], ?_⟩
  have hmod := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := ℓ) (k := v) (a := u) (b := 1)
  rw [mul_one, Nat.choose_one_right] at hmod
  have hnd : ¬ ℓ ∣ (ℓ ^ v * u).choose (ℓ ^ v) := fun h => hu ((Nat.ModEq.dvd_iff hmod dvd_rfl).1 h)
  exact CMThetaOne.norm_natCast_padicComplex ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hnd)

/-- **Kummer**: `C(ℓ^{c+1}, ℓ^c)` has valuation exactly `1`. -/
theorem norm_choose_pow_succ (c : ℕ) : ‖((ℓ ^ (c + 1)).choose (ℓ ^ c) : ℂ_[ℓ])‖ = ‖(ℓ : ℂ_[ℓ])‖ := by
  have hℓ := hℓp.out
  have hle : ℓ ^ c ≤ ℓ ^ (c + 1) := Nat.pow_le_pow_right hℓ.pos (Nat.le_succ c)
  have h := Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity hℓ hle (pow_ne_zero c hℓ.ne_zero)
  rw [Nat.Prime.emultiplicity_pow_self hℓ] at h
  have hC0 : (ℓ ^ (c + 1)).choose (ℓ ^ c) ≠ 0 := (Nat.choose_pos hle).ne'
  rw [← padicValNat_eq_emultiplicity hC0] at h
  have hv : padicValNat ℓ ((ℓ ^ (c + 1)).choose (ℓ ^ c)) = 1 := by
    have : padicValNat ℓ ((ℓ ^ (c + 1)).choose (ℓ ^ c)) + c = c + 1 := by exact_mod_cast h
    omega
  rw [norm_natCast_padicC _ hC0, hv, norm_ell_padicC]
  simp

/-- **`ℓ^j·δ/ℓ^{j′}` is integral** for `j′ < j` when `ℓδ` is. -/
theorem norm_pow_mul_mul_inv_pow_le {δ : ℂ_[ℓ]} (hδ : ‖(ℓ : ℂ_[ℓ]) * δ‖ ≤ 1) {j j' : ℕ} (h : j' < j) :
    ‖(ℓ : ℂ_[ℓ]) ^ j * δ * ((ℓ : ℂ_[ℓ]) ^ j')⁻¹‖ ≤ 1 := by
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓp.out.ne_zero
  obtain ⟨t, rfl⟩ : ∃ t, j = j' + 1 + t := ⟨j - j' - 1, by omega⟩
  have e : (ℓ : ℂ_[ℓ]) ^ (j' + 1 + t) * δ * ((ℓ : ℂ_[ℓ]) ^ j')⁻¹ = (ℓ : ℂ_[ℓ]) ^ t * ((ℓ : ℂ_[ℓ]) * δ) := by
    field_simp
    ring
  rw [e, norm_mul, norm_pow]
  exact mul_le_one_of_le (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ ℓ)) hδ

/-- **`L_0 = 0`.** -/
theorem lc_zero : coeff 0 (logLT ℂ_[ℓ] ℓ) = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_logLT _ hℓp.out.one_lt]

/-- **`L^F_0 = 0`.** -/
theorem lcF_zero : lcF ℓ 0 = 0 := by
  rw [lcF, ite_eq_left (dvd_zero ℓ), Nat.zero_div, lc_zero]

/-- **`L^F_1 = 0`.** -/
theorem lcF_one : lcF ℓ 1 = 0 := by
  rw [lcF, ite_eq_right hℓp.out.not_dvd_one]

/-- **`L^F` vanishes at even powers of `ℓ`.** -/
theorem lcF_pow_even (j : ℕ) : lcF ℓ (ℓ ^ (2 * j)) = 0 := lcF_of_not fun k h => pow_even_ne_odd j k h

/-- **`L` vanishes at odd powers of `ℓ`.** -/
theorem lc_pow_odd (j : ℕ) : coeff (ℓ ^ (2 * j + 1)) (logLT ℂ_[ℓ] ℓ) = 0 :=
  lc_of_not fun k h => pow_even_ne_odd k j h.symm

/-- **The models of S3**: for a column `g` with `g_0`, `g_1` integral and integral defect coefficients, every
initial segment is matched modulo integral elements by some `a·L + b·ℓ⁻¹L^F`, `a, b` integral. The induction on
the degree `N`: the defect at `X^iX′^{N−i}` gives `C(N, i)·ρ_N` integral for the remainder `ρ`; for `N` not a
power of `ℓ` some `C(N, i)` is a unit (Lucas), and for `N = ℓ^{c+1}` the binomial `C(N, ℓ^c)` has valuation `1`
(Kummer), so `ℓρ_N` is integral and the model is corrected at degree `N` by `ℓ^jρ_N·L` (`c + 1 = 2j`) or
`ℓ^{j+1}ρ_N·ℓ⁻¹L^F` (`c + 1 = 2j + 1`), which changes the lower coefficients only by integral elements. -/
theorem quasiLog_model {g : ℕ → ℂ_[ℓ]} (h0 : ‖g 0‖ ≤ 1) (h1 : ‖g 1‖ ≤ 1) (hd : ∀ i j, ‖dC ℓ g i j‖ ≤ 1)
    (N : ℕ) : ∃ a b : ℂ_[ℓ], ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ∀ m < N,
      ‖g m - a * coeff m (logLT ℂ_[ℓ] ℓ) - b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m‖ ≤ 1 := by
  have hℓ := hℓp.out
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hn0 : 0 < ‖(ℓ : ℂ_[ℓ])‖ := norm_pos_iff.2 hℓ0
  induction N with
  | zero => exact ⟨0, 0, by simp, by simp, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨a, b, ha, hb, hρ⟩ := ih
    set ρ : ℕ → ℂ_[ℓ] := fun m => g m - a * coeff m (logLT ℂ_[ℓ] ℓ) - b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m with hρdef
    have hdρ : ∀ i j, ‖dC ℓ ρ i j‖ ≤ 1 := fun i j => by
      rw [hρdef, dC_sub, dC_sub, dC_smul, dC_smul, dC_logLT, mul_zero, sub_zero]
      refine norm_sub_le_one (hd i j) ?_
      rw [norm_mul, norm_mul, norm_inv]
      calc ‖b‖ * ‖(ℓ : ℂ_[ℓ])‖⁻¹ * ‖dC ℓ (lcF ℓ) i j‖ ≤ 1 * ‖(ℓ : ℂ_[ℓ])‖⁻¹ * ‖(ℓ : ℂ_[ℓ])‖ := by
            gcongr
            exact norm_dC_lcF_le i j
        _ = 1 := by field_simp
    -- if the remainder is integral at `N`, the model persists
    have keep : ‖ρ N‖ ≤ 1 → ∃ a b : ℂ_[ℓ], ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ∀ m < N + 1,
        ‖g m - a * coeff m (logLT ℂ_[ℓ] ℓ) - b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m‖ ≤ 1 := fun hN =>
      ⟨a, b, ha, hb, fun m hm => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
        · exact hρ m hm
        · exact hN⟩
    by_cases hpow : ∃ c, N = ℓ ^ (c + 1)
    · obtain ⟨c, rfl⟩ := hpow
      have hlρ : ‖(ℓ : ℂ_[ℓ]) * ρ (ℓ ^ (c + 1))‖ ≤ 1 := by
        have hlt : ℓ ^ c < ℓ ^ (c + 1) := Nat.pow_lt_pow_right hℓ.one_lt (Nat.lt_succ_self c)
        have := norm_choose_mul_le (pow_pos hℓ.pos c) hlt hρ (hdρ _ _)
        rwa [norm_mul, norm_choose_pow_succ, ← norm_mul] at this
      set δ := ρ (ℓ ^ (c + 1))
      rcases Nat.even_or_odd (c + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- `c + 1 = 2j`: correct `a`
        rw [show j + j = 2 * j by ring] at hj
        have hj1 : 1 ≤ j := by omega
        refine ⟨a + (ℓ : ℂ_[ℓ]) ^ j * δ, b, ?_, hb, fun m hm => ?_⟩
        · refine norm_add_le_one ha ?_
          have := norm_pow_mul_mul_inv_pow_le hlρ (j := j) (j' := 0) (by omega)
          simpa using this
        · have e : g m - (a + (ℓ : ℂ_[ℓ]) ^ j * δ) * coeff m (logLT ℂ_[ℓ] ℓ) - b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m =
              ρ m - (ℓ : ℂ_[ℓ]) ^ j * δ * coeff m (logLT ℂ_[ℓ] ℓ) := by simp only [hρdef]; ring
          rw [e]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
          · by_cases hm' : ∃ j', m = ℓ ^ (2 * j')
            · obtain ⟨j', rfl⟩ := hm'
              have hj' : j' < j := by
                rw [hj] at hm
                have := (Nat.pow_lt_pow_iff_right hℓ.one_lt).1 hm
                omega
              rw [lc_pow]
              exact norm_sub_le_one (hρ _ hm) (norm_pow_mul_mul_inv_pow_le hlρ hj')
            · push Not at hm'
              rw [lc_of_not hm', mul_zero, sub_zero]
              exact hρ m hm
          · have hL : coeff (ℓ ^ (c + 1)) (logLT ℂ_[ℓ] ℓ) = ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ := by rw [hj, lc_pow]
            rw [hL, show (ℓ : ℂ_[ℓ]) ^ j * δ * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ = δ by field_simp]
            show ‖δ - δ‖ ≤ 1
            simp
      · -- `c + 1 = 2j + 1`: correct `b`
        refine ⟨a, b + (ℓ : ℂ_[ℓ]) ^ (j + 1) * δ, ha, ?_, fun m hm => ?_⟩
        · refine norm_add_le_one hb ?_
          have := norm_pow_mul_mul_inv_pow_le hlρ (j := j + 1) (j' := 0) (by omega)
          simpa using this
        · have e : g m - a * coeff m (logLT ℂ_[ℓ] ℓ) - (b + (ℓ : ℂ_[ℓ]) ^ (j + 1) * δ) * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m =
              ρ m - (ℓ : ℂ_[ℓ]) ^ j * δ * lcF ℓ m := by
            simp only [hρdef]
            field_simp
            ring
          rw [e]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
          · by_cases hm' : ∃ j', m = ℓ ^ (2 * j' + 1)
            · obtain ⟨j', rfl⟩ := hm'
              have hj' : j' < j := by
                rw [hj] at hm
                have := (Nat.pow_lt_pow_iff_right hℓ.one_lt).1 hm
                omega
              rw [lcF_pow]
              exact norm_sub_le_one (hρ _ hm) (norm_pow_mul_mul_inv_pow_le hlρ hj')
            · push Not at hm'
              rw [lcF_of_not hm', mul_zero, sub_zero]
              exact hρ m hm
          · have hL : lcF ℓ (ℓ ^ (c + 1)) = ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ := by rw [hj, lcF_pow]
            rw [hL, show (ℓ : ℂ_[ℓ]) ^ j * δ * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ = δ by field_simp]
            show ‖δ - δ‖ ≤ 1
            simp
    · push Not at hpow
      rcases (by omega : N = 0 ∨ N = 1 ∨ 2 ≤ N) with rfl | rfl | h2
      · refine keep ?_
        simp only [hρdef, lc_zero, lcF_zero, mul_zero, sub_zero]
        exact h0
      · refine keep ?_
        simp only [hρdef, coeff_one_logLT, lcF_one, mul_zero, sub_zero, mul_one]
        exact norm_sub_le_one h1 ha
      · have hN : ∀ c, N ≠ ℓ ^ c := fun c hc => by
          rcases c with _ | c
          · simp at hc; omega
          · exact hpow c hc
        obtain ⟨i, hi0, hiN, hC⟩ := exists_norm_choose_eq_one h2 hN
        refine keep ?_
        have := norm_choose_mul_le hi0 hiN hρ (hdρ i (N - i))
        rwa [norm_mul, hC, one_mul] at this

/-- **`‖ℓ‖ < 1`.** -/
theorem norm_ell_lt_one : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
  rw [norm_ell_padicC]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓp.out.one_lt)

/-- **`ℓ^{−j}·w` is integral** when `‖w‖ ≤ ‖ℓ‖^j`. -/
theorem norm_inv_pow_mul_le_one {w : ℂ_[ℓ]} {j : ℕ} (h : ‖w‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ j) :
    ‖((ℓ : ℂ_[ℓ]) ^ j)⁻¹ * w‖ ≤ 1 := by
  have hn0 : 0 < ‖(ℓ : ℂ_[ℓ])‖ := norm_pos_iff.2 (by exact_mod_cast hℓp.out.ne_zero)
  rw [norm_mul, norm_inv, norm_pow]
  calc (‖(ℓ : ℂ_[ℓ])‖ ^ j)⁻¹ * ‖w‖ ≤ (‖(ℓ : ℂ_[ℓ])‖ ^ j)⁻¹ * ‖(ℓ : ℂ_[ℓ])‖ ^ j := by gcongr
    _ = 1 := inv_mul_cancel₀ (pow_ne_zero j hn0.ne')

/-- **`ℓ^j·w` has norm at most `‖ℓ‖^j`** for integral `w`. -/
theorem norm_pow_mul_le {w : ℂ_[ℓ]} (h : ‖w‖ ≤ 1) (j : ℕ) : ‖(ℓ : ℂ_[ℓ]) ^ j * w‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ j := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) h

/-- **`ℓ`-adically Cauchy sequences converge** (`ℂ_ℓ` is complete), with the same rate. -/
theorem exists_lim {x : ℕ → ℂ_[ℓ]} (h : ∀ j J, j ≤ J → ‖x J - x j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ j) :
    ∃ a, ∀ j, ‖a - x j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ j := by
  have hc : CauchySeq x := cauchySeq_of_le_geometric ‖(ℓ : ℂ_[ℓ])‖ 1 norm_ell_lt_one fun n => by
    rw [dist_eq_norm, norm_sub_rev, one_mul]
    exact h n (n + 1) (Nat.le_succ n)
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨a, fun j => ?_⟩
  have ht : Filter.Tendsto (fun J => ‖x J - x j‖) Filter.atTop (nhds ‖a - x j‖) := (ha.sub_const (x j)).norm
  exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨j, fun J hJ => h j J hJ⟩)

/-- **S3, one column**: a column `g` with `g_0`, `g_1` integral and integral defect coefficients is
`a·L + b·ℓ⁻¹L^F` modulo integral elements, `a, b` integral: `a = lim ℓ^j g_{ℓ^{2j}}`, `b = ℓ·lim ℓ^j g_{ℓ^{2j+1}}`,
the sequences being Cauchy by the models (`quasiLog_model`). -/
theorem quasiLog_col {g : ℕ → ℂ_[ℓ]} (h0 : ‖g 0‖ ≤ 1) (h1 : ‖g 1‖ ≤ 1) (hd : ∀ i j, ‖dC ℓ g i j‖ ≤ 1) :
    ∃ a b : ℂ_[ℓ], ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ∀ m,
      ‖g m - a * coeff m (logLT ℂ_[ℓ] ℓ) - b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m‖ ≤ 1 := by
  have hℓ := hℓp.out
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hn1 : ‖(ℓ : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ ℓ
  have M := quasiLog_model h0 h1 hd
  set x : ℕ → ℂ_[ℓ] := fun j => (ℓ : ℂ_[ℓ]) ^ j * g (ℓ ^ (2 * j)) with hx
  set z : ℕ → ℂ_[ℓ] := fun j => (ℓ : ℂ_[ℓ]) ^ j * g (ℓ ^ (2 * j + 1)) with hz
  -- a model approximates the two sequences
  have hxa : ∀ {N : ℕ} {a b : ℂ_[ℓ]}, (∀ m < N, ‖g m - a * coeff m (logLT ℂ_[ℓ] ℓ) -
      b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m‖ ≤ 1) → ∀ i, ℓ ^ (2 * i) < N → ‖x i - a‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ i := by
    intro N a b hm i hi
    have h := norm_pow_mul_le (hm _ hi) i
    rw [lc_pow, lcF_pow_even, mul_zero, sub_zero] at h
    convert h using 2
    simp only [hx]
    field_simp
  have hzb : ∀ {N : ℕ} {a b : ℂ_[ℓ]}, (∀ m < N, ‖g m - a * coeff m (logLT ℂ_[ℓ] ℓ) -
      b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m‖ ≤ 1) → ∀ i, ℓ ^ (2 * i + 1) < N →
      ‖z i - (ℓ : ℂ_[ℓ])⁻¹ * b‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ i := by
    intro N a b hm i hi
    have h := norm_pow_mul_le (hm _ hi) i
    rw [lc_pow_odd, lcF_pow, mul_zero, sub_zero] at h
    convert h using 2
    simp only [hz]
    field_simp
  have hmono : ∀ {i J : ℕ}, i ≤ J → ∀ t, ℓ ^ (2 * i + t) ≤ ℓ ^ (2 * J + t) := fun hiJ t =>
    Nat.pow_le_pow_right hℓ.pos (by omega)
  have hxC : ∀ j J, j ≤ J → ‖x J - x j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ j := fun j J hjJ => by
    obtain ⟨a, b, -, -, hm⟩ := M (ℓ ^ (2 * J) + 1)
    have h1 := hxa hm J (Nat.lt_succ_self _)
    have h2 := hxa hm j (Nat.lt_succ_of_le (by simpa using hmono hjJ 0))
    rw [← sub_sub_sub_cancel_right (x J) (x j) a]
    exact (norm_sub_le_max' _ _).trans (max_le (h1.trans (pow_le_pow_of_le_one (norm_nonneg _) hn1 hjJ)) h2)
  have hzC : ∀ j J, j ≤ J → ‖z J - z j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ j := fun j J hjJ => by
    obtain ⟨a, b, -, -, hm⟩ := M (ℓ ^ (2 * J + 1) + 1)
    have h1 := hzb hm J (Nat.lt_succ_self _)
    have h2 := hzb hm j (Nat.lt_succ_of_le (hmono hjJ 1))
    rw [← sub_sub_sub_cancel_right (z J) (z j) ((ℓ : ℂ_[ℓ])⁻¹ * b)]
    exact (norm_sub_le_max' _ _).trans (max_le (h1.trans (pow_le_pow_of_le_one (norm_nonneg _) hn1 hjJ)) h2)
  obtain ⟨A, hA⟩ := exists_lim hxC
  obtain ⟨Z, hZ⟩ := exists_lim hzC
  refine ⟨A, (ℓ : ℂ_[ℓ]) * Z, ?_, ?_, fun m => ?_⟩
  · obtain ⟨a, b, ha, -, hm⟩ := M 2
    have h := hxa hm 0 (by simp)
    rw [pow_zero] at h
    have hA0 := hA 0
    rw [pow_zero] at hA0
    rw [show A = (A - x 0) + (x 0 - a) + a by ring]
    exact norm_add_le_one (norm_add_le_one hA0 h) ha
  · obtain ⟨a, b, -, hb, hm⟩ := M (ℓ + 1)
    have h := hzb hm 0 (by simp)
    rw [pow_zero] at h
    have hZ0 := hZ 0
    rw [pow_zero] at hZ0
    have e : (ℓ : ℂ_[ℓ]) * Z = (ℓ : ℂ_[ℓ]) * ((Z - z 0) + (z 0 - (ℓ : ℂ_[ℓ])⁻¹ * b)) + b := by
      field_simp
      ring
    rw [e]
    refine norm_add_le_one ?_ hb
    rw [norm_mul]
    exact mul_le_one_of_le hn1 (norm_add_le_one hZ0 h)
  · by_cases he : ∃ j, m = ℓ ^ (2 * j)
    · obtain ⟨j, rfl⟩ := he
      rw [lc_pow, lcF_pow_even, mul_zero, sub_zero]
      have e : g (ℓ ^ (2 * j)) - A * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ = ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ * -(A - x j) := by
        simp only [hx]
        field_simp
        ring
      rw [e]
      exact norm_inv_pow_mul_le_one (by rw [norm_neg]; exact hA j)
    by_cases ho : ∃ j, m = ℓ ^ (2 * j + 1)
    · obtain ⟨j, rfl⟩ := ho
      rw [lc_pow_odd, lcF_pow, mul_zero, sub_zero]
      have e : g (ℓ ^ (2 * j + 1)) - (ℓ : ℂ_[ℓ]) * Z * (ℓ : ℂ_[ℓ])⁻¹ * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ =
          ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ * -(Z - z j) := by
        simp only [hz]
        field_simp
        ring
      rw [e]
      exact norm_inv_pow_mul_le_one (by rw [norm_neg]; exact hZ j)
    · push Not at he ho
      obtain ⟨a, b, -, -, hm⟩ := M (m + 1)
      have h := hm m (Nat.lt_succ_self m)
      rw [lc_of_not he, lcF_of_not ho, mul_zero, mul_zero, sub_zero, sub_zero] at h ⊢
      exact h

end S3

/-! ## S5: two-sided quasi-bilinear forms are bilinear in `(L, ℓ⁻¹L^F)` -/

section S5

/-- **An element smaller than every power of `ℓ` vanishes.** -/
theorem eq_zero_of_norm_le_pow {w : ℂ_[ℓ]} (h : ∀ t : ℕ, ‖w‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ t) : w = 0 := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (ℓ : ℂ_[ℓ])) norm_ell_lt_one
  exact norm_le_zero_iff.1 (ge_of_tendsto' ht h)

/-- **The exactness trick**: if `‖x_i − y_j‖ ≤ ‖ℓ‖^{i+j}` for all `i, j`, then all `x_i` and `y_j` coincide. -/
theorem eq_of_norm_sub_le_pow {x y : ℕ → ℂ_[ℓ]} (h : ∀ i j, ‖x i - y j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ (i + j)) (i j : ℕ) :
    x i = y j := by
  have hn1 : ‖(ℓ : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ ℓ
  have hle : ∀ a b, a ≤ b → ‖(ℓ : ℂ_[ℓ])‖ ^ b ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ a := fun a b hab =>
    pow_le_pow_of_le_one (norm_nonneg _) hn1 hab
  refine sub_eq_zero.1 (eq_zero_of_norm_le_pow fun t => ?_)
  rw [show x i - y j = (x i - y t) - (x t - y t) + (x t - y j) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((norm_sub_le_max' _ _).trans (max_le ?_ ?_)) ?_)
  · exact (h i t).trans (hle _ _ (by omega))
  · exact (h t t).trans (hle _ _ (by omega))
  · exact (h t j).trans (hle _ _ (by omega))

/-- **Reading off a bound**: `‖ℓ^{−k}·w‖ ≤ 1` gives `‖w‖ ≤ ‖ℓ‖^k`. -/
theorem norm_le_pow_of_norm_inv_pow_mul_le {w : ℂ_[ℓ]} {k : ℕ} (h : ‖((ℓ : ℂ_[ℓ]) ^ k)⁻¹ * w‖ ≤ 1) :
    ‖w‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ k := by
  have hn0 : 0 < ‖(ℓ : ℂ_[ℓ])‖ := norm_pos_iff.2 (by exact_mod_cast hℓp.out.ne_zero)
  rw [norm_mul, norm_inv, norm_pow, inv_mul_le_iff₀ (by positivity), mul_one] at h
  exact h

/-- **S5**: if `β ≡ L(X)U(Y) + ℓ⁻¹L^F(X)V(Y)` modulo integral elements and `β` is symmetric, then `U` and `V`
are exactly `αL + γℓ⁻¹L^F` and `γL + δL^F` (compare the two expansions at `X^{ℓ^a}Y^{ℓ^b}`; the exactness trick). -/
theorem bilin_of_symm {β : ℕ → ℕ → ℂ_[ℓ]} {U V : ℕ → ℂ_[ℓ]}
    (h1 : ∀ m n, ‖β m n - coeff m (logLT ℂ_[ℓ] ℓ) * U n - (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m * V n‖ ≤ 1)
    (hsym : ∀ m n, β m n = β n m) :
    ∃ α γ δ : ℂ_[ℓ], ∀ n, U n = α * coeff n (logLT ℂ_[ℓ] ℓ) + γ * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ n ∧
      V n = γ * coeff n (logLT ℂ_[ℓ] ℓ) + δ * lcF ℓ n := by
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓp.out.ne_zero
  have hn1 : ‖(ℓ : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ ℓ
  have hS : ∀ m n, ‖coeff m (logLT ℂ_[ℓ] ℓ) * U n + (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m * V n -
      (coeff n (logLT ℂ_[ℓ] ℓ) * U m + (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ n * V m)‖ ≤ 1 := fun m n => by
    have h := norm_sub_le_one (h1 n m) (h1 m n)
    rw [hsym n m] at h
    convert h using 2
    ring
  -- the columns off the powers of `ℓ` vanish
  have hoff : ∀ n, (∀ j, n ≠ ℓ ^ (2 * j)) → (∀ j, n ≠ ℓ ^ (2 * j + 1)) → U n = 0 ∧ V n = 0 := by
    intro n he ho
    have hLn : coeff n (logLT ℂ_[ℓ] ℓ) = 0 := lc_of_not he
    have hFn : lcF ℓ n = 0 := lcF_of_not ho
    constructor
    · refine eq_zero_of_norm_le_pow fun t => norm_le_pow_of_norm_inv_pow_mul_le ?_
      have h := hS (ℓ ^ (2 * t)) n
      rw [hLn, hFn, lcF_pow_even, lc_pow] at h
      simpa using h
    · refine eq_zero_of_norm_le_pow fun t => (norm_le_pow_of_norm_inv_pow_mul_le (k := t + 1) ?_).trans
        (pow_le_pow_of_le_one (norm_nonneg _) hn1 (Nat.le_succ t))
      have h := hS (ℓ ^ (2 * t + 1)) n
      rw [hLn, hFn, lcF_pow, lc_pow_odd] at h
      convert h using 2
      simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero]
      rw [pow_succ, mul_inv]
      ring
  -- the even columns of `U`
  set x : ℕ → ℂ_[ℓ] := fun j => (ℓ : ℂ_[ℓ]) ^ j * U (ℓ ^ (2 * j)) with hx
  have hxx : ∀ i j, ‖x i - x j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ (i + j) := fun i j => by
    refine norm_le_pow_of_norm_inv_pow_mul_le ?_
    have h := hS (ℓ ^ (2 * j)) (ℓ ^ (2 * i))
    rw [lc_pow, lc_pow, lcF_pow_even, lcF_pow_even] at h
    convert h using 2
    simp only [hx]
    field_simp
    ring
  -- the odd columns of `U` and the even columns of `V`
  set x' : ℕ → ℂ_[ℓ] := fun j => (ℓ : ℂ_[ℓ]) ^ (j + 1) * U (ℓ ^ (2 * j + 1)) with hx'
  set y' : ℕ → ℂ_[ℓ] := fun i => (ℓ : ℂ_[ℓ]) ^ i * V (ℓ ^ (2 * i)) with hy'
  have hxy : ∀ j i, ‖x' j - y' i‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ (j + i) := fun j i => by
    refine (norm_le_pow_of_norm_inv_pow_mul_le (k := j + i + 1) ?_).trans
      (pow_le_pow_of_le_one (norm_nonneg _) hn1 (Nat.le_succ _))
    have h := hS (ℓ ^ (2 * i)) (ℓ ^ (2 * j + 1))
    rw [lc_pow, lc_pow_odd, lcF_pow_even, lcF_pow] at h
    convert h using 2
    simp only [hx', hy']
    field_simp
    ring
  -- the odd columns of `V`
  set w : ℕ → ℂ_[ℓ] := fun j => (ℓ : ℂ_[ℓ]) ^ j * V (ℓ ^ (2 * j + 1)) with hw
  have hww : ∀ i j, ‖w i - w j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ (i + j) := fun i j => by
    refine (norm_le_pow_of_norm_inv_pow_mul_le (k := i + j + 1) ?_).trans
      (pow_le_pow_of_le_one (norm_nonneg _) hn1 (Nat.le_succ _))
    have h := hS (ℓ ^ (2 * j + 1)) (ℓ ^ (2 * i + 1))
    rw [lc_pow_odd, lc_pow_odd, lcF_pow, lcF_pow] at h
    convert h using 2
    simp only [hw]
    field_simp
    ring
  refine ⟨x 0, x' 0, w 0, fun n => ?_⟩
  by_cases he : ∃ j, n = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := he
    have hU : x 0 = x j := eq_of_norm_sub_le_pow hxx 0 j
    have hV : x' 0 = y' j := eq_of_norm_sub_le_pow hxy 0 j
    rw [lc_pow, lcF_pow_even, hU, hV, mul_zero, add_zero, mul_zero, add_zero]
    simp only [hx, hy']
    constructor <;> field_simp
  by_cases ho : ∃ j, n = ℓ ^ (2 * j + 1)
  · obtain ⟨j, rfl⟩ := ho
    have hU : x' 0 = x' j := (eq_of_norm_sub_le_pow hxy 0 0).trans (eq_of_norm_sub_le_pow hxy j 0).symm
    have hV : w 0 = w j := eq_of_norm_sub_le_pow hww 0 j
    rw [lc_pow_odd, lcF_pow, hV, hU, mul_zero, zero_add, mul_zero, zero_add]
    simp only [hx', hw]
    constructor
    · field_simp
      ring
    · field_simp
  · push Not at he ho
    obtain ⟨hU, hV⟩ := hoff n he ho
    rw [hU, hV, lc_of_not he, lcF_of_not ho]
    simp

end S5

/-! ## The structure theorem -/

section Structure

variable {k : Subfield ℂ_[ℓ]} {φ : k →+* k}

/-- **The coefficients of `T f` in two variables.** -/
theorem coeff_tOpC_ex2 (f : MvPowerSeries (Fin 2) ℂ_[ℓ]) (m n : ℕ) :
    MvPowerSeries.coeff (ex2 m n) (tOpC k φ f) = MvPowerSeries.coeff (ex2 m n) f - (ℓ : ℂ_[ℓ])⁻¹ *
      (if ℓ ∣ m ∧ ℓ ∣ n then phiC k φ (MvPowerSeries.coeff (ex2 (m / ℓ) (n / ℓ)) f) else 0) := by
  by_cases h : ℓ ∣ m ∧ ℓ ∣ n
  · obtain ⟨⟨m', rfl⟩, ⟨n', rfl⟩⟩ := h
    have e : ex2 (ℓ * m') (ℓ * n') = ℓ • ex2 m' n' := by
      ext i
      fin_cases i <;> simp [ex2]
    rw [ite_eq_left ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, Nat.mul_div_cancel_left _ hℓp.out.pos,
      Nat.mul_div_cancel_left _ hℓp.out.pos, e, coeff_tOpC_smul]
  · rw [ite_eq_right h, mul_zero, sub_zero]
    rcases not_and_or.1 h with h | h
    · exact coeff_tOpC_of_not_dvd f (i := 0) (by simpa [ex2] using h)
    · exact coeff_tOpC_of_not_dvd f (i := 1) (by simpa [ex2] using h)

/-- **The coefficients of `T f` at `Y^n` in three variables.** -/
theorem coeff_tOpC_ex3_zero_zero (f : MvPowerSeries (Fin 3) ℂ_[ℓ]) (n : ℕ) :
    MvPowerSeries.coeff (ex3 0 0 n) (tOpC k φ f) = MvPowerSeries.coeff (ex3 0 0 n) f - (ℓ : ℂ_[ℓ])⁻¹ *
      (if ℓ ∣ n then phiC k φ (MvPowerSeries.coeff (ex3 0 0 (n / ℓ)) f) else 0) := by
  by_cases h : ℓ ∣ n
  · obtain ⟨n', rfl⟩ := h
    have e : ex3 0 0 (ℓ * n') = ℓ • ex3 0 0 n' := by
      ext i
      fin_cases i <;> simp [ex3]
    rw [ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hℓp.out.pos, e, coeff_tOpC_smul]
  · rw [ite_eq_right h, mul_zero, sub_zero]
    exact coeff_tOpC_of_not_dvd f (i := 2) (by simpa [ex3] using h)

/-- **`log_LT` has rational coefficients.** -/
theorem exists_ratCast_lc (m : ℕ) : ∃ q : ℚ, coeff m (logLT ℂ_[ℓ] ℓ) = q := by
  by_cases h : ∃ j, m = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := h
    exact ⟨((ℓ : ℚ) ^ j)⁻¹, by rw [lc_pow]; push_cast; rfl⟩
  · push Not at h
    exact ⟨0, by rw [lc_of_not h]; simp⟩

/-- **`log_LT(T^ℓ)` has rational coefficients.** -/
theorem exists_ratCast_lcF (m : ℕ) : ∃ q : ℚ, lcF ℓ m = q := by
  rw [lcF]
  split_ifs
  · exact exists_ratCast_lc _
  · exact ⟨0, by simp⟩

/-- **`serAB` has rational coefficients.** -/
theorem exists_ratCast_sAB (m n : ℕ) : ∃ q : ℚ, sAB ℓ m n = q := by
  by_cases h : ∃ i j, SupAB ℓ m n i j
  · obtain ⟨i, j, hij⟩ := h
    exact ⟨((ℓ : ℚ) ^ (i + j + 1))⁻¹, by rw [sAB_of hij]; push_cast; rfl⟩
  · push Not at h
    exact ⟨0, by rw [sAB_of_not h]; simp⟩

/-- **Rational numbers lie in `k` and are fixed by `phiC`.** -/
theorem mem_and_phiC_of_ratCast {x : ℂ_[ℓ]} (h : ∃ q : ℚ, x = q) : x ∈ k ∧ phiC k φ x = x := by
  obtain ⟨q, rfl⟩ := h
  exact ⟨SubfieldClass.ratCast_mem k q, phiC_ratCast q⟩

/-- **The coefficients of `L(X)·u(Y)`.** -/
theorem coeff_logX_mul_colY (u : ℕ → ℂ_[ℓ]) (m n : ℕ) :
    MvPowerSeries.coeff (ex2 m n) ((logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
      (PowerSeries.mk u).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ])) =
      coeff m (logLT ℂ_[ℓ] ℓ) * u n := by
  rw [coeff_subst_X0_mul_subst_X1, PowerSeries.coeff_mk]
  simp

/-- **`L(X)·u(Y)` is exactly additive in `X`.** -/
theorem deltaX_logX_mul_colY (u : ℕ → ℂ_[ℓ]) :
    deltaX ((logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
      (PowerSeries.mk u).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ])) = 0 := by
  ext e
  obtain ⟨i, j, n, rfl⟩ : ∃ i j n, e = ex3 i j n := ⟨e 0, e 1, e 2, eq_ex3 e⟩
  rw [coeff_deltaX, MvPowerSeries.coeff_zero]
  simp only [coeff_logX_mul_colY]
  rw [show (fun m => coeff m (logLT ℂ_[ℓ] ℓ) * u n) = fun m => u n * coeff m (logLT ℂ_[ℓ] ℓ) from
    funext fun m => mul_comm _ _, dC_smul, dC_logLT, mul_zero]

/-- **The pure `Y`-coefficients of `T B` are integral** when `deltaX B ≃ 0`: the coefficient of `Y^n` in
`T (deltaX B)` is `−(T B)_{0,n}`. -/
theorem norm_coeff_tOpC_zero_le (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    {B : MvPowerSeries (Fin 2) ℂ_[ℓ]} (hk : ∀ e, MvPowerSeries.coeff e B ∈ k) (hB : Simeq (deltaX B) 0)
    (n : ℕ) : ‖MvPowerSeries.coeff (ex2 0 n) (tOpC k φ B)‖ ≤ 1 := by
  have h0 : MvPowerSeries.constantCoeff (deltaX B) = 0 := by
    have := hB.1
    rwa [sub_zero] at this
  have hT := ((simeq_zero_iff_isIntK_tOpC hφ (coeff_deltaX_mem k hk) h0).1 hB) (ex3 0 0 n)
  have hc : ∀ n', MvPowerSeries.coeff (ex3 0 0 n') (deltaX B) = -MvPowerSeries.coeff (ex2 0 n') B := fun n' => by
    rw [coeff_deltaX, dC]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, ite_true]
    rw [fc, pow_zero, MvPowerSeries.coeff_one, ite_eq_left (by simp [ex2])]
    ring
  rw [coeff_tOpC_ex3_zero_zero, hc, hc] at hT
  rw [coeff_tOpC_ex2, Nat.zero_div]
  have e : (if ℓ ∣ 0 ∧ ℓ ∣ n then phiC k φ (MvPowerSeries.coeff (ex2 0 (n / ℓ)) B) else 0) =
      -(if ℓ ∣ n then phiC k φ (-MvPowerSeries.coeff (ex2 0 (n / ℓ)) B) else 0) := by
    by_cases hn : ℓ ∣ n
    · rw [ite_eq_left ⟨dvd_zero ℓ, hn⟩, ite_eq_left hn, phiC_neg (hk _), neg_neg]
    · rw [ite_eq_right fun h => hn h.2, ite_eq_right hn, neg_zero]
  rw [e, ← norm_neg]
  convert hT using 2
  ring

/-- **`L_m ∈ k`.** -/
theorem lc_mem (m : ℕ) : coeff m (logLT ℂ_[ℓ] ℓ) ∈ k := by
  obtain ⟨q, hq⟩ := exists_ratCast_lc (ℓ := ℓ) m
  rw [hq]
  exact SubfieldClass.ratCast_mem k q

/-- **`φ(L_m) = L_m`.** -/
theorem phiC_lc (m : ℕ) : phiC k φ (coeff m (logLT ℂ_[ℓ] ℓ)) = coeff m (logLT ℂ_[ℓ] ℓ) :=
  (mem_and_phiC_of_ratCast (exists_ratCast_lc m)).2

/-- **`L^F_m ∈ k`.** -/
theorem lcF_mem (m : ℕ) : lcF ℓ m ∈ k := by
  obtain ⟨q, hq⟩ := exists_ratCast_lcF (ℓ := ℓ) m
  rw [hq]
  exact SubfieldClass.ratCast_mem k q

/-- **`φ(L^F_m) = L^F_m`.** -/
theorem phiC_lcF (m : ℕ) : phiC k φ (lcF ℓ m) = lcF ℓ m := (mem_and_phiC_of_ratCast (exists_ratCast_lcF m)).2

/-- **`S_{m,n} ∈ k`.** -/
theorem sAB_mem (m n : ℕ) : sAB ℓ m n ∈ k := by
  obtain ⟨q, hq⟩ := exists_ratCast_sAB (ℓ := ℓ) m n
  rw [hq]
  exact SubfieldClass.ratCast_mem k q

/-- **`φ(S_{m,n}) = S_{m,n}`.** -/
theorem phiC_sAB (m n : ℕ) : phiC k φ (sAB ℓ m n) = sAB ℓ m n := (mem_and_phiC_of_ratCast (exists_ratCast_sAB m n)).2

/-- **`ℓ⁻¹` is fixed by `phiC`.** -/
theorem phiC_inv_ell : phiC k φ (ℓ : ℂ_[ℓ])⁻¹ = (ℓ : ℂ_[ℓ])⁻¹ :=
  (mem_and_phiC_of_ratCast ⟨(ℓ : ℚ)⁻¹, by push_cast; rfl⟩).2

/-- **S4, the one-sided form**: if `deltaX B ≃ 0` then, with `u = B_{1,·}` and `ψu_n = [ℓ ∣ n]·φ(u_{n/ℓ})`, there are
integral columns `a`, `b` with `T B ≡ L(X)·(u + a)(Y) + ℓ⁻¹L^F(X)·(b − ψu)(Y)` modulo integral elements (S1, S2,
and S3 for each column of `T(B − L(X)u(Y))`). -/
theorem quasiBilin (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {B : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hk : ∀ e, MvPowerSeries.coeff e B ∈ k) (hB : Simeq (deltaX B) 0) :
    ∃ a b : ℕ → ℂ_[ℓ], (∀ n, ‖a n‖ ≤ 1) ∧ (∀ n, ‖b n‖ ≤ 1) ∧ ∀ m n,
      ‖MvPowerSeries.coeff (ex2 m n) (tOpC k φ B) -
        coeff m (logLT ℂ_[ℓ] ℓ) * (MvPowerSeries.coeff (ex2 1 n) B + a n) - (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m *
          (b n - if ℓ ∣ n then phiC k φ (MvPowerSeries.coeff (ex2 1 (n / ℓ)) B) else 0)‖ ≤ 1 := by
  set u : ℕ → ℂ_[ℓ] := fun n => MvPowerSeries.coeff (ex2 1 n) B with hu
  set P := B - (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
    (PowerSeries.mk u).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) with hP
  have hPc : ∀ m n, MvPowerSeries.coeff (ex2 m n) P =
      MvPowerSeries.coeff (ex2 m n) B - coeff m (logLT ℂ_[ℓ] ℓ) * u n := fun m n => by
    rw [hP, map_sub, coeff_logX_mul_colY]
  have hkP : ∀ e, MvPowerSeries.coeff e P ∈ k := fun e => by
    rw [eq_ex2 e, hPc]
    exact k.sub_mem (hk _) (k.mul_mem (lc_mem _) (hk _))
  have hdp : IsXDp P := isXDp_of_biadd hφ hk hB
  have hΔ : deltaX P = deltaX B := by rw [hP, deltaX_sub, deltaX_logX_mul_colY, sub_zero]
  have hπ := isIntK_deltaX_tOpC hφ hkP hdp (hΔ ▸ hB)
  have hcol : ∀ n, ∃ a b : ℂ_[ℓ], ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ∀ m,
      ‖MvPowerSeries.coeff (ex2 m n) (tOpC k φ P) - a * coeff m (logLT ℂ_[ℓ] ℓ) -
        b * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m‖ ≤ 1 := fun n => by
    refine quasiLog_col ?_ ?_ fun i j => ?_
    · have e : MvPowerSeries.coeff (ex2 0 n) (tOpC k φ P) = MvPowerSeries.coeff (ex2 0 n) (tOpC k φ B) := by
        rw [coeff_tOpC_ex2, coeff_tOpC_ex2, hPc, hPc]
        simp only [lc_zero, Nat.zero_div, zero_mul, sub_zero]
      rw [e]
      exact norm_coeff_tOpC_zero_le hφ hk hB n
    · rw [coeff_tOpC_ex2, ite_eq_right fun h => hℓp.out.not_dvd_one h.1, mul_zero, sub_zero, hPc,
        coeff_one_logLT, one_mul, sub_self, norm_zero]
      exact zero_le_one
    · rw [← coeff_deltaX]
      exact hπ _
  choose a b ha hb hab using hcol
  refine ⟨a, b, ha, hb, fun m n => ?_⟩
  have e : MvPowerSeries.coeff (ex2 m n) (tOpC k φ B) - coeff m (logLT ℂ_[ℓ] ℓ) * (u n + a n) -
      (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m * (b n - if ℓ ∣ n then phiC k φ (u (n / ℓ)) else 0) =
      MvPowerSeries.coeff (ex2 m n) (tOpC k φ P) - a n * coeff m (logLT ℂ_[ℓ] ℓ) -
        b n * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m := by
    rw [coeff_tOpC_ex2, coeff_tOpC_ex2 (f := P), hPc]
    by_cases h : ℓ ∣ m ∧ ℓ ∣ n
    · rw [ite_eq_left h, ite_eq_left h, hPc, phiC_sub (hk _) (k.mul_mem (lc_mem _) (hk _)),
        phiC_mul (lc_mem _) (hk _), phiC_lc, lcF, ite_eq_left h.1, ite_eq_left h.2]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      have h0 : lcF ℓ m * (if ℓ ∣ n then phiC k φ (u (n / ℓ)) else 0) = 0 := by
        rcases not_and_or.1 h with hm | hn
        · rw [lcF, ite_eq_right hm, zero_mul]
        · rw [ite_eq_right hn, mul_zero]
      linear_combination (ℓ : ℂ_[ℓ])⁻¹ * h0
  rw [e]
  exact hab n m

variable (ℓ) in
/-- **`L(X)`** as a two-variable series. -/
abbrev logX : MvPowerSeries (Fin 2) ℂ_[ℓ] := (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ])

variable (ℓ) in
/-- **`L(Y)`** as a two-variable series. -/
abbrev logY : MvPowerSeries (Fin 2) ℂ_[ℓ] := (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ])

/-- **The coefficients of `α·L(X)L(Y) + γ·serAB`.** -/
theorem coeff_gaussForm (α γ : ℂ_[ℓ]) (m n : ℕ) :
    MvPowerSeries.coeff (ex2 m n) (MvPowerSeries.C α * logX ℓ * logY ℓ + MvPowerSeries.C γ * serAB ℓ) =
      α * (coeff m (logLT ℂ_[ℓ] ℓ) * coeff n (logLT ℂ_[ℓ] ℓ)) + γ * sAB ℓ m n := by
  rw [map_add, mul_assoc, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, coeff_subst_X0_mul_subst_X1]
  simp [ex2]

/-- **Closed subfields contain their `ℓ`-adic limits.** -/
theorem mem_of_approx (hk : IsClosed (k : Set ℂ_[ℓ])) {α : ℂ_[ℓ]} {s : ℕ → ℂ_[ℓ]} (hs : ∀ j, s j ∈ k)
    (h : ∀ j, ‖α - s j‖ ≤ ‖(ℓ : ℂ_[ℓ])‖ ^ j) : α ∈ k := by
  refine hk.mem_of_tendsto (b := Filter.atTop) ?_ (Filter.Eventually.of_forall hs)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_ell_lt_one (ℓ := ℓ)))
  rw [norm_sub_rev]
  exact h j

/-- **The structure theorem** (no hermitian hypothesis): over a closed subfield `k` with a Frobenius lift, a
symmetric series with coefficients in `k`, without constant term and biadditive up to `≃`, is
`≃ α·L(X)L(Y) + γ·serAB` with `α, γ ∈ k`, `φ γ = −γ`, `‖γ‖ ≤ 1`. From the one-sided form (`quasiBilin`) and the
symmetry, `U = u + a = αL + γℓ⁻¹L^F` and `V = b − ψu = γL + δL^F` exactly (`bilin_of_symm`); `α`, `γ` are limits of
elements of `k` (closedness); integrality of `b` at `Y^{ℓ^{2j+1}}`, `Y^{ℓ^{2j+2}}` gives `δ = −φ(α)` and
`φ(γ) = −γ`; then `T(B − αL(X)L(Y) − γ·serAB)` is integral (`serAB_frob`), and Dwork concludes. -/
theorem gauss_structure (k : Subfield ℂ_[ℓ]) {φ : k →+* k} (hk : IsClosed (k : Set ℂ_[ℓ]))
    (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {B : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hkB : ∀ n, MvPowerSeries.coeff n B ∈ k) (h0 : MvPowerSeries.constantCoeff B = 0)
    (hsym : MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] B = B) (hB : Simeq (deltaX B) 0) :
    ∃ α γ : k, φ γ = -γ ∧ ‖γ‖ ≤ 1 ∧
      Simeq B (MvPowerSeries.C (α : ℂ_[ℓ]) * logX ℓ * logY ℓ + MvPowerSeries.C (γ : ℂ_[ℓ]) * serAB ℓ) := by
  have hℓ := hℓp.out
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hn1 : ‖(ℓ : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ ℓ
  have hlk : (ℓ : ℂ_[ℓ]) ∈ k := natCast_mem k ℓ
  have hlik : (ℓ : ℂ_[ℓ])⁻¹ ∈ k := k.inv_mem hlk
  obtain ⟨a, b, ha, hb, hR⟩ := quasiBilin hφ hkB hB
  set u : ℕ → ℂ_[ℓ] := fun n => MvPowerSeries.coeff (ex2 1 n) B with hu
  set ψu : ℕ → ℂ_[ℓ] := fun n => if ℓ ∣ n then phiC k φ (u (n / ℓ)) else 0 with hψu
  set βc : ℕ → ℕ → ℂ_[ℓ] := fun m n => MvPowerSeries.coeff (ex2 m n) (tOpC k φ B) with hβc
  have hBs : ∀ m n, MvPowerSeries.coeff (ex2 m n) B = MvPowerSeries.coeff (ex2 n m) B := fun m n => by
    rw [← coeff_subst_swap, hsym]
  have hβs : ∀ m n, βc m n = βc n m := fun m n => by
    simp only [hβc, coeff_tOpC_ex2, hBs m n, hBs (m / ℓ) (n / ℓ), and_comm]
  have hR' : ∀ m n, ‖βc m n - coeff m (logLT ℂ_[ℓ] ℓ) * (u n + a n) -
      (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m * (b n - ψu n)‖ ≤ 1 := hR
  obtain ⟨α, γ, δ, hUV⟩ := bilin_of_symm (U := fun n => u n + a n) (V := fun n => b n - ψu n) hR' hβs
  have hU : ∀ n, u n + a n = α * coeff n (logLT ℂ_[ℓ] ℓ) + γ * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ n := fun n => (hUV n).1
  have hV : ∀ n, b n - ψu n = γ * coeff n (logLT ℂ_[ℓ] ℓ) + δ * lcF ℓ n := fun n => (hUV n).2
  -- `α` and `γ` lie in `k`
  have hαk : α ∈ k := by
    refine mem_of_approx hk (s := fun j => (ℓ : ℂ_[ℓ]) ^ j * u (ℓ ^ (2 * j)))
      (fun j => k.mul_mem (k.pow_mem hlk j) (hkB _)) fun j => ?_
    have h := hU (ℓ ^ (2 * j))
    rw [lc_pow, lcF_pow_even, mul_zero, add_zero] at h
    have e : α - (ℓ : ℂ_[ℓ]) ^ j * u (ℓ ^ (2 * j)) = (ℓ : ℂ_[ℓ]) ^ j * a (ℓ ^ (2 * j)) := by
      have : α = (ℓ : ℂ_[ℓ]) ^ j * (u (ℓ ^ (2 * j)) + a (ℓ ^ (2 * j))) := by rw [h]; field_simp
      rw [this]
      ring
    rw [e]
    exact norm_pow_mul_le (ha _) j
  have hγk : γ ∈ k := by
    refine mem_of_approx hk (s := fun j => (ℓ : ℂ_[ℓ]) ^ (j + 1) * u (ℓ ^ (2 * j + 1)))
      (fun j => k.mul_mem (k.pow_mem hlk _) (hkB _)) fun j => ?_
    have h := hU (ℓ ^ (2 * j + 1))
    rw [lc_pow_odd, lcF_pow, mul_zero, zero_add] at h
    have e : γ - (ℓ : ℂ_[ℓ]) ^ (j + 1) * u (ℓ ^ (2 * j + 1)) = (ℓ : ℂ_[ℓ]) ^ (j + 1) * a (ℓ ^ (2 * j + 1)) := by
      have : γ = (ℓ : ℂ_[ℓ]) ^ (j + 1) * (u (ℓ ^ (2 * j + 1)) + a (ℓ ^ (2 * j + 1))) := by
        rw [h]
        field_simp
        ring
      rw [this]
      ring
    rw [e]
    exact (norm_pow_mul_le (ha _) (j + 1)).trans (pow_le_pow_of_le_one (norm_nonneg _) hn1 (Nat.le_succ j))
  -- `a` takes values in `k`; Frobenius on `u`
  have hUk : ∀ n, α * coeff n (logLT ℂ_[ℓ] ℓ) + γ * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ n ∈ k := fun n =>
    k.add_mem (k.mul_mem hαk (lc_mem n)) (k.mul_mem (k.mul_mem hγk hlik) (lcF_mem n))
  have hu' : ∀ n, u n = α * coeff n (logLT ℂ_[ℓ] ℓ) + γ * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ n - a n := fun n => by
    rw [← hU n]
    ring
  have hak : ∀ n, a n ∈ k := fun n => by
    have : a n = α * coeff n (logLT ℂ_[ℓ] ℓ) + γ * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ n - u n := by
      rw [← hU n]
      ring
    rw [this]
    exact k.sub_mem (hUk n) (hkB _)
  have hphiu : ∀ n, phiC k φ (u n) = phiC k φ α * coeff n (logLT ℂ_[ℓ] ℓ) +
      phiC k φ γ * (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ n - phiC k φ (a n) := fun n => by
    rw [hu' n, phiC_sub (hUk n) (hak n), phiC_add (k.mul_mem hαk (lc_mem n))
      (k.mul_mem (k.mul_mem hγk hlik) (lcF_mem n)), phiC_mul hαk (lc_mem n),
      phiC_mul (k.mul_mem hγk hlik) (lcF_mem n), phiC_mul hγk hlik, phiC_lc, phiC_lcF, phiC_inv_ell]
  have hb' : ∀ n, b n = γ * coeff n (logLT ℂ_[ℓ] ℓ) + δ * lcF ℓ n + ψu n := fun n => by
    rw [← hV n]
    ring
  have hψ : ∀ n, ψu (ℓ * n) = phiC k φ (u n) := fun n => by
    simp only [hψu]
    rw [ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hℓ.pos]
  -- the Frobenius relations
  have hδ : phiC k φ α = -δ := by
    rw [eq_neg_iff_add_eq_zero]
    refine eq_zero_of_norm_le_pow fun j => norm_le_pow_of_norm_inv_pow_mul_le ?_
    have h := hb' (ℓ ^ (2 * j + 1))
    rw [lc_pow_odd, lcF_pow, show ℓ ^ (2 * j + 1) = ℓ * ℓ ^ (2 * j) by ring, hψ, hphiu, lc_pow,
      lcF_pow_even] at h
    have e : ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ * (phiC k φ α + δ) = b (ℓ * ℓ ^ (2 * j)) + phiC k φ (a (ℓ ^ (2 * j))) := by
      rw [h]
      ring
    rw [e]
    exact norm_add_le_one (hb _) (norm_phiC_le_one hφ (hak _) (ha _))
  have hγφ : phiC k φ γ = -γ := by
    rw [eq_neg_iff_add_eq_zero]
    refine eq_zero_of_norm_le_pow fun j => (norm_le_pow_of_norm_inv_pow_mul_le (k := j + 1) ?_).trans
      (pow_le_pow_of_le_one (norm_nonneg _) hn1 (Nat.le_succ j))
    have h := hb' (ℓ ^ (2 * (j + 1)))
    rw [lc_pow, lcF_pow_even, show ℓ ^ (2 * (j + 1)) = ℓ * ℓ ^ (2 * j + 1) by ring, hψ, hphiu, lc_pow_odd,
      lcF_pow] at h
    have e : ((ℓ : ℂ_[ℓ]) ^ (j + 1))⁻¹ * (phiC k φ γ + γ) =
        b (ℓ * ℓ ^ (2 * j + 1)) + phiC k φ (a (ℓ ^ (2 * j + 1))) := by
      rw [h]
      field_simp
      ring
    rw [e]
    exact norm_add_le_one (hb _) (norm_phiC_le_one hφ (hak _) (ha _))
  refine ⟨⟨α, hαk⟩, ⟨γ, hγk⟩, ?_, ?_, ?_⟩
  · exact Subtype.ext (by rw [← phiC_of_mem hγk, hγφ]; rfl)
  · -- `γ = ℓ·(u_ℓ + a_ℓ)` and `ℓ·u_ℓ = ℓ·B_{ℓ,1}` is integral by S1
    change ‖γ‖ ≤ 1
    have hlo : coeff ℓ (logLT ℂ_[ℓ] ℓ) = 0 := by simpa using lc_pow_odd (ℓ := ℓ) 0
    have hlF : lcF ℓ ℓ = 1 := by simpa using lcF_pow (ℓ := ℓ) 0
    have h := hU ℓ
    rw [hlo, hlF, mul_zero, zero_add, mul_one] at h
    have e : γ = (ℓ : ℂ_[ℓ]) * (MvPowerSeries.coeff (ex2 ℓ 1) B - coeff ℓ (logLT ℂ_[ℓ] ℓ) *
        MvPowerSeries.coeff (ex2 1 1) B) + (ℓ : ℂ_[ℓ]) * a ℓ := by
      rw [hlo, zero_mul, sub_zero, ← hBs, ← mul_add]
      change γ = (ℓ : ℂ_[ℓ]) * (u ℓ + a ℓ)
      rw [h]
      field_simp
    rw [e]
    refine norm_add_le_one (by exact_mod_cast norm_mul_coeff_sub_le_of_biadd hφ hkB hB ℓ 1) ?_
    rw [norm_mul]
    exact mul_le_one_of_le hn1 (ha ℓ)
  · rw [simeq_iff_sub]
    set D := B - (MvPowerSeries.C α * logX ℓ * logY ℓ + MvPowerSeries.C γ * serAB ℓ) with hD
    have hDc : ∀ m n, MvPowerSeries.coeff (ex2 m n) D = MvPowerSeries.coeff (ex2 m n) B -
        (α * (coeff m (logLT ℂ_[ℓ] ℓ) * coeff n (logLT ℂ_[ℓ] ℓ)) + γ * sAB ℓ m n) := fun m n => by
      rw [hD, map_sub, coeff_gaussForm]
    have hGk : ∀ m n, α * (coeff m (logLT ℂ_[ℓ] ℓ) * coeff n (logLT ℂ_[ℓ] ℓ)) + γ * sAB ℓ m n ∈ k :=
      fun m n => k.add_mem (k.mul_mem hαk (k.mul_mem (lc_mem m) (lc_mem n))) (k.mul_mem hγk (sAB_mem m n))
    have hDk : ∀ e, MvPowerSeries.coeff e D ∈ k := fun e => by
      rw [eq_ex2 e, hDc]
      exact k.sub_mem (hkB _) (hGk _ _)
    have hD0 : MvPowerSeries.constantCoeff D = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, show (0 : Fin 2 →₀ ℕ) = ex2 0 0 by simp [ex2], hDc,
        lc_zero, show ex2 0 0 = 0 by simp [ex2], MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0,
        show sAB ℓ 0 0 = 0 by simpa [sAB] using constantCoeff_serAB (ℓ := ℓ)]
      ring
    refine (simeq_zero_iff_isIntK_tOpC hφ hDk hD0).2 fun e => ?_
    obtain ⟨m, n, rfl⟩ : ∃ m n, e = ex2 m n := ⟨e 0, e 1, eq_ex2 e⟩
    have h' : (ℓ : ℂ_[ℓ])⁻¹ * ℓ = 1 := inv_mul_cancel₀ hℓ0
    have hF := serAB_frob (ℓ := ℓ) m n
    have key : MvPowerSeries.coeff (ex2 m n) (tOpC k φ D) = βc m n - coeff m (logLT ℂ_[ℓ] ℓ) * (u n + a n) -
        (ℓ : ℂ_[ℓ])⁻¹ * lcF ℓ m * (b n - ψu n) := by
      rw [hU n, hV n]
      simp only [hβc]
      rw [coeff_tOpC_ex2, coeff_tOpC_ex2 (f := B), hDc]
      by_cases h : ℓ ∣ m ∧ ℓ ∣ n
      · have hlm : lcF ℓ m = coeff (m / ℓ) (logLT ℂ_[ℓ] ℓ) := by rw [lcF, ite_eq_left h.1]
        have hln : lcF ℓ n = coeff (n / ℓ) (logLT ℂ_[ℓ] ℓ) := by rw [lcF, ite_eq_left h.2]
        rw [frobT, ite_eq_left h, hlm, hln] at hF
        rw [ite_eq_left h, ite_eq_left h, hDc, phiC_sub (hkB _) (hGk _ _),
          phiC_add (k.mul_mem hαk (k.mul_mem (lc_mem _) (lc_mem _))) (k.mul_mem hγk (sAB_mem _ _)),
          phiC_mul hαk (k.mul_mem (lc_mem _) (lc_mem _)), phiC_mul hγk (sAB_mem _ _),
          phiC_mul (lc_mem _) (lc_mem _), phiC_lc, phiC_lc, phiC_sAB, hγφ, hδ, hlm, hln]
        linear_combination (-γ * (ℓ : ℂ_[ℓ])⁻¹) * hF + (γ * sAB ℓ m n) * h'
      · rw [frobT, ite_eq_right h, zero_add] at hF
        rw [ite_eq_right h, ite_eq_right h]
        have hz : lcF ℓ m * lcF ℓ n = 0 := by
          rcases not_and_or.1 h with hm | hn
          · rw [lcF, ite_eq_right hm, zero_mul]
          · rw [show lcF ℓ n = 0 by rw [lcF, ite_eq_right hn], mul_zero]
        linear_combination (-γ * (ℓ : ℂ_[ℓ])⁻¹) * hF + (γ * sAB ℓ m n) * h' + ((ℓ : ℂ_[ℓ])⁻¹ * δ) * hz
    rw [key]
    exact hR' m n

end Structure

/-! ## The hermitian condition, and the classification -/

section Classification

variable {k : Subfield ℂ_[ℓ]} {φ : k →+* k}

/-- **`serAB` has no `X·Y^{ℓ^{2j}}` term.** -/
theorem sAB_one_pow_even (j : ℕ) : sAB ℓ 1 (ℓ ^ (2 * j)) = 0 := by
  refine sAB_of_not fun i j' h => ?_
  rcases h with ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩
  · exact pow_even_ne_odd j j' h
  · have : ℓ ≤ ℓ ^ (2 * j' + 1) := Nat.le_self_pow (by omega) ℓ
    have := hℓp.out.two_le
    omega

/-- **The `L(X)L(Y)` coefficient is read off the `X·Y^{ℓ^{2j}}` coefficients**: if `B ≃ α·L(X)L(Y) + γ·serAB`
with `α, γ ∈ k`, then `α = 0` iff these coefficients of `B` are bounded (Dwork: `B_{1,ℓ^{2j}} − α/ℓ^j` is
integral, the exponent `1` being prime to `ℓ`). -/
theorem alpha_eq_zero_iff (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {B : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hkB : ∀ n, MvPowerSeries.coeff n B ∈ k) {α γ : k}
    (hS : Simeq B (MvPowerSeries.C (α : ℂ_[ℓ]) * logX ℓ * logY ℓ + MvPowerSeries.C (γ : ℂ_[ℓ]) * serAB ℓ)) :
    α = 0 ↔ ∃ C : ℝ, ∀ j : ℕ, ‖MvPowerSeries.coeff (ex2 1 (ℓ ^ (2 * j))) B‖ ≤ C := by
  have hD := simeq_iff_sub.1 hS
  set D := B - (MvPowerSeries.C (α : ℂ_[ℓ]) * logX ℓ * logY ℓ + MvPowerSeries.C (γ : ℂ_[ℓ]) * serAB ℓ) with hDdef
  have hDc : ∀ m n, MvPowerSeries.coeff (ex2 m n) D = MvPowerSeries.coeff (ex2 m n) B -
      ((α : ℂ_[ℓ]) * (coeff m (logLT ℂ_[ℓ] ℓ) * coeff n (logLT ℂ_[ℓ] ℓ)) + (γ : ℂ_[ℓ]) * sAB ℓ m n) :=
    fun m n => by rw [hDdef, map_sub, coeff_gaussForm]
  have hDk : ∀ e, MvPowerSeries.coeff e D ∈ k := fun e => by
    rw [eq_ex2 e, hDc]
    exact k.sub_mem (hkB _) (k.add_mem (k.mul_mem α.2 (k.mul_mem (lc_mem _) (lc_mem _)))
      (k.mul_mem γ.2 (sAB_mem _ _)))
  have hD0 : MvPowerSeries.constantCoeff D = 0 := by
    have := hD.1
    rwa [sub_zero] at this
  have key : ∀ j, ‖MvPowerSeries.coeff (ex2 1 (ℓ ^ (2 * j))) B - (α : ℂ_[ℓ]) * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹‖ ≤ 1 :=
    fun j => by
      have h := norm_coeff_le_one_of_simeq_zero hφ hDk hD0 hD (e := ex2 1 (ℓ ^ (2 * j))) (i := 0)
        (by simpa [ex2] using hℓp.out.not_dvd_one)
      rwa [hDc, coeff_one_logLT, one_mul, lc_pow, sAB_one_pow_even, mul_zero, add_zero] at h
  constructor
  · rintro rfl
    refine ⟨1, fun j => ?_⟩
    have := key j
    rwa [ZeroMemClass.coe_zero, zero_mul, sub_zero] at this
  · rintro ⟨C, hC⟩
    refine Subtype.ext (norm_le_zero_iff.1 ?_)
    have hb : ∀ j, ‖(α : ℂ_[ℓ])‖ ≤ max C 1 * ‖(ℓ : ℂ_[ℓ])‖ ^ j := fun j => by
      have h1 : ‖(α : ℂ_[ℓ]) * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹‖ ≤ max C 1 := by
        rw [show (α : ℂ_[ℓ]) * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹ = MvPowerSeries.coeff (ex2 1 (ℓ ^ (2 * j))) B -
          (MvPowerSeries.coeff (ex2 1 (ℓ ^ (2 * j))) B - (α : ℂ_[ℓ]) * ((ℓ : ℂ_[ℓ]) ^ j)⁻¹) by ring]
        exact (norm_sub_le_max' _ _).trans (max_le_max (hC j) (key j))
      have hn0 : 0 < ‖(ℓ : ℂ_[ℓ])‖ ^ j := pow_pos (norm_pos_iff.2 (by exact_mod_cast hℓp.out.ne_zero)) j
      rw [norm_mul, norm_inv, norm_pow, mul_inv_le_iff₀ hn0] at h1
      exact h1
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (ℓ : ℂ_[ℓ])) norm_ell_lt_one).const_mul
      (max C 1)
    rw [mul_zero] at ht
    exact ge_of_tendsto' ht hb

/-- **The hermitian condition bounds the `X·Y^{ℓ^{2j}}` coefficients** (given one Teichmüller `ζ ∈ k` with
`‖ζ − ζ^ℓ‖ = 1`): `B(ζX, Y) − B(X, ζ^ℓY) ≃ 0` has the coefficient `(ζ − ζ^ℓ)·B_{1,ℓ^{2j}}` at the exponent
`(1, ℓ^{2j})`, integral by Dwork. -/
theorem bdd_of_isHerm (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {ζ : ℂ_[ℓ]} (hζk : ζ ∈ k)
    (hζ : ζ ^ (ℓ ^ 2) = ζ) (hζ1 : ‖ζ - ζ ^ ℓ‖ = 1) {B : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hkB : ∀ n, MvPowerSeries.coeff n B ∈ k) (hH : IsHerm B) :
    ∀ j : ℕ, ‖MvPowerSeries.coeff (ex2 1 (ℓ ^ (2 * j))) B‖ ≤ 1 := by
  intro j
  have hS := simeq_iff_sub.1 (hH ζ hζ)
  set H := MvPowerSeries.rescale ![ζ, 1] B - MvPowerSeries.rescale ![1, ζ ^ ℓ] B with hHdef
  have hHc : ∀ e : Fin 2 →₀ ℕ, MvPowerSeries.coeff e H = (ζ ^ e 0 - (ζ ^ ℓ) ^ e 1) * MvPowerSeries.coeff e B :=
    fun e => by
      rw [hHdef, map_sub, MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_rescale,
        Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
        Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one, one_mul]
      ring
  have hHk : ∀ e, MvPowerSeries.coeff e H ∈ k := fun e => by
    rw [hHc]
    exact k.mul_mem (k.sub_mem (k.pow_mem hζk _) (k.pow_mem (k.pow_mem hζk _) _)) (hkB e)
  have hH0 : MvPowerSeries.constantCoeff H = 0 := by
    have := hS.1
    rwa [sub_zero] at this
  have h := norm_coeff_le_one_of_simeq_zero hφ hHk hH0 hS (e := ex2 1 (ℓ ^ (2 * j))) (i := 0)
    (by simpa [ex2] using hℓp.out.not_dvd_one)
  rw [hHc] at h
  simp only [ex2, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true,
    Finsupp.single_eq_of_ne, add_zero, one_ne_zero, zero_add, pow_one] at h
  rw [← pow_mul, mul_comm ℓ, pow_mul, pow_pow_two_mul hζ, norm_mul, hζ1, one_mul] at h
  exact h

/-- **The classification under the bounded-coefficient form of the hermitian input**: over a closed subfield with
a Frobenius lift, a symmetric series with coefficients in `k`, without constant term, biadditive up to `≃`, whose
`X·Y^{ℓ^{2j}}` coefficients are bounded, is `≃ c·serAB` with `c ∈ k`, `φ(c) = −c`, `‖c‖ ≤ 1`. -/
theorem gauss_class_of_bdd (k : Subfield ℂ_[ℓ]) {φ : k →+* k} (hk : IsClosed (k : Set ℂ_[ℓ]))
    (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {B : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hkB : ∀ n, MvPowerSeries.coeff n B ∈ k) (h0 : MvPowerSeries.constantCoeff B = 0)
    (hsym : MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] B = B) (hB : Simeq (deltaX B) 0)
    (hbdd : ∃ C : ℝ, ∀ j : ℕ, ‖MvPowerSeries.coeff (ex2 1 (ℓ ^ (2 * j))) B‖ ≤ C) :
    ∃ c : k, φ c = -c ∧ ‖c‖ ≤ 1 ∧ Simeq B (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) := by
  obtain ⟨α, γ, hγ, hγ1, hS⟩ := gauss_structure k hk hφ hkB h0 hsym hB
  have hα : α = 0 := (alpha_eq_zero_iff hφ hkB hS).2 hbdd
  rw [hα, ZeroMemClass.coe_zero, map_zero, zero_mul, zero_mul, zero_add] at hS
  exact ⟨γ, hγ, hγ1, hS⟩

/-- **The uniqueness half of the classification, proved** for closed `k` containing a Teichmüller `ζ` with
`‖ζ − ζ^ℓ‖ = 1` (`gauss_structure`, `bdd_of_isHerm`, `alpha_eq_zero_iff`). For non-closed `k`, `GaussClass k φ` can
fail: over `ℚ(√ν)` a series `≃ c·serAB` with `c ∈ ℤ_ℓ√ν` outside `k` satisfies all its hypotheses. -/
theorem gaussClass_of_isClosed (k : Subfield ℂ_[ℓ]) (φ : k →+* k) (hk : IsClosed (k : Set ℂ_[ℓ]))
    (hζ : ∃ ζ ∈ k, ζ ^ (ℓ ^ 2) = ζ ∧ ‖ζ - ζ ^ ℓ‖ = 1) : GaussClass k φ := by
  intro hφ B hkB h0 hsym hB hH
  obtain ⟨ζ, hζk, hζ, hζ1⟩ := hζ
  exact gauss_class_of_bdd k hk hφ hkB h0 hsym ((biadd_iff_deltaX B).1 hB)
    ⟨1, bdd_of_isHerm hφ hζk hζ hζ1 hkB hH⟩

end Classification

/-! ## The side conditions for `unramC`, and the classification for the CM curve -/

section Unram

/-- **A root of unity of order prime to `ℓ`, other than `1`, is at distance `1` from `1`**: if `‖1 − w‖ < 1`, then
`Σ_{i<r} w^i ≡ r ≢ 0`, while `(1 − w)·Σ_{i<r} w^i = 1 − w^r = 0`. -/
theorem norm_one_sub_eq_one {w : ℂ_[ℓ]} {r : ℕ} (hr : ¬ ℓ ∣ r) (hw : w ^ r = 1) (hw1 : w ≠ 1) :
    ‖1 - w‖ = 1 := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero ℓ)
  have hw0 : ‖w‖ = 1 := by
    have h := congrArg norm hw
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hr0).1 h
  refine le_antisymm (norm_sub_le_one (by simp) hw0.le) (not_lt.1 fun hlt => ?_)
  have hs : ∑ i ∈ Finset.range r, w ^ i = 0 := by
    have h := mul_neg_geom_sum w r
    rw [hw, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (Ne.symm hw1))
  have hpow : ∀ i, ‖w ^ i - 1‖ ≤ ‖1 - w‖ := fun i => by
    rw [← geom_sum_mul, norm_mul, norm_sub_rev w 1]
    refine mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      zero_le_one fun t _ => ?_)
    rw [norm_pow, hw0, one_pow]
  have hsr : ‖∑ i ∈ Finset.range r, w ^ i - r‖ ≤ ‖1 - w‖ := by
    rw [show (r : ℂ_[ℓ]) = ∑ i ∈ Finset.range r, (1 : ℂ_[ℓ]) by simp, ← Finset.sum_sub_distrib]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => hpow i
  have hr1 : ‖(r : ℂ_[ℓ])‖ = 1 := CMThetaOne.norm_natCast_padicComplex ((Nat.Prime.coprime_iff_not_dvd hℓp.out).2 hr)
  rw [hs, zero_sub, norm_neg, hr1] at hsr
  exact absurd (hsr.trans_lt hlt) (lt_irrefl 1)

/-- **`unramC` contains a Teichmüller `ζ` with `‖ζ − ζ^ℓ‖ = 1`**: a primitive `(ℓ² − 1)`-th root of unity. -/
theorem exists_teich_unramC : ∃ ζ ∈ unramC ℓ, ζ ^ (ℓ ^ 2) = ζ ∧ ‖ζ - ζ ^ ℓ‖ = 1 := by
  have hℓ := hℓp.out
  have h2 := hℓ.two_le
  set n := ℓ ^ 2 - 1 with hn
  have hsq : ℓ ^ 2 = n + 1 := by
    have : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓ.pos
    omega
  have hn0 : n ≠ 0 := by
    have : 4 ≤ ℓ ^ 2 := by nlinarith
    omega
  have : NeZero ((n : ℕ) : ℂ_[ℓ]) := ⟨Nat.cast_ne_zero.2 hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[ℓ] n
  have hnd : ¬ ℓ ∣ n := fun h => hℓ.not_dvd_one (by
    have h' : ℓ ∣ ℓ ^ 2 := dvd_pow_self ℓ two_ne_zero
    rw [hsq] at h'
    exact (Nat.dvd_add_right h).1 h')
  refine ⟨ζ, ?_, ?_, ?_⟩
  · refine Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, Nat.pos_of_ne_zero hn0, hnd, hζ.pow_eq_one⟩)
  · rw [hsq, pow_succ, hζ.pow_eq_one, one_mul]
  · have hζ0 : ‖ζ‖ = 1 := by
      have h := congrArg norm hζ.pow_eq_one
      rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn0).1 h
    have e : ζ - ζ ^ ℓ = ζ * (1 - ζ ^ (ℓ - 1)) := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hℓ.one_le]
    have hw : (ζ ^ (ℓ - 1)) ^ (ℓ + 1) = 1 := by
      rw [← pow_mul, show (ℓ - 1) * (ℓ + 1) = n by rw [hn]; zify [hℓ.one_le, Nat.one_le_pow 2 ℓ hℓ.pos]; ring,
        hζ.pow_eq_one]
    have hw1 : ζ ^ (ℓ - 1) ≠ 1 := fun h => by
      have := Nat.le_of_dvd (by omega) ((hζ.pow_eq_one_iff_dvd _).1 h)
      have h4 : 2 * ℓ ≤ ℓ ^ 2 := by nlinarith
      omega
    have hnd' : ¬ ℓ ∣ ℓ + 1 := fun h => hℓ.not_dvd_one ((Nat.dvd_add_right (dvd_refl ℓ)).1 h)
    rw [e, norm_mul, hζ0, one_mul, norm_one_sub_eq_one hnd' hw hw1]

/-- **`unramC` is closed** (a topological closure). -/
theorem isClosed_unramC : IsClosed ((unramC ℓ : Subfield ℂ_[ℓ]) : Set ℂ_[ℓ]) :=
  Subfield.isClosed_topologicalClosure _

/-- **`GaussClass` holds for `unramC`.** -/
theorem gaussClass_unramC (φ : unramC ℓ →+* unramC ℓ) : GaussClass (unramC ℓ) φ :=
  gaussClass_of_isClosed _ φ isClosed_unramC exists_teich_unramC

/-- **The classification for the CM curve without `GaussClass`** (`be_classification_cm` with
`gaussClass_unramC`; only the hermitian input remains). -/
theorem be_classification_cm' (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified)
    (hs : CMs2Unram) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
    (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι : ℂ ≃+* ℂ_[ℓ]) {φ : unramC ℓ →+* unramC ℓ}
    (hφ : ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖)
    (hH : ∀ ε : ℂ_[ℓ], ε ∈ unramC ℓ → ‖ε‖ = 1 → IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) →
      IsHerm (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε)) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ c : unramC ℓ, φ c = -c ∧ ‖c‖ ≤ 1 ∧
      Simeq (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) :=
  be_classification_cm hb hj hu hs hd hd4 hcm hΔ h5 hdℓ hin ι hφ (gaussClass_unramC φ) hH

/-- **The classification for the CM curve under the bounded-coefficient form of the hermitian input**: instead of
`IsHerm (be …)`, the coefficients of `X·Y^{ℓ^{2j}}` in `be` are bounded (`gauss_class_of_bdd`; equivalent to the
hermitian property given the rest, by `alpha_eq_zero_iff` and `bdd_of_isHerm`). -/
theorem be_classification_cm_bdd (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified)
    (hs : CMs2Unram) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
    (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι : ℂ ≃+* ℂ_[ℓ]) {φ : unramC ℓ →+* unramC ℓ}
    (hφ : ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖)
    (hbdd : ∀ ε : ℂ_[ℓ], ε ∈ unramC ℓ → ‖ε‖ = 1 → IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) →
      ∃ C : ℝ, ∀ j : ℕ,
        ‖MvPowerSeries.coeff (ex2 1 (ℓ ^ (2 * j))) (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε)‖ ≤ C) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ c : unramC ℓ, φ c = -c ∧ ‖c‖ ≤ 1 ∧
      Simeq (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) := by
  have hℓ := hℓp.out.one_lt
  obtain ⟨ε, hεu, hε, ht⟩ := hb d Λ hd hd4 hcm hΔ ℓ h5 hdℓ hin ι
  obtain ⟨h2, h3⟩ := norm_g_le_one hj hd hd4 hcm hΔ h5 ι
  obtain ⟨h2u, h3u⟩ := hu d Λ hd hd4 hcm hΔ ℓ h5 hdℓ ι
  obtain ⟨hsu, -⟩ := hs d Λ hd hd4 hcm hΔ ℓ h5 hdℓ ι
  obtain ⟨hAdd, hODE⟩ := addLaw_weierODE_map Λ (ι : ℂ →+* ℂ_[ℓ])
  have hti : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) := fun n => (ht n).2
  have hk : ∀ n, MvPowerSeries.coeff n (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) ∈ unramC ℓ := fun n => by
    set be' := be ℓ (⟨ι Λ.g₂, h2u⟩ : unramC ℓ) ⟨ι Λ.g₃, h3u⟩ ⟨ι (ThetaNorm.s2 Λ), hsu⟩ ⟨ε, hεu⟩
    have h : MvPowerSeries.map (unramC ℓ).subtype be' = be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε :=
      map_be (unramC ℓ).subtype hℓ _ _ _ _
    rw [← h, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n be').2
  exact ⟨ε, hεu, hε, gauss_class_of_bdd (unramC ℓ) isClosed_unramC hφ hk (constantCoeff_be hℓ _ _ _ _)
    (be_symm _ _ _ _) ((biadd_iff_deltaX _).1 (be_biadd (by omega) h2 h3 hε hAdd hODE hti)) (hbdd ε hεu hε hti)⟩

end Unram

end

end CMFormalGauss
