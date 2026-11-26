import Mathlib
import CMFormalInert

/-!
# The Lubin–Tate formal group at an inert prime: the integral group law, Dwork's converse, the formal Gaussian

D1a′ of the D1 plan, continuing `CMFormalInert`: the integral height-2 Lubin–Tate group law (Hazewinkel's
functional-equation lemma), the converse of Dwork's lemma, and the formal objects of the Gaussian: the formal `σ*`,
the exponent `ph` and the pairing `be`.

**Congruences.** Over a nonarchimedean field, integral series congruent mod `ℓ` have `ℓ^m`-th powers congruent mod
`ℓ^{m+1}` (`norm_coeff_pow_sub_pow_le`, from Mathlib's `dvd_sub_pow_of_dvd_sub` over the unit ball), and a Frobenius
lift `φ` gives `F^φ(X^ℓ) ≡ F^ℓ (mod ℓ)` for every integral series `F` (`isDivK_frobS_sub_pow_of_isIntK`, from the
polynomial case by truncation). Agreement of the coefficients of total degree below `N` (`AgreeBelow`) passes to
powers, substitution and Frobenius, and gains a degree under `m`-th powers, `m ≥ 2`, of series without constant term.

**Hazewinkel's functional-equation lemma** (`isIntK_expLT_subst`). The logarithm satisfies
`log_LT(T) = T + ℓ⁻¹·log_LT(T^{ℓ²})` (`logLT_eq_X_add`). If `g` has no constant term and `g − ℓ⁻¹·g^{φ²}(X^{ℓ²})` is
integral, then `e(g)` is integral. With `h = e(g)`,
`h = (g − ℓ⁻¹g^{φ²}(X^{ℓ²})) + ℓ⁻¹(log_LT(h^{φ²}(X^{ℓ²})) − log_LT(h^{ℓ²}))`; in degree `n` the bracket only sees the
truncation `P` of `h` below `n`, where `P^{φ²}(X^{ℓ²}) ≡ P^{ℓ²} (mod ℓ)`, and `log_LT` keeps congruences mod `ℓ`
between integral series (`isDivK_logLT_subst_sub`: the term `T^{ℓ^{2j}}/ℓ^j` gains `ℓ^{2j+1}/ℓ^j`).

**The group law** `X ⊕ Y = e(log_LT(X) + log_LT(Y))` (`ltAdd`) has `log_LT(X ⊕ Y) = log_LT(X) + log_LT(Y)`
(`logLT_subst_ltAdd`), is defined over `ℚ` (`map_ltAdd`) and is integral (`isIntK_ltAdd`): over `ℚ_ℓ` the identity
lifts Frobenius (Fermat, `norm_sub_pow_le_padic`), and `g = log_LT(X) + log_LT(Y)` has
`g − ℓ⁻¹g(X^{ℓ²}, Y^{ℓ²}) = X + Y`.

**Dwork's converse** (`isDivK_of_isIntK_exp`). If `exp(f)` is integral, the Dwork defect `f^φ(X^ℓ) − ℓf` is
`ℓ`-divisible: with `F = exp(f)`, `exp(f^φ(X^ℓ) − ℓf) − 1 = (F^φ(X^ℓ) − F^ℓ)·F^{−ℓ} ≡ 0 (mod ℓ)`, and
`D = log(1 + (exp(D) − 1))` (`log_subst_exp_sub_one`, from Mathlib's `subst_log_exp_sub_one`) is `ℓ`-divisible when
`exp(D) ≡ 1` (`isDivK_of_isDivK_exp_sub_one`, as `‖ℓ^k/k‖ ≤ ‖ℓ‖`). With `simeq_zero_of_dwork` this is the criterion
`simeq_zero_iff_dwork`: for a series over a subfield of `ℂ_ℓ` carrying a Frobenius lift, `f ≃ 0` iff the Dwork defect
is `ℓ`-divisible.

**Roots** (`isIntK_of_pow_eq`). A series with unit constant term whose `N`-th power is integral, `ℓ ∤ N`, is
integral: the root extraction for the translates, whose `N`-th powers are rational functions.

**The formal Gaussian.** `logSig(z) = −s₂z²/2 − Σ_{k≥2} wpC(k)·z^{2k}/(2k(2k − 1))` is `log(σ*(z)/z)` (`logSig`),
`σ*(z) = z·exp(logSig(z))` (`sigF`), and the Gaussian exponent in Lubin–Tate coordinates is
`ph = −(log(log_LT(T)/T) + logSig(ε·log_LT(T)))` (`ph`), so that `εT·exp(−ph(T)) = σ*(ε·log_LT(T))`
(`C_mul_X_mul_exp_neg_ph`), i.e. `ph = −log Σ*` with `Σ*(T) = σ*(z(T))/(εT)`. The pairing is
`be(X, Y) = ph(X ⊕ Y) − ph(X) − ph(Y)` (`be`). Both are carried along field maps (`map_ph`, `map_be`), so they are
defined over any subfield containing `g₂, g₃, s₂, ε`, where Dwork's criterion applies.

**Main results:** `isIntK_expLT_subst`, `isIntK_ltAdd`, `logLT_subst_ltAdd`, `isDivK_of_isIntK_exp`,
`simeq_zero_iff_dwork`, `isIntK_of_pow_eq`, `C_mul_X_mul_exp_neg_ph`, `map_be`; the definitions `ltAdd`, `logSig`,
`sigF`, `ph`, `be`; and, as API for the classification `be ≃ c·serAB`, `constantCoeff_be`.
-/

namespace CMFormalInert

open PowerSeries

noncomputable section

/-! ## Congruences between integral series -/

section Cong

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} {ℓ : ℕ}

/-- **Divisibility over the unit ball from norms**: an `ℓ`-divisible series over the ball is `ℓ` times one. -/
theorem dvd_of_isDivK (hℓ : (ℓ : K) ≠ 0) {f : MvPowerSeries σ (ball1 K)}
    (hf : IsDivK ℓ (MvPowerSeries.map (ball1 K).subtype f)) : (ℓ : MvPowerSeries σ (ball1 K)) ∣ f := by
  have hg : ∀ n, MvPowerSeries.coeff n (MvPowerSeries.map (ball1 K).subtype f) / (ℓ : K) ∈ ball1 K := fun n => by
    change ‖_‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.2 hℓ)]
    exact hf n
  let g : MvPowerSeries σ (ball1 K) := fun n => ⟨_, hg n⟩
  refine ⟨g, ?_⟩
  ext n
  rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := ball1 K)), MvPowerSeries.coeff_C_mul]
  change _ = ((ℓ : ball1 K) : K) * (MvPowerSeries.coeff n (MvPowerSeries.map (ball1 K).subtype f) / (ℓ : K))
  rw [MvPowerSeries.coeff_map, Subring.coe_natCast, mul_div_cancel₀ _ hℓ]
  rfl

/-- **Norms from divisibility over the unit ball**: a multiple of `ℓ^k` has coefficients of norm `≤ ‖ℓ‖^k`. -/
theorem norm_coeff_map_le_of_dvd {k : ℕ} {f : MvPowerSeries σ (ball1 K)}
    (hf : (ℓ : MvPowerSeries σ (ball1 K)) ^ k ∣ f) (n : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff n (MvPowerSeries.map (ball1 K).subtype f)‖ ≤ ‖(ℓ : K)‖ ^ k := by
  obtain ⟨g, rfl⟩ := hf
  rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := ball1 K)), ← map_pow, map_mul, MvPowerSeries.map_C,
    MvPowerSeries.coeff_C_mul, norm_mul, MvPowerSeries.coeff_map]
  change ‖(((ℓ : ball1 K) ^ k : ball1 K) : K)‖ * _ ≤ _
  rw [SubmonoidClass.coe_pow, Subring.coe_natCast, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (MvPowerSeries.coeff n g).2

/-- **Powers of congruent series**: for integral `A ≡ B (mod ℓ)`, `A^{ℓ^m} ≡ B^{ℓ^m} (mod ℓ^{m+1})`. -/
theorem norm_coeff_pow_sub_pow_le (hℓ : (ℓ : K) ≠ 0) {A B : MvPowerSeries σ K} (hA : IsIntK A) (hB : IsIntK B)
    (hAB : IsDivK ℓ (A - B)) (m : ℕ) (n : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff n (A ^ ℓ ^ m - B ^ ℓ ^ m)‖ ≤ ‖(ℓ : K)‖ ^ (m + 1) := by
  obtain ⟨A', rfl⟩ := (isIntK_iff A).1 hA
  obtain ⟨B', rfl⟩ := (isIntK_iff B).1 hB
  rw [← map_sub] at hAB
  have h := dvd_sub_pow_of_dvd_sub (dvd_of_isDivK hℓ hAB) m
  rw [← map_pow, ← map_pow, ← map_sub]
  exact norm_coeff_map_le_of_dvd h n

end Cong

/-! ## Frobenius on integral series, and agreement in low degree -/

section Frob

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

omit [IsUltrametricDist K] hℓp in
/-- **Exponents divisible by `ℓ`** are `ℓ`-multiples. -/
theorem exists_eq_smul_of_dvd {α : σ →₀ ℕ} (h : ∀ i, ℓ ∣ α i) : ∃ β : σ →₀ ℕ, α = ℓ • β :=
  ⟨α.mapRange (· / ℓ) (by simp), by ext i; simp [Nat.mul_div_cancel' (h i)]⟩

omit hℓp in
/-- **A Frobenius lift preserves the unit ball.** -/
theorem norm_map_le_one {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖) {x : K}
    (hx : ‖x‖ ≤ 1) : ‖φ x‖ ≤ 1 := by
  have h1 : ‖x ^ ℓ‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have h2 : ‖φ x - x ^ ℓ‖ ≤ 1 := (hφ x hx).trans (IsUltrametricDist.norm_natCast_le_one K ℓ)
  calc ‖φ x‖ = ‖(φ x - x ^ ℓ) + x ^ ℓ‖ := by rw [sub_add_cancel]
    _ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 h1)

/-- **The Frobenius of an integral series is integral.** -/
theorem IsIntK.frobS {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖)
    {F : MvPowerSeries σ K} (hF : IsIntK F) : IsIntK (frobS ℓ φ F) := fun α => by
  by_cases hdiv : ∀ i, ℓ ∣ α i
  · obtain ⟨β, rfl⟩ := exists_eq_smul_of_dvd hdiv
    rw [coeff_frobS_smul]
    exact norm_map_le_one hφ (hF β)
  · push Not at hdiv
    obtain ⟨i, hi⟩ := hdiv
    rw [coeff_frobS_of_not_dvd _ _ hi, norm_zero]
    exact zero_le_one

/-- **Agreement below degree `N`**: the coefficients of total degree `< N` coincide. -/
def AgreeBelow (N : ℕ) (a b : MvPowerSeries σ K) : Prop :=
  ∀ β : σ →₀ ℕ, β.degree < N → MvPowerSeries.coeff β a = MvPowerSeries.coeff β b

omit [IsUltrametricDist K] hℓp in
/-- **Agreement is monotone.** -/
theorem AgreeBelow.mono {N M : ℕ} {a b : MvPowerSeries σ K} (h : AgreeBelow N a b) (hMN : M ≤ N) :
    AgreeBelow M a b := fun β hβ => h β (lt_of_lt_of_le hβ hMN)

omit [IsUltrametricDist K] hℓp in
/-- **A truncation agrees with the series** below its degree. -/
theorem agreeBelow_truncTotal [Finite σ] (N : ℕ) (a : MvPowerSeries σ K) :
    AgreeBelow N a (MvPowerSeries.truncTotal N a : MvPolynomial σ K) := fun β hβ => by
  rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hβ]

omit [IsUltrametricDist K] hℓp in
/-- **Agreement passes to powers** (finite index set). -/
theorem AgreeBelow.pow_eq [Finite σ] {N : ℕ} {a b : MvPowerSeries σ K} (h : AgreeBelow N a b) (m : ℕ) :
    AgreeBelow N (a ^ m) (b ^ m) := by
  have ht : MvPowerSeries.truncTotal N a = MvPowerSeries.truncTotal N b := by
    ext γ
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs with hγ
    · exact h γ hγ
    · rfl
  intro β hβ
  rw [← MvPowerSeries.coeff_truncTotal_pow _ hβ, ht, MvPowerSeries.coeff_truncTotal_pow _ hβ]

omit [IsUltrametricDist K] hℓp in
/-- **Agreement passes to substitution**: `f(a)` and `f(b)` agree below `N` when `a` and `b` do. -/
theorem AgreeBelow.subst [Finite σ] {N : ℕ} {a b : MvPowerSeries σ K} (h : AgreeBelow N a b)
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (f : K⟦X⟧) :
    AgreeBelow N (f.subst a) (f.subst b) := fun β hβ => by
  rw [PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero ha),
    PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hb)]
  exact finsum_congr fun d => by rw [h.pow_eq d β hβ]

omit [IsUltrametricDist K] in
/-- **Agreement passes to Frobenius**, with the degree bound multiplied by `ℓ`. -/
theorem AgreeBelow.frobS {N : ℕ} {a b : MvPowerSeries σ K} (h : AgreeBelow N a b) (φ : K →+* K) :
    AgreeBelow (ℓ * N) (frobS ℓ φ a) (frobS ℓ φ b) := fun α hα => by
  by_cases hdiv : ∀ i, ℓ ∣ α i
  · obtain ⟨β, rfl⟩ := exists_eq_smul_of_dvd hdiv
    rw [coeff_frobS_smul, coeff_frobS_smul, h β]
    rw [map_nsmul, smul_eq_mul] at hα
    exact Nat.lt_of_mul_lt_mul_left hα
  · push Not at hdiv
    obtain ⟨i, hi⟩ := hdiv
    rw [coeff_frobS_of_not_dvd _ _ hi, coeff_frobS_of_not_dvd _ _ hi]

omit [IsUltrametricDist K] hℓp in
/-- **Agreement of powers gains a degree**: if `a`, `b` have no constant term and agree below `N`, then
`a^m`, `b^m` agree below `N + 1` for `m ≥ 2`. -/
theorem AgreeBelow.pow_succ {N m : ℕ} {a b : MvPowerSeries σ K} (h : AgreeBelow N a b)
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (hm : 2 ≤ m) :
    AgreeBelow (N + 1) (a ^ m) (b ^ m) := fun β hβ => by
  classical
  rw [← sub_eq_zero, ← map_sub, ← geom_sum₂_mul, mul_comm, MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : p.1.degree < N
  · rw [map_sub, h p.1 h1, sub_self, zero_mul]
  · have h2 : p.2 = 0 := by
      have h3 := congrArg Finsupp.degree hp
      rw [map_add] at h3
      have h4 : p.2.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff _).1 h4
    rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow, map_pow, ha, hb]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero, one_mul, zero_pow (by omega : m - 1 - 0 ≠ 0)]
    · rw [zero_pow hi0.ne', zero_mul]

/-- **The Frobenius congruence for integral series**: `F^φ(X^ℓ) ≡ F^ℓ (mod ℓ)` for integral `F`, when `φ` lifts
Frobenius on the unit ball. -/
theorem isDivK_frobS_sub_pow_of_isIntK [Finite σ] {φ : K →+* K}
    (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖) {F : MvPowerSeries σ K} (hF : IsIntK F) :
    IsDivK ℓ (frobS ℓ φ F - F ^ ℓ) := by
  classical
  intro α
  set N := α.degree + 1
  set P : MvPowerSeries σ K := ((MvPowerSeries.truncTotal N F : MvPolynomial σ K) : MvPowerSeries σ K)
    with hPdef
  have hFP := agreeBelow_truncTotal N F
  have hPc : ∀ β, MvPowerSeries.coeff β P = if β.degree < N then MvPowerSeries.coeff β F else 0 :=
    fun β => by rw [hPdef, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
  have hPi : IsIntK P := fun β => by
    rw [hPc]
    split_ifs
    · exact hF β
    · simp
  have e1 : MvPowerSeries.coeff α (frobS ℓ φ F) = MvPowerSeries.coeff α (frobS ℓ φ P) :=
    (hFP.frobS φ) α (by have := hℓp.out.two_le; show α.degree < ℓ * (α.degree + 1); nlinarith)
  have e2 : MvPowerSeries.coeff α (F ^ ℓ) = MvPowerSeries.coeff α (P ^ ℓ) := hFP.pow_eq ℓ α (by omega)
  have hPsum : P = ∑ β ∈ (MvPowerSeries.truncTotal N F).support,
      MvPowerSeries.monomial β (MvPowerSeries.coeff β P) := by
    ext γ
    rw [map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq]
    split_ifs with hγ
    · rfl
    · rw [hPdef, MvPolynomial.coeff_coe]
      exact MvPolynomial.notMem_support_iff.1 hγ
  have := isDivK_frobS_sub_pow hφ (MvPowerSeries.truncTotal N F).support
    (fun β => MvPowerSeries.coeff β P) (fun β _ => hPi β)
  rw [← hPsum] at this
  rw [map_sub, e1, e2, ← map_sub]
  exact this α

end Frob

/-! ## Hazewinkel's functional-equation lemma -/

section Hazewinkel

/-- **The functional equation of `log_LT`**: `log_LT(T) = T + ℓ⁻¹·log_LT(T^{ℓ²})`. -/
theorem logLT_eq_X_add (K : Type) [Field K] [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) :
    logLT K ℓ = X + (ℓ : K)⁻¹ • (logLT K ℓ).subst (X ^ (ℓ ^ 2) : K⟦X⟧) := by
  have hq : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  ext n
  rw [map_add, coeff_smul, coeff_subst_X_pow hq, coeff_X, smul_eq_mul]
  by_cases h : ∃ j : ℕ, n = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := h
    rw [coeff_logLT_pow K hℓ]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hnd : ¬ ℓ ^ 2 ∣ ℓ ^ (2 * 0) := by
        rw [mul_zero, pow_zero, Nat.dvd_one]
        have : 4 ≤ ℓ ^ 2 := by nlinarith
        omega
      rw [ite_eq_right hnd]
      simp
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hd : ℓ ^ 2 ∣ ℓ ^ (2 * (i + 1)) := pow_dvd_pow ℓ (by omega)
      have hq' : ℓ ^ (2 * (i + 1)) / ℓ ^ 2 = ℓ ^ (2 * i) := by
        rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, Nat.mul_div_cancel _ (by positivity)]
      have h1 : ℓ ^ (2 * (i + 1)) ≠ 1 := by
        have := Nat.one_lt_pow (show 2 * (i + 1) ≠ 0 by omega) hℓ
        omega
      rw [ite_eq_left hd, hq', coeff_logLT_pow K hℓ, ite_eq_right h1, Algebra.algebraMap_self, RingHom.id_apply,
        zero_add, ← mul_inv, ← pow_succ']
  · push Not at h
    rw [coeff_logLT_of_ne K h, ite_eq_right (by have := h 0; simpa using this)]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ (by positivity), coeff_logLT_of_ne K fun j hj => h (j + 1) (by
        rw [hj, ← pow_add]; ring_nf)]
      simp
    · simp

/-- **The functional equation after substitution**: `log_LT(a) = a + ℓ⁻¹·log_LT(a^{ℓ²})`. -/
theorem logLT_subst_eq {K : Type} [Field K] [CharZero K] {σ : Type} {ℓ : ℕ} (hℓ : 1 < ℓ)
    {a : MvPowerSeries σ K} (ha : HasSubst a) :
    (logLT K ℓ).subst a = a + (ℓ : K)⁻¹ • (logLT K ℓ).subst (a ^ (ℓ ^ 2)) := by
  have hq : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  conv_lhs => rw [logLT_eq_X_add K hℓ]
  rw [subst_add ha, subst_X ha, subst_smul ha, subst_comp_subst_apply (HasSubst.X_pow hq) ha, subst_pow ha,
    subst_X ha]

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

omit [IsUltrametricDist K] in
/-- **Frobenius commutes with `log_LT`** (its coefficients are rational). -/
theorem frobS_logLT_subst (φ : K →+* K) {a : MvPowerSeries σ K} (ha : MvPowerSeries.constantCoeff a = 0) :
    frobS ℓ φ ((logLT K ℓ).subst a) = (logLT K ℓ).subst (frobS ℓ φ a) := by
  have has : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hma : PowerSeries.HasSubst (MvPowerSeries.map φ a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [MvPowerSeries.constantCoeff_map, ha, map_zero])
  change MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ ((logLT K ℓ).subst a)) =
    (logLT K ℓ).subst (MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ a))
  rw [PowerSeries.map_subst has, map_logLT, PowerSeries.expand_subst _ _ hma]

/-- **`log_LT` respects congruences**: for integral `A ≡ B (mod ℓ)` without constant terms,
`log_LT(A) ≡ log_LT(B) (mod ℓ)` (the term `T^{ℓ^{2j}}/ℓ^j` gains `ℓ^{2j+1}/ℓ^j`). -/
theorem isDivK_logLT_subst_sub [CharZero K] {A B : MvPowerSeries σ K} (hA : IsIntK A) (hB : IsIntK B)
    (hA0 : MvPowerSeries.constantCoeff A = 0) (hB0 : MvPowerSeries.constantCoeff B = 0) (hAB : IsDivK ℓ (A - B)) :
    IsDivK ℓ ((logLT K ℓ).subst A - (logLT K ℓ).subst B) := by
  classical
  have hℓ := hℓp.out
  have hℓ0 : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.2 hℓ.ne_zero
  have hn0 : 0 < ‖(ℓ : K)‖ := norm_pos_iff.2 hℓ0
  have hn1 : ‖(ℓ : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K ℓ
  intro α
  set s := Finset.range ((α.sum fun _ e => e) + 1)
  have hsupp : ∀ C : MvPowerSeries σ K, MvPowerSeries.constantCoeff C = 0 →
      (Function.support fun d : ℕ => coeff d (logLT K ℓ) • MvPowerSeries.coeff α (C ^ d)) ⊆ s := by
    intro C hC d hd
    simp only [Function.mem_support, ne_eq, Finset.coe_range, Set.mem_Iio, s] at hd ⊢
    by_contra hlt
    exact hd (by rw [coeff_pow_eq_zero hC (by omega), smul_zero])
  rw [map_sub, PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hA0),
    PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hB0), finsum_eq_sum_of_support_subset _ (hsupp A hA0),
    finsum_eq_sum_of_support_subset _ (hsupp B hB0), ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => ?_
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub]
  by_cases hd : ∃ j : ℕ, d = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := hd
    rw [coeff_logLT_pow K hℓ.one_lt, norm_mul, norm_inv, norm_pow, pow_mul]
    have h1 := norm_coeff_pow_sub_pow_le hℓ0 hA hB hAB (2 * j) α
    rw [pow_mul] at h1
    calc (‖(ℓ : K)‖ ^ j)⁻¹ * ‖MvPowerSeries.coeff α (A ^ (ℓ ^ 2) ^ j - B ^ (ℓ ^ 2) ^ j)‖
        ≤ (‖(ℓ : K)‖ ^ j)⁻¹ * ‖(ℓ : K)‖ ^ (2 * j + 1) := by gcongr
      _ = ‖(ℓ : K)‖ * ‖(ℓ : K)‖ ^ j := by
        field_simp
        ring
      _ ≤ ‖(ℓ : K)‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hn1
      _ = ‖(ℓ : K)‖ := mul_one _
  · push Not at hd
    rw [coeff_logLT_of_ne K hd, zero_mul, norm_zero]
    exact norm_nonneg _

/-- **Hazewinkel's functional-equation lemma** (integrality): let `φ` lift Frobenius on the unit ball. If `g` has
no constant term and `g − ℓ⁻¹·g^{φ²}(X^{ℓ²})` is integral, then `e(g) = log_LT^{−1}(g)` is integral. By induction on
the degree: `h = e(g)` satisfies `h = (g − ℓ⁻¹g^{φ²}(X^{ℓ²})) + ℓ⁻¹(log_LT(h^{φ²}(X^{ℓ²})) − log_LT(h^{ℓ²}))`, and in
degree `n` the bracket only sees the truncation `P` of `h` below `n`, where `P^{φ²}(X^{ℓ²}) ≡ P^{ℓ²} (mod ℓ)`. -/
theorem isIntK_expLT_subst [CharZero K] [Finite σ] {φ : K →+* K}
    (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖) {g : MvPowerSeries σ K}
    (hg0 : MvPowerSeries.constantCoeff g = 0) (hg : IsIntK (g - (ℓ : K)⁻¹ • frobS ℓ φ (frobS ℓ φ g))) :
    IsIntK ((expLT K ℓ).subst g) := by
  classical
  have hℓ := hℓp.out
  have hℓ0 : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.2 hℓ.ne_zero
  have hn0 : 0 < ‖(ℓ : K)‖ := norm_pos_iff.2 hℓ0
  set L := logLT K ℓ with hL
  set h := (expLT K ℓ).subst g with hdef
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero hg0
  have hEs : HasSubst (expLT K ℓ) := HasSubst.of_constantCoeff_zero' (constantCoeff_expLT K ℓ)
  have h0 : MvPowerSeries.constantCoeff h = 0 := constantCoeff_subst_eq_zero hg0 _ (constantCoeff_expLT K ℓ)
  have hfr0 : ∀ a : MvPowerSeries σ K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff (frobS ℓ φ a) = 0 := fun a ha => by rw [constantCoeff_frobS, ha, map_zero]
  have hLh : L.subst h = g := by
    rw [hdef, ← subst_comp_subst_apply hEs hgs, hL, logLT_subst_expLT K hℓ.one_lt, subst_X hgs]
  have hq0 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ.ne_zero
  have hq2 : 2 ≤ ℓ ^ 2 := le_trans hℓ.two_le (Nat.le_self_pow two_ne_zero ℓ)
  have hpow0 : MvPowerSeries.constantCoeff (h ^ (ℓ ^ 2)) = 0 := by
    rw [map_pow, h0, zero_pow hq0]
  -- `h = (g − ℓ⁻¹g^{φ²}(X^{ℓ²})) + ℓ⁻¹(log_LT(h^{φ²}(X^{ℓ²})) − log_LT(h^{ℓ²}))`
  have key : h = (g - (ℓ : K)⁻¹ • frobS ℓ φ (frobS ℓ φ g)) +
      (ℓ : K)⁻¹ • (L.subst (frobS ℓ φ (frobS ℓ φ h)) - L.subst (h ^ (ℓ ^ 2))) := by
    have e1 : frobS ℓ φ (frobS ℓ φ g) = L.subst (frobS ℓ φ (frobS ℓ φ h)) := by
      rw [← hLh, frobS_logLT_subst φ h0, frobS_logLT_subst φ (hfr0 h h0)]
    have e2 : g = h + (ℓ : K)⁻¹ • L.subst (h ^ (ℓ ^ 2)) := by
      rw [← hLh, hL, logLT_subst_eq hℓ.one_lt (HasSubst.of_constantCoeff_zero h0)]
    rw [e1, smul_sub, e2]
    abel
  suffices H : ∀ n : ℕ, ∀ α : σ →₀ ℕ, α.degree < n → ‖MvPowerSeries.coeff α h‖ ≤ 1 from
    fun α => H _ α (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro α hα; exact absurd hα (Nat.not_lt_zero _)
  | succ n ih =>
    intro α hα
    rcases Nat.lt_succ_iff_lt_or_eq.1 hα with hlt | hdeg
    · exact ih α hlt
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [(Finsupp.degree_eq_zero_iff α).1 hdeg, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, norm_zero]
      exact zero_le_one
    set P : MvPowerSeries σ K := ((MvPowerSeries.truncTotal n h : MvPolynomial σ K) : MvPowerSeries σ K)
      with hPdef
    have hhP : AgreeBelow n h P := agreeBelow_truncTotal n h
    have hPi : IsIntK P := fun β => by
      rw [hPdef, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
      split_ifs with hβ
      · exact ih β hβ
      · simp
    have hP0 : MvPowerSeries.constantCoeff P = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← hhP 0 (by simpa using hn),
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    have hPp0 : MvPowerSeries.constantCoeff (P ^ (ℓ ^ 2)) = 0 := by
      rw [map_pow, hP0, zero_pow hq0]
    -- the bracket only sees `P` in degree `n`
    have hq : n + 1 ≤ ℓ * (ℓ * n) := by have := hℓ.two_le; nlinarith
    have s1 : MvPowerSeries.coeff α (L.subst (frobS ℓ φ (frobS ℓ φ h))) =
        MvPowerSeries.coeff α (L.subst (frobS ℓ φ (frobS ℓ φ P))) :=
      ((((hhP.frobS φ).frobS φ).mono hq).subst (hfr0 _ (hfr0 h h0)) (hfr0 _ (hfr0 P hP0)) L) α (by omega)
    have s2 : MvPowerSeries.coeff α (L.subst (h ^ (ℓ ^ 2))) = MvPowerSeries.coeff α (L.subst (P ^ (ℓ ^ 2))) :=
      ((hhP.pow_succ h0 hP0 hq2).subst hpow0 hPp0 L) α (by omega)
    -- the Frobenius congruence `P^{φ²}(X^{ℓ²}) ≡ P^{ℓ²} (mod ℓ)`
    have hP1 := isDivK_frobS_sub_pow_of_isIntK hφ hPi
    have hP2 := isDivK_frobS_sub_pow_of_isIntK hφ (hPi.frobS hφ)
    have hP3 : IsDivK ℓ ((frobS ℓ φ P) ^ ℓ - (P ^ ℓ) ^ ℓ) := fun β => by
      have := norm_coeff_pow_sub_pow_le hℓ0 (hPi.frobS hφ) (hPi.pow ℓ) hP1 1 β
      rw [pow_one] at this
      exact this.trans (pow_le_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K ℓ) (by omega))
    have hcong : IsDivK ℓ (frobS ℓ φ (frobS ℓ φ P) - P ^ (ℓ ^ 2)) := by
      have e : frobS ℓ φ (frobS ℓ φ P) - P ^ (ℓ ^ 2) =
          (frobS ℓ φ (frobS ℓ φ P) - (frobS ℓ φ P) ^ ℓ) + ((frobS ℓ φ P) ^ ℓ - (P ^ ℓ) ^ ℓ) := by
        rw [← pow_mul, ← sq]
        ring
      rw [e]
      exact hP2.add hP3
    have hC := isDivK_logLT_subst_sub (((hPi.frobS hφ).frobS hφ)) (hPi.pow _) (hfr0 _ (hfr0 P hP0)) hPp0 hcong α
    have hc : MvPowerSeries.coeff α h = MvPowerSeries.coeff α (g - (ℓ : K)⁻¹ • frobS ℓ φ (frobS ℓ φ g)) +
        (ℓ : K)⁻¹ * MvPowerSeries.coeff α (L.subst (frobS ℓ φ (frobS ℓ φ P)) - L.subst (P ^ (ℓ ^ 2))) := by
      conv_lhs => rw [key]
      simp only [map_add, map_sub, MvPowerSeries.coeff_smul, s1, s2]
    rw [hc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hg α) ?_)
    rw [norm_mul, norm_inv]
    calc ‖(ℓ : K)‖⁻¹ * _ ≤ ‖(ℓ : K)‖⁻¹ * ‖(ℓ : K)‖ := by gcongr
      _ = 1 := inv_mul_cancel₀ hn0.ne'

end Hazewinkel

/-! ## The integral Lubin–Tate group law -/

section GroupLaw

/-- **Fermat in `ℤ_ℓ`**: the identity lifts Frobenius on the unit ball of `ℚ_ℓ`. -/
theorem norm_sub_pow_le_padic {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (x : ℚ_[ℓ]) (hx : ‖x‖ ≤ 1) :
    ‖RingHom.id ℚ_[ℓ] x - x ^ ℓ‖ ≤ ‖(ℓ : ℚ_[ℓ])‖ := by
  set y : ℤ_[ℓ] := ⟨x, hx⟩
  have hmem : y - y ^ ℓ ∈ RingHom.ker (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ) := by
    rw [RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card]
    exact sub_self _
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
    PadicInt.norm_lt_one_iff_dvd] at hmem
  obtain ⟨c, hc⟩ := hmem
  have e : RingHom.id ℚ_[ℓ] x - x ^ ℓ = ((y - y ^ ℓ : ℤ_[ℓ]) : ℚ_[ℓ]) := rfl
  rw [e, hc, PadicInt.coe_mul, norm_mul, PadicInt.coe_natCast]
  exact mul_le_of_le_one_right (norm_nonneg _) c.2

/-- **The Lubin–Tate formal group law** `X ⊕ Y = e(log_LT(X) + log_LT(Y))` (D1a′). -/
def ltAdd (K : Type) [Field K] (ℓ : ℕ) : MvPowerSeries (Fin 2) K :=
  (expLT K ℓ).subst ((logLT K ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) +
    (logLT K ℓ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))

/-- **The sum of logarithms has no constant term.** -/
theorem constantCoeff_logLT_add {K : Type} [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) :
    MvPowerSeries.constantCoeff ((logLT K ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) +
      (logLT K ℓ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = 0 := by
  rw [map_add, constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 0) _ (constantCoeff_logLT K hℓ),
    constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) _ (constantCoeff_logLT K hℓ), add_zero]

/-- **The group law has no constant term.** -/
theorem constantCoeff_ltAdd {K : Type} [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) :
    MvPowerSeries.constantCoeff (ltAdd K ℓ) = 0 :=
  constantCoeff_subst_eq_zero (constantCoeff_logLT_add hℓ) _ (constantCoeff_expLT K ℓ)

/-- **The logarithm of the group law**: `log_LT(X ⊕ Y) = log_LT(X) + log_LT(Y)`. -/
theorem logLT_subst_ltAdd {K : Type} [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) :
    (logLT K ℓ).subst (ltAdd K ℓ) = (logLT K ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) +
      (logLT K ℓ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  have hg := HasSubst.of_constantCoeff_zero (constantCoeff_logLT_add (K := K) hℓ)
  rw [ltAdd, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (constantCoeff_expLT K ℓ)) hg,
    logLT_subst_expLT K hℓ, subst_X hg]

/-- **The group law is defined over `ℚ`**: field maps carry it to itself. -/
theorem map_ltAdd {K L : Type} [Field K] [Field L] (f : K →+* L) {ℓ : ℕ} (hℓ : 1 < ℓ) :
    MvPowerSeries.map f (ltAdd K ℓ) = ltAdd L ℓ := by
  have hX : ∀ i : Fin 2, HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := fun i => HasSubst.X i
  rw [ltAdd, PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (constantCoeff_logLT_add hℓ)), map_expLT f hℓ,
    map_add, PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1), map_logLT, MvPowerSeries.map_X,
    MvPowerSeries.map_X, ltAdd]

/-- **The variables are integral.** -/
theorem isIntK_X {K : Type} [NormedField K] {σ : Type} (i : σ) : IsIntK (MvPowerSeries.X i : MvPowerSeries σ K) :=
  fun n => by
    classical
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp

/-- **The group law over `ℚ_ℓ` is integral** (Hazewinkel's lemma with `φ = id`, for
`g = log_LT(X) + log_LT(Y)`, where `g − ℓ⁻¹g(X^{ℓ²}, Y^{ℓ²}) = X + Y`). -/
theorem isIntK_ltAdd_padic {ℓ : ℕ} [hℓp : Fact ℓ.Prime] : IsIntK (ltAdd ℚ_[ℓ] ℓ) := by
  have hℓ := hℓp.out
  set L := logLT ℚ_[ℓ] ℓ
  have hX0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hfX : ∀ a : MvPowerSeries (Fin 2) ℚ_[ℓ], frobS ℓ (RingHom.id ℚ_[ℓ]) a = MvPowerSeries.expand ℓ hℓ.ne_zero a :=
    fun a => by simp [frobS, MvPowerSeries.map_id]
  have hfr : ∀ i : Fin 2, frobS ℓ (RingHom.id ℚ_[ℓ]) (frobS ℓ (RingHom.id ℚ_[ℓ]) (L.subst (MvPowerSeries.X i))) =
      L.subst ((MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[ℓ]) ^ (ℓ ^ 2)) := fun i => by
    rw [frobS_logLT_subst _ (hX0 i), frobS_logLT_subst _ (by rw [constantCoeff_frobS, hX0, map_zero]), hfX, hfX,
      MvPowerSeries.expand_X, map_pow, MvPowerSeries.expand_X, ← pow_mul, ← sq]
  apply isIntK_expLT_subst norm_sub_pow_le_padic (constantCoeff_logLT_add hℓ.one_lt)
  have e : ∀ i : Fin 2, L.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[ℓ]) =
      MvPowerSeries.X i + (ℓ : ℚ_[ℓ])⁻¹ • L.subst ((MvPowerSeries.X i : MvPowerSeries (Fin 2) ℚ_[ℓ]) ^ (ℓ ^ 2)) :=
    fun i => logLT_subst_eq hℓ.one_lt (HasSubst.X i)
  rw [map_add, map_add, hfr, hfr, e 0, e 1]
  have e2 : MvPowerSeries.X 0 + (ℓ : ℚ_[ℓ])⁻¹ • L.subst ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ_[ℓ]) ^ (ℓ ^ 2)) +
      (MvPowerSeries.X 1 + (ℓ : ℚ_[ℓ])⁻¹ • L.subst ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ_[ℓ]) ^ (ℓ ^ 2))) -
      (ℓ : ℚ_[ℓ])⁻¹ • (L.subst ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ_[ℓ]) ^ (ℓ ^ 2)) +
        L.subst ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ_[ℓ]) ^ (ℓ ^ 2))) =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
    rw [smul_add]
    abel
  rw [e2]
  exact fun n => by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (isIntK_X 0 n) (isIntK_X 1 n))

/-- **The Lubin–Tate group law is integral** (D1a′, item 1): `X ⊕ Y = e(log_LT(X) + log_LT(Y))` has coefficients in
the unit ball of `ℂ_ℓ` (indeed in `ℤ_(ℓ)`). -/
theorem isIntK_ltAdd {ℓ : ℕ} [hℓp : Fact ℓ.Prime] : IsIntK (ltAdd ℂ_[ℓ] ℓ) := fun n => by
  rw [← map_ltAdd (algebraMap ℚ_[ℓ] ℂ_[ℓ]) hℓp.out.one_lt, MvPowerSeries.coeff_map]
  exact (PadicComplex.norm_extends' ℓ _).trans_le (isIntK_ltAdd_padic n)

end GroupLaw

/-! ## Dwork's converse -/

section DworkConverse

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

omit [NormedField K] [IsUltrametricDist K] in
/-- **`log` inverts `exp`**: `log(1 + (exp(D) − 1)) = D` for `D` without constant term. -/
theorem log_subst_exp_sub_one {A : Type} [CommRing A] [Algebra ℚ A] {D : MvPowerSeries σ A}
    (hD : MvPowerSeries.constantCoeff D = 0) : (PowerSeries.log A).subst ((PowerSeries.exp A).subst D - 1) = D := by
  have hDs : HasSubst D := HasSubst.of_constantCoeff_zero hD
  have h := congrArg (PowerSeries.subst D) (PowerSeries.subst_log_exp_sub_one A)
  have h1 : (1 : A⟦X⟧).subst D = (1 : MvPowerSeries σ A) := by
    rw [← map_one (PowerSeries.C (R := A)), subst_C, map_one]
  rwa [subst_comp_subst_apply HasSubst.exp_sub_one hDs, subst_X hDs, subst_sub hDs, h1] at h

omit [IsUltrametricDist K] in
/-- **`v_ℓ(k) ≤ k − 1`** for `k ≥ 1`. -/
theorem padicValNat_le_sub_one {k : ℕ} (hk : k ≠ 0) : padicValNat ℓ k ≤ k - 1 := by
  have h1 : ℓ ^ padicValNat ℓ k ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) pow_padicValNat_dvd
  have h2 : k < ℓ ^ k := Nat.lt_pow_self hℓp.out.one_lt
  have := (Nat.pow_lt_pow_iff_right hℓp.out.one_lt).1 (lt_of_le_of_lt h1 h2)
  omega

/-- **`log(1 + ℓ·integral) ≡ 0 (mod ℓ)`**: for `g` without constant term and `ℓ`-divisible, `log(1 + g)` is
`ℓ`-divisible (`‖ℓ^k/k‖ ≤ ‖ℓ‖`; the norm on `ℕ` being `ℓ`-adic). -/
theorem isDivK_log_subst [CharZero K] (hK : ∀ n : ℕ, ‖(n : K)‖ = ‖(n : ℚ_[ℓ])‖) {g : MvPowerSeries σ K}
    (hg : IsDivK ℓ g) (hg0 : MvPowerSeries.constantCoeff g = 0) : IsDivK ℓ ((PowerSeries.log K).subst g) := by
  classical
  intro α
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓp.out.pos
  have hℓn : ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ := by rw [hK, Padic.norm_p]
  set s := Finset.range ((α.sum fun _ e => e) + 1)
  have hsupp : (Function.support fun d : ℕ => coeff d (PowerSeries.log K) • MvPowerSeries.coeff α (g ^ d)) ⊆ s := by
    intro d hd
    simp only [Function.mem_support, ne_eq, Finset.coe_range, Set.mem_Iio, s] at hd ⊢
    by_contra hlt
    exact hd (by rw [coeff_pow_eq_zero hg0 (by omega), smul_zero])
  rw [PowerSeries.coeff_subst (HasSubst.of_constantCoeff_zero hg0), finsum_eq_sum_of_support_subset _ hsupp]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => ?_
  rw [PowerSeries.coeff_log, smul_eq_mul]
  split_ifs with hd
  · rw [zero_mul, norm_zero]
    exact norm_nonneg _
  · rw [map_div₀, map_pow, map_neg, map_one, map_natCast, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow,
      hK d, norm_natCast_padic d hd]
    have hv := padicValNat_le_sub_one (ℓ := ℓ) hd
    calc 1 / (ℓ : ℝ) ^ (-(padicValNat ℓ d : ℤ)) * ‖MvPowerSeries.coeff α (g ^ d)‖
        ≤ (ℓ : ℝ) ^ (padicValNat ℓ d) * ‖(ℓ : K)‖ ^ d := by
          rw [zpow_neg, one_div, inv_inv, zpow_natCast]
          exact mul_le_mul_of_nonneg_left (norm_coeff_pow_le_of_isDivK hg _ _) (by positivity)
      _ ≤ (ℓ : ℝ) ^ (d - 1) * ‖(ℓ : K)‖ ^ d := by
          gcongr
          exact_mod_cast hℓp.out.one_le
      _ = ‖(ℓ : K)‖ := by
          obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
          rw [hℓn, Nat.add_sub_cancel, pow_succ, inv_pow]
          field_simp

/-- **`exp(D) ≡ 1 (mod ℓ)` forces `D ≡ 0 (mod ℓ)`** for `D` without constant term (`D = log(exp D)`). -/
theorem isDivK_of_isDivK_exp_sub_one [CharZero K] (hK : ∀ n : ℕ, ‖(n : K)‖ = ‖(n : ℚ_[ℓ])‖)
    {D : MvPowerSeries σ K} (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hD : IsDivK ℓ ((PowerSeries.exp K).subst D - 1)) : IsDivK ℓ D := by
  have h0 : MvPowerSeries.constantCoeff ((PowerSeries.exp K).subst D - 1) = 0 := by
    rw [map_sub, PowerSeries.constantCoeff_subst_of_constantCoeff_zero hD0]
    simp
  rw [← log_subst_exp_sub_one hD0]
  exact isDivK_log_subst hK hD h0

/-- **Dwork's converse**: if `f` has no constant term and `exp(f)` is integral, the Dwork defect `f^φ(X^ℓ) − ℓf` is
`ℓ`-divisible (`φ` a Frobenius lift, the norm on `ℕ` `ℓ`-adic). With `F = exp(f)`:
`exp(f^φ(X^ℓ) − ℓf) − 1 = (F^φ(X^ℓ) − F^ℓ)·F^{−ℓ} ≡ 0 (mod ℓ)`. -/
theorem isDivK_of_isIntK_exp [CharZero K] [Finite σ] (hK : ∀ n : ℕ, ‖(n : K)‖ = ‖(n : ℚ_[ℓ])‖) {φ : K →+* K}
    (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖) {f : MvPowerSeries σ K}
    (hf0 : MvPowerSeries.constantCoeff f = 0) (hF : IsIntK ((PowerSeries.exp K).subst f)) :
    IsDivK ℓ (frobS ℓ φ f - ℓ • f) := by
  set F := (PowerSeries.exp K).subst f with hFdef
  have hfr0 : MvPowerSeries.constantCoeff (frobS ℓ φ f) = 0 := by rw [constantCoeff_frobS, hf0, map_zero]
  have hnf0 : MvPowerSeries.constantCoeff (ℓ • f) = 0 := by rw [map_nsmul, hf0, smul_zero]
  have hD0 : MvPowerSeries.constantCoeff (frobS ℓ φ f - ℓ • f) = 0 := by rw [map_sub, hfr0, hnf0, sub_zero]
  have hF0 : MvPowerSeries.constantCoeff F = 1 := by
    rw [hFdef, PowerSeries.constantCoeff_subst_of_constantCoeff_zero hf0]
    simp
  have hFl0 : MvPowerSeries.constantCoeff (F ^ ℓ) = 1 := by rw [map_pow, hF0, one_pow]
  have hexp : (PowerSeries.exp K).subst (frobS ℓ φ f - ℓ • f) * F ^ ℓ = frobS ℓ φ F := by
    rw [hFdef, frobS_exp_subst φ hf0, ← exp_subst_nsmul hf0, ← exp_subst_add hD0 hnf0, sub_add_cancel]
  have hinv : (PowerSeries.exp K).subst (frobS ℓ φ f - ℓ • f) - 1 = (frobS ℓ φ F - F ^ ℓ) * (F ^ ℓ)⁻¹ := by
    rw [← hexp, ← sub_one_mul, mul_assoc, MvPowerSeries.mul_inv_cancel _ (by rw [hFl0]; exact one_ne_zero),
      mul_one]
  refine isDivK_of_isDivK_exp_sub_one hK hD0 ?_
  rw [hinv]
  exact (isDivK_frobS_sub_pow_of_isIntK hφ hF).mul_isInt ((hF.pow ℓ).inv hFl0)

/-- **Dwork's criterion for `≃`, both directions** (D1a′, item 2): for a series over a subfield `k` of `ℂ_ℓ` with a
Frobenius lift `φ`, without constant term, `f ≃ 0` iff its Dwork defect `f^φ(X^ℓ) − ℓf` is `ℓ`-divisible. -/
theorem simeq_zero_iff_dwork [Finite σ] (k : Subfield ℂ_[ℓ]) {φ : k →+* k}
    (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {f : MvPowerSeries σ k}
    (hf0 : MvPowerSeries.constantCoeff f = 0) :
    Simeq (MvPowerSeries.map k.subtype f) 0 ↔ IsDivK ℓ (frobS ℓ φ f - ℓ • f) := by
  refine ⟨fun h => ?_, simeq_zero_of_dwork k hφ hf0⟩
  have hK : ∀ n : ℕ, ‖(n : k)‖ = ‖(n : ℚ_[ℓ])‖ := fun n => by
    change ‖((n : k) : ℂ_[ℓ])‖ = _
    have e1 : ((n : k) : ℂ_[ℓ]) = (n : ℂ_[ℓ]) := map_natCast k.subtype n
    have e2 : ((n : ℚ_[ℓ]) : ℂ_[ℓ]) = (n : ℂ_[ℓ]) := by norm_cast
    rw [e1, ← e2, PadicComplex.norm_extends']
  have hm0 : MvPowerSeries.constantCoeff (MvPowerSeries.map k.subtype f) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hf0, map_zero]
  refine isDivK_of_isIntK_exp hK hφ hf0 fun α => ?_
  have h2 := h.2 α
  rw [sub_zero, expMv_eq_subst hm0, ← PowerSeries.map_exp k.subtype,
    ← PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf0), MvPowerSeries.coeff_map] at h2
  exact h2

end DworkConverse

/-! ## The formal `σ*`, the Gaussian exponent `ph` and the pairing `be` -/

section Gaussian

variable {K : Type} [Field K] [CharZero K]

/-- **The exponent of `σ*(z)/z`**: `logSig(z) = −s₂z²/2 − Σ_{k≥2} wpC(k)·z^{2k}/(2k(2k − 1))`. With
`σ*(z) = σ(z)·e^{−s₂z²/2}` this is `log(σ*(z)/z)`, since `log(σ(z)/z) = −Σ_{k≥2} wpC(k)·z^{2k}/(2k(2k − 1))` by
`℘ = −(log σ)″`. -/
def logSig (a b s : K) : K⟦X⟧ :=
  mk fun n => if n = 2 then -s / 2 else if Even n then -wpC a b (n / 2) / ((n : K) * ((n : K) - 1)) else 0

/-- **`logSig` has no constant term.** -/
theorem constantCoeff_logSig (a b s : K) : constantCoeff (logSig a b s) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, logSig, coeff_mk]
  simp [wpC]

/-- **The formal `σ*`**: `σ*(z) = z·exp(logSig(z))`. -/
def sigF (a b s : K) : K⟦X⟧ := X * (exp K).subst (logSig a b s)

/-- **The series `log_LT(T)/T`**. -/
def logLTDivX (K : Type) [Field K] (ℓ : ℕ) : K⟦X⟧ := mk fun n => coeff (n + 1) (logLT K ℓ)

omit [CharZero K] in
/-- **`T·(log_LT(T)/T) = log_LT(T)`.** -/
theorem X_mul_logLTDivX {ℓ : ℕ} (hℓ : 1 < ℓ) : X * logLTDivX K ℓ = logLT K ℓ := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul,
      constantCoeff_logLT K hℓ]
  · rw [coeff_succ_X_mul, logLTDivX, coeff_mk]

omit [CharZero K] in
/-- **`log_LT(T)/T` has constant term `1`.** -/
theorem constantCoeff_logLTDivX (ℓ : ℕ) : constantCoeff (logLTDivX K ℓ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, logLTDivX, coeff_mk, coeff_one_logLT]

/-- **The Gaussian exponent** `ph(T) = −log Σ*(T)` (D1a′), where `Σ*(T) = σ*(z(T))/(εT)` and `z(T) = ε·log_LT(T)`:
`ph = −(log(log_LT(T)/T) + logSig(ε·log_LT(T)))`. -/
def ph (ℓ : ℕ) (a b s ε : K) : K⟦X⟧ :=
  -(logOf (logLTDivX K ℓ) + (logSig a b s).subst (C ε * logLT K ℓ))

/-- **`ph` has no constant term.** -/
theorem constantCoeff_ph {ℓ : ℕ} (hℓ : 1 < ℓ) (a b s ε : K) : constantCoeff (ph ℓ a b s ε) = 0 := by
  have h : constantCoeff ((logSig a b s).subst (C ε * logLT K ℓ)) = 0 :=
    constantCoeff_subst_eq_zero (constantCoeff_C_mul_logLT hℓ ε) _ (constantCoeff_logSig a b s)
  rw [ph, map_neg, map_add, constantCoeff_logOf (constantCoeff_logLTDivX ℓ), h, add_zero, neg_zero]

/-- **`ph` is minus the logarithm of the formal `Σ*`**: `εT·exp(−ph(T)) = σ*(ε·log_LT(T))`. -/
theorem C_mul_X_mul_exp_neg_ph {ℓ : ℕ} (hℓ : 1 < ℓ) (a b s ε : K) :
    C ε * X * (exp K).subst (-ph ℓ a b s ε) = (sigF a b s).subst (C ε * logLT K ℓ) := by
  set u := logLTDivX K ℓ
  set z := C ε * logLT K ℓ with hz
  have hz0 : constantCoeff z = 0 := constantCoeff_C_mul_logLT hℓ ε
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  have hu1 : constantCoeff (u - 1) = 0 := by rw [map_sub, constantCoeff_logLTDivX, map_one, sub_self]
  have hus : HasSubst (u - 1) := HasSubst.of_constantCoeff_zero' hu1
  have hL0 : constantCoeff (logOf u) = 0 := constantCoeff_logOf (constantCoeff_logLTDivX ℓ)
  have hS0 : constantCoeff ((logSig a b s).subst z) = 0 :=
    constantCoeff_subst_eq_zero hz0 _ (constantCoeff_logSig a b s)
  have hexpu : (exp K).subst (logOf u) = u := by
    rw [logOf_eq, ← subst_comp_subst_apply HasSubst.log hus, subst_exp_log, subst_add hus, subst_X hus,
      ← map_one (C (R := K)), subst_C, map_one]
    change 1 + (u - 1) = u
    ring
  have hexpS : (exp K).subst ((logSig a b s).subst z) = PowerSeries.subst z ((exp K).subst (logSig a b s)) := by
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (constantCoeff_logSig a b s)) hzs]
  have hadd : (exp K).subst (logOf u + (logSig a b s).subst z) =
      (exp K).subst (logOf u) * (exp K).subst ((logSig a b s).subst z) := exp_subst_add hL0 hS0
  have hsig : (sigF a b s).subst z = z * PowerSeries.subst z ((exp K).subst (logSig a b s)) := by
    rw [sigF, subst_mul hzs, subst_X hzs]
  rw [ph, neg_neg, hadd, hexpu, hexpS, hsig, hz, ← X_mul_logLTDivX hℓ]
  simp only [mul_assoc, u]

end Gaussian

/-- **The Gaussian pairing** `be(X, Y) = ph(X ⊕ Y) − ph(X) − ph(Y)` (D1a′). -/
def be {K : Type} [Field K] [CharZero K] (ℓ : ℕ) (a b s ε : K) : MvPowerSeries (Fin 2) K :=
  (ph ℓ a b s ε).subst (ltAdd K ℓ) - (ph ℓ a b s ε).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
    (ph ℓ a b s ε).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)

/-- **`be` has no constant term.** -/
theorem constantCoeff_be {K : Type} [Field K] [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) (a b s ε : K) :
    MvPowerSeries.constantCoeff (be ℓ a b s ε) = 0 := by
  rw [be, map_sub, map_sub, constantCoeff_subst_eq_zero (constantCoeff_ltAdd hℓ) _ (constantCoeff_ph hℓ a b s ε),
    constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 0) _ (constantCoeff_ph hℓ a b s ε),
    constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) _ (constantCoeff_ph hℓ a b s ε), sub_zero,
    sub_zero]



/-! ## Roots of integral series -/

section Root

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type}

/-- **Prime-to-`ℓ` roots of integral series are integral**: if `V^N = U` with `U` integral, `V(0)` a unit and
`‖N‖ = 1`, then `V` is integral (in degree `n`, `N·V(0)^{N−1}·V_α = U_α − (P^N)_α` for the truncation `P` of `V`
below `n`). This is the root extraction for the translates `G_q`, whose `N`-th power is a rational function. -/
theorem isIntK_of_pow_eq [Finite σ] {N : ℕ} (hN : ‖(N : K)‖ = 1) {U V : MvPowerSeries σ K} (hU : IsIntK U)
    (hV0 : ‖MvPowerSeries.constantCoeff V‖ = 1) (hVU : V ^ N = U) : IsIntK V := by
  classical
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  set v₀ := MvPowerSeries.constantCoeff V
  suffices H : ∀ n : ℕ, ∀ α : σ →₀ ℕ, α.degree < n → ‖MvPowerSeries.coeff α V‖ ≤ 1 from
    fun α => H _ α (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro α hα; exact absurd hα (Nat.not_lt_zero _)
  | succ n ih =>
    intro α hα
    rcases Nat.lt_succ_iff_lt_or_eq.1 hα with hlt | hdeg
    · exact ih α hlt
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [(Finsupp.degree_eq_zero_iff α).1 hdeg, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hV0]
    set P : MvPowerSeries σ K := ((MvPowerSeries.truncTotal n V : MvPolynomial σ K) : MvPowerSeries σ K)
      with hPdef
    have hVP : AgreeBelow n V P := agreeBelow_truncTotal n V
    have hPi : IsIntK P := fun β => by
      rw [hPdef, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
      split_ifs with hβ
      · exact ih β hβ
      · simp
    have hP0 : MvPowerSeries.constantCoeff P = v₀ := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← hVP 0 (by simpa using hn),
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    -- the coefficient `α` of `V^N − P^N = (V − P)·Σ V^iP^{N−1−i}` is `V_α·N·v₀^{N−1}`
    have hPα : MvPowerSeries.coeff α P = 0 := by
      rw [hPdef, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite, ite_eq_right (by omega)]
    have hS0 : MvPowerSeries.constantCoeff (∑ i ∈ Finset.range N, V ^ i * P ^ (N - 1 - i)) =
        (N : K) * v₀ ^ (N - 1) := by
      have e : ∀ i ∈ Finset.range N, v₀ ^ i * v₀ ^ (N - 1 - i) = v₀ ^ (N - 1) := fun i hi => by
        rw [← pow_add]
        congr 1
        rw [Finset.mem_range] at hi
        omega
      rw [map_sum]
      simp only [map_mul, map_pow, hP0]
      change ∑ i ∈ Finset.range N, v₀ ^ i * v₀ ^ (N - 1 - i) = _
      rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hc : MvPowerSeries.coeff α (V ^ N) - MvPowerSeries.coeff α (P ^ N) =
        MvPowerSeries.coeff α V * ((N : K) * v₀ ^ (N - 1)) := by
      rw [← map_sub, ← geom_sum₂_mul, mul_comm, MvPowerSeries.coeff_mul, Finset.sum_eq_single (α, 0)]
      · rw [map_sub, hPα, sub_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hS0]
      · intro p hp hne
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        by_cases h1 : p.1.degree < n
        · rw [map_sub, hVP p.1 h1, sub_self, zero_mul]
        · exfalso
          have h3 := congrArg Finsupp.degree hp
          rw [map_add] at h3
          have h4 : p.2.degree = 0 := by omega
          have h2 : p.2 = 0 := (Finsupp.degree_eq_zero_iff _).1 h4
          apply hne
          rw [h2, add_zero] at hp
          exact Prod.ext hp h2
      · intro h
        exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (add_zero α)) h
    have hu : ‖(N : K) * v₀ ^ (N - 1)‖ = 1 := by rw [norm_mul, norm_pow, hN, hV0, one_pow, one_mul]
    have hk : ‖MvPowerSeries.coeff α V * ((N : K) * v₀ ^ (N - 1))‖ ≤ 1 := by
      rw [← hc, hVU, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hU α) (by rw [norm_neg]; exact hPi.pow N α))
    rwa [norm_mul, hu, mul_one] at hk

end Root

/-! ## Fields of definition -/

section Maps

variable {K L : Type} [Field K] [Field L]

/-- **The Laurent coefficients of `℘` are polynomial in `g₂`, `g₃`**: field maps carry `wpC` to `wpC`. -/
theorem map_wpC (f : K →+* L) (a b : K) (k : ℕ) : f (wpC a b k) = wpC (f a) (f b) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [wpC]
    | 1 => simp [wpC]
    | 2 => simp [wpC, map_div₀, map_ofNat]
    | 3 => simp [wpC, map_div₀, map_ofNat]
    | k + 4 =>
      rw [wpC, wpC, map_mul, map_div₀, map_sum]
      congr 1
      · simp [map_ofNat]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, ih _ (by omega), ih _ (by omega)]

/-- **`log_LT(T)/T` is defined over `ℚ`.** -/
theorem map_logLTDivX (f : K →+* L) (ℓ : ℕ) : map f (logLTDivX K ℓ) = logLTDivX L ℓ := by
  ext n
  rw [coeff_map, logLTDivX, logLTDivX, coeff_mk, coeff_mk, ← coeff_map, map_logLT]

variable [CharZero K] [CharZero L]

/-- **`logSig` is carried to `logSig`** by field maps. -/
theorem map_logSig (f : K →+* L) (a b s : K) : map f (logSig a b s) = logSig (f a) (f b) (f s) := by
  ext n
  simp only [logSig, coeff_map, coeff_mk]
  split_ifs <;> simp [map_div₀, map_wpC, map_ofNat]

/-- **The Gaussian exponent is carried to the Gaussian exponent**: `ph` is defined over any field containing
`g₂, g₃, s₂, ε`. -/
theorem map_ph (f : K →+* L) {ℓ : ℕ} (hℓ : 1 < ℓ) (a b s ε : K) :
    map f (ph ℓ a b s ε) = ph ℓ (f a) (f b) (f s) (f ε) := by
  have hu : constantCoeff (logLTDivX K ℓ - 1) = 0 := by
    rw [map_sub, constantCoeff_logLTDivX, map_one, sub_self]
  have h1 : map f (logOf (logLTDivX K ℓ)) = logOf (logLTDivX L ℓ) := by
    have h : map f ((PowerSeries.log K).subst (logLTDivX K ℓ - 1)) =
        (map f (PowerSeries.log K)).subst (map f (logLTDivX K ℓ - 1)) :=
      map_subst (HasSubst.of_constantCoeff_zero' hu) _
    rw [logOf_eq, h, map_log, map_sub, map_one, map_logLTDivX, logOf_eq]
  have h2 : map f ((logSig a b s).subst (C ε * logLT K ℓ)) = (logSig (f a) (f b) (f s)).subst
      (C (f ε) * logLT L ℓ) := by
    have h : map f ((logSig a b s).subst (C ε * logLT K ℓ)) =
        (map f (logSig a b s)).subst (map f (C ε * logLT K ℓ)) :=
      map_subst (HasSubst.of_constantCoeff_zero' (constantCoeff_C_mul_logLT hℓ ε)) _
    rw [h, map_logSig, map_mul, map_C, map_logLT]
  rw [ph, ph, map_neg, map_add, h1, h2]

/-- **The Gaussian pairing is carried to the Gaussian pairing**: `be` is defined over any field containing
`g₂, g₃, s₂, ε`. -/
theorem map_be (f : K →+* L) {ℓ : ℕ} (hℓ : 1 < ℓ) (a b s ε : K) :
    MvPowerSeries.map f (be ℓ a b s ε) = be ℓ (f a) (f b) (f s) (f ε) := by
  have hX : ∀ i : Fin 2, HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := fun i => HasSubst.X i
  have hA : HasSubst (ltAdd K ℓ) := HasSubst.of_constantCoeff_zero (constantCoeff_ltAdd hℓ)
  rw [be, be, map_sub, map_sub, PowerSeries.map_subst hA, PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1)]
  change (map f (ph ℓ a b s ε)).subst _ - (map f (ph ℓ a b s ε)).subst _ - (map f (ph ℓ a b s ε)).subst _ = _
  rw [map_ph f hℓ, map_ltAdd f hℓ, MvPowerSeries.map_X, MvPowerSeries.map_X]

end Maps

end

end CMFormalInert
