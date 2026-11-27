import EllipticSigma
import EllipticDivisor

/-!
# The formal Gaussian at an inert prime: biadditivity of `be`, the translates, and `c·serAB`

D1a′ of the D1 plan, concluded as far as it goes: the Gaussian pairing `be(X, Y) = ph(X ⊕ Y) − ph(X) − ph(Y)` of
`CMFormalGroup` is biadditive up to `≃`, the translates `εT·G_q(z(T))` are integral units, and the explicit Gaussian
`c·serAB` is biadditive; the uniqueness half of the classification `be ≃ c·serAB` is stated here (`GaussClass`) and
proved for closed `k` in `CMFormalGauss`.

**From the analytic to the formal.** `tay f = Σ ∂ⁿf(0)/n!·zⁿ` (`tay`) is additive, multiplicative and compatible
with dilations on functions analytic at `0` (`tay_mul`, `tay_comp_mul`), and `tay(σ*/z) = exp(logSig)` (`tay_sigE`,
from `EllipticSigma.sigE_taylor`), `tay(z²℘) = P` (`wpF`), `tay(z³℘′) = −2R` (`wpR`). On every line `w = λz`,
`‖λ‖ ≤ 1`, the addition law `σ(z + w)σ(z − w) = σ(z)²σ(w)²(℘(w) − ℘(z))` (`EllipticAdd.sigmaW_add_mul_sub`) becomes
`(z² − w²)E(z + w)E(z − w) = E(z)²E(w)²(z²P(w) − w²P(z))`; a two-variable series vanishing on infinitely many lines
vanishes (`eq_zero_of_subst_lineSub`), so this formal addition law (`AddLaw`) holds for the lattice's `g₂, g₃, s₂`
(`addLaw_lattice`), as does `4R² = 4P³ − g₂z⁴P − g₃z⁶` (`WeierODE`, from `℘′² = 4℘³ − g₂℘ − g₃`), and both are
carried along field maps (`addLaw_weierODE_map`), e.g. to `ℂ_ℓ` by `ι`.

**`℘` in Lubin–Tate coordinates.** With `z(T) = ε·log_LT(T)` and `ρ(T) = ε²T²℘(z(T))` (`rhoLT`), `t = zP/R` and the
differential equation give `A₁²(4ρ³ − g₂T⁴ρ − g₃T⁶) = 4ρ²` for `t(z(T)) = T·A₁(T)` (`rhoLT_rel`), so `w = ρ⁻¹`
satisfies a fixed-point equation with integral data and `ρ` is integral when CM-b makes `t(z(T))` integral
(`isInt_rhoLT`); `ρ` is even (`rescale_neg_rhoLT`).

**The parallelogram law** (`parallelogram`): `ph(X ⊕ Y) + ph(X ⊖ Y) ≃ 2ph(X) + 2ph(Y)`. With `S_A = exp(−ph(A))`
and `ε·A·S_A = z_A·E(z_A)` (`C_mul_mul_expMv_neg_ph`), the addition law at `(z_X, z_Y)` and `T²P(z) = z²ρ` give
`exp(2ph(X) + 2ph(Y) − ph(X ⊕ Y) − ph(X ⊖ Y)) = ε²·Δ·U₁U₂`, integral: `X²ρ(Y) − Y²ρ(X) = (X² − Y²)Δ` with `Δ` built
from a divided difference (`sq_mul_sub_sq_mul`, `divDiff`), and `X ± Y = (X ⊕± Y)·U` with `U` integral, from
`X ⊕ Y = Y + X·G` (`exists_units_ltAdd_ltSub`). Points of the group are handled through their logarithms
(`lgP`, `eq_of_lgP_eq`).

**Biadditivity** (`be_biadd`, `be_biadd_cm`). Five instances of the parallelogram law give
`B(u ⊕ v, y) + B(u ⊖ v, y) ≃ 2B(u, y)` (`bP_star`); at `u = 0` the pairing is odd (`bP_odd`), and then additive
(`bP_add`). No `[½]` is needed: `≃` is halved by a square root (`simeq_zero_of_two_mul`, `ℓ ≠ 2`). `be` is symmetric
(`be_symm`).

**The translates** (`isInt_translate`, `th0_eq_exp_neg_ph_mul`). For a torsion point `q` with
`G_qᴺ = P(℘) + ℘′Q(℘)` (`EllipticDivisor.Gq_pow_eq_poly`), `ℓ ∤ N`, the `N`-th power of `U(T) = εT·G_q(z(T))` is
`εᴺ(Σ p_iT^{N−2i}ρ^i − 2Σ q_iT^{N−2i−3}ρ^{i+1}A₁⁻¹)`, integral when the coefficients of `P`, `Q` are; `U(0) = 1`, and
`U` is an `N`-th root (`isIntK_of_pow_eq`), without Dwork. `th0 = σ*·G_t` gives `th0 = exp(−ph)·U_t` in Lubin–Tate
coordinates.

**The explicit Gaussian is biadditive** (`serAB_biadd`): for `φ(c) = −c`, `‖c‖ ≤ 1`, the Dwork defect of
`c·Δ`, `Δ = serAB(X ⊕ X′, Y) − serAB(X, Y) − serAB(X′, Y)`, is `−c·(Δ(X^ℓ, X′^ℓ, Y^ℓ) + ℓΔ)`, and
`Δ(X^ℓ, X′^ℓ, Y^ℓ) + ℓΔ = M(X^ℓ ⊕ X′^ℓ, Y) − M((X ⊕ X′)^ℓ, Y)` with `M = serAB(U, V^ℓ) − log_LT(U)log_LT(V)`
(`subst_serAB_frob`, `isDivK_expand_serDef`). The terms with `i ≤ j` of `serAB(U, V^ℓ)` cancel against
`log_LT(U)log_LT(V)` exactly where the coefficient would be too large, so `M` is of divided-power type in `U`
(`mSer_typeM`), and `U^ℓ ⊕ V^ℓ ≡ (U ⊕ V)^ℓ (mod ℓ)` (`isDivK_addP_pow_sub`) makes the difference `ℓ`-divisible
(`isDivK_subst_sub`).

**The classification** (`GaussClass`, `be_classification`, `be_classification_cm`). The uniqueness half is the
statement `GaussClass`: a symmetric, hermitian (`IsHerm`), biadditive series over a subfield with a Frobenius lift
is `≃ c·serAB`. From it and the hermitian property of `be` (the CM sesquilinearity, an arithmetic input), `be` is
symmetric and biadditive with coefficients in `K^ur`, so `be ≃ c·serAB` with `φ(c) = −c`, `‖c‖ ≤ 1`.

**Inputs** (hypotheses): CM-b `CMInertLubinTate`, CM-c `CMThetaOne.CMjIntegral`, CM-a′ `CMUnramified`, the
strengthened CM-d `CMs2Unram` (`ι(s₂) ∈ K^ur`, integral, at `ℓ ∤ d`); for the translates, the integrality of the
coefficients of `P`, `Q` in `G_qᴺ = P(℘) + ℘′Q(℘)` and the degree bounds `2 deg P ≤ N`, `2 deg Q + 3 ≤ N`; for the
classification, `GaussClass` and the hermitian property of `be`. Frobenius lifts are parameters.

**Main results:** `addLaw_lattice`, `weierODE_lattice`, `addLaw_weierODE_map`, `isInt_rhoLT`, `parallelogram`,
`be_symm`, `be_biadd`, `be_biadd_cm`, `isInt_translate`, `th0_eq_exp_neg_ph_mul`, `serAB_biadd`,
`isHerm_C_mul_serAB`, `be_classification`, `be_classification_cm`; the definitions `tay`, `wpF`, `wpR`, `expSig`,
`AddLaw`, `WeierODE`, `rhoLT`, `lgP`, `addP`, `ltSub`, `bP`, `IsHerm`, `GaussClass`, `CMUnramified`, `CMs2Unram`.
-/

namespace CMFormalBiadd

open PowerSeries CMFormalInert

noncomputable section

/-! ## Taylor series at `0` -/

section Taylor

open Filter Topology

/-- **The Taylor series at `0`** of a function `ℂ → ℂ`: `Σ_n ∂ⁿf(0)/n!·zⁿ`. -/
def tay (f : ℂ → ℂ) : ℂ⟦X⟧ := mk fun n => iteratedDeriv n f 0 / n.factorial

/-- **The coefficients of `tay`**, by definition. -/
theorem coeff_tay (f : ℂ → ℂ) (n : ℕ) : coeff n (tay f) = iteratedDeriv n f 0 / n.factorial := coeff_mk _ _

/-- **`tay` only sees a neighbourhood of `0`.** -/
theorem tay_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) : tay f = tay g := by
  ext n
  rw [coeff_tay, coeff_tay, h.iteratedDeriv_eq]

/-- **`tay` is multiplicative** on functions analytic at `0` (Leibniz). -/
theorem tay_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z * g z) = tay f * tay g := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  rw [coeff_tay, coeff_tay, ← Nat.choose_mul_factorial_mul_factorial hi]
  push_cast
  field_simp

/-- **`tay` is additive.** -/
theorem tay_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z + g z) = tay f + tay g := by
  ext n
  rw [map_add, coeff_tay, coeff_tay, coeff_tay, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

/-- **`tay` commutes with differences.** -/
theorem tay_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z - g z) = tay f - tay g := by
  ext n
  rw [map_sub, coeff_tay, coeff_tay, coeff_tay, iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_div]

/-- **`tay` of a constant.** -/
theorem tay_const (c : ℂ) : tay (fun _ => c) = C c := by
  ext n
  rw [coeff_tay, iteratedDeriv_const, coeff_C]
  split_ifs <;> simp_all

/-- **`tay` of the identity.** -/
theorem tay_id : tay (fun z => z) = X := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_id_zero, coeff_X]
  split_ifs <;> simp_all

/-- **`tay` of powers.** -/
theorem tay_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) : tay (fun z => f z ^ n) = tay f ^ n := by
  induction n with
  | zero => simpa using tay_const 1
  | succ n ih =>
    simp only [pow_succ]
    rw [tay_mul (f := fun z => f z ^ n) (hf.pow n) hf, ih]

/-- **`tay` of a dilation**: `tay(f(c·)) = tay(f)(cz)`, for `f` analytic on an open set mapped into itself by `c·`. -/
theorem tay_comp_mul {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (h0 : (0 : ℂ) ∈ s) (hf : AnalyticOnNhd ℂ f s) (c : ℂ)
    (hc : Set.MapsTo (fun x => c * x) s s) : tay (fun z => f (c * z)) = rescale c (tay f) := by
  ext n
  have h := iteratedDerivWithin_comp_const_smul (n := n) h0 hs.uniqueDiffOn (hf.contDiffOn hs.uniqueDiffOn) c hc
  rw [mul_zero, iteratedDerivWithin_of_isOpen hs h0, iteratedDerivWithin_of_isOpen hs h0, smul_eq_mul] at h
  rw [coeff_tay, coeff_rescale, coeff_tay, h, mul_div_assoc]

end Taylor

/-! ## The formal `℘` and the formal addition law of `σ*` -/

section Formal

variable {K : Type} [Field K]

/-- **`z²℘(z)`, formally**: `1 + Σ_{k≥1} wpC(k)·z^{2k}` (`wpC(1) = 0`). -/
def wpF (a b : K) : K⟦X⟧ := mk fun n => if n = 0 then 1 else if Even n then wpC a b (n / 2) else 0

/-- **`−z³℘′(z)/2`, formally**: `1 − Σ_{k≥1}(k − 1)·wpC(k)·z^{2k}`. -/
def wpR (a b : K) : K⟦X⟧ :=
  mk fun n => if n = 0 then 1 else if Even n then -(((n / 2 : ℕ) : K) - 1) * wpC a b (n / 2) else 0

/-- **The formal parameter** `t = −2℘/℘′ = z·P/R`. -/
theorem tSer_eq (a b : K) : tSer a b = X * wpF a b * (wpR a b)⁻¹ := rfl

/-- **The formal differential equation of `℘`**: `℘′² = 4℘³ − g₂℘ − g₃`, i.e. `4R² = 4P³ − g₂z⁴P − g₃z⁶`. -/
def WeierODE (a b : K) : Prop := 4 * wpR a b ^ 2 = 4 * wpF a b ^ 3 - C a * X ^ 4 * wpF a b - C b * X ^ 6

variable [CharZero K]

/-- **`σ*(z)/z`, formally**: `exp(logSig(z))`. -/
def expSig (a b s : K) : K⟦X⟧ := (exp K).subst (logSig a b s)

/-- **The formal addition law of `σ*`**: `σ*(z + w)σ*(z − w) = σ*(z)²σ*(w)²(℘(w) − ℘(z))`, multiplied out:
`(z² − w²)·E(z + w)E(z − w) = E(z)²E(w)²·(z²P(w) − w²P(z))` with `E = σ*/z` (`expSig`) and `P = z²℘` (`wpF`). -/
def AddLaw (a b s : K) : Prop :=
  ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 - MvPowerSeries.X 1 ^ 2) *
      (expSig a b s).subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) *
      (expSig a b s).subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
    (expSig a b s).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 *
      (expSig a b s).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2 *
      (MvPowerSeries.X 0 ^ 2 * (wpF a b).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
        MvPowerSeries.X 1 ^ 2 * (wpF a b).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))

end Formal

/-! ## Substitution in substitutions -/

section SubstSubst

variable {R : Type} [CommRing R] {σ τ : Type}

/-- **Substituting into a substitution**: `(G ∘ a) ∘ ψ = G ∘ (a ∘ ψ)`. -/
theorem subst_subst (G : R⟦X⟧) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {ψ : σ → MvPowerSeries τ R} (hψ : MvPowerSeries.HasSubst ψ) :
    MvPowerSeries.subst ψ (G.subst a) = G.subst (MvPowerSeries.subst ψ a) := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero ha).const hψ]

end SubstSubst

/-! ## Restriction to lines `w = λz` -/

section Line

/-- **The line `w = λz`** as a substitution `(z, w) ↦ (X, λX)`. -/
def lineSub {K : Type} [Field K] (c : K) : Fin 2 → K⟦X⟧ := ![X, C c * X]

/-- **The line substitution is admissible.** -/
theorem hasSubst_lineSub {K : Type} [Field K] (c : K) : MvPowerSeries.HasSubst (lineSub c) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i
    · exact constantCoeff_X
    · change constantCoeff (C c * X) = 0
      simp

open Classical in
/-- **The coefficients on a line**: `[zⁿ]F(z, λz) = Σ_{j ≤ n} F_{n−j, j}·λ^j`. -/
theorem coeff_subst_lineSub {K : Type} [Field K] (F : MvPowerSeries (Fin 2) K) (c : K) (n : ℕ) :
    coeff n (MvPowerSeries.subst (lineSub c) F) = ∑ j ∈ Finset.range (n + 1),
      MvPowerSeries.coeff (Finsupp.single 0 (n - j) + Finsupp.single 1 j) F * c ^ j := by
  have hpow : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => lineSub c s ^ e) = C (c ^ d 1) * X ^ (d 0 + d 1) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [lineSub, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_pow, ← map_pow, pow_add]
    ring
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst (hasSubst_lineSub c)]
  set s := (Finset.range (n + 1)).image fun j => Finsupp.single (0 : Fin 2) (n - j) + Finsupp.single 1 j
  have hsupp : (Function.support fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F •
      MvPowerSeries.coeff (Finsupp.single () n) (d.prod fun s e => lineSub c s ^ e)) ⊆ s := by
    intro d hd
    rw [Function.mem_support, hpow, ← PowerSeries.coeff, coeff_C_mul_X_pow] at hd
    split_ifs at hd with h
    · simp only [s, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      refine ⟨d 1, by omega, ?_⟩
      ext i
      fin_cases i
      · simp; omega
      · simp
    · simp at hd
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [hpow, ← PowerSeries.coeff, coeff_C_mul_X_pow, smul_eq_mul]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.single_apply]
    rw [ite_eq_left (by simp; omega)]
    simp
  · intro i hi j hj hij
    have := congrArg (fun d : Fin 2 →₀ ℕ => d 1) hij
    simpa using this

/-- **A two-variable series vanishing on infinitely many lines vanishes**: if `F(z, λz) = 0` for all `λ` in an
infinite set, then `F = 0` (the coefficient of `zⁿ` is a polynomial in `λ` with infinitely many roots). -/
theorem eq_zero_of_subst_lineSub {K : Type} [Field K] {F : MvPowerSeries (Fin 2) K} {S : Set K} (hS : S.Infinite)
    (hF : ∀ c ∈ S, MvPowerSeries.subst (lineSub c) F = 0) : F = 0 := by
  ext e
  rw [MvPowerSeries.coeff_zero]
  set n := e 0 + e 1
  set p : Polynomial K := ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (MvPowerSeries.coeff (Finsupp.single 0 (n - j) + Finsupp.single 1 j) F) * Polynomial.X ^ j
  have hp : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p (hS.mono fun c hc => ?_)
    have := congrArg (coeff n) (hF c hc)
    rw [coeff_subst_lineSub, map_zero] at this
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact this
  have h := congrArg (Polynomial.coeff · (e 1)) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h
  rw [Finset.sum_eq_single (e 1)] at h
  · have he : Finsupp.single 0 (n - e 1) + Finsupp.single 1 (e 1) = e := by
      ext i
      fin_cases i <;> simp [n]
    rwa [ite_eq_left rfl, he] at h
  · intro j _ hj
    exact ite_eq_right (Ne.symm hj)
  · intro h'
    exact absurd (Finset.mem_range.2 (by omega)) h'

end Line

/-! ## The lattice: the formal identities from the analytic ones -/

section Lattice

open EllipticAdd EllipticSigma EllipticDivisor ThetaNorm Filter Topology

variable (Λ : PeriodPair)

/-- **A ball around `0` meets the lattice only in `0`.** -/
theorem exists_ball_sdiff : ∃ r > 0, Metric.ball (0 : ℂ) r ⊆ (Λ.lattice \ {0} : Set ℂ)ᶜ :=
  Metric.isOpen_iff.1 Λ.isOpen_compl_lattice_sdiff 0 (by simp)

/-- **The Taylor series of `σ*/z` is `exp(logSig)`** (`EllipticSigma.sigE_taylor`). -/
theorem tay_sigE : tay (sigE Λ) = expSig Λ.g₂ Λ.g₃ (s2 Λ) := by
  ext n
  have h : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [coeff_tay, sigE_taylor, expSig, mul_div_cancel_left₀ _ h]

/-- **`wpU = z²℘` is analytic near `0`.** -/
theorem analyticOnNhd_wpU : AnalyticOnNhd ℂ (wpU Λ) (Λ.lattice \ {0} : Set ℂ)ᶜ := fun z hz => by
  have := Λ.analyticOnNhd_weierstrassPExcept 0 z hz
  unfold wpU
  fun_prop

/-- **The Taylor series of `z²℘` is `wpF`** (`℘ = z⁻² + Σ lc(n)zⁿ`, `wpC(k) = lc(2k − 2)`). -/
theorem tay_wpU : tay (wpU Λ) = wpF Λ.g₂ Λ.g₃ := by
  have e : wpU Λ = fun z => 1 + z ^ 2 * Λ.weierstrassPExcept 0 z := rfl
  rw [e, tay_add, tay_mul, tay_pow, tay_const, tay_id]
  rotate_left
  all_goals try fun_prop
  ext n
  rw [map_add, coeff_C, coeff_X_pow_mul', wpF, coeff_mk, coeff_tay]
  rcases n with _ | _ | n
  · simp
  · simp
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega),
      show n + 1 + 1 - 2 = n by omega, ← lc, zero_add]
    split_ifs with h
    · obtain ⟨k, hk⟩ := h
      rw [wpC_eq_lc, show 2 * ((n + 1 + 1) / 2) - 2 = n by omega]
    · have hn : Odd n := by
        rw [Nat.not_even_iff_odd] at h
        obtain ⟨k, hk⟩ := h
        exact ⟨k - 1, by omega⟩
      rw [lc_odd Λ hn]

/-- **`z³℘′` is analytic near `0`.** -/
theorem analyticAt_wpV : AnalyticAt ℂ (wpV Λ) 0 := by
  have := Λ.analyticAt_derivWeierstrassPExcept 0
  unfold wpV
  fun_prop

/-- **The Taylor series of `z³℘′` is `−2·wpR`.** -/
theorem tay_wpV : tay (wpV Λ) = -2 * wpR Λ.g₂ Λ.g₃ := by
  have hE := Λ.analyticAt_derivWeierstrassPExcept 0
  have e : wpV Λ = fun z => -2 + z ^ 3 * Λ.derivWeierstrassPExcept 0 z := rfl
  have hd : ∀ k, coeff k (tay (Λ.derivWeierstrassPExcept 0)) = (k + 1) * lc Λ (k + 1) := fun k => by
    have hev : deriv (Λ.weierstrassPExcept 0) =ᶠ[𝓝 0] Λ.derivWeierstrassPExcept 0 :=
      Filter.eventuallyEq_of_mem (Λ.isOpen_compl_lattice_sdiff.mem_nhds (by simp))
        (Λ.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0)
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    rw [coeff_tay, ← hev.iteratedDeriv_eq, ← iteratedDeriv_succ', lc, Nat.factorial_succ]
    push_cast
    field_simp
  rw [e, tay_add, tay_mul, tay_pow, tay_const, tay_id]
  rotate_left
  all_goals try fun_prop
  ext n
  rw [map_add, coeff_C, coeff_X_pow_mul', wpR, show (-2 : ℂ⟦X⟧) = C (-2) from by rw [map_neg, map_ofNat],
    coeff_C_mul, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp [wpC]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega),
      show n + 1 + 1 + 1 - 3 = n by omega, hd, zero_add]
    split_ifs with h
    · obtain ⟨k, hk⟩ := h
      obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨k - 2, by omega⟩
      rw [show (2 * m + 1 + 1 + 1 + 1) / 2 = m + 2 by omega, wpC_eq_lc,
        show 2 * (m + 2) - 2 = 2 * m + 1 + 1 by omega]
      push_cast
      ring
    · have hn : Odd (n + 1) := by
        rw [Nat.not_even_iff_odd] at h
        obtain ⟨k, hk⟩ := h
        exact ⟨k - 1, by omega⟩
      rw [lc_odd Λ hn, mul_zero, mul_zero]

/-- **The formal differential equation for the lattice** (from Mathlib's `℘′² = 4℘³ − g₂℘ − g₃`). -/
theorem weierODE_lattice : WeierODE Λ.g₂ Λ.g₃ := by
  obtain ⟨r, hr, hball⟩ := exists_ball_sdiff Λ
  have hU := analyticOnNhd_wpU Λ 0 (by simp)
  have hV := analyticAt_wpV Λ
  have hz : ∀ z ∈ Metric.ball (0 : ℂ) r, wpV Λ z ^ 2 - 4 * wpU Λ z ^ 3 + Λ.g₂ * z ^ 4 * wpU Λ z +
      Λ.g₃ * z ^ 6 = 0 := by
    intro z hzr
    by_cases h0 : z = 0
    · subst h0
      simp [wpU, wpV]
      norm_num
    · have hzl : z ∉ Λ.lattice := fun h => hball hzr ⟨h, h0⟩
      rw [← sq_mul_weierstrassP Λ h0, ← cube_mul_derivWeierstrassP Λ h0]
      linear_combination z ^ 6 * Λ.derivWeierstrassP_sq z hzl
  have hev : (fun z => wpV Λ z ^ 2 - 4 * wpU Λ z ^ 3 + Λ.g₂ * z ^ 4 * wpU Λ z + Λ.g₃ * z ^ 6) =ᶠ[𝓝 0]
      fun _ => (0 : ℂ) := Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hr) hz
  have h := tay_congr hev
  rw [tay_const, map_zero, tay_add, tay_add, tay_sub, tay_pow, tay_mul, tay_pow, tay_mul, tay_mul, tay_pow,
    tay_mul, tay_pow, tay_const, tay_const, tay_const, tay_id, tay_wpU, tay_wpV] at h
  rotate_left
  all_goals try fun_prop
  rw [map_ofNat] at h
  unfold WeierODE
  linear_combination h

/-- **`σ*/z` is entire.** -/
theorem analyticAt_sigE (x : ℂ) : AnalyticAt ℂ (sigE Λ) x :=
  (differentiable_sigE Λ).differentiableOn.analyticOnNhd isOpen_univ x (Set.mem_univ x)

/-- **The addition law of `σ*` on a line `w = λz`**, for `z` in a ball meeting the lattice only in `0` and
`‖λ‖ ≤ 1`: `(z² − w²)·E(z + w)E(z − w) = E(z)²E(w)²·(z²·w²℘(w) − w²·z²℘(z))` (`EllipticAdd.sigmaW_add_mul_sub`, with
`σ = z·E·e^{s₂z²/2}`; the Gaussian factors cancel). -/
theorem sigE_add_line {r : ℝ} (hball : Metric.ball (0 : ℂ) r ⊆ (Λ.lattice \ {0} : Set ℂ)ᶜ) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) :
    (z ^ 2 - (c * z) ^ 2) * sigE Λ ((1 + c) * z) * sigE Λ ((1 - c) * z) =
      sigE Λ z ^ 2 * sigE Λ (c * z) ^ 2 * (z ^ 2 * wpU Λ (c * z) - (c * z) ^ 2 * wpU Λ z) := by
  have hσ0 : sigE Λ 0 = 1 := by simp [sigE, sigP_zero]
  by_cases hz0 : z = 0
  · subst hz0
    simp
  by_cases hc0 : c = 0
  · subst hc0
    simp [hσ0, (analyticAt_wpU Λ).2]
    ring
  set w := c * z with hw
  have hw0 : w ≠ 0 := mul_ne_zero hc0 hz0
  have hwr : w ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [hw, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) hz
  have hzl : z ∉ Λ.lattice := fun h => hball hz ⟨h, hz0⟩
  have hwl : w ∉ Λ.lattice := fun h => hball hwr ⟨h, hw0⟩
  have key := sigmaW_add_mul_sub Λ hzl hwl
  have hP : ∀ u, sigmaW Λ u = u * (sigE Λ u * Complex.exp (s2 Λ * u ^ 2 / 2)) := fun u => by
    rw [sigmaW_eq, sigE, mul_assoc, ← Complex.exp_add,
      show -(s2 Λ) * u ^ 2 / 2 + s2 Λ * u ^ 2 / 2 = 0 by ring, Complex.exp_zero, mul_one]
  rw [hP, hP, hP, hP] at key
  have hE : Complex.exp (s2 Λ * (z + w) ^ 2 / 2) * Complex.exp (s2 Λ * (z - w) ^ 2 / 2) =
      Complex.exp (s2 Λ * z ^ 2 / 2) ^ 2 * Complex.exp (s2 Λ * w ^ 2 / 2) ^ 2 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hne : Complex.exp (s2 Λ * (z + w) ^ 2 / 2) * Complex.exp (s2 Λ * (z - w) ^ 2 / 2) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  rw [← sq_mul_weierstrassP Λ hw0, ← sq_mul_weierstrassP Λ hz0, show (1 + c) * z = z + w by ring,
    show (1 - c) * z = z - w by ring]
  refine mul_right_cancel₀ hne ?_
  linear_combination key - (sigE Λ z ^ 2 * sigE Λ w ^ 2 *
    (z ^ 2 * (w ^ 2 * Λ.weierstrassP w) - w ^ 2 * (z ^ 2 * Λ.weierstrassP z))) * hE

/-- **Substituting the line into a substitution.** -/
theorem subst_lineSub_subst {K : Type} [Field K] (c : K) (G : K⟦X⟧) {a : MvPowerSeries (Fin 2) K}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst (lineSub c) (G.subst a) = G.subst (MvPowerSeries.subst (lineSub c) a) :=
  subst_subst G ha (hasSubst_lineSub c)

/-- **The line substitution on the variables.** -/
theorem subst_lineSub_X {K : Type} [Field K] (c : K) (i : Fin 2) :
    MvPowerSeries.subst (lineSub c) (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = lineSub c i :=
  MvPowerSeries.subst_X (hasSubst_lineSub c) i

/-- **The formal addition law for the lattice** (`AddLaw` for `g₂`, `g₃`, `s₂` of `Λ`): both sides agree on every
line `w = λz`, `‖λ‖ ≤ 1`, by the analytic addition law and `tay`, so they agree (`eq_zero_of_subst_lineSub`). -/
theorem addLaw_lattice : AddLaw Λ.g₂ Λ.g₃ (s2 Λ) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_sdiff Λ
  set E := expSig Λ.g₂ Λ.g₃ (s2 Λ) with hEdef
  set P := wpF Λ.g₂ Λ.g₃ with hPdef
  unfold AddLaw
  rw [← sub_eq_zero]
  set S : Set ℂ := Set.range fun n : ℕ => ((n : ℂ) + 2)⁻¹
  have hS : S.Infinite := Set.infinite_range_of_injective fun m n h => by
    have h' : ((m : ℂ) + 2) = (n : ℂ) + 2 := inv_injective h
    exact_mod_cast add_right_cancel h'
  refine eq_zero_of_subst_lineSub hS fun c hcS => ?_
  obtain ⟨n, hn⟩ := hcS
  have hc : ‖c‖ ≤ 1 := by
    rw [← hn, norm_inv]
    refine inv_le_one_of_one_le₀ ?_
    have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]
    exact_mod_cast (by omega : 1 ≤ n + 2)
  -- the analytic side
  have hσ := analyticAt_sigE Λ
  have hU : AnalyticAt ℂ (wpU Λ) 0 := (analyticAt_wpU Λ).1
  have hmaps : Set.MapsTo (fun x => c * x) (Metric.ball (0 : ℂ) r) (Metric.ball (0 : ℂ) r) := fun x hx => by
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) hx
  have hUc : AnalyticAt ℂ (fun z => wpU Λ (c * z)) 0 := by
    have h := (analyticOnNhd_wpU Λ) (c * 0) (by simp)
    exact h.comp_of_eq (by fun_prop) rfl
  have tE : ∀ c' : ℂ, tay (fun z => sigE Λ (c' * z)) = rescale c' E := fun c' => by
    rw [tay_comp_mul isOpen_univ (Set.mem_univ 0) (fun x _ => hσ x) c' (Set.mapsTo_univ _ _), tay_sigE]
  have tU : tay (fun z => wpU Λ (c * z)) = rescale c P := by
    rw [tay_comp_mul Metric.isOpen_ball (Metric.mem_ball_self hr) ((analyticOnNhd_wpU Λ).mono hball) c hmaps,
      tay_wpU]
  have tz : tay (fun z => c * z) = C c * X := by
    rw [tay_mul, tay_const, tay_id] <;> fun_prop
  have hg : (fun z => (z ^ 2 - (c * z) ^ 2) * sigE Λ ((1 + c) * z) * sigE Λ ((1 - c) * z) -
      sigE Λ z ^ 2 * sigE Λ (c * z) ^ 2 * (z ^ 2 * wpU Λ (c * z) - (c * z) ^ 2 * wpU Λ z)) =ᶠ[𝓝 0]
      fun _ => (0 : ℂ) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hr) fun z hz => by
      rw [sigE_add_line Λ hball hc hz, sub_self]
  have h := tay_congr hg
  rw [tay_const, map_zero, tay_sub, tay_mul, tay_mul, tay_sub, tay_pow, tay_pow, tay_id, tz, tE, tE, tay_mul,
    tay_mul, tay_pow, tay_pow, tay_sub, tay_mul, tay_mul, tay_pow, tay_pow, tay_id, tz, tU, tE, tay_wpU,
    show (tay fun z => sigE Λ z) = E from tay_sigE Λ] at h
  rotate_left
  all_goals try fun_prop
  -- the formal side
  have hX0 : MvPowerSeries.subst (lineSub c) (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ) = X :=
    subst_lineSub_X c 0
  have hX1 : MvPowerSeries.subst (lineSub c) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ) = C c * X :=
    subst_lineSub_X c 1
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hs := hasSubst_lineSub c
  simp only [MvPowerSeries.subst_sub hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_pow hs]
  rw [subst_lineSub_subst c _ (by rw [map_add, h0, h0, add_zero]),
    subst_lineSub_subst c _ (by rw [map_sub, h0, h0, sub_zero]),
    subst_lineSub_subst c _ (h0 0), subst_lineSub_subst c _ (h0 1), subst_lineSub_subst c _ (h0 0),
    subst_lineSub_subst c _ (h0 1), MvPowerSeries.subst_add hs, MvPowerSeries.subst_sub hs, hX0, hX1, X_subst,
    X_subst]
  have e1 : ∀ c' : ℂ, PowerSeries.subst (C c' * X : ℂ⟦X⟧) E = rescale c' E := fun c' => by
    rw [rescale_eq_subst, smul_eq_C_mul]
  have e2 : ∀ c' : ℂ, PowerSeries.subst (C c' * X : ℂ⟦X⟧) P = rescale c' P := fun c' => by
    rw [rescale_eq_subst, smul_eq_C_mul]
  rw [show (X + C c * X : ℂ⟦X⟧) = C (1 + c) * X by rw [map_add, map_one]; ring,
    show (X - C c * X : ℂ⟦X⟧) = C (1 - c) * X by rw [map_sub, map_one]; ring, e1, e1, e1, e2]
  linear_combination h

end Lattice

/-! ## Fields of definition of the formal identities -/

section Maps

variable {K L : Type} [Field K] [Field L] (f : K →+* L)

/-- **`wpF` is carried to `wpF`** by field maps. -/
theorem map_wpF (a b : K) : map f (wpF a b) = wpF (f a) (f b) := by
  ext n
  simp only [coeff_map, wpF, coeff_mk]
  split_ifs <;> simp [map_wpC]

/-- **`wpR` is carried to `wpR`** by field maps. -/
theorem map_wpR (a b : K) : map f (wpR a b) = wpR (f a) (f b) := by
  ext n
  simp only [coeff_map, wpR, coeff_mk]
  split_ifs <;> simp [map_wpC]

/-- **The formal differential equation is carried along field maps.** -/
theorem WeierODE.map {a b : K} (h : WeierODE a b) : WeierODE (f a) (f b) := by
  have h' := congrArg (PowerSeries.map f) h
  simp only [map_mul, map_sub, map_pow, map_ofNat, map_C, map_X, map_wpF, map_wpR] at h'
  exact h'

/-- **Field maps commute with substitution into a series without constant term.** -/
theorem map_subst_two (G : K⟦X⟧) {a : MvPowerSeries (Fin 2) K} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.map f (G.subst a) = (PowerSeries.map f G).subst (MvPowerSeries.map f a) :=
  PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha) G

variable [CharZero K] [CharZero L]

/-- **`expSig` is carried to `expSig`** by field maps. -/
theorem map_expSig (a b s : K) : map f (expSig a b s) = expSig (f a) (f b) (f s) := by
  have h : map f ((exp K).subst (logSig a b s)) = (map f (exp K)).subst (map f (logSig a b s)) :=
    PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' (constantCoeff_logSig a b s)) _
  rw [expSig, h, map_exp, map_logSig, expSig]


/-- **The formal addition law is carried along field maps.** -/
theorem AddLaw.map {a b s : K} (h : AddLaw a b s) : AddLaw (f a) (f b) (f s) := by
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have h' := congrArg (MvPowerSeries.map f) h
  simp only [map_mul, map_sub, map_pow] at h'
  rw [map_subst_two f _ (by rw [map_add, h0, h0, add_zero]), map_subst_two f _ (by rw [map_sub, h0, h0, sub_zero]),
    map_subst_two f _ (h0 0), map_subst_two f _ (h0 1), map_subst_two f _ (h0 0), map_subst_two f _ (h0 1),
    map_add, map_sub, MvPowerSeries.map_X, MvPowerSeries.map_X, map_expSig, map_wpF] at h'
  exact h'

end Maps

/-- **The formal identities hold for the image of every lattice** in a field of characteristic `0` (e.g. under
`ι : ℂ ≃+* ℂ_ℓ`). -/
theorem addLaw_weierODE_map {K : Type} [Field K] [CharZero K] (Λ : PeriodPair) (f : ℂ →+* K) :
    AddLaw (f Λ.g₂) (f Λ.g₃) (f (ThetaNorm.s2 Λ)) ∧ WeierODE (f Λ.g₂) (f Λ.g₃) :=
  ⟨(addLaw_lattice Λ).map f, (weierODE_lattice Λ).map f⟩

/-! ## Integral series: substitution and roots -/

section IntSubst

variable {K : Type} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
/-- **`IsInt` as `IsIntK`** (a one-variable series is a series in the variables `Unit`). -/
theorem _root_.CMFormalInert.IsInt.isIntK {f : K⟦X⟧} (hf : IsInt f) : IsIntK (f : MvPowerSeries Unit K) := fun n => by
  have : n = Finsupp.single () (n ()) := by ext; simp
  rw [this]
  exact hf (n ())

omit [IsUltrametricDist K] in
/-- **`IsIntK` as `IsInt`.** -/
theorem _root_.CMFormalInert.IsIntK.isInt {f : K⟦X⟧} (hf : IsIntK (f : MvPowerSeries Unit K)) : IsInt f :=
  fun _ => hf _

/-- **Integral series are closed under addition.** -/
theorem _root_.CMFormalInert.IsIntK.add {σ : Type} {f g : MvPowerSeries σ K} (hf : IsIntK f) (hg : IsIntK g) :
    IsIntK (f + g) :=
  fun n => by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

omit [IsUltrametricDist K] in
/-- **Integral series are closed under negation.** -/
theorem _root_.CMFormalInert.IsIntK.neg {σ : Type} {f : MvPowerSeries σ K} (hf : IsIntK f) : IsIntK (-f) := fun n => by
  rw [map_neg, norm_neg]
  exact hf n

/-- **Integral series are closed under subtraction.** -/
theorem _root_.CMFormalInert.IsIntK.sub {σ : Type} {f g : MvPowerSeries σ K} (hf : IsIntK f) (hg : IsIntK g) :
    IsIntK (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

omit [IsUltrametricDist K] in
/-- **Integral constants.** -/
theorem isIntK_C {σ : Type} {c : K} (hc : ‖c‖ ≤ 1) : IsIntK (MvPowerSeries.C c : MvPowerSeries σ K) := fun n => by
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · simp

/-- **Integral one-variable series are closed under addition.** -/
theorem _root_.CMFormalInert.IsInt.add {f g : K⟦X⟧} (hf : IsInt f) (hg : IsInt g) : IsInt (f + g) :=
  (hf.isIntK.add hg.isIntK).isInt

/-- **Integral one-variable series are closed under subtraction.** -/
theorem _root_.CMFormalInert.IsInt.sub {f g : K⟦X⟧} (hf : IsInt f) (hg : IsInt g) : IsInt (f - g) :=
  (hf.isIntK.sub hg.isIntK).isInt

/-- **Integral one-variable series are closed under powers.** -/
theorem _root_.CMFormalInert.IsInt.pow {f : K⟦X⟧} (hf : IsInt f) (n : ℕ) : IsInt (f ^ n) :=
  (hf.isIntK.pow n).isInt

/-- **Finite sums of integral one-variable series.** -/
theorem isInt_sum {ι : Type} (s : Finset ι) {f : ι → K⟦X⟧} (hf : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun n => by simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

omit [IsUltrametricDist K] in
/-- **Integral one-variable constants.** -/
theorem isInt_C {c : K} (hc : ‖c‖ ≤ 1) : IsInt (C c) := fun n => by
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

omit [IsUltrametricDist K] in
/-- **`X^k` is integral.** -/
theorem isInt_X_pow (k : ℕ) : IsInt (X ^ k : K⟦X⟧) := fun n => by
  rw [coeff_X_pow]
  split_ifs <;> simp

/-- **A fixed-point equation with integral data has an integral solution**: if
`c₀·w = U·(c₀ − c₁T⁴w² − c₂T⁶w³)` with `U`, `c₁`, `c₂` integral and `‖c₀‖ = 1`, then `w` is integral (in degree
`n` the right side only sees `w` below degree `n`). -/
theorem isInt_of_eq_mul {U w : K⟦X⟧} {c₀ c₁ c₂ : K} (hc₀ : ‖c₀‖ = 1) (hc₁ : ‖c₁‖ ≤ 1) (hc₂ : ‖c₂‖ ≤ 1)
    (hU : IsInt U) (hw : C c₀ * w = U * (C c₀ - C c₁ * X ^ 4 * w ^ 2 - C c₂ * X ^ 6 * w ^ 3)) : IsInt w := by
  suffices H : ∀ n, ∀ m < n, ‖coeff m w‖ ≤ 1 from fun m => H (m + 1) m (Nat.lt_succ_self m)
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hlt | rfl
    · exact ih m hlt
    set w' : K⟦X⟧ := ((trunc m w : Polynomial K) : K⟦X⟧) with hw'
    have hw'i : IsInt w' := fun k => by
      rw [hw', Polynomial.coeff_coe, coeff_trunc]
      split_ifs with h
      · exact ih k h
      · simp
    obtain ⟨q, hq⟩ : X ^ m ∣ w - w' := X_pow_dvd_iff.2 fun k hk => by
      rw [map_sub, hw', Polynomial.coeff_coe, coeff_trunc, ite_eq_left hk, sub_self]
    have hdiff : U * (C c₀ - C c₁ * X ^ 4 * w ^ 2 - C c₂ * X ^ 6 * w ^ 3) =
        U * (C c₀ - C c₁ * X ^ 4 * w' ^ 2 - C c₂ * X ^ 6 * w' ^ 3) +
          X ^ (m + 1) * (-(U * q * (C c₁ * X ^ 3 * (w + w') + C c₂ * X ^ 5 * (w ^ 2 + w * w' + w' ^ 2)))) := by
      linear_combination (-(U * (C c₁ * X ^ 4 * (w + w') + C c₂ * X ^ 6 * (w ^ 2 + w * w' + w' ^ 2)))) * hq
    have hc := congrArg (coeff m) hw
    rw [hdiff, map_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero, coeff_C_mul] at hc
    have hR : IsInt (U * (C c₀ - C c₁ * X ^ 4 * w' ^ 2 - C c₂ * X ^ 6 * w' ^ 3)) :=
      hU.mul ((((isInt_C hc₀.le).sub (((isInt_C hc₁).mul (isInt_X_pow 4)).mul (hw'i.pow 2)))).sub
        (((isInt_C hc₂).mul (isInt_X_pow 6)).mul (hw'i.pow 3)))
    have := hR m
    rwa [← hc, norm_mul, hc₀, one_mul] at this

end IntSubst

/-! ## Divided differences and even series -/

section DivDiff

variable {K : Type} [Field K]

/-- **The divided difference** `(g(X) − g(Y))/(X − Y)`: the coefficient of `X^iY^j` is `g_{i+j+1}`. -/
def divDiff (g : K⟦X⟧) : MvPowerSeries (Fin 2) K := fun e => coeff (e 0 + e 1 + 1) g

/-- **The coefficients of the divided difference.** -/
theorem coeff_divDiff (g : K⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (divDiff g) = coeff (e 0 + e 1 + 1) g := rfl

/-- **The divided difference divides**: `(X − Y)·Δg = g(X) − g(Y)`. -/
theorem X_sub_X_mul_divDiff (g : K⟦X⟧) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) * divDiff g =
      g.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
        g.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  classical
  ext e
  rw [sub_mul, map_sub, map_sub, coeff_subst_single, coeff_subst_single, MvPowerSeries.X, MvPowerSeries.X,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul]
  simp only [coeff_divDiff, one_mul]
  have h0 : Finsupp.single (0 : Fin 2) 1 ≤ e ↔ 1 ≤ e 0 := Finsupp.single_le_iff
  have h1 : Finsupp.single (1 : Fin 2) 1 ≤ e ↔ 1 ≤ e 1 := Finsupp.single_le_iff
  have e0 : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
    constructor
    · intro h; rw [h]; simp
    · intro h; ext i; fin_cases i <;> simp [h]
  have e1 : e = Finsupp.single 1 (e 1) ↔ e 0 = 0 := by
    constructor
    · intro h; rw [h]; simp
    · intro h; ext i; fin_cases i <;> simp [h]
  simp only [h0, h1, e0, e1]
  have s0 : 1 ≤ e 0 → (e - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 + (e - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 1 + 1 =
      e 0 + e 1 := fun h => by
    simp; omega
  have s1 : 1 ≤ e 1 → (e - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 + (e - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 + 1 =
      e 0 + e 1 := fun h => by
    simp; omega
  by_cases ha : 1 ≤ e 0 <;> by_cases hb : 1 ≤ e 1
  · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_right (by omega), ite_eq_right (by omega), s0 ha, s1 hb, sub_self,
      sub_self]
  · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_left (by omega), ite_eq_right (by omega), s0 ha,
      show e 1 = 0 by omega, add_zero]
  · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_right (by omega), ite_eq_left (by omega), s1 hb,
      show e 0 = 0 by omega, zero_add]
  · rw [ite_eq_right ha, ite_eq_right hb, ite_eq_left (by omega), ite_eq_left (by omega), show e 0 = 0 by omega,
      show e 1 = 0 by omega, sub_self, sub_self]

/-- **The odd part of a series has rescaling sign `−1`**: if `g(−T) = g(T)`, the odd coefficients vanish. -/
theorem coeff_eq_zero_of_rescale [CharZero K] {g : K⟦X⟧} (hg : rescale (-1 : K) g = g) {n : ℕ} (hn : Odd n) :
    coeff n g = 0 := by
  have h := congrArg (coeff n) hg
  rw [coeff_rescale, hn.neg_one_pow] at h
  have : (2 : K) * coeff n g = 0 := by linear_combination -h
  simpa using this

/-- **The shifted compression** `τ(u) = Σ_k g_{2k+2}u^k` of an even series. -/
def evenTail (g : K⟦X⟧) : K⟦X⟧ := mk fun k => coeff (2 * k + 2) g

/-- **An even series is `g₀ + T²·τ(T²)`.** -/
theorem eq_C_add_X_sq_mul_evenTail [CharZero K] {g : K⟦X⟧} (hg : rescale (-1 : K) g = g) :
    g = C (coeff 0 g) + X ^ 2 * (evenTail g).subst (X ^ 2 : K⟦X⟧) := by
  ext n
  rw [map_add, coeff_C, coeff_X_pow_mul', coeff_subst_X_pow two_ne_zero]
  rcases n with _ | _ | n
  · simp
  · simp only [one_ne_zero, ↓reduceIte, zero_add]
    rw [coeff_eq_zero_of_rescale hg odd_one]
    simp
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), zero_add, show n + 1 + 1 - 2 = n by omega]
    split_ifs with h
    · obtain ⟨k, hk⟩ := h
      rw [evenTail, coeff_mk, Algebra.algebraMap_self, RingHom.id_apply, show 2 * (n / 2) + 2 = n + 1 + 1 by omega]
    · exact coeff_eq_zero_of_rescale hg (by rw [Nat.odd_iff]; omega)

/-- **The even divided difference**: for even `g`, `X²g(Y) − Y²g(X) = (X² − Y²)·(g₀ − X²Y²·Δτ(X², Y²))`. -/
theorem sq_mul_sub_sq_mul [CharZero K] {g : K⟦X⟧} (hg : rescale (-1 : K) g = g) :
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 * g.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
        MvPowerSeries.X 1 ^ 2 * g.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) =
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * (MvPowerSeries.C (coeff 0 g) -
        MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 *
          MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2, MvPowerSeries.X 1 ^ 2]
            (divDiff (evenTail g))) := by
  set τ := evenTail g
  set ψ : Fin 2 → MvPowerSeries (Fin 2) K := ![MvPowerSeries.X 0 ^ 2, MvPowerSeries.X 1 ^ 2]
  have hψ : MvPowerSeries.HasSubst ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i <;> simp [ψ]
  have hsplit : ∀ i : Fin 2, g.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.C (coeff 0 g) +
        MvPowerSeries.X i ^ 2 * τ.subst ((MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ^ 2) := by
    intro i
    have hXi : HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := HasSubst.X i
    conv_lhs => rw [eq_C_add_X_sq_mul_evenTail hg]
    rw [subst_add hXi, subst_mul hXi, subst_pow hXi, subst_X hXi, subst_C,
      subst_comp_subst_apply (HasSubst.X_pow two_ne_zero) hXi, subst_pow hXi, subst_X hXi]
  have hdd := congrArg (MvPowerSeries.subst ψ) (X_sub_X_mul_divDiff τ)
  rw [MvPowerSeries.subst_mul hψ, MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_sub hψ,
    MvPowerSeries.subst_X hψ, MvPowerSeries.subst_X hψ, subst_subst τ (MvPowerSeries.constantCoeff_X 0) hψ,
    subst_subst τ (MvPowerSeries.constantCoeff_X 1) hψ, MvPowerSeries.subst_X hψ, MvPowerSeries.subst_X hψ] at hdd
  simp only [ψ, Matrix.cons_val_zero, Matrix.cons_val_one] at hdd
  rw [hsplit 0, hsplit 1]
  linear_combination (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 : MvPowerSeries (Fin 2) K) * hdd

end DivDiff

/-! ## The Weierstrass `℘` in Lubin–Tate coordinates -/

section OneVar

variable {K : Type} [Field K]

/-- **The model's parameter in Lubin–Tate coordinates**: `z(T) = ε·log_LT(T)`. -/
def zLT (ℓ : ℕ) (ε : K) : K⟦X⟧ := C ε * logLT K ℓ

/-- **`ε²T²℘(z(T))`**, written as `ε⁻²·(log_LT(T)/T)⁻²·P(z(T))` (`P = z²℘`). -/
def rhoLT (ℓ : ℕ) (a b ε : K) : K⟦X⟧ := C ε⁻¹ ^ 2 * (logLTDivX K ℓ)⁻¹ ^ 2 * (wpF a b).subst (zLT ℓ ε)

/-- **`z(T)` has no constant term.** -/
theorem constantCoeff_zLT {ℓ : ℕ} (hℓ : 1 < ℓ) (ε : K) : constantCoeff (zLT ℓ ε) = 0 :=
  constantCoeff_C_mul_logLT hℓ ε

/-- **`T²·P(z(T)) = z(T)²·ρ(T)`**, i.e. `ρ = ε²T²℘(z(T))`. -/
theorem X_sq_mul_wpF_subst {ℓ : ℕ} (hℓ : 1 < ℓ) {ε : K} (hε : ε ≠ 0) (a b : K) :
    X ^ 2 * (wpF a b).subst (zLT ℓ ε) = zLT ℓ ε ^ 2 * rhoLT ℓ a b ε := by
  have h1 : logLTDivX K ℓ * (logLTDivX K ℓ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_logLTDivX]; exact one_ne_zero)
  have h2 : C ε * C ε⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hε, map_one]
  have hz : zLT ℓ ε = C ε * (X * logLTDivX K ℓ) := by rw [zLT, X_mul_logLTDivX hℓ]
  rw [rhoLT]
  set W := (wpF a b).subst (zLT ℓ ε)
  rw [hz, show (C ε * (X * logLTDivX K ℓ)) ^ 2 * (C ε⁻¹ ^ 2 * (logLTDivX K ℓ)⁻¹ ^ 2 * W) =
    X ^ 2 * W * ((C ε * C ε⁻¹) ^ 2 * (logLTDivX K ℓ * (logLTDivX K ℓ)⁻¹) ^ 2) by ring, h1, h2]
  ring

/-- **The constant term of `P(z(T))` is `1`.** -/
theorem constantCoeff_wpF_subst {ℓ : ℕ} (hℓ : 1 < ℓ) (a b ε : K) :
    constantCoeff ((wpF a b).subst (zLT ℓ ε)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' (HasSubst.of_constantCoeff_zero' (constantCoeff_zLT hℓ ε)),
    finsum_eq_single _ 0]
  · simp [wpF]
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_zLT hℓ, zero_pow hd, smul_zero]

/-- **The constant term of `ρ` is `ε⁻²`.** -/
theorem constantCoeff_rhoLT {ℓ : ℕ} (hℓ : 1 < ℓ) (a b ε : K) : constantCoeff (rhoLT ℓ a b ε) = ε⁻¹ ^ 2 := by
  rw [rhoLT, map_mul, map_mul, map_pow, map_pow, constantCoeff_C, constantCoeff_wpF_subst hℓ,
    PowerSeries.constantCoeff_inv, constantCoeff_logLTDivX]
  simp

/-- **The relation of `ρ` with the formal parameter**: if `t(z(T)) = T·A₁(T)`, then
`A₁²·(4ρ³ − g₂T⁴ρ − g₃T⁶) = 4ρ²` (from `t = zP/R` and `4R² = 4P³ − g₂z⁴P − g₃z⁶`, with `T²P(z) = z²ρ`). -/
theorem rhoLT_rel [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) {a b ε : K} (hε : ε ≠ 0) (hODE : WeierODE a b) {A₁ : K⟦X⟧}
    (hA : (tSer a b).subst (zLT ℓ ε) = X * A₁) :
    A₁ ^ 2 * (4 * rhoLT ℓ a b ε ^ 3 - C a * X ^ 4 * rhoLT ℓ a b ε - C b * X ^ 6) = 4 * rhoLT ℓ a b ε ^ 2 := by
  set z := zLT ℓ ε with hzdef
  have hz0 : constantCoeff z = 0 := constantCoeff_zLT hℓ ε
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  set P := (wpF a b).subst z with hPdef
  set R := (wpR a b).subst z with hRdef
  set ρ := rhoLT ℓ a b ε
  have hR0 : constantCoeff (wpR a b) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, wpR, coeff_mk]
    simp
  -- `t·R = X·P`, substituted
  have htR : tSer a b * wpR a b = X * wpF a b := by
    rw [tSer_eq, mul_assoc, mul_assoc, PowerSeries.inv_mul_cancel _ hR0, mul_one]
  have hAR : X * A₁ * R = z * P := by
    have := congrArg (PowerSeries.subst z) htR
    rwa [subst_mul hzs, subst_mul hzs, subst_X hzs, hA] at this
  -- the differential equation, substituted
  have hODEz : 4 * R ^ 2 = 4 * P ^ 3 - C a * z ^ 4 * P - C b * z ^ 6 := by
    have h4 : (4 : K⟦X⟧) = C 4 := (map_ofNat C 4).symm
    have := congrArg (PowerSeries.subst z) hODE
    rw [h4] at this
    simp only [subst_mul hzs, subst_sub hzs, subst_pow hzs, subst_X hzs] at this
    rw [subst_C, subst_C, subst_C] at this
    rw [h4]
    exact this
  have hXP : X ^ 2 * P = z ^ 2 * ρ := X_sq_mul_wpF_subst hℓ hε a b
  have step1 : (X * A₁) ^ 2 * (4 * P ^ 3 - C a * z ^ 4 * P - C b * z ^ 6) = 4 * z ^ 2 * P ^ 2 := by
    linear_combination -((X * A₁) ^ 2) * hODEz + 4 * (X * A₁ * R + z * P) * hAR
  have hz6 : z ^ 6 * X ^ 2 ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ X_ne_zero)
    intro h
    have := congrArg (coeff 1) h
    rw [hzdef, zLT, coeff_C_mul, coeff_one_logLT, map_zero, mul_one] at this
    exact hε this
  refine mul_left_cancel₀ hz6 ?_
  set u := z ^ 2 * ρ
  set v := X ^ 2 * P
  linear_combination X ^ 6 * step1 - (X ^ 2 * A₁ ^ 2 * (4 * (u ^ 2 + u * v + v ^ 2) - C a * X ^ 4 * z ^ 4) -
    4 * z ^ 2 * X ^ 2 * (u + v)) * hXP

end OneVar

/-! ## Parity -/

section Parity

variable {K : Type} [Field K]

/-- **Rescaling fixes constants.** -/
theorem rescale_C_eq (r c : K) : rescale r (C c) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

/-- **`log_LT` is odd** (its exponents `ℓ^{2j}` are odd). -/
theorem rescale_neg_logLT {ℓ : ℕ} (hℓ : Odd ℓ) : rescale (-1 : K) (logLT K ℓ) = -logLT K ℓ := by
  ext n
  rw [coeff_rescale, map_neg]
  by_cases h : ∃ j : ℕ, n = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := h
    rw [(hℓ.pow : Odd (ℓ ^ (2 * j))).neg_one_pow]
    ring
  · push Not at h
    rw [coeff_logLT_of_ne K h]
    simp

/-- **`log_LT(T)/T` is even.** -/
theorem rescale_neg_logLTDivX {ℓ : ℕ} (hℓ : Odd ℓ) : rescale (-1 : K) (logLTDivX K ℓ) = logLTDivX K ℓ := by
  ext n
  rw [coeff_rescale, logLTDivX, coeff_mk]
  by_cases h : ∃ j : ℕ, n + 1 = ℓ ^ (2 * j)
  · obtain ⟨j, hj⟩ := h
    have : Even n := by
      have ho : Odd (n + 1) := hj ▸ hℓ.pow
      rcases ho with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    rw [this.neg_one_pow, one_mul]
  · push Not at h
    rw [coeff_logLT_of_ne K h]
    simp

/-- **`P = z²℘` is even.** -/
theorem rescale_neg_wpF (a b : K) : rescale (-1 : K) (wpF a b) = wpF a b := by
  ext n
  rw [coeff_rescale, wpF, coeff_mk]
  split_ifs with h0 h1
  · simp [h0]
  · rw [h1.neg_one_pow, one_mul]
  · simp

/-- **A substitution of an odd series into an even one does not see the sign.** -/
theorem subst_neg_of_rescale {G z : K⟦X⟧} (hG : rescale (-1 : K) G = G) (hz : constantCoeff z = 0) :
    G.subst (-z) = G.subst z := by
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' hz
  conv_rhs => rw [← hG]
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp)) hzs,
    subst_smul hzs, subst_X hzs, neg_one_smul]

/-- **`ρ` is even.** -/
theorem rescale_neg_rhoLT {ℓ : ℕ} (hℓ : 1 < ℓ) (hodd : Odd ℓ) (a b ε : K) :
    rescale (-1 : K) (rhoLT ℓ a b ε) = rhoLT ℓ a b ε := by
  have hz0 := constantCoeff_zLT (K := K) hℓ ε
  have hinv : rescale (-1 : K) (logLTDivX K ℓ)⁻¹ = (logLTDivX K ℓ)⁻¹ := by
    have h1 : constantCoeff (logLTDivX K ℓ) ≠ 0 := by rw [constantCoeff_logLTDivX]; exact one_ne_zero
    rw [PowerSeries.eq_inv_iff_mul_eq_one h1]
    nth_rewrite 2 [← rescale_neg_logLTDivX (K := K) hodd]
    rw [← map_mul, PowerSeries.inv_mul_cancel _ h1, map_one]
  have hz : rescale (-1 : K) (zLT ℓ ε) = -zLT ℓ ε := by
    rw [zLT, map_mul, rescale_neg_logLT hodd, mul_neg, rescale_C_eq]
  rw [rhoLT, map_mul, map_mul, map_pow, map_pow, hinv, rescale_subst hz0, hz,
    subst_neg_of_rescale (rescale_neg_wpF a b) hz0, rescale_C_eq]

end Parity

/-! ## `ρ` is integral -/

section RhoInt

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`ρ = ε²T²℘(z(T))` is integral** (CM-b): with `t(z(T)) = T·A₁(T)` integral, `w = ρ⁻¹` satisfies
`4w = A₁²(4 − g₂T⁴w² − g₃T⁶w³)` (`rhoLT_rel`), so `w` is integral (`isInt_of_eq_mul`), with constant term `ε²`. -/
theorem isInt_rhoLT (hℓ2 : ℓ ≠ 2) {a b ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε))) : IsInt (rhoLT ℓ a b ε) := by
  have hℓ := hℓp.out.one_lt
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  set A := (tSer a b).subst (zLT ℓ ε) with hAdef
  have hA0 : constantCoeff A = 0 :=
    constantCoeff_subst_eq_zero (constantCoeff_zLT hℓ ε) _ (constantCoeff_tSer a b)
  set A₁ : ℂ_[ℓ]⟦X⟧ := mk fun n => coeff (n + 1) A
  have hA : A = X * A₁ := by
    ext n
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, hA0, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X,
        zero_mul]
    · rw [coeff_succ_X_mul, coeff_mk]
  have hA₁ : IsInt A₁ := fun n => by rw [coeff_mk]; exact ht (n + 1)
  set ρ := rhoLT ℓ a b ε
  have hρ0 : constantCoeff ρ = ε⁻¹ ^ 2 := constantCoeff_rhoLT hℓ a b ε
  have hρne : constantCoeff ρ ≠ 0 := by rw [hρ0]; exact pow_ne_zero 2 (inv_ne_zero hε0)
  set w := ρ⁻¹
  have hρw : ρ * w = 1 := PowerSeries.mul_inv_cancel ρ hρne
  have hstar := rhoLT_rel hℓ hε0 hODE hA.symm.symm
  have h4 : (4 : ℂ_[ℓ]⟦X⟧) = C 4 := (map_ofNat C 4).symm
  have hw : C 4 * w = A₁ ^ 2 * (C 4 - C a * X ^ 4 * w ^ 2 - C b * X ^ 6 * w ^ 3) := by
    rw [← h4]
    linear_combination (-w ^ 3) * hstar + (A₁ ^ 2 * (4 * (ρ ^ 2 * w ^ 2 + ρ * w + 1) - C a * X ^ 4 * w ^ 2) -
      4 * w * (ρ * w + 1)) * hρw
  have hn4 : ‖(4 : ℂ_[ℓ])‖ = 1 := by
    have := CMThetaOne.norm_natCast_padicComplex (ℓ := ℓ) (n := 4) (by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hℓp.out Nat.prime_two).2 hℓ2))
    exact_mod_cast this
  have hwi : IsInt w := isInt_of_eq_mul hn4 ha hb (hA₁.pow 2) hw
  -- `ρ = ε⁻²·(ε⁻²w)⁻¹`, with `ε⁻²w` integral of constant term `1`
  have hw0 : constantCoeff w = ε ^ 2 := by
    rw [PowerSeries.constantCoeff_inv, hρ0, inv_pow, inv_inv]
  set c := (ε ^ 2)⁻¹
  have hc : ‖c‖ = 1 := by rw [norm_inv, norm_pow, hε, one_pow, inv_one]
  have hv1 : MvPowerSeries.constantCoeff ((C c * w : ℂ_[ℓ]⟦X⟧) : MvPowerSeries Unit ℂ_[ℓ]) = 1 := by
    change constantCoeff (C c * w) = 1
    rw [map_mul, constantCoeff_C, hw0, inv_mul_cancel₀ (pow_ne_zero 2 hε0)]
  have hvi : IsInt (C c * w) := (isInt_C hc.le).mul hwi
  have hV := (hvi.isIntK.inv hv1).isInt
  have hVinv : (C c * w)⁻¹ * (C c * w) = 1 := PowerSeries.inv_mul_cancel _ (by
    change MvPowerSeries.constantCoeff ((C c * w : ℂ_[ℓ]⟦X⟧) : MvPowerSeries Unit ℂ_[ℓ]) ≠ 0
    rw [hv1]; exact one_ne_zero)
  have hρeq : ρ = C c * (C c * w)⁻¹ := by
    linear_combination (-ρ) * hVinv + C c * (C c * w)⁻¹ * hρw
  rw [hρeq]
  exact (isInt_C hc.le).mul hV

end RhoInt

/-! ## Points of the Lubin–Tate group -/

section Points

variable {K : Type} [Field K] {ℓ : ℕ} {σ : Type}

/-- **The logarithm of a point** `A` (a series without constant term): `log_LT(A)`. -/
def lgP (ℓ : ℕ) (A : MvPowerSeries σ K) : MvPowerSeries σ K := (logLT K ℓ).subst A

/-- **The point with logarithm `g`**: `e(g)`. -/
def exP (ℓ : ℕ) (g : MvPowerSeries σ K) : MvPowerSeries σ K := (expLT K ℓ).subst g

/-- **`log_LT(A)` has no constant term.** -/
theorem constantCoeff_lgP (hℓ : 1 < ℓ) {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.constantCoeff (lgP ℓ A) = 0 :=
  constantCoeff_subst_eq_zero hA _ (constantCoeff_logLT K hℓ)

/-- **`e(log_LT(A)) = A`.** -/
theorem exP_lgP (hℓ : 1 < ℓ) {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0) :
    exP ℓ (lgP ℓ A) = A := by
  rw [exP, lgP, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (constantCoeff_logLT K hℓ))
    (HasSubst.of_constantCoeff_zero hA), expLT_subst_logLT K hℓ, subst_X (HasSubst.of_constantCoeff_zero hA)]

/-- **Points are determined by their logarithms.** -/
theorem eq_of_lgP_eq (hℓ : 1 < ℓ) {A B : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (h : lgP ℓ A = lgP ℓ B) : A = B := by
  rw [← exP_lgP hℓ hA, h, exP_lgP hℓ hB]

/-- **Substituting `−A`** is substituting `A` into `G(−T)`. -/
theorem subst_neg_eq {G : K⟦X⟧} {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0) :
    G.subst (-A) = (rescale (-1 : K) G).subst A := by
  have hAs : HasSubst A := HasSubst.of_constantCoeff_zero hA
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp)) hAs, subst_smul hAs,
    subst_X hAs, neg_one_smul]

/-- **`[−1]A = −A`**: `log_LT(−A) = −log_LT(A)` (`log_LT` is odd). -/
theorem lgP_neg (hodd : Odd ℓ) {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0) :
    lgP ℓ (-A) = -lgP ℓ A := by
  have hAs : HasSubst A := HasSubst.of_constantCoeff_zero hA
  rw [lgP, subst_neg_eq hA, rescale_neg_logLT hodd, lgP, ← neg_one_smul K (logLT K ℓ), subst_smul hAs,
    neg_one_smul]

/-- **`log_LT` of a substitution into the group law**: `log_LT(ψ₀ ⊕ ψ₁) = log_LT(ψ₀) + log_LT(ψ₁)`. -/
theorem lgP_subst_ltAdd (hℓ : 1 < ℓ) {ψ : Fin 2 → MvPowerSeries σ K}
    (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) :
    lgP ℓ (MvPowerSeries.subst ψ (ltAdd K ℓ)) = lgP ℓ (ψ 0) + lgP ℓ (ψ 1) := by
  have hψ : MvPowerSeries.HasSubst ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0
  rw [lgP, ← subst_subst _ (constantCoeff_ltAdd hℓ) hψ, logLT_subst_ltAdd hℓ, MvPowerSeries.subst_add hψ,
    subst_subst _ (MvPowerSeries.constantCoeff_X 0) hψ, subst_subst _ (MvPowerSeries.constantCoeff_X 1) hψ,
    MvPowerSeries.subst_X hψ, MvPowerSeries.subst_X hψ, lgP, lgP]

/-- **The difference law** `X ⊖ Y = X ⊕ (−Y)`. -/
def ltSub (K : Type) [Field K] (ℓ : ℕ) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![MvPowerSeries.X 0, -MvPowerSeries.X 1] (ltAdd K ℓ)

/-- **The difference law has no constant term.** -/
theorem constantCoeff_ltSub (hℓ : 1 < ℓ) : MvPowerSeries.constantCoeff (ltSub K ℓ) = 0 := by
  refine MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => ?_)
    (fun i => ?_) (constantCoeff_ltAdd hℓ) <;> fin_cases i <;> simp

/-- **`log_LT(X ⊖ Y) = log_LT(X) − log_LT(Y)`.** -/
theorem lgP_ltSub (hℓ : 1 < ℓ) (hodd : Odd ℓ) :
    lgP ℓ (ltSub K ℓ) = lgP ℓ (MvPowerSeries.X 0) - lgP ℓ (MvPowerSeries.X 1) := by
  rw [ltSub, lgP_subst_ltAdd hℓ (fun i => by fin_cases i <;> simp)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [lgP_neg hodd (MvPowerSeries.constantCoeff_X 1), sub_eq_add_neg]

/-- **`log_LT(X ⊕ Y) = log_LT(X) + log_LT(Y)`.** -/
theorem lgP_ltAdd (hℓ : 1 < ℓ) :
    lgP ℓ (ltAdd K ℓ) = lgP ℓ (MvPowerSeries.X 0) + lgP ℓ (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  rw [lgP, logLT_subst_ltAdd hℓ, lgP, lgP]

open Classical in
/-- **The coefficients of `F(0, Y)`.** -/
theorem coeff_subst_zero_X (F : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst ![0, MvPowerSeries.X 1] F) =
      if e 0 = 0 then MvPowerSeries.coeff (Finsupp.single 1 (e 1)) F else 0 := by
  have hψ : MvPowerSeries.HasSubst (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) s ^ e)
      = (0 : MvPowerSeries (Fin 2) K) ^ d 0 * MvPowerSeries.X 1 ^ d 1 := fun d => by
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    rfl
  rw [MvPowerSeries.coeff_subst hψ, finsum_eq_single _ (Finsupp.single 1 (e 1))]
  · have hd0 : (Finsupp.single (1 : Fin 2) (e 1)) 0 = 0 := by simp
    have hd1 : (Finsupp.single (1 : Fin 2) (e 1)) 1 = e 1 := by simp
    rw [hprod, smul_eq_mul, hd0, hd1, pow_zero, one_mul, MvPowerSeries.coeff_X_pow]
    by_cases h : e 0 = 0
    · have he : e = Finsupp.single 1 (e 1) := by
        ext i
        fin_cases i <;> simp [h]
      rw [ite_eq_left he, ite_eq_left h, mul_one]
    · have he : e ≠ Finsupp.single 1 (e 1) := fun he => h (by rw [he]; simp)
      rw [ite_eq_right he, ite_eq_right h, mul_zero]
  · intro d hd
    rw [hprod, smul_eq_mul]
    rcases Nat.eq_zero_or_pos (d 0) with h0 | h0
    · rw [h0, pow_zero, one_mul, MvPowerSeries.coeff_X_pow, ite_eq_right, mul_zero]
      intro he
      apply hd
      ext i
      fin_cases i
      · simp [h0]
      · have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) he
        simp at this
        simp [this]
    · rw [zero_pow h0.ne', zero_mul, map_zero, mul_zero]

end Points

/-! ## The quotient `(X ⊕ Y − Y)/X` and the units `(X ± Y)/(X ⊕± Y)` -/

section GroupUnits

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

omit hℓp in
/-- **`log_LT(0) = 0`.** -/
theorem lgP_zero {K : Type} [Field K] {σ : Type} (hℓ : 1 < ℓ) : lgP ℓ (0 : MvPowerSeries σ K) = 0 := by
  rw [lgP, PowerSeries.subst_zero_eq_C_constantCoeff, constantCoeff_logLT K hℓ, map_zero, map_zero]

omit hℓp in
/-- **`0 ⊕ Y = Y`.** -/
theorem subst_zero_ltAdd {K : Type} [Field K] (hℓ : 1 < ℓ) :
    MvPowerSeries.subst ![0, MvPowerSeries.X 1] (ltAdd K ℓ) = (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  have h0 : ∀ i, MvPowerSeries.constantCoeff
      ((![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) i) = 0 := fun i => by fin_cases i <;> simp
  refine eq_of_lgP_eq hℓ (MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 (constantCoeff_ltAdd hℓ)) (MvPowerSeries.constantCoeff_X 1) ?_
  rw [lgP_subst_ltAdd hℓ h0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [lgP_zero hℓ, zero_add]

/-- **The quotient `(X ⊕ Y − Y)/X` is integral**: `X ⊕ Y = Y + X·G` with `G` integral. -/
theorem exists_ltAdd_eq :
    ∃ G : MvPowerSeries (Fin 2) ℂ_[ℓ], IsIntK G ∧ ltAdd ℂ_[ℓ] ℓ = MvPowerSeries.X 1 + MvPowerSeries.X 0 * G := by
  classical
  have hℓ := hℓp.out.one_lt
  have hdvd : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) ∣ ltAdd ℂ_[ℓ] ℓ - MvPowerSeries.X 1 := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    have h := congrArg (MvPowerSeries.coeff m) (subst_zero_ltAdd (K := ℂ_[ℓ]) hℓ)
    rw [coeff_subst_zero_X, ite_eq_left hm] at h
    have hm' : Finsupp.single 1 (m 1) = m := by
      ext i
      fin_cases i <;> simp [hm]
    rw [hm'] at h
    rw [map_sub, h, sub_self]
  obtain ⟨G, hG⟩ := hdvd
  refine ⟨G, fun e => ?_, by rw [← hG]; ring⟩
  have h := congrArg (MvPowerSeries.coeff (e + Finsupp.single 0 1)) hG
  rw [show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) = MvPowerSeries.monomial (Finsupp.single 0 1) 1
    from rfl, MvPowerSeries.coeff_monomial_mul, ite_eq_left le_add_self, add_tsub_cancel_right, one_mul] at h
  rw [← h]
  exact (isIntK_ltAdd.sub (isIntK_X 1)) _

/-- **`X + Y = (X ⊕ Y)·U₁` and `X − Y = (X ⊖ Y)·U₂` with `U₁`, `U₂` integral**: substitute
`(X ⊕ Y, −Y)` and `(X ⊖ Y, Y)` in `X ⊕ Y = Y + X·G`, where `(X ⊕ Y) ⊖ Y = X = (X ⊖ Y) ⊕ Y`. -/
theorem exists_units_ltAdd_ltSub (hℓ2 : ℓ ≠ 2) :
    ∃ U₁ U₂ : MvPowerSeries (Fin 2) ℂ_[ℓ], IsIntK U₁ ∧ IsIntK U₂ ∧
      MvPowerSeries.X 0 + MvPowerSeries.X 1 = ltAdd ℂ_[ℓ] ℓ * U₁ ∧
      MvPowerSeries.X 0 - MvPowerSeries.X 1 = ltSub ℂ_[ℓ] ℓ * U₂ := by
  have hℓ := hℓp.out.one_lt
  have hodd : Odd ℓ := hℓp.out.odd_of_ne_two hℓ2
  obtain ⟨G, hGi, hG⟩ := exists_ltAdd_eq (ℓ := ℓ)
  set X0 : MvPowerSeries (Fin 2) ℂ_[ℓ] := MvPowerSeries.X 0
  set X1 : MvPowerSeries (Fin 2) ℂ_[ℓ] := MvPowerSeries.X 1
  have hX0 : MvPowerSeries.constantCoeff X0 = 0 := MvPowerSeries.constantCoeff_X 0
  have hX1 : MvPowerSeries.constantCoeff X1 = 0 := MvPowerSeries.constantCoeff_X 1
  have hA0 : MvPowerSeries.constantCoeff (ltAdd ℂ_[ℓ] ℓ) = 0 := constantCoeff_ltAdd hℓ
  have hS0 : MvPowerSeries.constantCoeff (ltSub ℂ_[ℓ] ℓ) = 0 := constantCoeff_ltSub hℓ
  have hSi : IsIntK (ltSub ℂ_[ℓ] ℓ) := isIntK_ltAdd.subst (fun i => by
    fin_cases i
    · exact isIntK_X 0
    · exact (isIntK_X 1).neg) (fun i => by fin_cases i <;> simp)
  set ψ₁ : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ] := ![ltAdd ℂ_[ℓ] ℓ, -X1]
  set ψ₂ : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ] := ![ltSub ℂ_[ℓ] ℓ, X1]
  have h₁0 : ∀ i, MvPowerSeries.constantCoeff (ψ₁ i) = 0 := fun i => by
    fin_cases i
    · exact hA0
    · simp [ψ₁, hX1]
  have h₂0 : ∀ i, MvPowerSeries.constantCoeff (ψ₂ i) = 0 := fun i => by
    fin_cases i
    · exact hS0
    · exact hX1
  have hψ₁ := MvPowerSeries.hasSubst_of_constantCoeff_zero h₁0
  have hψ₂ := MvPowerSeries.hasSubst_of_constantCoeff_zero h₂0
  -- `(X ⊕ Y) ⊖ Y = X` and `(X ⊖ Y) ⊕ Y = X`
  have e₁ : MvPowerSeries.subst ψ₁ (ltAdd ℂ_[ℓ] ℓ) = X0 := by
    refine eq_of_lgP_eq hℓ (MvPowerSeries.constantCoeff_subst_eq_zero hψ₁ h₁0 hA0) hX0 ?_
    rw [lgP_subst_ltAdd hℓ h₁0]
    simp only [ψ₁, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [lgP_ltAdd hℓ, lgP_neg hodd hX1]
    ring
  have e₂ : MvPowerSeries.subst ψ₂ (ltAdd ℂ_[ℓ] ℓ) = X0 := by
    refine eq_of_lgP_eq hℓ (MvPowerSeries.constantCoeff_subst_eq_zero hψ₂ h₂0 hA0) hX0 ?_
    rw [lgP_subst_ltAdd hℓ h₂0]
    simp only [ψ₂, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [lgP_ltSub hℓ hodd]
    ring
  have f₁ := congrArg (MvPowerSeries.subst ψ₁) hG
  rw [e₁, MvPowerSeries.subst_add hψ₁, MvPowerSeries.subst_mul hψ₁, MvPowerSeries.subst_X hψ₁,
    MvPowerSeries.subst_X hψ₁] at f₁
  have f₂ := congrArg (MvPowerSeries.subst ψ₂) hG
  rw [e₂, MvPowerSeries.subst_add hψ₂, MvPowerSeries.subst_mul hψ₂, MvPowerSeries.subst_X hψ₂,
    MvPowerSeries.subst_X hψ₂] at f₂
  simp only [ψ₁, ψ₂, Matrix.cons_val_zero, Matrix.cons_val_one] at f₁ f₂
  refine ⟨MvPowerSeries.subst ψ₁ G, MvPowerSeries.subst ψ₂ G, hGi.subst (fun i => ?_) h₁0,
    hGi.subst (fun i => ?_) h₂0, by linear_combination f₁, by linear_combination f₂⟩
  · fin_cases i
    · exact isIntK_ltAdd
    · exact (isIntK_X 1).neg
  · fin_cases i
    · exact hSi
    · exact isIntK_X 1

end GroupUnits

/-! ## The parallelogram law -/

section Parallelogram

variable {K : Type} [Field K] {σ : Type}

/-- **`z(A) = ε·log_LT(A)`** at a point `A`. -/
theorem subst_zLT {ℓ : ℕ} (ε : K) {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0) :
    (zLT ℓ ε).subst A = MvPowerSeries.C ε * lgP ℓ A := by
  rw [zLT, subst_mul (HasSubst.of_constantCoeff_zero hA), subst_C, lgP]

/-- **The formal addition law at two points** `u`, `v`:
`(u² − v²)·E(u + v)E(u − v) = E(u)²E(v)²·(u²P(v) − v²P(u))`. -/
theorem AddLaw.subst [CharZero K] {a b s : K} (h : AddLaw a b s) {u v : MvPowerSeries σ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    (u ^ 2 - v ^ 2) * (expSig a b s).subst (u + v) * (expSig a b s).subst (u - v) =
      (expSig a b s).subst u ^ 2 * (expSig a b s).subst v ^ 2 *
        (u ^ 2 * (wpF a b).subst v - v ^ 2 * (wpF a b).subst u) := by
  set ψ : Fin 2 → MvPowerSeries σ K := ![u, v]
  have h0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0 := fun i => by
    fin_cases i
    · exact hu
    · exact hv
  have hψ := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have h' := congrArg (MvPowerSeries.subst ψ) h
  simp only [MvPowerSeries.subst_mul hψ, MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_pow hψ] at h'
  rw [subst_subst _ (by rw [map_add, hX, hX, add_zero]) hψ, subst_subst _ (by rw [map_sub, hX, hX, sub_zero]) hψ,
    subst_subst _ (hX 0) hψ, subst_subst _ (hX 1) hψ, subst_subst _ (hX 0) hψ, subst_subst _ (hX 1) hψ,
    MvPowerSeries.subst_add hψ, MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_X hψ,
    MvPowerSeries.subst_X hψ] at h'
  exact h'

/-- **`T²P(z(T)) = z(T)²ρ(T)` at a point.** -/
theorem sq_mul_wpF_subst_pt {ℓ : ℕ} (hℓ : 1 < ℓ) {ε : K} (hε : ε ≠ 0) (a b : K) {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) :
    A ^ 2 * (wpF a b).subst (MvPowerSeries.C ε * lgP ℓ A) =
      (MvPowerSeries.C ε * lgP ℓ A) ^ 2 * (rhoLT ℓ a b ε).subst A := by
  have hAs : HasSubst A := HasSubst.of_constantCoeff_zero hA
  have h := congrArg (PowerSeries.subst A) (X_sq_mul_wpF_subst hℓ hε a b)
  rw [subst_mul hAs, subst_mul hAs, subst_pow hAs, subst_pow hAs, subst_X hAs,
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (constantCoeff_zLT hℓ ε)) hAs, subst_zLT ε hA] at h
  exact h

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`σ*` at a point**: `εA·exp(−ph(A)) = z·E(z)` with `z = ε·log_LT(A)` (`C_mul_X_mul_exp_neg_ph` at `A`). -/
theorem C_mul_mul_expMv_neg_ph (a b s ε : ℂ_[ℓ]) {A : MvPowerSeries σ ℂ_[ℓ]}
    (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.C ε * A * expMv (-(ph ℓ a b s ε).subst A) =
      MvPowerSeries.C ε * lgP ℓ A * (expSig a b s).subst (MvPowerSeries.C ε * lgP ℓ A) := by
  have hℓ := hℓp.out.one_lt
  have hAs : HasSubst A := HasSubst.of_constantCoeff_zero hA
  have hp0 := constantCoeff_ph hℓ a b s ε
  have hpA : MvPowerSeries.constantCoeff ((ph ℓ a b s ε).subst A) = 0 := constantCoeff_subst_eq_zero hA _ hp0
  have hu0 : MvPowerSeries.constantCoeff (MvPowerSeries.C ε * lgP ℓ A) = 0 := by
    rw [map_mul, constantCoeff_lgP hℓ hA, mul_zero]
  have h := congrArg (PowerSeries.subst A) (C_mul_X_mul_exp_neg_ph hℓ a b s ε)
  rw [subst_mul hAs, subst_mul hAs, subst_C, subst_X hAs,
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by rw [map_neg, hp0, neg_zero])) hAs,
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (constantCoeff_C_mul_logLT hℓ ε)) hAs,
    ← neg_one_smul ℂ_[ℓ] (ph ℓ a b s ε), subst_smul hAs, neg_one_smul,
    ← expMv_eq_subst (by rw [map_neg, hpA, neg_zero])] at h
  rw [h, show (C ε * logLT ℂ_[ℓ] ℓ) = zLT ℓ ε from rfl, subst_zLT ε hA, sigF,
    subst_mul (HasSubst.of_constantCoeff_zero hu0), subst_X (HasSubst.of_constantCoeff_zero hu0), expSig]

/-- **The variables are nonzero.** -/
theorem mvX_ne_zero {K : Type} [Field K] (i : Fin 2) : (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  simp at this

/-- **`X² − Y² ≠ 0`.** -/
theorem sq_sub_sq_ne_zero {K : Type} [Field K] :
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 - MvPowerSeries.X 1 ^ 2 ≠ 0 := by
  classical
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 2)) h
  rw [map_sub, MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X_pow, ite_eq_left rfl, ite_eq_right, map_zero,
    sub_zero] at this
  · exact one_ne_zero this
  · intro h'
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h'
    simp at this

/-- **Coefficients of an integral one-variable series give integral series.** -/
theorem isInt_evenTail {K : Type} [NormedField K] {g : K⟦X⟧} (hg : IsInt g) : IsInt (evenTail g) := fun n => by
  rw [evenTail, coeff_mk]
  exact hg _

/-- **The divided difference of an integral series is integral.** -/
theorem isIntK_divDiff {K : Type} [NormedField K] {g : K⟦X⟧} (hg : IsInt g) : IsIntK (divDiff g) := fun e => by
  rw [coeff_divDiff]
  exact hg _

/-- **The parallelogram law** (D1a′, item 3): `ph(X ⊕ Y) + ph(X ⊖ Y) ≃ 2ph(X) + 2ph(Y)` in Lubin–Tate coordinates,
given the formal addition law and the differential equation (`addLaw_weierODE_map` for a lattice), integral
`g₂`, `g₃` and the CM-b integrality of `t(z(T))`. With `S_A = exp(−ph(A))`, `ε·A·S_A = z_A·E(z_A)`
(`C_mul_mul_expMv_neg_ph`), the addition law of `σ*` and `T²P(z) = z²ρ` give
`exp(2ph(X) + 2ph(Y) − ph(X ⊕ Y) − ph(X ⊖ Y)) = ε²·Δ·U₁U₂`, where `X² ρ(Y) − Y²ρ(X) = (X² − Y²)·Δ`
(`sq_mul_sub_sq_mul`, `ρ` even and integral) and `X ± Y = (X ⊕± Y)·U` (`exists_units_ltAdd_ltSub`). -/
theorem parallelogram (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε))) :
    Simeq (2 * (ph ℓ a b s ε).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) +
        2 * (ph ℓ a b s ε).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]))
      ((ph ℓ a b s ε).subst (ltAdd ℂ_[ℓ] ℓ) + (ph ℓ a b s ε).subst (ltSub ℂ_[ℓ] ℓ)) := by
  have hℓ := hℓp.out.one_lt
  have hodd : Odd ℓ := hℓp.out.odd_of_ne_two hℓ2
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  set p := ph ℓ a b s ε
  set X0 : MvPowerSeries (Fin 2) ℂ_[ℓ] := MvPowerSeries.X 0 with hX0
  set X1 : MvPowerSeries (Fin 2) ℂ_[ℓ] := MvPowerSeries.X 1 with hX1
  set Pa := ltAdd ℂ_[ℓ] ℓ
  set Ps := ltSub ℂ_[ℓ] ℓ
  have c0 : MvPowerSeries.constantCoeff X0 = 0 := MvPowerSeries.constantCoeff_X 0
  have c1 : MvPowerSeries.constantCoeff X1 = 0 := MvPowerSeries.constantCoeff_X 1
  have ca : MvPowerSeries.constantCoeff Pa = 0 := constantCoeff_ltAdd hℓ
  have cs : MvPowerSeries.constantCoeff Ps = 0 := constantCoeff_ltSub hℓ
  have hp0 := constantCoeff_ph hℓ a b s ε
  have cp : ∀ A : MvPowerSeries (Fin 2) ℂ_[ℓ], MvPowerSeries.constantCoeff A = 0 →
      MvPowerSeries.constantCoeff (-p.subst A) = 0 := fun A hA => by
    rw [map_neg, constantCoeff_subst_eq_zero hA _ hp0, neg_zero]
  -- `ε·A·exp(−ph(A)) = z_A·E(z_A)` at the four points
  have F0 := C_mul_mul_expMv_neg_ph a b s ε c0
  have F1 := C_mul_mul_expMv_neg_ph a b s ε c1
  have Fa := C_mul_mul_expMv_neg_ph a b s ε ca
  have Fs := C_mul_mul_expMv_neg_ph a b s ε cs
  rw [lgP_ltAdd hℓ, mul_add] at Fa
  rw [lgP_ltSub hℓ hodd, mul_sub] at Fs
  set S0 := expMv (-p.subst X0)
  set S1 := expMv (-p.subst X1)
  set Sa := expMv (-p.subst Pa)
  set Ss := expMv (-p.subst Ps)
  set z0 := MvPowerSeries.C ε * lgP ℓ X0
  set z1 := MvPowerSeries.C ε * lgP ℓ X1
  have cz0 : MvPowerSeries.constantCoeff z0 = 0 := by rw [map_mul, constantCoeff_lgP hℓ c0, mul_zero]
  have cz1 : MvPowerSeries.constantCoeff z1 = 0 := by rw [map_mul, constantCoeff_lgP hℓ c1, mul_zero]
  set E := expSig a b s
  set P := wpF a b
  set ρ := rhoLT ℓ a b ε
  -- the addition law, `T²P(z) = z²ρ`, the units and the even divided difference
  have F2 := hAdd.subst cz0 cz1
  have F30 := sq_mul_wpF_subst_pt hℓ hε0 a b c0
  have F31 := sq_mul_wpF_subst_pt hℓ hε0 a b c1
  obtain ⟨U1, U2, hU1, hU2, F4a, F4s⟩ := exists_units_ltAdd_ltSub (ℓ := ℓ) hℓ2
  have F5 := sq_mul_sub_sq_mul (rescale_neg_rhoLT hℓ hodd a b ε)
  set Δ := MvPowerSeries.C (coeff 0 ρ) - X0 ^ 2 * X1 ^ 2 *
    MvPowerSeries.subst ![X0 ^ 2, X1 ^ 2] (divDiff (evenTail ρ))
  set ρ0 := ρ.subst X0
  set ρ1 := ρ.subst X1
  set Cε := (MvPowerSeries.C ε : MvPowerSeries (Fin 2) ℂ_[ℓ])
  have stepA : Cε ^ 2 * Pa * Ps * Sa * Ss =
      E.subst z0 ^ 2 * E.subst z1 ^ 2 * (z0 ^ 2 * P.subst z1 - z1 ^ 2 * P.subst z0) := by
    linear_combination (Cε * Ps * Ss) * Fa + ((z0 + z1) * E.subst (z0 + z1)) * Fs + F2
  have stepB : X0 ^ 2 * X1 ^ 2 * (E.subst z0 ^ 2 * E.subst z1 ^ 2 * (z0 ^ 2 * P.subst z1 - z1 ^ 2 * P.subst z0)) =
      (Cε * X0 * S0) ^ 2 * (Cε * X1 * S1) ^ 2 * ((X0 ^ 2 - X1 ^ 2) * Δ) := by
    linear_combination E.subst z0 ^ 2 * E.subst z1 ^ 2 * z0 ^ 2 * X0 ^ 2 * F31 -
      E.subst z0 ^ 2 * E.subst z1 ^ 2 * z1 ^ 2 * X1 ^ 2 * F30 -
      (z0 * E.subst z0 + Cε * X0 * S0) * (z1 * E.subst z1) ^ 2 * (X0 ^ 2 * ρ1 - X1 ^ 2 * ρ0) * F0 -
      (Cε * X0 * S0) ^ 2 * (z1 * E.subst z1 + Cε * X1 * S1) * (X0 ^ 2 * ρ1 - X1 ^ 2 * ρ0) * F1 +
      (Cε * X0 * S0) ^ 2 * (Cε * X1 * S1) ^ 2 * F5
  have hN : Cε ^ 2 * (X0 ^ 2 - X1 ^ 2) * X0 ^ 2 * X1 ^ 2 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) sq_sub_sq_ne_zero) (pow_ne_zero _ (mvX_ne_zero 0)))
      (pow_ne_zero _ (mvX_ne_zero 1))
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [MvPowerSeries.constantCoeff_C, map_zero] at this
    exact hε0 this
  have key : Sa * Ss = Cε ^ 2 * S0 ^ 2 * S1 ^ 2 * Δ * U1 * U2 := by
    refine mul_left_cancel₀ hN ?_
    linear_combination X0 ^ 2 * X1 ^ 2 * U1 * U2 * stepA + U1 * U2 * stepB +
      Cε ^ 2 * X0 ^ 2 * X1 ^ 2 * Sa * Ss * ((X0 - X1) * F4a + Pa * U1 * F4s)
  -- `exp(2ph(X) + 2ph(Y) − ph(X ⊕ Y) − ph(X ⊖ Y)) = ε²·Δ·U₁U₂`
  have cdiff : MvPowerSeries.constantCoeff (2 * p.subst X0 + 2 * p.subst X1 - (p.subst Pa + p.subst Ps)) = 0 := by
    rw [map_sub, map_add, map_add, map_mul, map_mul, constantCoeff_subst_eq_zero c0 _ hp0,
      constantCoeff_subst_eq_zero c1 _ hp0, constantCoeff_subst_eq_zero ca _ hp0, constantCoeff_subst_eq_zero cs _ hp0]
    simp
  refine ⟨cdiff, ?_⟩
  have hS : ∀ A : MvPowerSeries (Fin 2) ℂ_[ℓ], MvPowerSeries.constantCoeff A = 0 →
      MvPowerSeries.constantCoeff (expMv (-p.subst A)) = 1 := fun A hA => constantCoeff_expMv (cp A hA)
  have hprod : expMv (2 * p.subst X0 + 2 * p.subst X1 - (p.subst Pa + p.subst Ps)) * (S0 ^ 2 * S1 ^ 2) =
      Sa * Ss := by
    rw [← expMv_add (cp Pa ca) (cp Ps cs), sq, sq, ← expMv_add (cp X0 c0) (cp X0 c0),
      ← expMv_add (cp X1 c1) (cp X1 c1),
      ← expMv_add (by rw [map_add, cp X0 c0, add_zero]) (by rw [map_add, cp X1 c1, add_zero]),
      ← expMv_add cdiff (by rw [map_add, map_add, map_add, cp X0 c0, cp X1 c1]; simp)]
    congr 1
    ring
  have hS0 : S0 ^ 2 * S1 ^ 2 ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_mul, map_pow, map_pow, hS X0 c0, hS X1 c1, map_zero] at this
    simp at this
  have hΨ : expMv (2 * p.subst X0 + 2 * p.subst X1 - (p.subst Pa + p.subst Ps)) = Cε ^ 2 * Δ * U1 * U2 := by
    refine mul_right_cancel₀ hS0 ?_
    rw [hprod, key]
    ring
  rw [hΨ]
  have hρ := isInt_rhoLT hℓ2 ha hb hε hODE ht
  have hΔ : IsIntK Δ := (isIntK_C (hρ 0)).sub (((isIntK_X 0).pow 2 |>.mul ((isIntK_X 1).pow 2)).mul
    ((isIntK_divDiff (isInt_evenTail hρ)).subst (fun i => by
      fin_cases i
      · exact (isIntK_X 0).pow 2
      · exact (isIntK_X 1).pow 2) (fun i => by fin_cases i <;> simp [c0, c1])))
  exact (((isIntK_C (by rw [hε])).pow 2).mul hΔ).mul hU1 |>.mul hU2

end Parallelogram

/-! ## Biadditivity of `be` -/

section Biadd

/-! ### The subgroup of series `≃ 0` -/

section SimeqZero

variable {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **Sums of series `≃ 0`.** -/
theorem simeq_zero_add {f g : MvPowerSeries σ ℂ_[ℓ]} (hf : Simeq f 0) (hg : Simeq g 0) : Simeq (f + g) 0 := by
  simpa using hf.add hg

/-- **Negatives of series `≃ 0`.** -/
theorem simeq_zero_neg {f : MvPowerSeries σ ℂ_[ℓ]} (hf : Simeq f 0) : Simeq (-f) 0 := by
  simpa using hf.neg

/-- **Differences of series `≃ 0`.** -/
theorem simeq_zero_sub {f g : MvPowerSeries σ ℂ_[ℓ]} (hf : Simeq f 0) (hg : Simeq g 0) : Simeq (f - g) 0 := by
  rw [sub_eq_add_neg]
  exact simeq_zero_add hf (simeq_zero_neg hg)

/-- **Doubles of series `≃ 0`.** -/
theorem simeq_zero_two_mul {f : MvPowerSeries σ ℂ_[ℓ]} (hf : Simeq f 0) : Simeq (2 * f) 0 := by
  rw [two_mul]
  exact simeq_zero_add hf hf

/-- **Halving** (`ℓ ≠ 2`): if `2f ≃ 0` then `f ≃ 0`, as `exp(f)` is a square root of the integral `exp(2f)` with
constant term `1` (`isIntK_of_pow_eq`). -/
theorem simeq_zero_of_two_mul [Finite σ] (hℓ2 : ℓ ≠ 2) {f : MvPowerSeries σ ℂ_[ℓ]} (hf : Simeq (2 * f) 0) :
    Simeq f 0 := by
  have h0 : MvPowerSeries.constantCoeff f = 0 := by
    have := hf.1
    rw [sub_zero, map_mul, map_ofNat] at this
    simpa using this
  refine ⟨by rw [sub_zero, h0], ?_⟩
  have h2 : ‖((2 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    CMThetaOne.norm_natCast_padicComplex ((Nat.coprime_primes hℓp.out Nat.prime_two).2 hℓ2)
  have hU := hf.2
  rw [sub_zero, two_mul, expMv_add h0 h0, ← sq] at hU
  rw [sub_zero]
  exact isIntK_of_pow_eq h2 hU (by rw [constantCoeff_expMv h0, norm_one]) rfl

end SimeqZero

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {σ : Type}

/-- **The sum of two points** `A ⊕ B`. -/
def addP (A B : MvPowerSeries σ ℂ_[ℓ]) : MvPowerSeries σ ℂ_[ℓ] :=
  MvPowerSeries.subst ![A, B] (ltAdd ℂ_[ℓ] ℓ)

/-- **A pair of points substitutes.** -/
theorem hasSubst_pair {A B : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) : MvPowerSeries.HasSubst ![A, B] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i
    · exact hA
    · exact hB

/-- **`A ⊕ B` has no constant term.** -/
theorem constantCoeff_addP {A B : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) : MvPowerSeries.constantCoeff (addP A B) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hA hB) (fun i => by
    fin_cases i
    · exact hA
    · exact hB) (constantCoeff_ltAdd hℓp.out.one_lt)

/-- **`A ⊕ B` is integral** for integral `A`, `B`. -/
theorem isIntK_addP {A B : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hAi : IsIntK A) (hBi : IsIntK B) : IsIntK (addP A B) :=
  isIntK_ltAdd.subst (fun i => by
    fin_cases i
    · exact hAi
    · exact hBi) (fun i => by
    fin_cases i
    · exact hA
    · exact hB)

/-- **`log_LT(A ⊕ B) = log_LT(A) + log_LT(B)`.** -/
theorem lgP_addP {A B : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) : lgP ℓ (addP A B) = lgP ℓ A + lgP ℓ B := by
  rw [addP, lgP_subst_ltAdd hℓp.out.one_lt (fun i => by
    fin_cases i
    · exact hA
    · exact hB)]
  rfl

/-- **`A ⊖ B = A ⊕ (−B)`** as a substitution into `ltSub`. -/
theorem subst_pair_ltSub {A B : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst ![A, B] (ltSub ℂ_[ℓ] ℓ) = addP A (-B) := by
  have hψ : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, -MvPowerSeries.X 1] :
      Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp
  rw [ltSub, MvPowerSeries.subst_comp_subst_apply hψ (hasSubst_pair hA hB), addP]
  congr 1
  funext i
  fin_cases i
  · simp [MvPowerSeries.subst_X (hasSubst_pair hA hB)]
  · show MvPowerSeries.subst ![A, B] (-MvPowerSeries.X 1) = -B
    rw [← MvPowerSeries.coe_substAlgHom (hasSubst_pair hA hB), map_neg, MvPowerSeries.coe_substAlgHom,
      MvPowerSeries.subst_X (hasSubst_pair hA hB)]
    rfl

/-- **`ph(0) = 0`.** -/
theorem subst_zero_eq_zero {K : Type} [Field K] {τ : Type} {f : K⟦X⟧} (hf : constantCoeff f = 0) :
    f.subst (0 : MvPowerSeries τ K) = 0 := by
  rw [PowerSeries.subst_zero_eq_C_constantCoeff, hf, map_zero, map_zero]

/-- **Two points with equal logarithms are equal**, with the constant-term conditions discharged. -/
theorem addP_comm {A B : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) : addP A B = addP B A :=
  eq_of_lgP_eq hℓp.out.one_lt (constantCoeff_addP hA hB) (constantCoeff_addP hB hA) (by
    rw [lgP_addP hA hB, lgP_addP hB hA, add_comm])

/-- **The parallelogram law at two integral points** `A`, `B`:
`2ph(A) + 2ph(B) ≃ ph(A ⊕ B) + ph(A ⊕ (−B))` (`parallelogram`, substituted). -/
theorem parallelogram_pt (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε)))
    {A B : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0)
    (hAi : IsIntK A) (hBi : IsIntK B) :
    Simeq (2 * (ph ℓ a b s ε).subst A + 2 * (ph ℓ a b s ε).subst B)
      ((ph ℓ a b s ε).subst (addP A B) + (ph ℓ a b s ε).subst (addP A (-B))) := by
  have hℓ := hℓp.out.one_lt
  have hψ := hasSubst_pair hA hB
  have h := (parallelogram hℓ2 ha hb hε hAdd hODE ht).subst (ψ := ![A, B]) (fun i => by
    fin_cases i
    · exact hAi
    · exact hBi) (fun i => by
    fin_cases i
    · exact hA
    · exact hB)
  rw [← MvPowerSeries.coe_substAlgHom hψ, map_add, map_add, map_mul, map_mul, map_ofNat,
    MvPowerSeries.coe_substAlgHom, subst_subst _ (MvPowerSeries.constantCoeff_X 0) hψ,
    subst_subst _ (MvPowerSeries.constantCoeff_X 1) hψ, subst_subst _ (constantCoeff_ltAdd hℓ) hψ,
    subst_subst _ (constantCoeff_ltSub hℓ) hψ, MvPowerSeries.subst_X hψ, MvPowerSeries.subst_X hψ,
    subst_pair_ltSub hA hB] at h
  exact h

/-- **The pairing at two points**: `B(A, Y) = ph(A ⊕ Y) − ph(A) − ph(Y)`. -/
def bP (p : ℂ_[ℓ]⟦X⟧) (A Y : MvPowerSeries σ ℂ_[ℓ]) : MvPowerSeries σ ℂ_[ℓ] :=
  p.subst (addP A Y) - p.subst A - p.subst Y

/-- **A point with given logarithm**: equality of points from their logarithms (a convenience form). -/
theorem addP_eq_addP {A B C D : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hC : MvPowerSeries.constantCoeff C = 0)
    (hD : MvPowerSeries.constantCoeff D = 0) (h : lgP ℓ A + lgP ℓ B = lgP ℓ C + lgP ℓ D) :
    addP A B = addP C D :=
  eq_of_lgP_eq hℓp.out.one_lt (constantCoeff_addP hA hB) (constantCoeff_addP hC hD) (by
    rw [lgP_addP hA hB, lgP_addP hC hD, h])

variable [Finite σ]

/-- **The pairing is additive up to symmetry**: `B(u ⊕ v, y) + B(u ⊖ v, y) ≃ 2B(u, y)`, from five instances of the
parallelogram law (`2·(lhs − rhs) = −D₁ + D₂ − D₃ − D₄ + 2D₅`) and halving. -/
theorem bP_star (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε)))
    {u v y : MvPowerSeries σ ℂ_[ℓ]} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) (hy : MvPowerSeries.constantCoeff y = 0) (hui : IsIntK u)
    (hvi : IsIntK v) (hyi : IsIntK y) :
    Simeq (bP (ph ℓ a b s ε) (addP u v) y + bP (ph ℓ a b s ε) (addP u (-v)) y -
      2 * bP (ph ℓ a b s ε) u y) 0 := by
  have hodd : Odd ℓ := hℓp.out.odd_of_ne_two hℓ2
  set p := ph ℓ a b s ε
  have par := @parallelogram_pt ℓ hℓp σ hℓ2 a b s ε ha hb hε hAdd hODE ht
  have hv' : MvPowerSeries.constantCoeff (-v) = 0 := by rw [map_neg, hv, neg_zero]
  have hy' : MvPowerSeries.constantCoeff (-y) = 0 := by rw [map_neg, hy, neg_zero]
  have huv := constantCoeff_addP hu hv
  have humv := constantCoeff_addP hu hv'
  have huy := constantCoeff_addP hu hy
  have humy := constantCoeff_addP hu hy'
  have iuv := isIntK_addP hu hv hui hvi
  have iumv := isIntK_addP hu hv' hui hvi.neg
  have iuy := isIntK_addP hu hy hui hyi
  have iumy := isIntK_addP hu hy' hui hyi.neg
  have lv' := lgP_neg (K := ℂ_[ℓ]) hodd hv
  have ly' := lgP_neg (K := ℂ_[ℓ]) hodd hy
  have I1 := simeq_iff_sub.1 (par huy hv iuy hvi)
  have I2 := simeq_iff_sub.1 (par humy hv iumy hvi)
  have I3 := simeq_iff_sub.1 (par huv hy iuv hyi)
  have I4 := simeq_iff_sub.1 (par humv hy iumv hyi)
  have I5 := simeq_iff_sub.1 (par hu hy hui hyi)
  rw [addP_eq_addP huy hv huv hy (by rw [lgP_addP hu hy, lgP_addP hu hv]; ring),
    addP_eq_addP huy hv' humv hy (by rw [lgP_addP hu hy, lgP_addP hu hv', lv']; ring)] at I1
  rw [addP_eq_addP humy hv huv hy' (by rw [lgP_addP hu hy', lgP_addP hu hv, ly']; ring),
    addP_eq_addP humy hv' humv hy' (by rw [lgP_addP hu hy', lgP_addP hu hv', lv', ly']; ring)] at I2
  have e : 2 * (bP p (addP u v) y + bP p (addP u (-v)) y - 2 * bP p u y) =
      -(2 * p.subst (addP u y) + 2 * p.subst v - (p.subst (addP (addP u v) y) + p.subst (addP (addP u (-v)) y))) +
      (2 * p.subst (addP u (-y)) + 2 * p.subst v -
        (p.subst (addP (addP u v) (-y)) + p.subst (addP (addP u (-v)) (-y)))) -
      (2 * p.subst (addP u v) + 2 * p.subst y - (p.subst (addP (addP u v) y) + p.subst (addP (addP u v) (-y)))) -
      (2 * p.subst (addP u (-v)) + 2 * p.subst y -
        (p.subst (addP (addP u (-v)) y) + p.subst (addP (addP u (-v)) (-y)))) +
      2 * (2 * p.subst u + 2 * p.subst y - (p.subst (addP u y) + p.subst (addP u (-y)))) := by
    simp only [bP]
    ring
  refine simeq_zero_of_two_mul hℓ2 ?_
  rw [e]
  exact simeq_zero_add (simeq_zero_sub (simeq_zero_sub (simeq_zero_add (simeq_zero_neg I1) I2) I3) I4)
    (simeq_zero_two_mul I5)

/-- **The pairing is odd**: `B(v, y) + B(−v, y) ≃ 0` (`bP_star` at `u = 0`). -/
theorem bP_odd (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε)))
    {v y : MvPowerSeries σ ℂ_[ℓ]} (hv : MvPowerSeries.constantCoeff v = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (hvi : IsIntK v) (hyi : IsIntK y) :
    Simeq (bP (ph ℓ a b s ε) v y + bP (ph ℓ a b s ε) (-v) y) 0 := by
  have hℓ := hℓp.out.one_lt
  have hodd : Odd ℓ := hℓp.out.odd_of_ne_two hℓ2
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries σ ℂ_[ℓ]) = 0 := map_zero _
  have h0i : IsIntK (0 : MvPowerSeries σ ℂ_[ℓ]) := fun n => by simp
  have hv' : MvPowerSeries.constantCoeff (-v) = 0 := by rw [map_neg, hv, neg_zero]
  have h := bP_star hℓ2 ha hb hε hAdd hODE ht h0 hv hy h0i hvi hyi
  have e1 : ∀ w : MvPowerSeries σ ℂ_[ℓ], MvPowerSeries.constantCoeff w = 0 → addP 0 w = w := fun w hw =>
    eq_of_lgP_eq hℓ (constantCoeff_addP h0 hw) hw (by rw [lgP_addP h0 hw, lgP_zero hℓ, zero_add])
  rw [e1 v hv, e1 (-v) hv'] at h
  have e2 : bP (ph ℓ a b s ε) (0 : MvPowerSeries σ ℂ_[ℓ]) y = 0 := by
    rw [bP, e1 y hy, subst_zero_eq_zero (constantCoeff_ph hℓ a b s ε)]
    ring
  rwa [e2, mul_zero, sub_zero] at h

/-- **The pairing is additive in the first variable**: `B(u ⊕ v, y) ≃ B(u, y) + B(v, y)`. -/
theorem bP_add (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε)))
    {u v y : MvPowerSeries σ ℂ_[ℓ]} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) (hy : MvPowerSeries.constantCoeff y = 0) (hui : IsIntK u)
    (hvi : IsIntK v) (hyi : IsIntK y) :
    Simeq (bP (ph ℓ a b s ε) (addP u v) y) (bP (ph ℓ a b s ε) u y + bP (ph ℓ a b s ε) v y) := by
  have hodd : Odd ℓ := hℓp.out.odd_of_ne_two hℓ2
  have hℓ := hℓp.out.one_lt
  set p := ph ℓ a b s ε
  have hu' : MvPowerSeries.constantCoeff (-u) = 0 := by rw [map_neg, hu, neg_zero]
  have hv' : MvPowerSeries.constantCoeff (-v) = 0 := by rw [map_neg, hv, neg_zero]
  have S1 := bP_star hℓ2 ha hb hε hAdd hODE ht hu hv hy hui hvi hyi
  have S2 := bP_star hℓ2 ha hb hε hAdd hODE ht hv hu hy hvi hui hyi
  have O := bP_odd hℓ2 ha hb hε hAdd hODE ht (constantCoeff_addP hu hv') hy (isIntK_addP hu hv' hui hvi.neg) hyi
  rw [addP_comm hv hu] at S2
  have e : -addP u (-v) = addP v (-u) := eq_of_lgP_eq hℓ (by rw [map_neg, constantCoeff_addP hu hv', neg_zero])
    (constantCoeff_addP hv hu') (by
      rw [lgP_neg hodd (constantCoeff_addP hu hv'), lgP_addP hu hv', lgP_addP hv hu', lgP_neg hodd hu,
        lgP_neg hodd hv]
      ring)
  rw [e] at O
  rw [simeq_iff_sub]
  refine simeq_zero_of_two_mul hℓ2 ?_
  have e2 : 2 * (bP p (addP u v) y - (bP p u y + bP p v y)) =
      (bP p (addP u v) y + bP p (addP u (-v)) y - 2 * bP p u y) +
        (bP p (addP u v) y + bP p (addP v (-u)) y - 2 * bP p v y) -
        (bP p (addP u (-v)) y + bP p (addP v (-u)) y) := by ring
  rw [e2]
  exact simeq_zero_sub (simeq_zero_add S1 S2) O

omit [Finite σ] in
/-- **`be` at two points is the pairing `bP`.** -/
theorem subst_be (a b s ε : ℂ_[ℓ]) {A Y : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hY : MvPowerSeries.constantCoeff Y = 0) :
    MvPowerSeries.subst ![A, Y] (be ℓ a b s ε) = bP (ph ℓ a b s ε) A Y := by
  have hℓ := hℓp.out.one_lt
  have hψ := hasSubst_pair hA hY
  rw [be, MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_sub hψ, subst_subst _ (constantCoeff_ltAdd hℓ) hψ,
    subst_subst _ (MvPowerSeries.constantCoeff_X 0) hψ, subst_subst _ (MvPowerSeries.constantCoeff_X 1) hψ,
    MvPowerSeries.subst_X hψ, MvPowerSeries.subst_X hψ, bP]
  rfl

end Biadd

/-! ## Biadditivity of `be`, and the CM curve -/

section BeBiadd

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`be` is symmetric**: `be(Y, X) = be(X, Y)` (the group law is commutative). -/
theorem be_symm (a b s ε : ℂ_[ℓ]) :
    MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (be ℓ a b s ε) = be ℓ a b s ε := by
  have c0 := MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (0 : Fin 2)
  have c1 := MvPowerSeries.constantCoeff_X (R := ℂ_[ℓ]) (1 : Fin 2)
  have hid : MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] (be ℓ a b s ε) = be ℓ a b s ε := by
    have : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) = MvPowerSeries.X := by
      funext i
      fin_cases i <;> rfl
    rw [this, MvPowerSeries.subst_self]
    rfl
  rw [subst_be a b s ε c1 c0, ← hid, subst_be a b s ε c0 c1, bP, bP, addP_comm c1 c0]
  ring

/-- **Biadditivity of the Gaussian pairing** (D1a′, item 3): `be(X ⊕ X′, Y) ≃ be(X, Y) + be(X′, Y)` in three
variables (and in `Y` by `be_symm`), given the formal addition law and differential equation of `σ*` and `℘`
(`addLaw_weierODE_map`), integral `g₂`, `g₃`, `ℓ ≠ 2`, `‖ε‖ = 1` and the CM-b integrality of `t(ε·log_LT(T))`. -/
theorem be_biadd (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε))) :
    Simeq (MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2]
        (be ℓ a b s ε))
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2] (be ℓ a b s ε) +
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2]
          (be ℓ a b s ε)) := by
  have c : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  rw [subst_be a b s ε (constantCoeff_addP (c 0) (c 1)) (c 2), subst_be a b s ε (c 0) (c 2),
    subst_be a b s ε (c 1) (c 2)]
  exact bP_add hℓ2 ha hb hε hAdd hODE ht (c 0) (c 1) (c 2) (isIntK_X 0) (isIntK_X 1) (isIntK_X 2)

/-- **`g₂`, `g₃` of the `Δ = 1` CM lattice are integral** at `ℓ ≥ 5` (CM-c: `j = 1728g₂³` is an algebraic integer,
and `46656g₃² = 1728g₂³ − 1728`). -/
theorem norm_g_le_one (hj : CMThetaOne.CMjIntegral) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : HasCM d Λ) (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (ι : ℂ ≃+* ℂ_[ℓ]) :
    ‖ι Λ.g₂‖ ≤ 1 ∧ ‖ι Λ.g₃‖ ≤ 1 := by
  have hpr : ℓ.Prime := hℓp.out
  have hjΛ : IsIntegral ℤ (1728 * Λ.g₂ ^ 3) := by simpa [hΔ] using hj d Λ hd hd4 hcm
  have hjι : ‖ι (1728 * Λ.g₂ ^ 3)‖ ≤ 1 := CMThetaOne.norm_le_one_of_isIntegral (ι : ℂ →+* ℂ_[ℓ]) hjΛ
  have hn1728 : ‖((1728 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    CMThetaOne.norm_natCast_padicComplex (by simpa using CMThetaOne.coprime_two_three hpr h5 6 3)
  have hn46656 : ‖((46656 : ℕ) : ℂ_[ℓ])‖ = 1 :=
    CMThetaOne.norm_natCast_padicComplex (by simpa using CMThetaOne.coprime_two_three hpr h5 6 6)
  have e1728 : ι 1728 = ((1728 : ℕ) : ℂ_[ℓ]) := by rw [map_ofNat ι 1728, Nat.cast_ofNat]
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow, e1728, hn1728, one_mul] at hjι
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hjι
  · have heq : ι (46656 * Λ.g₃ ^ 2) = ι (1728 * Λ.g₂ ^ 3) - ((1728 : ℕ) : ℂ_[ℓ]) := by
      rw [show (46656 : ℂ) * Λ.g₃ ^ 2 = 1728 * Λ.g₂ ^ 3 - 1728 by linear_combination -1728 * hΔ, map_sub, e1728]
    have hle : ‖ι (46656 * Λ.g₃ ^ 2)‖ ≤ 1 := by
      rw [heq, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hjι (by rw [norm_neg]; exact hn1728.le))
    have e46656 : ι 46656 = ((46656 : ℕ) : ℂ_[ℓ]) := by rw [map_ofNat ι 46656, Nat.cast_ofNat]
    rw [map_mul, map_pow, norm_mul, norm_pow, e46656, hn46656, one_mul] at hle
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hle

/-- **Biadditivity for the CM curve at an inert prime** (D1a′, item 3, with the inputs CM-b and CM-c): for the
`Δ = 1` model of a CM lattice and an inert `ℓ ≥ 5`, `ℓ ∤ d`, the Lubin–Tate unit `ε` of CM-b makes
`be = ph(X ⊕ Y) − ph(X) − ph(Y)` (for `g₂`, `g₃`, `s₂` of the lattice) biadditive up to `≃`. -/
theorem be_biadd_cm (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) {d : ℕ} {Λ : PeriodPair}
    (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ) (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ)
    (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι : ℂ ≃+* ℂ_[ℓ]) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) ∧
      Simeq (MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2]
          (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε))
        (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2]
            (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) +
          MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2]
            (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε)) := by
  obtain ⟨ε, hεu, hε, ht⟩ := hb d Λ hd hd4 hcm hΔ ℓ h5 hdℓ hin ι
  obtain ⟨h2, h3⟩ := norm_g_le_one hj hd hd4 hcm hΔ h5 ι
  obtain ⟨hAdd, hODE⟩ := addLaw_weierODE_map Λ (ι : ℂ →+* ℂ_[ℓ])
  have hti : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) := fun n => (ht n).2
  exact ⟨ε, hεu, hε, hti, be_biadd (by omega) h2 h3 hε hAdd hODE hti⟩

end BeBiadd

/-! ## Congruences under substitution -/

section CongSubst

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {σ : Type}

/-- **Coefficient bounds pass to products with integral series** (ultrametric). -/
theorem norm_coeff_mul_le {F G : MvPowerSeries σ ℂ_[ℓ]} {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ n, ‖MvPowerSeries.coeff n F‖ ≤ r) (hG : IsIntK G) (n : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff n (F * G)‖ ≤ r := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun p _ => ?_
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 F‖ * ‖MvPowerSeries.coeff p.2 G‖ ≤ r * 1 :=
        mul_le_mul (hF _) (hG _) (norm_nonneg _) hr
    _ = r := mul_one r

/-- **`ℓ`-divisibility is kept by integral substitution.** -/
theorem _root_.CMFormalInert.IsDivK.subst_int {τ : Type} [Finite τ] {F : MvPowerSeries τ ℂ_[ℓ]} (hF : IsDivK ℓ F)
    {ψ : τ → MvPowerSeries σ ℂ_[ℓ]} (hψ : ∀ i, IsIntK (ψ i)) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) :
    IsDivK ℓ (MvPowerSeries.subst ψ F) := by
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓp.out.ne_zero
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0
  have hF' : IsIntK (MvPowerSeries.C (ℓ : ℂ_[ℓ])⁻¹ * F) := fun n => by
    rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hF n) (norm_nonneg _)
  have e : F = MvPowerSeries.C (ℓ : ℂ_[ℓ]) * (MvPowerSeries.C (ℓ : ℂ_[ℓ])⁻¹ * F) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hℓ0, map_one, one_mul]
  intro n
  rw [e, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_C, MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hF'.subst hψ hψ0 n)

/-- **Divided-power type congruences** (the shape of `serAB(U, V^ℓ) − log_LT(U)log_LT(V)`): if every coefficient
`M_e ≠ 0` has `e₀ = ℓ^m` with `‖M_e‖·‖ℓ‖^m ≤ 1`, then `M(A, Y) ≡ M(A′, Y) (mod ℓ)` for integral `A ≡ A′ (mod ℓ)` and
integral `Y` (as `A^{ℓ^m} ≡ A′^{ℓ^m} (mod ℓ^{m+1})`). -/
theorem isDivK_subst_sub {M : MvPowerSeries (Fin 2) ℂ_[ℓ]}
    (hM : ∀ e, MvPowerSeries.coeff e M ≠ 0 → ∃ m, e 0 = ℓ ^ m ∧ ‖MvPowerSeries.coeff e M‖ * ‖(ℓ : ℂ_[ℓ])‖ ^ m ≤ 1)
    {A A' Y : MvPowerSeries σ ℂ_[ℓ]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hA' : MvPowerSeries.constantCoeff A' = 0) (hY : MvPowerSeries.constantCoeff Y = 0) (hAi : IsIntK A)
    (hA'i : IsIntK A') (hYi : IsIntK Y) (hAA : IsDivK ℓ (A - A')) :
    IsDivK ℓ (MvPowerSeries.subst ![A, Y] M - MvPowerSeries.subst ![A', Y] M) := by
  classical
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓp.out.ne_zero
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
  by_cases he : MvPowerSeries.coeff e M = 0
  · rw [he, norm_zero, zero_mul]
    exact norm_nonneg _
  obtain ⟨m, hm, hle⟩ := hM e he
  rw [hm]
  have h1 := norm_coeff_mul_le (by positivity)
    (norm_coeff_pow_sub_pow_le hℓ0 hAi hA'i hAA m) (hYi.pow (e 1)) α
  calc ‖MvPowerSeries.coeff e M‖ * ‖MvPowerSeries.coeff α ((A ^ ℓ ^ m - A' ^ ℓ ^ m) * Y ^ e 1)‖
      ≤ ‖MvPowerSeries.coeff e M‖ * ‖(ℓ : ℂ_[ℓ])‖ ^ (m + 1) := by gcongr
    _ = ‖MvPowerSeries.coeff e M‖ * ‖(ℓ : ℂ_[ℓ])‖ ^ m * ‖(ℓ : ℂ_[ℓ])‖ := by ring
    _ ≤ 1 * ‖(ℓ : ℂ_[ℓ])‖ := by gcongr
    _ = ‖(ℓ : ℂ_[ℓ])‖ := one_mul _

end CongSubst

/-! ## The explicit Gaussian is biadditive (existence half of the classification) -/

section SerABBiadd

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

open Classical in
/-- **The coefficients of `F(X, Y^ℓ)`.** -/
theorem coeff_subst_X_X_pow {K : Type} [Field K] (F : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1 ^ ℓ] F) =
      if ℓ ∣ e 1 then MvPowerSeries.coeff (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1 / ℓ)) F else 0 := by
  have hℓ0 : ℓ ≠ 0 := hℓp.out.ne_zero
  have hψ : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1 ^ ℓ] :
      Fin 2 → MvPowerSeries (Fin 2) K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hℓ0]
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e =>
      (![MvPowerSeries.X 0, MvPowerSeries.X 1 ^ ℓ] : Fin 2 → MvPowerSeries (Fin 2) K) s ^ e) =
      MvPowerSeries.monomial (Finsupp.single 0 (d 0) + Finsupp.single 1 (ℓ * d 1)) 1 := fun d => by
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← pow_mul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]
  rw [MvPowerSeries.coeff_subst hψ]
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    rw [finsum_eq_single _ (Finsupp.single 0 (e 0) + Finsupp.single 1 q)]
    · rw [hprod, MvPowerSeries.coeff_monomial, ite_eq_left, smul_eq_mul, mul_one, hq,
        Nat.mul_div_cancel_left _ hℓp.out.pos]
      ext i
      fin_cases i <;> simp [hq]
    · intro d hd
      rw [hprod, MvPowerSeries.coeff_monomial, ite_eq_right, smul_zero]
      intro he
      apply hd
      have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) he
      have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) he
      simp at h0 h1
      ext i
      fin_cases i
      · simp [h0]
      · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
        simp
        have := Nat.eq_of_mul_eq_mul_left hℓp.out.pos (h1.symm.trans hq)
        omega
  · refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [hprod, MvPowerSeries.coeff_monomial, ite_eq_right, smul_zero]
    intro he
    apply h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) he
    simp at h1
    exact ⟨d 1, h1⟩

/-- **`M(U, V) = serAB(U, V^ℓ) − log_LT(U)·log_LT(V)`**: the defect series of the existence proof. -/
def mSer (ℓ : ℕ) [Fact ℓ.Prime] : MvPowerSeries (Fin 2) ℂ_[ℓ] :=
  MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1 ^ ℓ] (serAB ℓ) -
    (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
      (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ])

/-- **`‖ℓ^{−k}‖·‖ℓ‖^m ≤ 1` for `k ≤ m`.** -/
theorem norm_inv_pow_mul_le {k m : ℕ} (h : k ≤ m) : ‖((ℓ : ℂ_[ℓ]) ^ k)⁻¹‖ * ‖(ℓ : ℂ_[ℓ])‖ ^ m ≤ 1 := by
  have hpos : 0 < ‖(ℓ : ℂ_[ℓ])‖ := norm_pos_iff.2 (by exact_mod_cast hℓp.out.ne_zero)
  have hle : ‖(ℓ : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ ℓ
  rw [norm_inv, norm_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact pow_le_pow_of_le_one hpos.le hle h

/-- **`M` has divided-power type**: a nonzero coefficient `M_e` has `e₀ = ℓ^m` and `‖M_e‖·‖ℓ‖^m ≤ 1`. The terms
`X^{ℓ^{2i}}Y^{ℓ^{2j+2}}` (`i ≤ j`) of `serAB(X, Y^ℓ)` cancel against `log_LT(X)log_LT(Y)`; what is left is
`X^{ℓ^{2j+1}}Y^{ℓ^{2i+1}}/ℓ^{i+j+1}` (`i ≤ j`) and `−X^{ℓ^{2i}}Y^{ℓ^{2j}}/ℓ^{i+j}` (`j ≤ i`): this is where the
restriction `i ≤ j` of `serAB` enters. -/
theorem mSer_typeM (e : Fin 2 →₀ ℕ) (he : MvPowerSeries.coeff e (mSer ℓ) ≠ 0) :
    ∃ m, e 0 = ℓ ^ m ∧ ‖MvPowerSeries.coeff e (mSer ℓ)‖ * ‖(ℓ : ℂ_[ℓ])‖ ^ m ≤ 1 := by
  have hℓ := hℓp.out.one_lt
  have hc : MvPowerSeries.coeff e (mSer ℓ) =
      (if ℓ ∣ e 1 then sAB ℓ (e 0) (e 1 / ℓ) else 0) - coeff (e 0) (logLT ℂ_[ℓ] ℓ) * coeff (e 1) (logLT ℂ_[ℓ] ℓ) := by
    rw [mSer, map_sub, coeff_subst_X_X_pow, coeff_subst_X0_mul_subst_X1]
  rw [hc] at he ⊢
  by_cases hS : ℓ ∣ e 1 ∧ ∃ i j, SupAB ℓ (e 0) (e 1 / ℓ) i j
  · obtain ⟨hd, i, j, hij⟩ := hS
    rw [ite_eq_left hd, sAB_of hij] at he ⊢
    obtain ⟨q, hq⟩ := hd
    rcases hij with ⟨hle, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩
    · -- `(ℓ^{2i}, ℓ^{2j+2})`: the two terms cancel
      exfalso
      apply he
      have he1 : e 1 = ℓ ^ (2 * (j + 1)) := by
        rw [hq, Nat.mul_div_cancel_left _ hℓp.out.pos] at h1
        rw [hq, h1, ← pow_succ']
        ring_nf
      rw [h0, he1, lc_pow, lc_pow, ← mul_inv, ← pow_add, show i + (j + 1) = i + j + 1 by ring, sub_self]
    · -- `(ℓ^{2j+1}, ℓ^{2i+1})`
      refine ⟨2 * j + 1, h0, ?_⟩
      rw [h0, lc_of_not (fun k hk => pow_even_ne_odd k j hk.symm), zero_mul, sub_zero]
      exact norm_inv_pow_mul_le (by omega)
  · have hT : (if ℓ ∣ e 1 then sAB ℓ (e 0) (e 1 / ℓ) else 0) = 0 := by
      split_ifs with hd
      · exact sAB_of_not fun i j h => hS ⟨hd, i, j, h⟩
      · rfl
    rw [hT, zero_sub] at he
    rw [hT, zero_sub, norm_neg]
    have hL : coeff (e 0) (logLT ℂ_[ℓ] ℓ) * coeff (e 1) (logLT ℂ_[ℓ] ℓ) ≠ 0 := by
      intro h; apply he; rw [h, neg_zero]
    obtain ⟨i, h0⟩ : ∃ i, e 0 = ℓ ^ (2 * i) := by
      by_contra h
      push Not at h
      exact hL (by rw [lc_of_not h, zero_mul])
    obtain ⟨j, h1⟩ : ∃ j, e 1 = ℓ ^ (2 * j) := by
      by_contra h
      push Not at h
      exact hL (by rw [lc_of_not h, mul_zero])
    refine ⟨2 * i, h0, ?_⟩
    rw [h0, h1, lc_pow, lc_pow, ← mul_inv, ← pow_add]
    refine norm_inv_pow_mul_le ?_
    by_contra hji
    push Not at hji
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    apply hS
    refine ⟨⟨ℓ ^ (2 * j' + 1), by rw [h1]; ring⟩, i, j', by omega, Or.inl ⟨h0, ?_⟩⟩
    rw [h1, show 2 * (j' + 1) = (2 * j' + 1) + 1 by ring, pow_succ, Nat.mul_div_cancel _ hℓp.out.pos]

/-- **`expand` is the substitution `Xᵢ ↦ Xᵢ^ℓ`.** -/
theorem expand_eq_subst {σ : Type} (F : MvPowerSeries σ ℂ_[ℓ]) :
    MvPowerSeries.expand ℓ hℓp.out.ne_zero F = MvPowerSeries.subst (fun i => MvPowerSeries.X i ^ ℓ) F := by
  rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

/-- **The Frobenius defect of `serAB` at two points**:
`serAB(P^ℓ, Q^ℓ) + ℓ·serAB(P, Q) = log_LT(P^ℓ)log_LT(Q) + log_LT(P)log_LT(Q^ℓ)` (`expand_serAB_add_smul`). -/
theorem subst_serAB_frob {σ : Type} {P Q : MvPowerSeries σ ℂ_[ℓ]} (hP : MvPowerSeries.constantCoeff P = 0)
    (hQ : MvPowerSeries.constantCoeff Q = 0) :
    MvPowerSeries.subst ![P ^ ℓ, Q ^ ℓ] (serAB ℓ) + (ℓ : ℂ_[ℓ]) • MvPowerSeries.subst ![P, Q] (serAB ℓ) =
      lgP ℓ (P ^ ℓ) * lgP ℓ Q + lgP ℓ P * lgP ℓ (Q ^ ℓ) := by
  have hℓ0 := hℓp.out.ne_zero
  have hψ := hasSubst_pair hP hQ
  have h := congrArg (MvPowerSeries.subst ![P, Q]) (expand_serAB_add_smul (ℓ := ℓ))
  have hX : MvPowerSeries.HasSubst (fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[ℓ]) ^ ℓ) :=
    MvPowerSeries.HasSubst.X_pow hℓ0
  have hXℓ : HasSubst (X ^ ℓ : ℂ_[ℓ]⟦X⟧) := HasSubst.X_pow hℓ0
  rw [MvPowerSeries.subst_add hψ, expand_eq_subst, MvPowerSeries.subst_comp_subst_apply hX hψ,
    MvPowerSeries.subst_smul hψ, MvPowerSeries.subst_add hψ, MvPowerSeries.subst_mul hψ,
    MvPowerSeries.subst_mul hψ, subst_subst _ (MvPowerSeries.constantCoeff_X 0) hψ,
    subst_subst _ (MvPowerSeries.constantCoeff_X 1) hψ, subst_subst _ (MvPowerSeries.constantCoeff_X 0) hψ,
    subst_subst _ (MvPowerSeries.constantCoeff_X 1) hψ, MvPowerSeries.subst_X hψ, MvPowerSeries.subst_X hψ] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [logLTF, subst_comp_subst_apply hXℓ (HasSubst.of_constantCoeff_zero hP),
    subst_comp_subst_apply hXℓ (HasSubst.of_constantCoeff_zero hQ),
    subst_pow (HasSubst.of_constantCoeff_zero hP), subst_pow (HasSubst.of_constantCoeff_zero hQ),
    subst_X (HasSubst.of_constantCoeff_zero hP), subst_X (HasSubst.of_constantCoeff_zero hQ)] at h
  have e : (fun s => MvPowerSeries.subst ![P, Q] ((MvPowerSeries.X s : MvPowerSeries (Fin 2) ℂ_[ℓ]) ^ ℓ)) =
      ![P ^ ℓ, Q ^ ℓ] := by
    funext i
    fin_cases i <;> simp [MvPowerSeries.subst_pow hψ, MvPowerSeries.subst_X hψ]
  rw [e] at h
  exact h

/-- **The Frobenius congruence of the group law at two points**: `U^ℓ ⊕ V^ℓ ≡ (U ⊕ V)^ℓ (mod ℓ)` for integral
`U`, `V` (over `ℚ_ℓ` from `isDivK_frobS_sub_pow_of_isIntK` with `φ = id`). -/
theorem isDivK_addP_pow_sub {σ : Type} {U V : MvPowerSeries σ ℂ_[ℓ]} (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hUi : IsIntK U) (hVi : IsIntK V) :
    IsDivK ℓ (addP (U ^ ℓ) (V ^ ℓ) - addP U V ^ ℓ) := by
  have hℓ := hℓp.out.one_lt
  have hℓ0 := hℓp.out.ne_zero
  -- over `ℚ_ℓ`
  have hQ := isDivK_frobS_sub_pow_of_isIntK (φ := RingHom.id ℚ_[ℓ]) norm_sub_pow_le_padic
    (isIntK_ltAdd_padic (ℓ := ℓ))
  have hfr : frobS ℓ (RingHom.id ℚ_[ℓ]) (ltAdd ℚ_[ℓ] ℓ) = MvPowerSeries.expand ℓ hℓ0 (ltAdd ℚ_[ℓ] ℓ) := by
    simp [frobS, MvPowerSeries.map_id]
  rw [hfr] at hQ
  -- to `ℂ_ℓ`
  have hC : IsDivK ℓ (MvPowerSeries.expand ℓ hℓ0 (ltAdd ℂ_[ℓ] ℓ) - ltAdd ℂ_[ℓ] ℓ ^ ℓ) := fun n => by
    have h := hQ n
    rw [← map_ltAdd (algebraMap ℚ_[ℓ] ℂ_[ℓ]) hℓ, ← MvPowerSeries.map_expand, ← map_pow, ← map_sub,
      MvPowerSeries.coeff_map]
    have e : ‖(ℓ : ℂ_[ℓ])‖ = ‖(ℓ : ℚ_[ℓ])‖ := by
      rw [show (ℓ : ℂ_[ℓ]) = ((ℓ : ℚ_[ℓ]) : ℂ_[ℓ]) by norm_cast, PadicComplex.norm_extends']
    rw [e]
    exact (PadicComplex.norm_extends' ℓ _).trans_le h
  have h0 : ∀ i, MvPowerSeries.constantCoeff ((![U, V] : Fin 2 → MvPowerSeries σ ℂ_[ℓ]) i) = 0 := fun i => by
    fin_cases i
    · exact hU
    · exact hV
  have hψ := hasSubst_pair hU hV
  have h := hC.subst_int (ψ := ![U, V]) (fun i => by
    fin_cases i
    · exact hUi
    · exact hVi) h0
  rw [MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_pow hψ, expand_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_pow hℓ0) hψ] at h
  have e : (fun s => MvPowerSeries.subst ![U, V] ((MvPowerSeries.X s : MvPowerSeries (Fin 2) ℂ_[ℓ]) ^ ℓ)) =
      ![U ^ ℓ, V ^ ℓ] := by
    funext i
    fin_cases i <;> simp [MvPowerSeries.subst_pow hψ, MvPowerSeries.subst_X hψ]
  rw [e] at h
  exact h

/-- **The additivity defect of `serAB` in the first variable**:
`serAB(X ⊕ X′, Y) − serAB(X, Y) − serAB(X′, Y)`. -/
def serDef (ℓ : ℕ) [Fact ℓ.Prime] : MvPowerSeries (Fin 3) ℂ_[ℓ] :=
  MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2] (serAB ℓ) -
    MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 2] (serAB ℓ) -
    MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] (serAB ℓ)

/-- **`serAB` has no constant term.** -/
theorem constantCoeff_serAB : MvPowerSeries.constantCoeff (serAB ℓ) = 0 := by
  have h := coeff_serAB_of_not (ℓ := ℓ) (n := 0) (fun i j h => by
    rcases h with ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩⟩ <;> simp at h0 <;>
      exact absurd h0.symm (pow_ne_zero _ hℓp.out.ne_zero))
  simpa using h

/-- **The additivity defect has no constant term.** -/
theorem constantCoeff_serDef : MvPowerSeries.constantCoeff (serDef ℓ) = 0 := by
  have cX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have h : ∀ {U V : MvPowerSeries (Fin 3) ℂ_[ℓ]}, MvPowerSeries.constantCoeff U = 0 →
      MvPowerSeries.constantCoeff V = 0 → MvPowerSeries.constantCoeff (MvPowerSeries.subst ![U, V] (serAB ℓ)) = 0 :=
    fun hU hV => MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hU hV) (fun i => by
      fin_cases i
      · exact hU
      · exact hV) constantCoeff_serAB
  rw [serDef, map_sub, map_sub, h (constantCoeff_addP (cX 0) (cX 1)) (cX 2), h (cX 0) (cX 2), h (cX 1) (cX 2),
    sub_zero, sub_zero]

/-- **The Frobenius defect of the additivity defect is `ℓ`-divisible**:
`Δ(X^ℓ, X′^ℓ, Y^ℓ) + ℓΔ = M(X^ℓ ⊕ X′^ℓ, Y) − M((X ⊕ X′)^ℓ, Y) ≡ 0 (mod ℓ)`
(`subst_serAB_frob`, `mSer_typeM`, `isDivK_addP_pow_sub`). -/
theorem isDivK_expand_serDef :
    IsDivK ℓ (MvPowerSeries.expand ℓ hℓp.out.ne_zero (serDef ℓ) + (ℓ : ℂ_[ℓ]) • serDef ℓ) := by
  have hℓ0 := hℓp.out.ne_zero
  set X0 : MvPowerSeries (Fin 3) ℂ_[ℓ] := MvPowerSeries.X 0
  set X1 : MvPowerSeries (Fin 3) ℂ_[ℓ] := MvPowerSeries.X 1
  set X2 : MvPowerSeries (Fin 3) ℂ_[ℓ] := MvPowerSeries.X 2
  have c0 : MvPowerSeries.constantCoeff X0 = 0 := MvPowerSeries.constantCoeff_X 0
  have c1 : MvPowerSeries.constantCoeff X1 = 0 := MvPowerSeries.constantCoeff_X 1
  have c2 : MvPowerSeries.constantCoeff X2 = 0 := MvPowerSeries.constantCoeff_X 2
  have cp : ∀ U : MvPowerSeries (Fin 3) ℂ_[ℓ], MvPowerSeries.constantCoeff U = 0 →
      MvPowerSeries.constantCoeff (U ^ ℓ) = 0 := fun U hU => by rw [map_pow, hU, zero_pow hℓ0]
  set P := addP X0 X1
  have cP := constantCoeff_addP c0 c1
  set A := addP (X0 ^ ℓ) (X1 ^ ℓ)
  have cA := constantCoeff_addP (cp X0 c0) (cp X1 c1)
  have iP := isIntK_addP c0 c1 (isIntK_X 0) (isIntK_X 1)
  -- `Δ(X^ℓ, X′^ℓ, Y^ℓ)`
  have hexp : MvPowerSeries.expand ℓ hℓ0 (serDef ℓ) =
      MvPowerSeries.subst ![A, X2 ^ ℓ] (serAB ℓ) - MvPowerSeries.subst ![X0 ^ ℓ, X2 ^ ℓ] (serAB ℓ) -
        MvPowerSeries.subst ![X1 ^ ℓ, X2 ^ ℓ] (serAB ℓ) := by
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
    have hP : MvPowerSeries.expand ℓ hℓ0 P = A := by
      rw [show P = MvPowerSeries.subst ![X0, X1] (ltAdd ℂ_[ℓ] ℓ) from rfl,
        MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair c0 c1), hpair (hX 0) (hX 1)]
      rfl
    rw [serDef, map_sub, map_sub, MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair cP c2),
      MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair c0 c2), MvPowerSeries.expand_subst ℓ hℓ0 (hasSubst_pair c1 c2),
      hpair hP (hX 2), hpair (hX 0) (hX 2), hpair (hX 1) (hX 2)]
  have T1 := subst_serAB_frob cP c2
  have T2 := subst_serAB_frob c0 c2
  have T3 := subst_serAB_frob c1 c2
  have hLP : lgP ℓ P = lgP ℓ X0 + lgP ℓ X1 := lgP_addP c0 c1
  have hLA : lgP ℓ A = lgP ℓ (X0 ^ ℓ) + lgP ℓ (X1 ^ ℓ) := lgP_addP (cp X0 c0) (cp X1 c1)
  have hM : ∀ U V : MvPowerSeries (Fin 3) ℂ_[ℓ], MvPowerSeries.constantCoeff U = 0 →
      MvPowerSeries.constantCoeff V = 0 →
      MvPowerSeries.subst ![U, V] (mSer ℓ) = MvPowerSeries.subst ![U, V ^ ℓ] (serAB ℓ) - lgP ℓ U * lgP ℓ V := by
    intro U V hU hV
    have hψ := hasSubst_pair hU hV
    have hX : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1 ^ ℓ] :
        Fin 2 → MvPowerSeries (Fin 2) ℂ_[ℓ]) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hℓ0]
    rw [mSer, MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_mul hψ, MvPowerSeries.subst_comp_subst_apply hX hψ,
      subst_subst _ (MvPowerSeries.constantCoeff_X 0) hψ, subst_subst _ (MvPowerSeries.constantCoeff_X 1) hψ,
      MvPowerSeries.subst_X hψ, MvPowerSeries.subst_X hψ]
    congr 2
    funext i
    fin_cases i <;> simp [MvPowerSeries.subst_pow hψ, MvPowerSeries.subst_X hψ]
  have key : MvPowerSeries.expand ℓ hℓ0 (serDef ℓ) + (ℓ : ℂ_[ℓ]) • serDef ℓ =
      MvPowerSeries.subst ![A, X2] (mSer ℓ) - MvPowerSeries.subst ![P ^ ℓ, X2] (mSer ℓ) := by
    rw [hexp, hM A X2 cA c2, hM (P ^ ℓ) X2 (cp P cP) c2, serDef]
    simp only [smul_sub]
    linear_combination T1 - T2 - T3 + lgP ℓ (X2 ^ ℓ) * hLP + lgP ℓ X2 * hLA
  rw [key]
  exact isDivK_subst_sub mSer_typeM cA (cp P cP) c2
    (isIntK_addP (cp X0 c0) (cp X1 c1) ((isIntK_X 0).pow ℓ) ((isIntK_X 1).pow ℓ)) (iP.pow ℓ) (isIntK_X 2)
    (isDivK_addP_pow_sub c0 c1 (isIntK_X 0) (isIntK_X 1))

open Classical in
/-- **`serAB` over any field** (its coefficients `ℓ^{−(i+j+1)}` are rational). -/
def serABK (K : Type) [Field K] (ℓ : ℕ) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ Finset.range (n 0 + n 1 + 1), ∑ j ∈ Finset.range (n 0 + n 1 + 1),
    if i ≤ j ∧ ((n 0 = ℓ ^ (2 * i) ∧ n 1 = ℓ ^ (2 * j + 1)) ∨ (n 1 = ℓ ^ (2 * i) ∧ n 0 = ℓ ^ (2 * j + 1)))
    then ((ℓ : K) ^ (i + j + 1))⁻¹ else 0

omit hℓp in
/-- **`serABK` is carried to `serABK`** by field maps. -/
theorem map_serABK {K L : Type} [Field K] [Field L] (f : K →+* L) :
    MvPowerSeries.map f (serABK K ℓ) = serABK L ℓ := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change f (serABK K ℓ n) = serABK L ℓ n
  simp only [serABK, map_sum, apply_ite f, map_inv₀, map_pow, map_natCast, map_zero]

/-- **The additivity defect of `serAB` over any field.** -/
def serDefK (K : Type) [Field K] (ℓ : ℕ) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] (ltAdd K ℓ), MvPowerSeries.X 2]
      (serABK K ℓ) -
    MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 2] (serABK K ℓ) -
    MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] (serABK K ℓ)

/-- **`serDefK` over `ℂ_ℓ` is `serDef`.** -/
theorem serDefK_eq : serDefK ℂ_[ℓ] ℓ = serDef ℓ := rfl

omit hℓp in
/-- **`serDefK` is carried to `serDefK`** by field maps. -/
theorem map_serDefK {K L : Type} [Field K] [Field L] (f : K →+* L) (hℓ : 1 < ℓ) :
    MvPowerSeries.map f (serDefK K ℓ) = serDefK L ℓ := by
  have hX : ∀ {M : Type} [Field M] (i : Fin 3),
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) M) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hS : ∀ {M : Type} [Field M], MvPowerSeries.constantCoeff
      (MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] (ltAdd M ℓ) : MvPowerSeries (Fin 3) M) = 0 :=
    fun {M} _ => MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i <;> simp) (fun i => by fin_cases i <;> simp) (constantCoeff_ltAdd hℓ)
  have hpair : ∀ {M : Type} [Field M] {U V : MvPowerSeries (Fin 3) M}, MvPowerSeries.constantCoeff U = 0 →
      MvPowerSeries.constantCoeff V = 0 → MvPowerSeries.HasSubst (![U, V] : Fin 2 → MvPowerSeries (Fin 3) M) :=
    fun hU hV => MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i
      · exact hU
      · exact hV
  have hmapS : MvPowerSeries.map f
      (MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] (ltAdd K ℓ) : MvPowerSeries (Fin 3) K) =
      MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] (ltAdd L ℓ) := by
    rw [MvPowerSeries.map_subst (hpair (hX 0) (hX 1)), map_ltAdd f hℓ]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [serDefK, map_sub, map_sub, MvPowerSeries.map_subst (hpair hS (hX 2)),
    MvPowerSeries.map_subst (hpair (hX 0) (hX 2)), MvPowerSeries.map_subst (hpair (hX 1) (hX 2)), map_serABK,
    serDefK]
  congr 2 <;> [congr 1; congr 1; congr 1] <;> funext i <;> fin_cases i <;> simp [hmapS]

/-- **The explicit Gaussian is biadditive** (existence half of the classification, D1a′ item 5): for `c` in a
subfield `k` of `ℂ_ℓ` with a Frobenius lift `φ`, `φ(c) = −c` and `‖c‖ ≤ 1`,
`c·serAB(X ⊕ X′, Y) ≃ c·serAB(X, Y) + c·serAB(X′, Y)`. The Dwork defect of `c·Δ` is
`−c·(Δ(X^ℓ, X′^ℓ, Y^ℓ) + ℓΔ)`, `ℓ`-divisible by `isDivK_expand_serDef`; Dwork's lemma (`simeq_zero_of_dwork`). -/
theorem serAB_biadd (k : Subfield ℂ_[ℓ]) {φ : k →+* k} (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    {c : k} (hc : φ c = -c) (hc1 : ‖c‖ ≤ 1) :
    Simeq (MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2]
        (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ))
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2]
          (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) +
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2]
          (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ)) := by
  have hℓ := hℓp.out.one_lt
  have hℓ0 := hℓp.out.ne_zero
  have cX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[ℓ]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  rw [simeq_iff_sub]
  have e : MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2]
        (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) -
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2]
          (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) +
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2]
          (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ)) = MvPowerSeries.C (c : ℂ_[ℓ]) * serDef ℓ := by
    rw [MvPowerSeries.subst_mul (hasSubst_pair (constantCoeff_addP (cX 0) (cX 1)) (cX 2)),
      MvPowerSeries.subst_mul (hasSubst_pair (cX 0) (cX 2)), MvPowerSeries.subst_mul (hasSubst_pair (cX 1) (cX 2)),
      MvPowerSeries.subst_C, MvPowerSeries.subst_C, MvPowerSeries.subst_C, serDef]
    ring
  rw [e]
  set F : MvPowerSeries (Fin 3) k := MvPowerSeries.C c * serDefK k ℓ
  have hF : MvPowerSeries.map k.subtype F = MvPowerSeries.C (c : ℂ_[ℓ]) * serDef ℓ := by
    rw [map_mul, MvPowerSeries.map_C, map_serDefK _ hℓ, serDefK_eq]
    rfl
  have hF0 : MvPowerSeries.constantCoeff F = 0 := by
    have h0 := constantCoeff_serDef (ℓ := ℓ)
    have h := congrArg MvPowerSeries.constantCoeff hF
    rw [MvPowerSeries.constantCoeff_map,
      show MvPowerSeries.constantCoeff (MvPowerSeries.C (c : ℂ_[ℓ]) * serDef ℓ) = 0 by rw [map_mul, h0, mul_zero]] at h
    exact k.subtype_injective (by rw [h, map_zero])
  rw [← hF]
  refine simeq_zero_of_dwork k hφ hF0 fun n => ?_
  have hmap : MvPowerSeries.map k.subtype (frobS ℓ φ F - ℓ • F) =
      (MvPowerSeries.expand ℓ hℓ0 (serDef ℓ) + (ℓ : ℂ_[ℓ]) • serDef ℓ) * (-MvPowerSeries.C (c : ℂ_[ℓ])) := by
    have hφF : MvPowerSeries.map φ F = MvPowerSeries.C (-c) * serDefK k ℓ := by
      rw [map_mul, MvPowerSeries.map_C, hc, map_serDefK _ hℓ]
    rw [map_sub, map_nsmul, hF, frobS, RingHom.comp_apply, hφF]
    change MvPowerSeries.map k.subtype (MvPowerSeries.expand ℓ hℓ0 (MvPowerSeries.C (-c) * serDefK k ℓ)) - _ = _
    rw [MvPowerSeries.map_expand, map_mul, MvPowerSeries.map_C, map_serDefK _ hℓ, serDefK_eq, map_mul,
      MvPowerSeries.expand_C]
    simp only [nsmul_eq_mul, MvPowerSeries.smul_eq_C_mul, map_natCast, Subfield.coe_subtype, map_neg]
    ring
  have h := (isDivK_expand_serDef (ℓ := ℓ)).mul_isInt (isIntK_C (σ := Fin 3) (c := -(c : ℂ_[ℓ]))
    (by rw [norm_neg]; exact hc1)) n
  rw [map_neg] at h
  have hn := congrArg (MvPowerSeries.coeff n) hmap
  rw [MvPowerSeries.coeff_map] at hn
  change ‖((MvPowerSeries.coeff n (frobS ℓ φ F - ℓ • F) : k) : ℂ_[ℓ])‖ ≤ ‖((ℓ : k) : ℂ_[ℓ])‖
  rw [show ((ℓ : k) : ℂ_[ℓ]) = (ℓ : ℂ_[ℓ]) from map_natCast k.subtype ℓ]
  change ‖k.subtype (MvPowerSeries.coeff n (frobS ℓ φ F - ℓ • F))‖ ≤ _
  rw [hn]
  exact h

end SerABBiadd

/-! ## The translates `G_q` in Lubin–Tate coordinates: the analytic side -/

section TranslatesAnalytic

open EllipticAdd EllipticSigma EllipticDivisor ThetaNorm CMThetaOne Filter Topology

variable (Λ : PeriodPair)

/-- **`th0 = (σ*/z)·(z·G_t)`** near `0`: `σ*(z + t)e^{−(π/A)t̄z}/σ*(t) = sigE(z)·GqRes_t(z)`. -/
theorem th0L_eq_sigE_mul {q z : ℂ} (hq : q ∉ Λ.lattice) (hz : sigP Λ z ≠ 0) :
    th0L Λ q z = sigE Λ z * GqRes Λ q z := by
  have hsq := sigmaW_ne_zero Λ hq
  rw [th0L_eq, sigE, GqRes, etaR, sgStar, sgStar]
  have hne : Complex.exp (-s2 Λ * q ^ 2 / 2) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  simp only [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The Taylor series of `th0`** is `exp(logSig)·tay(z·G_t)`. -/
theorem tay_th0L {q : ℂ} (hq : q ∉ Λ.lattice) :
    tay (th0L Λ q) = expSig Λ.g₂ Λ.g₃ (s2 Λ) * tay (GqRes Λ q) := by
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), sigP Λ z ≠ 0 :=
    (differentiable_sigP Λ).continuous.continuousAt.eventually_ne (by rw [sigP_zero]; exact one_ne_zero)
  rw [tay_congr (hev.mono fun z hz => th0L_eq_sigE_mul Λ hq hz),
    tay_mul (analyticAt_sigE Λ 0) (analyticAt_GqRes Λ hq).1, tay_sigE]

/-- **`tay` of a finite sum.** -/
theorem tay_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    tay (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, tay (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tay_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [tay_add (hf a (Finset.mem_insert_self a s)) (Finset.analyticAt_fun_sum _ fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)), ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **`G_qᴺ` near `0`**: if `G_qᴺ = P(℘) + ℘′Q(℘)` with `2 deg P ≤ N`, `2 deg Q + 3 ≤ N`, then
`(z·G_q)ᴺ = Σ p_i z^{N−2i}(z²℘)^i + Σ q_i z^{N−2i−3}(z³℘′)(z²℘)^i`. -/
theorem GqRes_pow_eventually {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} {P Q : Polynomial ℂ}
    (hPQ : ∀ z ∉ Λ.lattice, Gq Λ q z ^ N = P.eval (Λ.weierstrassP z) + Λ.derivWeierstrassP z * Q.eval
      (Λ.weierstrassP z)) (hdP : 2 * P.natDegree ≤ N) (hdQ : 2 * Q.natDegree + 3 ≤ N) :
    (fun z => GqRes Λ q z ^ N) =ᶠ[𝓝 0] fun z =>
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ (N - 2 * i) * wpU Λ z ^ i +
        ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * z ^ (N - 2 * i - 3) * wpV Λ z * wpU Λ z ^ i := by
  obtain ⟨r, hr, hball⟩ := exists_ball_sdiff Λ
  have hU := analyticOnNhd_wpU Λ
  have hV := analyticAt_wpV Λ
  -- the two sides agree off `0`
  have hpunct : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → GqRes Λ q z ^ N =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ (N - 2 * i) * wpU Λ z ^ i +
        ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * z ^ (N - 2 * i - 3) * wpV Λ z * wpU Λ z ^ i := by
    intro z hzr hz0
    have hzl : z ∉ Λ.lattice := fun h => hball hzr ⟨h, hz0⟩
    rw [← mul_Gq Λ hz0, mul_pow, hPQ z hzl, Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range,
      Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : 2 * i ≤ N := by have := Finset.mem_range.1 hi; omega
      rw [← sq_mul_weierstrassP Λ hz0]
      obtain ⟨m, hm⟩ : ∃ m, N = m + 2 * i := ⟨N - 2 * i, by omega⟩
      rw [hm, show m + 2 * i - 2 * i = m by omega]
      ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : 2 * i + 3 ≤ N := by have := Finset.mem_range.1 hi; omega
      rw [← sq_mul_weierstrassP Λ hz0, ← cube_mul_derivWeierstrassP Λ hz0]
      obtain ⟨m, hm⟩ : ∃ m, N = m + 2 * i + 3 := ⟨N - 2 * i - 3, by omega⟩
      rw [hm, show m + 2 * i + 3 - 2 * i - 3 = m by omega]
      ring
  -- and at `0` by continuity
  have hL : ContinuousAt (fun z => GqRes Λ q z ^ N) 0 := ((analyticAt_GqRes Λ hq).1.pow N).continuousAt
  have hR : ContinuousAt (fun z =>
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ (N - 2 * i) * wpU Λ z ^ i +
        ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * z ^ (N - 2 * i - 3) * wpV Λ z * wpU Λ z ^ i) 0 := by
    have hU0 : AnalyticAt ℂ (wpU Λ) 0 := hU 0 (by simp)
    exact (Finset.analyticAt_fun_sum (𝕜 := ℂ) _ (fun i _ => by fun_prop)).add
      (Finset.analyticAt_fun_sum (𝕜 := ℂ) _ (fun i _ => by fun_prop)) |>.continuousAt
  have h0 : GqRes Λ q 0 ^ N =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (0 : ℂ) ^ (N - 2 * i) * wpU Λ 0 ^ i +
        ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * (0 : ℂ) ^ (N - 2 * i - 3) * wpV Λ 0 * wpU Λ 0 ^ i := by
    refine tendsto_nhds_unique (f := fun z => GqRes Λ q z ^ N) (l := 𝓝[≠] (0 : ℂ))
      (hL.tendsto.mono_left nhdsWithin_le_nhds) ?_
    refine (hR.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hr)] with z hz0 hzr
    exact (hpunct z hzr hz0).symm
  filter_upwards [Metric.ball_mem_nhds 0 hr] with z hzr
  by_cases hz0 : z = 0
  · rw [hz0]; exact h0
  · exact hpunct z hzr hz0

end TranslatesAnalytic

/-! ## The translates `G_q` in Lubin–Tate coordinates -/

section Translates

/-- **`(z·G_q)ᴺ`, formally**: `Σ p_i z^{N−2i}P^i + Σ q_i z^{N−2i−3}(−2R)P^i` (`P = z²℘`, `−2R = z³℘′`). -/
def gqForm {K : Type} [Field K] (a b : K) (p q : ℕ → K) (dP dQ N : ℕ) : K⟦X⟧ :=
  ∑ i ∈ Finset.range (dP + 1), C (p i) * X ^ (N - 2 * i) * wpF a b ^ i +
    ∑ i ∈ Finset.range (dQ + 1), C (q i) * X ^ (N - 2 * i - 3) * (-2 * wpR a b) * wpF a b ^ i

/-- **`gqForm` is carried along field maps.** -/
theorem map_gqForm {K L : Type} [Field K] [Field L] (f : K →+* L) (a b : K) (p q : ℕ → K) (dP dQ N : ℕ) :
    map f (gqForm a b p q dP dQ N) = gqForm (f a) (f b) (f ∘ p) (f ∘ q) dP dQ N := by
  simp only [gqForm, map_add, map_sum, map_mul, map_pow, map_C, map_X, map_neg, map_ofNat, map_wpF, map_wpR,
    Function.comp]

open EllipticAdd EllipticSigma EllipticDivisor ThetaNorm in
/-- **The Taylor series of `(z·G_q)ᴺ`** is `gqForm` (from `GqRes_pow_eventually`). -/
theorem tay_GqRes_pow (Λ : PeriodPair) {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} {P Q : Polynomial ℂ}
    (hPQ : ∀ z ∉ Λ.lattice, Gq Λ q z ^ N = P.eval (Λ.weierstrassP z) + Λ.derivWeierstrassP z * Q.eval
      (Λ.weierstrassP z)) (hdP : 2 * P.natDegree ≤ N) (hdQ : 2 * Q.natDegree + 3 ≤ N) :
    tay (GqRes Λ q) ^ N = gqForm Λ.g₂ Λ.g₃ P.coeff Q.coeff P.natDegree Q.natDegree N := by
  have hU : AnalyticAt ℂ (wpU Λ) 0 := (analyticAt_wpU Λ).1
  have hV := analyticAt_wpV Λ
  rw [← tay_pow (analyticAt_GqRes Λ hq).1, tay_congr (GqRes_pow_eventually Λ hq hPQ hdP hdQ),
    tay_add (Finset.analyticAt_fun_sum (𝕜 := ℂ) _ (fun i _ => by fun_prop))
      (Finset.analyticAt_fun_sum (𝕜 := ℂ) _ (fun i _ => by fun_prop)),
    tay_sum _ (fun i _ => by fun_prop), tay_sum _ (fun i _ => by fun_prop), gqForm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [tay_mul, tay_mul, tay_const, tay_pow (f := fun z => z) analyticAt_id, tay_id, tay_pow hU, tay_wpU] <;>
      fun_prop
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [tay_mul, tay_mul, tay_mul, tay_const, tay_pow (f := fun z => z) analyticAt_id, tay_id, tay_pow hU,
      tay_wpU, tay_wpV] <;> fun_prop

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **The translate in Lubin–Tate coordinates is an integral unit** (D1a′, item 2): for `q ∉ Λ` with
`G_qᴺ = P(℘) + ℘′Q(℘)` (`EllipticDivisor.Gq_pow_eq_poly`), `2 deg P ≤ N`, `2 deg Q + 3 ≤ N`, the coefficients of
`P`, `Q` integral under `ι` (the arithmetic input), `ℓ ∤ N`, integral `g₂`, `g₃` and the CM-b data `ε`, the series
`U(T) = εT·G_q(z(T)) = (log_LT(T)/T)⁻¹·(z·G_q)(z(T))` is integral with `U(0) = 1`. Its `N`-th power is
`εᴺ·(Σ p_i T^{N−2i}ρ^i − 2Σ q_i T^{N−2i−3}ρ^{i+1}A₁⁻¹)`, with `ρ = ε²T²℘(z(T))` and `t(z(T)) = T·A₁(T)` integral,
and the root is integral (`isIntK_of_pow_eq`): no Dwork. -/
theorem isInt_translate (hℓ2 : ℓ ≠ 2) (Λ : PeriodPair) (ι : ℂ →+* ℂ_[ℓ]) (h2 : ‖ι Λ.g₂‖ ≤ 1)
    (h3 : ‖ι Λ.g₃‖ ≤ 1) {ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1) (ht : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)))
    {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} (hN : ‖(N : ℂ_[ℓ])‖ = 1) {P Q : Polynomial ℂ}
    (hPQ : ∀ z ∉ Λ.lattice, EllipticDivisor.Gq Λ q z ^ N = P.eval (Λ.weierstrassP z) +
      Λ.derivWeierstrassP z * Q.eval (Λ.weierstrassP z)) (hdP : 2 * P.natDegree ≤ N)
    (hdQ : 2 * Q.natDegree + 3 ≤ N) (hPi : ∀ i, ‖ι (P.coeff i)‖ ≤ 1) (hQi : ∀ i, ‖ι (Q.coeff i)‖ ≤ 1) :
    IsInt ((logLTDivX ℂ_[ℓ] ℓ)⁻¹ * (map ι (tay (EllipticDivisor.GqRes Λ q))).subst (zLT ℓ ε)) ∧
      constantCoeff ((logLTDivX ℂ_[ℓ] ℓ)⁻¹ * (map ι (tay (EllipticDivisor.GqRes Λ q))).subst (zLT ℓ ε)) = 1 := by
  have hℓ := hℓp.out.one_lt
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  set a := ι Λ.g₂
  set b := ι Λ.g₃
  have hODE := (weierODE_lattice Λ).map ι
  set z := zLT ℓ ε with hzdef
  have hz0 : constantCoeff z = 0 := constantCoeff_zLT hℓ ε
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  set lam := logLTDivX ℂ_[ℓ] ℓ
  have hlam0 : constantCoeff lam = 1 := constantCoeff_logLTDivX ℓ
  have hlaml : lam * lam⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hlam0]; exact one_ne_zero)
  set g : ℂ_[ℓ]⟦X⟧ := (map ι (tay (EllipticDivisor.GqRes Λ q))).subst z
  set U := lam⁻¹ * g
  -- the constant term
  have hg0 : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hzs, finsum_eq_single _ 0]
    · simp [coeff_tay, (EllipticDivisor.analyticAt_GqRes Λ hq).2]
    · intro d hd
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, hz0, zero_pow hd, smul_zero]
  have hU0 : constantCoeff U = 1 := by
    rw [map_mul, hg0, mul_one, PowerSeries.constantCoeff_inv, hlam0, inv_one]
  refine ⟨?_, hU0⟩
  -- `t(z) = T·A₁`, `ρ`, and the relations of `P(z)`, `R(z)` with them
  set A := (tSer a b).subst z
  have hA0 : constantCoeff A = 0 := constantCoeff_subst_eq_zero hz0 _ (constantCoeff_tSer a b)
  set A₁ : ℂ_[ℓ]⟦X⟧ := mk fun n => coeff (n + 1) A
  have hA : A = X * A₁ := by
    ext n
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, hA0, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X,
        zero_mul]
    · rw [coeff_succ_X_mul, coeff_mk]
  have hA₁i : IsInt A₁ := fun n => by rw [coeff_mk]; exact ht (n + 1)
  have hA₁0 : constantCoeff A₁ = ε := by
    have h1 := congrArg (coeff 1) hA
    have h2 : coeff 1 ((tSer a b).subst z) = ε := by
      rw [coeff_one_subst hz0, coeff_one_tSer, hzdef, zLT, coeff_C_mul, coeff_one_logLT, one_mul, mul_one]
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h1
    rw [← h1]
    exact h2
  set ρ := rhoLT ℓ a b ε
  have hρi := isInt_rhoLT hℓ2 h2 h3 hε hODE ht
  set Pz := (wpF a b).subst z
  set Rz := (wpR a b).subst z
  have hz : z = C ε * X * lam := by rw [hzdef, zLT, ← X_mul_logLTDivX hℓ, mul_assoc]
  have hPz : Pz = C ε ^ 2 * lam ^ 2 * ρ := by
    have h : X ^ 2 * Pz = z ^ 2 * ρ := X_sq_mul_wpF_subst hℓ hε0 a b
    rw [hz] at h
    refine mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) ?_
    linear_combination h
  have hR0 : constantCoeff (wpR a b) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, wpR, coeff_mk]; simp
  have hRz : A₁ * Rz = C ε ^ 3 * lam ^ 3 * ρ := by
    have htR : tSer a b * wpR a b = X * wpF a b := by
      rw [tSer_eq, mul_assoc, mul_assoc, PowerSeries.inv_mul_cancel _ hR0, mul_one]
    have h : A * Rz = z * Pz := by
      have := congrArg (PowerSeries.subst z) htR
      rwa [subst_mul hzs, subst_mul hzs, subst_X hzs] at this
    rw [hA, hPz, hz] at h
    refine mul_left_cancel₀ X_ne_zero ?_
    linear_combination h
  -- `g^N = gqForm(z)`
  have hgN : g ^ N = (gqForm a b (ι ∘ P.coeff) (ι ∘ Q.coeff) P.natDegree Q.natDegree N).subst z := by
    rw [← subst_pow hzs, ← map_pow, tay_GqRes_pow Λ hq hPQ hdP hdQ, map_gqForm]
  have hform : (gqForm a b (ι ∘ P.coeff) (ι ∘ Q.coeff) P.natDegree Q.natDegree N).subst z =
      ∑ i ∈ Finset.range (P.natDegree + 1), C (ι (P.coeff i)) * z ^ (N - 2 * i) * Pz ^ i +
        ∑ i ∈ Finset.range (Q.natDegree + 1), C (ι (Q.coeff i)) * z ^ (N - 2 * i - 3) * (-2 * Rz) * Pz ^ i := by
    rw [gqForm, ← coe_substAlgHom hzs]
    simp only [map_add, map_sum, map_mul, map_pow, map_neg, map_ofNat, coe_substAlgHom, subst_X hzs, subst_C]
    rfl
  -- the `N`-th power of `U`
  set W := ∑ i ∈ Finset.range (P.natDegree + 1), C (ι (P.coeff i)) * C ε ^ N * X ^ (N - 2 * i) * ρ ^ i +
    ∑ i ∈ Finset.range (Q.natDegree + 1), C (ι (Q.coeff i)) * (-2) * C ε ^ N * X ^ (N - 2 * i - 3) * ρ ^ (i + 1) *
      A₁⁻¹
  have hA₁ne : constantCoeff A₁ ≠ 0 := by rw [hA₁0]; exact hε0
  have hA₁inv : A₁ * A₁⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hA₁ne
  have hUN : U ^ N = W := by
    have hne : lam ^ N * A₁ ≠ 0 := mul_ne_zero (pow_ne_zero _ (fun h => by
      have := congrArg constantCoeff h; rw [hlam0, map_zero] at this; exact one_ne_zero this))
      (fun h => hA₁ne (by rw [h, map_zero]))
    refine mul_right_cancel₀ hne ?_
    have hL : U ^ N * (lam ^ N * A₁) = g ^ N * A₁ := by
      rw [show U ^ N * (lam ^ N * A₁) = g ^ N * A₁ * (lam * lam⁻¹) ^ N by simp only [U]; ring, hlaml, one_pow, mul_one]
    rw [hL, hgN, hform, add_mul, Finset.sum_mul, Finset.sum_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : 2 * i ≤ N := by have := Finset.mem_range.1 hi; omega
      obtain ⟨m, hm⟩ : ∃ m, N = m + 2 * i := ⟨N - 2 * i, by omega⟩
      rw [hm, show m + 2 * i - 2 * i = m by omega, hz, hPz]
      ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : 2 * i + 3 ≤ N := by have := Finset.mem_range.1 hi; omega
      obtain ⟨m, hm⟩ : ∃ m, N = m + 2 * i + 3 := ⟨N - 2 * i - 3, by omega⟩
      rw [hm, show m + 2 * i + 3 - 2 * i - 3 = m by omega, hz, hPz]
      linear_combination (C (ι (Q.coeff i)) * (-2) * (C ε * X * lam) ^ m * (C ε ^ 2 * lam ^ 2 * ρ) ^ i) * hRz +
        -(C (ι (Q.coeff i)) * (-2) * C ε ^ (m + 2 * i + 3) * X ^ m * ρ ^ (i + 1) * lam ^ (m + 2 * i + 3)) * hA₁inv
  -- integrality of `W`, and the root
  have hA₁invi : IsInt A₁⁻¹ := by
    have hv1 : MvPowerSeries.constantCoeff ((C ε⁻¹ * A₁ : ℂ_[ℓ]⟦X⟧) : MvPowerSeries Unit ℂ_[ℓ]) = 1 := by
      change constantCoeff (C ε⁻¹ * A₁) = 1
      rw [map_mul, constantCoeff_C, hA₁0, inv_mul_cancel₀ hε0]
    have hi := ((isInt_C (by rw [norm_inv, hε, inv_one])).mul hA₁i).isIntK.inv hv1 |>.isInt
    have e : A₁⁻¹ = C ε⁻¹ * (C ε⁻¹ * A₁)⁻¹ := by
      rw [PowerSeries.inv_eq_iff_mul_eq_one hA₁ne]
      have h1 : (C ε⁻¹ * A₁)⁻¹ * (C ε⁻¹ * A₁) = 1 := PowerSeries.inv_mul_cancel _ (by
        change MvPowerSeries.constantCoeff ((C ε⁻¹ * A₁ : ℂ_[ℓ]⟦X⟧) : MvPowerSeries Unit ℂ_[ℓ]) ≠ 0
        rw [hv1]; exact one_ne_zero)
      linear_combination h1
    rw [e]
    exact (isInt_C (by rw [norm_inv, hε, inv_one])).mul hi
  have h2i : IsInt (-2 : ℂ_[ℓ]⟦X⟧) := by
    rw [show (-2 : ℂ_[ℓ]⟦X⟧) = C (-2) by rw [map_neg, map_ofNat]]
    exact isInt_C (by rw [norm_neg]; exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℂ_[ℓ] 2)
  have hWi : IsInt W := by
    refine IsInt.add (isInt_sum _ fun i _ => ?_) (isInt_sum _ fun i _ => ?_)
    · exact (((isInt_C (hPi i)).mul ((isInt_C hε.le).pow N)).mul (isInt_X_pow _)).mul (hρi.pow i)
    · exact (((((isInt_C (hQi i)).mul h2i).mul ((isInt_C hε.le).pow N)).mul (isInt_X_pow _)).mul
          (hρi.pow (i + 1))).mul hA₁invi
  exact (isIntK_of_pow_eq hN hWi.isIntK (by
    change ‖constantCoeff U‖ = 1
    rw [hU0, norm_one]) (by exact hUN)).isInt

/-- **`th0 = exp(−ph)·U` in Lubin–Tate coordinates**: the Taylor series of `th0` at the point `t`, carried to `ℂ_ℓ`
and composed with `z(T) = ε·log_LT(T)`, is `exp(−ph(T))·U_t(T)` with `U_t = εT·G_t(z(T))` the translate of
`isInt_translate` (`th0 = σ*·G_t`, `εT·exp(−ph) = σ*(z(T))`). -/
theorem th0_eq_exp_neg_ph_mul (Λ : PeriodPair) (ι : ℂ →+* ℂ_[ℓ]) {t : ℂ} (ht : t ∉ Λ.lattice) {ε : ℂ_[ℓ]}
    (hε : ε ≠ 0) :
    (map ι (tay (CMThetaOne.th0L Λ t))).subst (zLT ℓ ε) =
      (exp ℂ_[ℓ]).subst (-ph ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) *
        ((logLTDivX ℂ_[ℓ] ℓ)⁻¹ * (map ι (tay (EllipticDivisor.GqRes Λ t))).subst (zLT ℓ ε)) := by
  have hℓ := hℓp.out.one_lt
  set z := zLT ℓ ε with hzdef
  have hzs : HasSubst z := HasSubst.of_constantCoeff_zero' (constantCoeff_zLT hℓ ε)
  set lam := logLTDivX ℂ_[ℓ] ℓ
  have hlaml : lam * lam⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_logLTDivX]; exact one_ne_zero)
  set E := expSig (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ))
  -- `exp(−ph) = (log_LT(T)/T)·E(z(T))`
  have hexp : (exp ℂ_[ℓ]).subst (-ph ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) = lam * E.subst z := by
    have hzs' : HasSubst (C ε * logLT ℂ_[ℓ] ℓ) := HasSubst.of_constantCoeff_zero' (constantCoeff_C_mul_logLT hℓ ε)
    have h : C ε * X * (exp ℂ_[ℓ]).subst (-ph ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) = z * E.subst z := by
      have h0 := C_mul_X_mul_exp_neg_ph hℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε
      rw [sigF, subst_mul hzs', subst_X hzs'] at h0
      exact h0
    have hz' : z = C ε * X * lam := by rw [hzdef, zLT, ← X_mul_logLTDivX hℓ, mul_assoc]
    refine mul_left_cancel₀ (mul_ne_zero (by rwa [Ne, map_eq_zero_iff C (C_injective)]) X_ne_zero) ?_
    linear_combination h + E.subst z * hz'
  rw [tay_th0L Λ ht, map_mul, map_expSig, subst_mul hzs, hexp]
  change E.subst z * _ = lam * E.subst z * (lam⁻¹ * _)
  linear_combination (-(E.subst z * (map ι (tay (EllipticDivisor.GqRes Λ t))).subst z)) * hlaml

end Translates

/-! ## The classification `be ≃ c·serAB`: the uniqueness half as a statement -/

section Classification

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **The Teichmüller hermitian condition** on a two-variable series: `B(ζX, Y) ≃ B(X, ζ^ℓY)` for every
`ζ^{ℓ²} = ζ` (the `[ζ]` act by `T ↦ ζT` in Lubin–Tate coordinates; `ζ̄ = ζ^ℓ`). -/
def IsHerm (B : MvPowerSeries (Fin 2) ℂ_[ℓ]) : Prop :=
  ∀ ζ : ℂ_[ℓ], ζ ^ (ℓ ^ 2) = ζ → Simeq (MvPowerSeries.rescale ![ζ, 1] B) (MvPowerSeries.rescale ![1, ζ ^ ℓ] B)

/-- **`c·serAB` is hermitian**, exactly (`coeff_serAB_herm`). -/
theorem isHerm_C_mul_serAB (c : ℂ_[ℓ]) : IsHerm (MvPowerSeries.C c * serAB ℓ) := by
  intro ζ hζ
  have e : MvPowerSeries.rescale ![ζ, 1] (MvPowerSeries.C c * serAB ℓ) =
      MvPowerSeries.rescale ![1, ζ ^ ℓ] (MvPowerSeries.C c * serAB ℓ) := by
    ext n
    rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_rescale, Finsupp.prod_fintype _ _ (fun i => by simp),
      Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two, Fin.prod_univ_two, MvPowerSeries.coeff_C_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one, one_mul]
    have := coeff_serAB_herm hζ n
    linear_combination c * this
  rw [e]
  exact Simeq.refl _

/-- **The uniqueness half of the classification** (a statement): over a subfield `k` of `ℂ_ℓ` with a Frobenius
lift `φ`, every symmetric, hermitian series with coefficients in `k`, without constant term and biadditive up to `≃`
on the height-2 Lubin–Tate group, is `≃ c·serAB` for some `c ∈ k` with `φ(c) = −c`, `‖c‖ ≤ 1` (the hermitian
condition kills `b·log_LT(X)log_LT(Y)`). `serAB_biadd`, `coeff_serAB_swap` and `isHerm_C_mul_serAB` show that every
such `c·serAB` satisfies the hypotheses. It fails for some non-closed `k` (the constant `c` is an `ℓ`-adic limit);
`CMFormalGauss.gaussClass_of_isClosed` proves it for closed `k` containing a Teichmüller `ζ` with `‖ζ − ζ^ℓ‖ = 1`,
in particular for `unramC ℓ` (`gaussClass_unramC`). -/
def GaussClass (k : Subfield ℂ_[ℓ]) (φ : k →+* k) : Prop :=
  (∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) →
  ∀ B : MvPowerSeries (Fin 2) ℂ_[ℓ], (∀ n, MvPowerSeries.coeff n B ∈ k) → MvPowerSeries.constantCoeff B = 0 →
    MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] B = B →
    Simeq (MvPowerSeries.subst ![addP (MvPowerSeries.X 0) (MvPowerSeries.X 1), MvPowerSeries.X 2] B)
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2] B +
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[ℓ]), MvPowerSeries.X 2] B) →
    IsHerm B → ∃ c : k, φ c = -c ∧ ‖c‖ ≤ 1 ∧ Simeq B (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ)

/-- **The classification `be ≃ c·serAB`** (D1a′, item 5), from the uniqueness statement `GaussClass` and the
hermitian property of `be` (the CM sesquilinearity `be([α]X, Y) ≃ be(X, [ᾱ]Y)`, for the Teichmüller `α`): `be`
is symmetric (`be_symm`), biadditive (`be_biadd`) and has its coefficients in `k` when `g₂, g₃, s₂, ε` lie there. -/
theorem be_classification (k : Subfield ℂ_[ℓ]) {φ : k →+* k} (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖)
    (hG : GaussClass k φ) (hℓ2 : ℓ ≠ 2) {a b s ε : ℂ_[ℓ]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hε : ‖ε‖ = 1)
    (hAdd : AddLaw a b s) (hODE : WeierODE a b) (ht : IsInt ((tSer a b).subst (zLT ℓ ε))) (hak : a ∈ k)
    (hbk : b ∈ k) (hsk : s ∈ k) (hεk : ε ∈ k) (hH : IsHerm (be ℓ a b s ε)) :
    ∃ c : k, φ c = -c ∧ ‖c‖ ≤ 1 ∧ Simeq (be ℓ a b s ε) (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) := by
  have hℓ := hℓp.out.one_lt
  have hk : ∀ n, MvPowerSeries.coeff n (be ℓ a b s ε) ∈ k := fun n => by
    set be' := be ℓ (⟨a, hak⟩ : k) ⟨b, hbk⟩ ⟨s, hsk⟩ ⟨ε, hεk⟩
    have h : MvPowerSeries.map k.subtype be' = be ℓ a b s ε := map_be k.subtype hℓ _ _ _ _
    rw [← h, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n be').2
  exact hG hφ _ hk (constantCoeff_be hℓ a b s ε) (be_symm a b s ε) (be_biadd hℓ2 ha hb hε hAdd hODE ht) hH

/-- **CM-a′ (Weber; Shimura reciprocity)**: the `Δ = 1` invariants lie in `K^ur` at `ℓ ≥ 5`, `ℓ ∤ d` (D1Spec's
`CMUnramified`, an input). -/
def CMUnramified : Prop :=
  ∀ (d : ℕ) (Λ : PeriodPair), Squarefree d → d % 4 = 3 → HasCM d Λ → Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ¬ ℓ ∣ d → ∀ ι : ℂ ≃+* ℂ_[ℓ], ι Λ.g₂ ∈ unramC ℓ ∧ ι Λ.g₃ ∈ unramC ℓ

/-- **CM-d, strengthened (Masser; Katz)**: Masser's `s₂` of the `Δ = 1` CM lattice lies in `K^ur` and is integral at
`ℓ ≥ 5`, `ℓ ∤ d` (an input; `CMThetaOne.CMs2` asks integrality only). -/
def CMs2Unram : Prop :=
  ∀ (d : ℕ) (Λ : PeriodPair), Squarefree d → d % 4 = 3 → HasCM d Λ → Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ¬ ℓ ∣ d → ∀ ι : ℂ ≃+* ℂ_[ℓ],
      ι (ThetaNorm.s2 Λ) ∈ unramC ℓ ∧ ‖ι (ThetaNorm.s2 Λ)‖ ≤ 1

/-- **The classification for the CM curve** (D1a′, item 5, conditional): with CM-b, CM-c, CM-a′ and the
strengthened CM-d, a Frobenius lift `φ` on `K^ur`, the uniqueness statement `GaussClass` and the hermitian property
of `be` (CM sesquilinearity), the Lubin–Tate unit `ε` of CM-b has `be ≃ c·serAB` with `φ(c) = −c`, `‖c‖ ≤ 1`. -/
theorem be_classification_cm (hb : CMInertLubinTate) (hj : CMThetaOne.CMjIntegral) (hu : CMUnramified)
    (hs : CMs2Unram) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3) (hcm : HasCM d Λ)
    (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d) (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ))
    (ι : ℂ ≃+* ℂ_[ℓ]) {φ : unramC ℓ →+* unramC ℓ}
    (hφ : ∀ x : unramC ℓ, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : unramC ℓ)‖) (hG : GaussClass (unramC ℓ) φ)
    (hH : ∀ ε : ℂ_[ℓ], ε ∈ unramC ℓ → ‖ε‖ = 1 → IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) →
      IsHerm (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε)) :
    ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∃ c : unramC ℓ, φ c = -c ∧ ‖c‖ ≤ 1 ∧
      Simeq (be ℓ (ι Λ.g₂) (ι Λ.g₃) (ι (ThetaNorm.s2 Λ)) ε) (MvPowerSeries.C (c : ℂ_[ℓ]) * serAB ℓ) := by
  obtain ⟨ε, hεu, hε, ht⟩ := hb d Λ hd hd4 hcm hΔ ℓ h5 hdℓ hin ι
  obtain ⟨h2, h3⟩ := norm_g_le_one hj hd hd4 hcm hΔ h5 ι
  obtain ⟨h2u, h3u⟩ := hu d Λ hd hd4 hcm hΔ ℓ h5 hdℓ ι
  obtain ⟨hsu, -⟩ := hs d Λ hd hd4 hcm hΔ ℓ h5 hdℓ ι
  obtain ⟨hAdd, hODE⟩ := addLaw_weierODE_map Λ (ι : ℂ →+* ℂ_[ℓ])
  have hti : IsInt ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (zLT ℓ ε)) := fun n => (ht n).2
  exact ⟨ε, hεu, hε, be_classification (unramC ℓ) hφ hG (by omega) h2 h3 hε hAdd hODE hti h2u h3u hsu hεu
    (hH ε hεu hε hti)⟩

end Classification

end

end CMFormalBiadd
