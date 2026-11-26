import Mathlib

/-!
# The formal group of a CM curve at an inert prime: the Lubin–Tate exponential and the formal Gaussian

D1a′ of the D1 plan, the algebraic part: the Lubin–Tate exponential and its valuations, the divided-power
comparison for the `Δ = 1` model in Lubin–Tate coordinates, the Gaussian equivalence `≃` with Dwork's lemma, and
the explicit Gaussian pairing `serAB` with its Frobenius defect.

**The Lubin–Tate exponential.** `log_LT(T) = Σ_j T^{ℓ^{2j}}/ℓ^j` (`logLT`) has the compositional inverse
`e = log_LT^{−1}` (`expLT`, Mathlib's `substInvOfIsUnit`). For `π^{ℓ²−1} = ℓ` the rescaled logarithm
`log_LT(πT)/π = g(T) = Σ_j ℓ^{c_j}T^{ℓ^{2j}}`, `c_j = (ℓ^{2j} − 1)/(ℓ² − 1) − j ≥ 0`, has integer coefficients
(`rescale_logLT`), so its inverse `h` (`expLTInt`) does too, and `e(T) = π·h(T/π)` by uniqueness of inverses
(`expLT_eq`). Hence `π^{N−1}·e_N = h_N ∈ ℤ` (`pow_mul_coeff_expLT`): in `ℂ_ℓ`, `v(e_N) ≥ −(N − 1)/(ℓ² − 1)`
(`norm_coeff_expLT_le`). Comparing the two roots `π` and `ζπ` gives `e_N = 0` unless `N ≡ 1 (mod ℓ² − 1)`
(`coeff_expLT_eq_zero`).

**Divided powers.** For `F` integral and `‖u‖ ≤ 1`, `G(z) = F(e(uz))` has `G(πz) = F(π·B(z))` with `B` integral, so
`v(G_N) ≥ −(N − 1)/(ℓ² − 1)` for `N ≥ 1` (`norm_pow_mul_coeff_subst_expLT_le`, `norm_coeff_subst_expLT_le`). With
Legendre's formula `v(N!) − (N − 1)/(ℓ² − 1) = N·γ_ℓ − s_ℓ(N)/(ℓ − 1) + 1/(ℓ² − 1)`, `γ_ℓ = ℓ/(ℓ² − 1)`
(`padicValNat_factorial_sub`), the jets `N!·G_N` gain this much over divided powers
(`norm_factorial_mul_coeff_subst_expLT_le`).

**The CM curve** (input CM-b, `CMInertLubinTate`, taken as a hypothesis). If `t(ε·log_LT(T))` is integral with
`‖ε‖ = 1`, its inverse `T(t)` is integral and the formal logarithm of the model is `z(t) = ε·log_LT(T(t))`
(`exists_ltCoord`). Every series `P` integral in the formal parameter then has `z`-expansion `P(t(z))` with the
bounds above (`norm_coeff_subst_tSer_le`, `norm_factorial_mul_coeff_subst_tSer_le`); for the CM lattice at an inert
`ℓ ≥ 5` this is `cm_inert_jets`.

**The Gaussian equivalence.** `f ≃ g` (`Simeq`, D1Spec's) asks equal constant terms and `exp(f − g)` integral
(`expMv`, `IntS`). `expMv` is `exp` as a substitution (`expMv_eq_subst`), additive (`exp_subst_add`, from the
two-variable functional equation `exp_subst_add_two`), so `≃` is an equivalence relation compatible with sums,
negation (`Simeq.refl`, `Simeq.symm`, `Simeq.trans`, `Simeq.add`, `Simeq.neg`) and integral substitution
(`Simeq.subst`), and `ℓ·(integral) ≃ 0` (`simeq_smul_ell`).

**Dwork's lemma** (`dwork`). Let `φ` be a ring endomorphism of the coefficients lifting Frobenius on the unit ball
(`‖φx − x^ℓ‖ ≤ ‖ℓ‖`), the norm on `ℕ` being `ℓ`-adic, and `F^φ(X^ℓ)` the Frobenius of a series (`frobS`). If `f`
has no constant term and `f^φ(X^ℓ) − ℓf` is `ℓ`-divisible, then `exp(f)` is integral. The proof:
`exp(f^φ(X^ℓ) − ℓf) ≡ 1 (mod ℓ)` (`isDivK_exp_sub_one`), Frobenius commutes with `exp` (`frobS_exp_subst`), and
the main lemma (`isIntK_of_frobS_eq`): `F^φ(X^ℓ) = F^ℓ·V` with `V ≡ 1` forces `F` integral, by induction on the
total degree, comparing the degree-`n` coefficient of both sides with the Frobenius congruence
`P^φ(X^ℓ) ≡ P^ℓ (mod ℓ)` for the truncation `P` of `F` (`isDivK_frobS_sub_pow`). In `ℂ_ℓ` this is the criterion
`simeq_zero_of_dwork` for series over a subfield with a Frobenius lift.

**The explicit Gaussian** `serAB = Σ_{i ≤ j}(X^{ℓ^{2i}}Y^{ℓ^{2j+1}} + Y^{ℓ^{2i}}X^{ℓ^{2j+1}})/ℓ^{i+j+1}` (D1Spec's).
Its coefficients are `ℓ^{−(i+j+1)}` on the support pairs and `0` elsewhere (`coeff_serAB_of`, `coeff_serAB_of_not`);
it is symmetric (`coeff_serAB_swap`) and hermitian for the Teichmüller action, `serAB(ζX, Y) = serAB(X, ζ^ℓY)`
for `ζ^{ℓ²} = ζ` (`coeff_serAB_herm`). Its Frobenius defect is a product of logarithms (`expand_serAB_add_smul`):
`serAB(X^ℓ, Y^ℓ) + ℓ·serAB(X, Y) = log_LT(X^ℓ)·log_LT(Y) + log_LT(X)·log_LT(Y^ℓ)`, so for `c̄ = −c` the Dwork
defect of `c·serAB` is `−c·(log_LT(X^ℓ)log_LT(Y) + log_LT(X)log_LT(Y^ℓ))`.

**Main results:** `expLT_eq`, `pow_mul_coeff_expLT`, `coeff_expLT_eq_zero`, `norm_coeff_expLT_le`,
`norm_coeff_subst_expLT_le`, `norm_factorial_mul_coeff_subst_expLT_le`, `exists_ltCoord`, `cm_inert_jets`,
`Simeq.subst`, `simeq_smul_ell`, `dwork`, `simeq_zero_of_dwork`, `coeff_serAB_herm`, `expand_serAB_add_smul`; and,
as API for the many-variable theory, `expLT_subst_logLT`, `Simeq.neg`, `simeq_iff_sub`.
-/

namespace CMFormalInert

open PowerSeries

noncomputable section

/-! ## The closed unit ball and integral series -/

section Ball

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The closed unit ball** `{x : ‖x‖ ≤ 1}` of a nonarchimedean normed field, as a subring. -/
def ball1 : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    have ha' : ‖a‖ ≤ 1 := ha
    have hb' : ‖b‖ ≤ 1 := hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg b]
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

variable {K}

/-- **Products of numbers at most one**, the second nonnegative. -/
theorem mul_le_one_of_le {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hb0 : 0 ≤ b := by positivity) : a * b ≤ 1 := by
  nlinarith

/-- **Integral series**: every coefficient lies in the closed unit ball. -/
def IsInt (f : K⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ 1

/-- **Integral series are the series over the unit ball.** -/
theorem isInt_iff (f : K⟦X⟧) : IsInt f ↔ ∃ g : (ball1 K)⟦X⟧, map (ball1 K).subtype g = f := by
  constructor
  · intro h
    exact ⟨mk fun n => ⟨coeff n f, h n⟩, by ext n; simp⟩
  · rintro ⟨g, rfl⟩ n
    rw [coeff_map]
    exact (coeff n g).2

/-- **Products of integral series are integral.** -/
theorem IsInt.mul {f g : K⟦X⟧} (hf : IsInt f) (hg : IsInt g) : IsInt (f * g) := by
  obtain ⟨f', rfl⟩ := (isInt_iff f).1 hf
  obtain ⟨g', rfl⟩ := (isInt_iff g).1 hg
  exact (isInt_iff _).2 ⟨f' * g', map_mul _ _ _⟩

/-- **Substitution keeps integrality** (into an integral series without constant term). -/
theorem IsInt.subst {f a : K⟦X⟧} (hf : IsInt f) (ha : IsInt a) (ha0 : constantCoeff a = 0) :
    IsInt (f.subst a) := by
  obtain ⟨f', rfl⟩ := (isInt_iff f).1 hf
  obtain ⟨a', rfl⟩ := (isInt_iff a).1 ha
  have h0 : constantCoeff a' = 0 := by
    apply Subtype.ext
    have h := ha0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map] at h
    simpa [coeff_zero_eq_constantCoeff_apply] using h
  refine (isInt_iff _).2 ⟨f'.subst a', ?_⟩
  exact map_subst (HasSubst.of_constantCoeff_zero' h0) f'

/-- **The inverse of an integral series is integral** when its linear coefficient is a unit of the ball. -/
theorem IsInt.substInv {P : K⟦X⟧} (hP : IsInt P) (hP0 : constantCoeff P = 0) (hP1 : ‖coeff 1 P‖ = 1)
    (hu : IsUnit (coeff 1 P)) : IsInt (P.substInvOfIsUnit hu) := by
  obtain ⟨P', rfl⟩ := (isInt_iff P).1 hP
  have h0 : constantCoeff P' = 0 := by
    apply Subtype.ext
    have h := hP0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map] at h
    simpa [coeff_zero_eq_constantCoeff_apply] using h
  have hc : ((coeff 1 P' : ball1 K) : K) = coeff 1 (map (ball1 K).subtype P') := by rw [coeff_map]; rfl
  have hne : ((coeff 1 P' : ball1 K) : K) ≠ 0 := by
    intro h; rw [hc] at h; rw [h, norm_zero] at hP1; exact zero_ne_one hP1
  have hu' : IsUnit (coeff 1 P') := by
    have hm : ((coeff 1 P' : ball1 K) : K)⁻¹ ∈ ball1 K := by
      change ‖((coeff 1 P' : ball1 K) : K)⁻¹‖ ≤ 1
      rw [norm_inv, hc, hP1, inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
  have hQ0 : constantCoeff (map (ball1 K).subtype (P'.substInvOfIsUnit hu')) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_substInvOfIsUnit, map_zero]
  have heq : map (ball1 K).subtype (P'.substInvOfIsUnit hu') = (map (ball1 K).subtype P').substInvOfIsUnit hu := by
    apply eq_substInvOfIsUnit_of_subst_eq_X _ hP0 hu (HasSubst.of_constantCoeff_zero' hQ0)
    have h2 : map (ball1 K).subtype (P'.subst (P'.substInvOfIsUnit hu')) =
        (map (ball1 K).subtype P').subst (map (ball1 K).subtype (P'.substInvOfIsUnit hu')) :=
      map_subst (HasSubst.substInvOfIsUnit _ _) _
    rw [← h2, subst_substInvOfIsUnit_right _ h0, map_X]
  rw [← heq]
  exact (isInt_iff _).2 ⟨_, rfl⟩

end Ball

/-! ## The Lubin–Tate logarithm and exponential -/

section LT

open Classical in
/-- **The height-2 Lubin–Tate logarithm** `log_LT(T) = Σ_j T^{ℓ^{2j}}/ℓ^j` (D1Spec's `logLT`). -/
def logLT (K : Type) [Field K] (ℓ : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => if h : ∃ j : ℕ, n = ℓ ^ (2 * j) then ((ℓ : K) ^ Nat.find h)⁻¹ else 0

/-- **The exponent** `c_j = Σ_{i<j} ℓ^{2i} − j = (ℓ^{2j} − 1)/(ℓ² − 1) − j` of the rescaled logarithm. -/
def cExp (ℓ j : ℕ) : ℕ := (∑ i ∈ Finset.range j, ℓ ^ (2 * i)) - j

open Classical in
/-- **The rescaled logarithm** `g(T) = log_LT(πT)/π = Σ_j ℓ^{c_j} T^{ℓ^{2j}}` (for `π^{ℓ²−1} = ℓ`), over `ℤ`. -/
def logLTInt (ℓ : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if h : ∃ j : ℕ, n = ℓ ^ (2 * j) then (ℓ : ℤ) ^ cExp ℓ (Nat.find h) else 0

/-- **The exponent of an even power**: `Nat.find` recovers `j` from `ℓ^{2j}`. -/
theorem find_pow_eq {ℓ j : ℕ} (hℓ : 1 < ℓ) (h : ∃ i : ℕ, ℓ ^ (2 * j) = ℓ ^ (2 * i)) : Nat.find h = j := by
  have hs := Nat.find_spec h
  have := Nat.pow_right_injective (by omega : 2 ≤ ℓ) hs
  omega

/-- **The coefficients of `log_LT`**: `[T^{ℓ^{2j}}] log_LT = ℓ^{−j}`. -/
theorem coeff_logLT_pow (K : Type) [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) (j : ℕ) :
    coeff (ℓ ^ (2 * j)) (logLT K ℓ) = ((ℓ : K) ^ j)⁻¹ := by
  have h : ∃ i : ℕ, ℓ ^ (2 * j) = ℓ ^ (2 * i) := ⟨j, rfl⟩
  rw [logLT, coeff_mk, dite_eq_left h, find_pow_eq hℓ h]

/-- **The coefficients of `log_LT`** off the even powers of `ℓ` vanish. -/
theorem coeff_logLT_of_ne (K : Type) [Field K] {ℓ n : ℕ} (h : ∀ j : ℕ, n ≠ ℓ ^ (2 * j)) :
    coeff n (logLT K ℓ) = 0 := by
  rw [logLT, coeff_mk, dite_eq_right (by simpa using h)]

/-- **The coefficients of `g`**: `[T^{ℓ^{2j}}] g = ℓ^{c_j}`. -/
theorem coeff_logLTInt_pow {ℓ : ℕ} (hℓ : 1 < ℓ) (j : ℕ) :
    coeff (ℓ ^ (2 * j)) (logLTInt ℓ) = (ℓ : ℤ) ^ cExp ℓ j := by
  have h : ∃ i : ℕ, ℓ ^ (2 * j) = ℓ ^ (2 * i) := ⟨j, rfl⟩
  rw [logLTInt, coeff_mk, dite_eq_left h, find_pow_eq hℓ h]

/-- **The coefficients of `g`** off the even powers of `ℓ` vanish. -/
theorem coeff_logLTInt_of_ne {ℓ n : ℕ} (h : ∀ j : ℕ, n ≠ ℓ ^ (2 * j)) : coeff n (logLTInt ℓ) = 0 := by
  rw [logLTInt, coeff_mk, dite_eq_right (by simpa using h)]

/-- **`log_LT` is tangent to the identity**: its linear coefficient is `1`. -/
theorem coeff_one_logLT (K : Type) [Field K] (ℓ : ℕ) : coeff 1 (logLT K ℓ) = 1 := by
  have h : ∃ j : ℕ, 1 = ℓ ^ (2 * j) := ⟨0, by simp⟩
  rw [logLT, coeff_mk, dite_eq_left h, (Nat.find_eq_zero h).2 (by simp)]
  simp

/-- **`g` is tangent to the identity**: its linear coefficient is `1`. -/
theorem coeff_one_logLTInt (ℓ : ℕ) : coeff 1 (logLTInt ℓ) = 1 := by
  have h : ∃ j : ℕ, 1 = ℓ ^ (2 * j) := ⟨0, by simp⟩
  rw [logLTInt, coeff_mk, dite_eq_left h, (Nat.find_eq_zero h).2 (by simp)]
  simp [cExp]

/-- **Powers of `ℓ` are positive.** -/
theorem ne_pow_zero {ℓ : ℕ} (hℓ : 1 < ℓ) (j : ℕ) : (0 : ℕ) ≠ ℓ ^ (2 * j) :=
  (Nat.pow_pos (by omega : 0 < ℓ)).ne

/-- **`log_LT` has no constant term.** -/
theorem constantCoeff_logLT (K : Type) [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) : constantCoeff (logLT K ℓ) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logLT_of_ne K (ne_pow_zero hℓ)]

/-- **`g` has no constant term.** -/
theorem constantCoeff_logLTInt {ℓ : ℕ} (hℓ : 1 < ℓ) : constantCoeff (logLTInt ℓ) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logLTInt_of_ne (ne_pow_zero hℓ)]

/-- **The Lubin–Tate exponential** `e = log_LT^{-1}` (compositional inverse). -/
def expLT (K : Type) [Field K] (ℓ : ℕ) : PowerSeries K :=
  (logLT K ℓ).substInvOfIsUnit (by rw [coeff_one_logLT]; exact isUnit_one)

/-- **The integral model of the exponential** `h = g^{-1}` over `ℤ`, with `e(πT) = π·h(T)`. -/
def expLTInt (ℓ : ℕ) : PowerSeries ℤ :=
  (logLTInt ℓ).substInvOfIsUnit (by rw [coeff_one_logLTInt]; exact isUnit_one)

/-- **`e` has no constant term.** -/
theorem constantCoeff_expLT (K : Type) [Field K] (ℓ : ℕ) : constantCoeff (expLT K ℓ) = 0 :=
  constantCoeff_substInvOfIsUnit _ _

/-- **`h` has no constant term.** -/
theorem constantCoeff_expLTInt (ℓ : ℕ) : constantCoeff (expLTInt ℓ) = 0 :=
  constantCoeff_substInvOfIsUnit _ _

/-- **`e` is a right inverse**: `log_LT(e(T)) = T`. -/
theorem logLT_subst_expLT (K : Type) [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) :
    (logLT K ℓ).subst (expLT K ℓ) = X :=
  subst_substInvOfIsUnit_right _ (constantCoeff_logLT K hℓ) _

/-- **`e` is a left inverse**: `e(log_LT(T)) = T`. -/
theorem expLT_subst_logLT (K : Type) [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) :
    (expLT K ℓ).subst (logLT K ℓ) = X :=
  subst_substInvOfIsUnit_left _ (constantCoeff_logLT K hℓ) _

/-- **`h` is a right inverse**: `g(h(T)) = T`. -/
theorem logLTInt_subst_expLTInt {ℓ : ℕ} (hℓ : 1 < ℓ) : (logLTInt ℓ).subst (expLTInt ℓ) = X :=
  subst_substInvOfIsUnit_right _ (constantCoeff_logLTInt hℓ) _

/-- **The geometric sum**: `ℓ^{2j} = 1 + (ℓ² − 1)·Σ_{i<j} ℓ^{2i}`. -/
theorem pow_two_mul_eq (ℓ j : ℕ) (hℓ : 1 ≤ ℓ) :
    ℓ ^ (2 * j) = 1 + (ℓ ^ 2 - 1) * ∑ i ∈ Finset.range j, ℓ ^ (2 * i) := by
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ 2 = m + 1 := ⟨ℓ ^ 2 - 1, by have := Nat.one_le_pow 2 ℓ hℓ; omega⟩
  rw [hm, Nat.add_sub_cancel]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, hm, ih]
    ring

/-- **The exponents `c_j` are natural numbers**: `j ≤ Σ_{i<j} ℓ^{2i}`. -/
theorem le_sum_pow (ℓ j : ℕ) (hℓ : 1 ≤ ℓ) : j ≤ ∑ i ∈ Finset.range j, ℓ ^ (2 * i) := by
  calc j = ∑ _i ∈ Finset.range j, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => Nat.one_le_pow _ _ hℓ

/-- **The rescaling identity** `log_LT(πT) = π·g(T)` for `π^{ℓ²−1} = ℓ`. -/
theorem rescale_logLT {K : Type} [Field K] [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K}
    (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) :
    rescale π (logLT K ℓ) = C π * map (Int.castRingHom K) (logLTInt ℓ) := by
  have hℓK : (ℓ : K) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  ext n
  rw [coeff_rescale, coeff_C_mul, coeff_map]
  by_cases h : ∃ j : ℕ, n = ℓ ^ (2 * j)
  · obtain ⟨j, rfl⟩ := h
    rw [coeff_logLT_pow K hℓ, coeff_logLTInt_pow hℓ, cExp]
    have hle := le_sum_pow ℓ j hℓ.le
    set S := ∑ i ∈ Finset.range j, ℓ ^ (2 * i)
    have hpow : π ^ (ℓ ^ (2 * j)) = π * (ℓ : K) ^ S := by
      rw [pow_two_mul_eq ℓ j hℓ.le, pow_add, pow_one, pow_mul, hπ]
    rw [hpow, show S = (S - j) + j by omega, pow_add]
    simp only [eq_intCast, Int.cast_pow, Int.cast_natCast, Nat.add_sub_cancel]
    field_simp
  · push Not at h
    rw [coeff_logLT_of_ne K h, coeff_logLTInt_of_ne h]
    simp

/-- **`π ≠ 0`** when `π^{ℓ²−1} = ℓ`. -/
theorem ne_zero_of_pow_eq {K : Type} [Field K] [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K}
    (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) : π ≠ 0 := by
  rintro rfl
  have h4 : ℓ ^ 2 - 1 ≠ 0 := by have : 4 ≤ ℓ ^ 2 := by nlinarith
                                omega
  rw [zero_pow h4] at hπ
  exact (show (ℓ : K) ≠ 0 by exact_mod_cast (show ℓ ≠ 0 by omega)) hπ.symm

/-- **The exponential in terms of its integral model**: `e(T) = π·h(T/π)` for `π^{ℓ²−1} = ℓ`. -/
theorem expLT_eq {K : Type} [Field K] [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K} (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) :
    expLT K ℓ = C π * rescale π⁻¹ (map (Int.castRingHom K) (expLTInt ℓ)) := by
  have hπ0 := ne_zero_of_pow_eq hℓ hπ
  set H := map (Int.castRingHom K) (expLTInt ℓ) with hHdef
  set G := map (Int.castRingHom K) (logLTInt ℓ) with hGdef
  have hH0 : constantCoeff H = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hHdef, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_expLTInt, map_zero]
  have hGH : G.subst H = X := by
    have h2 : map (Int.castRingHom K) ((logLTInt ℓ).subst (expLTInt ℓ)) = G.subst H :=
      map_subst (HasSubst.of_constantCoeff_zero' (constantCoeff_expLTInt ℓ)) _
    rw [← h2, logLTInt_subst_expLTInt hℓ, map_X]
  set A := rescale π⁻¹ H with hAdef
  have hA0 : constantCoeff A = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hAdef, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hH0,
      mul_zero]
  have hAs : HasSubst A := HasSubst.of_constantCoeff_zero' hA0
  have hHs : HasSubst H := HasSubst.of_constantCoeff_zero' hH0
  have hCX : HasSubst (C π * X : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hiX : HasSubst (π⁻¹ • X : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  symm
  apply eq_substInvOfIsUnit_of_subst_eq_X _ (constantCoeff_logLT K hℓ)
  · exact HasSubst.of_constantCoeff_zero' (by simp [hA0])
  · have e1 : C π * A = (C π * X).subst A := by
      rw [subst_mul hAs, subst_X hAs, subst_C]
      rfl
    have e2 : (logLT K ℓ).subst (C π * X) = rescale π (logLT K ℓ) := by
      rw [rescale_eq_subst, smul_eq_C_mul]
    have e3 : G.subst A = π⁻¹ • X := by
      rw [hAdef, rescale_eq_subst, ← subst_comp_subst_apply hHs hiX, hGH, subst_X hiX]
    rw [e1, ← subst_comp_subst_apply hCX hAs, e2, rescale_logLT hℓ hπ, subst_mul hAs, subst_C, e3]
    rw [smul_eq_C_mul, ← mul_assoc]
    change C π * C π⁻¹ * X = X
    rw [← map_mul, mul_inv_cancel₀ hπ0, map_one, one_mul]

/-- **The coefficients of the exponential**: `π^{N−1}·e_N = h_N ∈ ℤ` for `π^{ℓ²−1} = ℓ`. -/
theorem pow_mul_coeff_expLT {K : Type} [Field K] [CharZero K] {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K}
    (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) (N : ℕ) : π ^ (N - 1) * coeff N (expLT K ℓ) = ((coeff N (expLTInt ℓ) : ℤ) : K) := by
  have hπ0 := ne_zero_of_pow_eq hℓ hπ
  rw [expLT_eq hℓ hπ, coeff_C_mul, coeff_rescale, coeff_map, eq_intCast]
  rcases N with _ | N
  · simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_expLTInt]
  · rw [Nat.add_sub_cancel, inv_pow, pow_succ]
    field_simp

/-- **`log_LT` is defined over `ℚ`**: it is mapped to itself by field maps. -/
theorem map_logLT {K L : Type} [Field K] [Field L] (f : K →+* L) (ℓ : ℕ) :
    map f (logLT K ℓ) = logLT L ℓ := by
  ext n
  simp only [logLT, coeff_map, coeff_mk]
  split_ifs <;> simp

/-- **`e` is defined over `ℚ`**: it is mapped to itself by field maps. -/
theorem map_expLT {K L : Type} [Field K] [Field L] (f : K →+* L) {ℓ : ℕ} (hℓ : 1 < ℓ) :
    map f (expLT K ℓ) = expLT L ℓ := by
  have h0 : constantCoeff (expLT K ℓ) = 0 := constantCoeff_expLT K ℓ
  apply eq_substInvOfIsUnit_of_subst_eq_X _ (constantCoeff_logLT L hℓ)
  · apply HasSubst.of_constantCoeff_zero'
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · have h2 : map f ((logLT K ℓ).subst (expLT K ℓ)) = (map f (logLT K ℓ)).subst (map f (expLT K ℓ)) :=
      map_subst (HasSubst.of_constantCoeff_zero' h0) _
    rw [← map_logLT f ℓ, ← h2, logLT_subst_expLT K hℓ, map_X]

/-- **Rescaling commutes with substitution**: `(f∘a)(rT) = f(a(rT))`. -/
theorem rescale_subst {K : Type} [Field K] {f a : K⟦X⟧} (ha : constantCoeff a = 0) (r : K) :
    rescale r (f.subst a) = f.subst (rescale r a) := by
  have has : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  have hrX : HasSubst (r • X : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [rescale_eq_subst, rescale_eq_subst, subst_comp_subst_apply has hrX]

/-- **Support of the exponential over `ℂ`**: `e_N = 0` unless `N ≡ 1 (mod ℓ² − 1)` (two roots `π`, `ζπ`). -/
theorem coeff_expLT_complex_eq_zero {ℓ N : ℕ} (hℓ : 1 < ℓ) (hN : ¬ (ℓ ^ 2 - 1) ∣ (N - 1)) :
    coeff N (expLT ℂ ℓ) = 0 := by
  have hm : ℓ ^ 2 - 1 ≠ 0 := by have : 4 ≤ ℓ ^ 2 := by nlinarith
                                omega
  set π : ℂ := (ℓ : ℂ) ^ (((ℓ ^ 2 - 1 : ℕ) : ℂ)⁻¹)
  have hπ : π ^ (ℓ ^ 2 - 1) = ℓ := Complex.cpow_nat_inv_pow _ hm
  have hζ := Complex.isPrimitiveRoot_exp (ℓ ^ 2 - 1) hm
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ((ℓ ^ 2 - 1 : ℕ) : ℂ))
  have hζπ : (ζ * π) ^ (ℓ ^ 2 - 1) = ℓ := by rw [mul_pow, hζ.pow_eq_one, one_mul, hπ]
  have e1 := pow_mul_coeff_expLT hℓ hπ N
  have e2 := pow_mul_coeff_expLT hℓ hζπ N
  rw [← e1, mul_pow, mul_assoc] at e2
  have hne : ζ ^ (N - 1) ≠ 1 := fun h => hN ((hζ.pow_eq_one_iff_dvd _).1 h)
  have hπ0 : π ^ (N - 1) ≠ 0 := pow_ne_zero _ (ne_zero_of_pow_eq hℓ hπ)
  have : (ζ ^ (N - 1) - 1) * (π ^ (N - 1) * coeff N (expLT ℂ ℓ)) = 0 := by rw [sub_mul, e2, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact (mul_eq_zero.1 h).resolve_left hπ0

/-- **Support of the exponential**: `e_N = 0` unless `N ≡ 1 (mod ℓ² − 1)`, over any field of characteristic `0`. -/
theorem coeff_expLT_eq_zero (K : Type) [Field K] [CharZero K] {ℓ N : ℕ} (hℓ : 1 < ℓ)
    (hN : ¬ (ℓ ^ 2 - 1) ∣ (N - 1)) : coeff N (expLT K ℓ) = 0 := by
  have hQ : coeff N (expLT ℚ ℓ) = 0 := by
    have h := coeff_expLT_complex_eq_zero hℓ hN
    rw [← map_expLT (algebraMap ℚ ℂ) hℓ, coeff_map] at h
    exact (FaithfulSMul.algebraMap_injective ℚ ℂ) (by rw [h, map_zero])
  rw [← map_expLT (algebraMap ℚ K) hℓ, coeff_map, hQ, map_zero]

end LT

/-! ## Valuations of the exponential -/

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- **The exponential bound, normed form**: `‖π^{N−1}·e_N‖ ≤ 1` for `π^{ℓ²−1} = ℓ` in a nonarchimedean field of
characteristic `0`. -/
theorem norm_pow_mul_coeff_expLT_le {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K} (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) (N : ℕ) :
    ‖π ^ (N - 1) * coeff N (expLT K ℓ)‖ ≤ 1 := by
  rw [pow_mul_coeff_expLT hℓ hπ]
  exact IsUltrametricDist.norm_intCast_le_one K _

omit [CharZero K] in
/-- **`π` is integral** when `π^{ℓ²−1} = ℓ`. -/
theorem norm_le_one_of_pow_eq {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K} (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) : ‖π‖ ≤ 1 := by
  have hm : ℓ ^ 2 - 1 ≠ 0 := by have : 4 ≤ ℓ ^ 2 := by nlinarith
                                omega
  have h1 : ‖π‖ ^ (ℓ ^ 2 - 1) ≤ 1 := by
    rw [← norm_pow, hπ]
    exact IsUltrametricDist.norm_natCast_le_one K ℓ
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm).1 h1

/-- **The divided-power comparison** (one variable): if `F` is integral and `‖u‖ ≤ 1`, the series
`G(z) = F(e(u·z))` has `‖π^{N−1}·G_N‖ ≤ 1` for `N ≥ 1`, i.e. `v(G_N) ≥ −(N − 1)/(ℓ² − 1)`. -/
theorem norm_pow_mul_coeff_subst_expLT_le {ℓ : ℕ} (hℓ : 1 < ℓ) {π : K} (hπ : π ^ (ℓ ^ 2 - 1) = ℓ)
    {F : K⟦X⟧} (hF : IsInt F) {u : K} (hu : ‖u‖ ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖π ^ (N - 1) * coeff N (F.subst (rescale u (expLT K ℓ)))‖ ≤ 1 := by
  have hπ0 := ne_zero_of_pow_eq hℓ hπ
  have hπ1 := norm_le_one_of_pow_eq hℓ hπ
  set H := map (Int.castRingHom K) (expLTInt ℓ) with hHdef
  set B := rescale u H with hBdef
  have hH0 : constantCoeff H = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hHdef, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_expLTInt, map_zero]
  have hB0 : constantCoeff B = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hBdef, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hH0,
      mul_zero]
  have hBi : IsInt B := fun n => by
    rw [hBdef, coeff_rescale, hHdef, coeff_map, norm_mul, norm_pow]
    exact mul_le_one_of_le (pow_le_one₀ (norm_nonneg _) hu) (IsUltrametricDist.norm_intCast_le_one K _)
  have he0 : constantCoeff (rescale u (expLT K ℓ)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_expLT, mul_zero]
  -- `G(πz) = F(π·B(z))`
  have hresc : rescale π (rescale u (expLT K ℓ)) = C π * B := by
    rw [rescale_rescale, mul_comm, ← rescale_rescale, expLT_eq hℓ hπ, map_mul, rescale_rescale,
      inv_mul_cancel₀ hπ0, rescale_one, RingHom.id_apply, map_mul, hBdef]
    congr 1
    ext n
    simp only [coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  have hG : rescale π (F.subst (rescale u (expLT K ℓ))) = F.subst (C π * B) := by
    rw [rescale_subst he0, hresc]
  -- split off the constant term of `F`
  set F₁ : K⟦X⟧ := mk fun p => coeff (p + 1) F
  have hF₁ : IsInt F₁ := fun n => by simpa [F₁] using hF (n + 1)
  have hCB0 : constantCoeff (C π * B) = 0 := by simp [hB0]
  have hCBs : HasSubst (C π * B) := HasSubst.of_constantCoeff_zero' hCB0
  have hCBi : IsInt (C π * B) := fun n => by
    rw [coeff_C_mul, norm_mul]
    exact mul_le_one_of_le hπ1 (hBi n)
  have hsplit : F.subst (C π * B) = C π * (B * F₁.subst (C π * B)) + C (constantCoeff F) := by
    conv_lhs => rw [eq_X_mul_shift_add_const F]
    rw [subst_add hCBs, subst_mul hCBs, subst_X hCBs, subst_C]
    change C π * B * F₁.subst (C π * B) + C (constantCoeff F) = _
    ring
  have hc := congrArg (coeff N) hG
  rw [coeff_rescale, hsplit, map_add, coeff_C_mul, coeff_C, ite_eq_right (by omega), add_zero] at hc
  have hc' : π ^ (N - 1) * coeff N (F.subst (rescale u (expLT K ℓ))) =
      coeff N (B * F₁.subst (C π * B)) := by
    apply mul_left_cancel₀ hπ0
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hN, hc]
  rw [hc']
  exact (hBi.mul (hF₁.subst hCBi hCB0)) N

end Norm

/-! ## The bounds in `ℂ_ℓ` -/

section PadicC

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **The norm of an integer in `ℂ_ℓ`** is `ℓ^{−v_ℓ(n)}`. -/
theorem norm_natCast_padicC (n : ℕ) (hn : n ≠ 0) : ‖(n : ℂ_[ℓ])‖ = (ℓ : ℝ) ^ (-(padicValNat ℓ n : ℤ)) := by
  rw [show (n : ℂ_[ℓ]) = ((n : ℚ_[ℓ]) : ℂ_[ℓ]) by norm_cast, PadicComplex.norm_extends',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn), Padic.valuation_natCast]

/-- **The norm of `ℓ` in `ℂ_ℓ`** is `ℓ^{−1}`. -/
theorem norm_ell_padicC : ‖(ℓ : ℂ_[ℓ])‖ = (ℓ : ℝ)⁻¹ := by
  rw [norm_natCast_padicC ℓ hℓp.out.ne_zero, padicValNat_self, Nat.cast_one, zpow_neg_one]

/-- **A root `π^{ℓ²−1} = ℓ`** exists in `ℂ_ℓ`. -/
theorem exists_root_padicC : ∃ π : ℂ_[ℓ], π ^ (ℓ ^ 2 - 1) = ℓ := by
  have : 4 ≤ ℓ ^ 2 := by nlinarith [hℓp.out.two_le]
  exact IsAlgClosed.exists_pow_nat_eq _ (by omega)

/-- **The norm of `π`**: `‖π‖^{ℓ²−1} = ℓ^{−1}`. -/
theorem norm_pow_root {π : ℂ_[ℓ]} (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) : ‖π‖ ^ (ℓ ^ 2 - 1) = (ℓ : ℝ)⁻¹ := by
  rw [← norm_pow, hπ, norm_ell_padicC]

/-- **Removing `π`**: from `‖π^{N−1}·x‖ ≤ 1` to `‖x‖^{ℓ²−1} ≤ ℓ^{N−1}`. -/
theorem norm_pow_le_of_root {π x : ℂ_[ℓ]} (hπ : π ^ (ℓ ^ 2 - 1) = ℓ) (N : ℕ) (h : ‖π ^ (N - 1) * x‖ ≤ 1) :
    ‖x‖ ^ (ℓ ^ 2 - 1) ≤ (ℓ : ℝ) ^ (N - 1) := by
  have h1 := pow_le_one₀ (n := ℓ ^ 2 - 1) (norm_nonneg _) h
  rw [norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm (N - 1), pow_mul, norm_pow_root hπ, inv_pow] at h1
  rwa [inv_mul_le_iff₀ (by have := hℓp.out.pos; positivity), mul_one] at h1

/-- **Real exponents**: from `a^m ≤ ℓ^{N−1}` to `a ≤ ℓ^{(N−1)/m}` (`m = ℓ² − 1`). -/
theorem le_rpow_of_pow_le {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 1 ≤ N) (h : a ^ (ℓ ^ 2 - 1) ≤ (ℓ : ℝ) ^ (N - 1)) :
    a ≤ (ℓ : ℝ) ^ (((N : ℝ) - 1) / ((ℓ : ℝ) ^ 2 - 1)) := by
  have h4 : 4 ≤ ℓ ^ 2 := by nlinarith [hℓp.out.two_le]
  have hm : ℓ ^ 2 - 1 ≠ 0 := by omega
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hcast : (((ℓ ^ 2 - 1 : ℕ) : ℝ)) = (ℓ : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hcastN : (((N - 1 : ℕ) : ℝ)) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]
    push_cast
    ring
  calc a = (a ^ (ℓ ^ 2 - 1)) ^ (((ℓ ^ 2 - 1 : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast ha hm).symm
    _ ≤ ((ℓ : ℝ) ^ (N - 1)) ^ (((ℓ ^ 2 - 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg ha _) h (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = (ℓ : ℝ) ^ (((N : ℝ) - 1) / ((ℓ : ℝ) ^ 2 - 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0, hcastN, hcast, div_eq_mul_inv]

/-- **The Lubin–Tate exponential bound** `v(e_N) ≥ −(N − 1)/(ℓ² − 1)` in `ℂ_ℓ`, as `‖e_N‖^{ℓ²−1} ≤ ℓ^{N−1}`. -/
theorem norm_coeff_expLT_pow_le (N : ℕ) : ‖coeff N (expLT ℂ_[ℓ] ℓ)‖ ^ (ℓ ^ 2 - 1) ≤ (ℓ : ℝ) ^ (N - 1) := by
  obtain ⟨π, hπ⟩ := exists_root_padicC (ℓ := ℓ)
  exact norm_pow_le_of_root hπ N (norm_pow_mul_coeff_expLT_le hℓp.out.one_lt hπ N)

/-- **The Lubin–Tate exponential bound** `v(e_N) ≥ −(N − 1)/(ℓ² − 1)` in `ℂ_ℓ` (`N ≥ 1`). -/
theorem norm_coeff_expLT_le {N : ℕ} (hN : 1 ≤ N) :
    ‖coeff N (expLT ℂ_[ℓ] ℓ)‖ ≤ (ℓ : ℝ) ^ (((N : ℝ) - 1) / ((ℓ : ℝ) ^ 2 - 1)) :=
  le_rpow_of_pow_le (norm_nonneg _) hN (norm_coeff_expLT_pow_le N)

/-- **The divided-power comparison in `ℂ_ℓ`**: for integral `F` and `‖u‖ ≤ 1`, the coefficients of
`G(z) = F(e(u·z))` have `v(G_N) ≥ −(N − 1)/(ℓ² − 1)` for `N ≥ 1`. -/
theorem norm_coeff_subst_expLT_le {F : ℂ_[ℓ]⟦X⟧} (hF : IsInt F) {u : ℂ_[ℓ]} (hu : ‖u‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) : ‖coeff N (F.subst (rescale u (expLT ℂ_[ℓ] ℓ)))‖ ≤
      (ℓ : ℝ) ^ (((N : ℝ) - 1) / ((ℓ : ℝ) ^ 2 - 1)) := by
  obtain ⟨π, hπ⟩ := exists_root_padicC (ℓ := ℓ)
  exact le_rpow_of_pow_le (norm_nonneg _) hN
    (norm_pow_le_of_root hπ N (norm_pow_mul_coeff_subst_expLT_le hℓp.out.one_lt hπ hF hu hN))

/-- **Legendre's formula, rearranged**: `v(N!) − (N − 1)/(ℓ² − 1) = N·γ_ℓ − s_ℓ(N)/(ℓ − 1) + 1/(ℓ² − 1)` with
`γ_ℓ = ℓ/(ℓ² − 1)` and `s_ℓ` the digit sum: the gain of the Lubin–Tate jets over divided powers. -/
theorem padicValNat_factorial_sub (N : ℕ) :
    (padicValNat ℓ N.factorial : ℝ) - ((N : ℝ) - 1) / ((ℓ : ℝ) ^ 2 - 1) =
      N * ℓ / ((ℓ : ℝ) ^ 2 - 1) - ((ℓ.digits N).sum : ℝ) / ((ℓ : ℝ) - 1) + 1 / ((ℓ : ℝ) ^ 2 - 1) := by
  have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.out.two_le
  have hL := sub_one_mul_padicValNat_factorial (p := ℓ) N
  have hs := Nat.digit_sum_le ℓ N
  have hL' : ((ℓ : ℝ) - 1) * padicValNat ℓ N.factorial = N - ((ℓ.digits N).sum : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hL
    simp only [Nat.cast_mul, Nat.cast_sub hs, Nat.cast_sub hℓp.out.one_le, Nat.cast_one] at this
    exact this
  have h1 : (ℓ : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (ℓ : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hv : (padicValNat ℓ N.factorial : ℝ) = (N - ((ℓ.digits N).sum : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [← hL']
    field_simp
  rw [hv, show (ℓ : ℝ) ^ 2 - 1 = ((ℓ : ℝ) - 1) * ((ℓ : ℝ) + 1) by ring]
  field_simp
  ring

/-- **The jets of a Lubin–Tate-integral series** (one variable): for integral `F`, `‖u‖ ≤ 1` and `N ≥ 1`,
`‖N!·G_N‖ ≤ ℓ^{−(N·γ_ℓ − s_ℓ(N)/(ℓ−1) + 1/(ℓ²−1))}` with `G(z) = F(e(u·z))`. -/
theorem norm_factorial_mul_coeff_subst_expLT_le {F : ℂ_[ℓ]⟦X⟧} (hF : IsInt F) {u : ℂ_[ℓ]} (hu : ‖u‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) : ‖(N.factorial : ℂ_[ℓ]) * coeff N (F.subst (rescale u (expLT ℂ_[ℓ] ℓ)))‖ ≤
      (ℓ : ℝ) ^ (-(N * ℓ / ((ℓ : ℝ) ^ 2 - 1) - ((ℓ.digits N).sum : ℝ) / ((ℓ : ℝ) - 1) +
        1 / ((ℓ : ℝ) ^ 2 - 1))) := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓp.out.pos
  rw [← padicValNat_factorial_sub, norm_mul, norm_natCast_padicC _ (Nat.factorial_ne_zero N), neg_sub,
    Real.rpow_sub hℓ0, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast, Real.rpow_neg hℓ0.le, div_eq_mul_inv,
    mul_comm]
  gcongr
  exact norm_coeff_subst_expLT_le hF hu hN

end PadicC

/-! ## The `u = 1` model at an inert prime (CM-b) -/

section Curve

/-- **Complex multiplication**: `Λ` has CM by `O_F`, `F = ℚ(√−d)`, `d ≡ 3 (mod 4)` (D1Spec's `HasCM`). -/
def HasCM (d : ℕ) (Λ : PeriodPair) : Prop :=
  ∀ z ∈ Λ.lattice, (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 * z ∈ Λ.lattice

/-- **The completed maximal unramified extension** of `ℚ_ℓ` in `ℂ_ℓ` (D1Spec's `unramC`). -/
def unramC (ℓ : ℕ) [Fact ℓ.Prime] : Subfield ℂ_[ℓ] :=
  (Subfield.closure {ζ : ℂ_[ℓ] | ∃ n : ℕ, 0 < n ∧ ¬ ℓ ∣ n ∧ ζ ^ n = 1}).topologicalClosure

/-- **The Laurent coefficients of `℘`**: `℘ = z^{−2} + Σ_{k≥2} wpC(k)·z^{2k−2}` (D1Spec's `wpC`). -/
def wpC {K : Type} [Field K] (a b : K) : ℕ → K
  | 0 => 0
  | 1 => 0
  | 2 => a / 20
  | 3 => b / 28
  | k + 4 => 3 / ((2 * ((k : K) + 4) + 1) * ((k : K) + 1)) *
      ∑ m : Fin (k + 1), wpC a b (m.val + 2) * wpC a b (k + 2 - m.val)
termination_by k => k
decreasing_by all_goals omega

/-- **The formal parameter** `t = −2℘/℘′` as a series in `z` (D1Spec's `tSer`). -/
def tSer {K : Type} [Field K] (a b : K) : PowerSeries K :=
  PowerSeries.X * PowerSeries.mk (fun n => if n = 0 then 1 else if Even n then wpC a b (n / 2) else 0) *
    (PowerSeries.mk fun n => if n = 0 then 1 else if Even n then -(((n / 2 : ℕ) : K) - 1) * wpC a b (n / 2) else 0)⁻¹

/-- **CM-b (Deuring, Lubin–Tate, Honda)**, stated for the `Δ = 1` model (`u = 1`): at an inert `ℓ ≥ 5`, some unit
`ε ∈ K^ur` makes `t(ε·log_LT(T))` integral over `O_{K^ur}` (D1Spec's `CMInertLubinTate`, an input). -/
def CMInertLubinTate : Prop :=
  ∀ (d : ℕ) (Λ : PeriodPair), Squarefree d → d % 4 = 3 → HasCM d Λ → Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ¬ ℓ ∣ d → (¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) →
      ∀ ι : ℂ ≃+* ℂ_[ℓ], ∃ ε ∈ unramC ℓ, ‖ε‖ = 1 ∧ ∀ n : ℕ,
        PowerSeries.coeff n ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (PowerSeries.C ε * logLT ℂ_[ℓ] ℓ)) ∈ unramC ℓ ∧
          ‖PowerSeries.coeff n ((tSer (ι Λ.g₂) (ι Λ.g₃)).subst (PowerSeries.C ε * logLT ℂ_[ℓ] ℓ))‖ ≤ 1

/-- **`t(z)` has no constant term.** -/
theorem constantCoeff_tSer {K : Type} [Field K] (a b : K) : constantCoeff (tSer a b) = 0 := by
  simp [tSer]

/-- **`t(z)` is tangent to the identity**: `t = z + O(z²)`. -/
theorem coeff_one_tSer {K : Type} [Field K] (a b : K) : coeff 1 (tSer a b) = 1 := by
  rw [tSer, mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_inv]
  simp [← coeff_zero_eq_constantCoeff_apply]

/-- **The linear coefficient of a composite** is the product of the linear coefficients. -/
theorem coeff_one_subst {K : Type} [Field K] {f g : K⟦X⟧} (hg : constantCoeff g = 0) :
    coeff 1 (f.subst g) = coeff 1 f * coeff 1 g := by
  obtain ⟨g₁, rfl⟩ : X ∣ g := X_dvd_iff.2 hg
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg), finsum_eq_single _ 1]
  · simp
  · intro d hd
    rcases d with _ | _ | d
    · simp
    · exact absurd rfl hd
    · rw [mul_pow, coeff_X_pow_mul', ite_eq_right (by omega), smul_zero]

/-- **`e(rT)` has no constant term.** -/
theorem constantCoeff_rescale_expLT {K : Type} [Field K] (ℓ : ℕ) (r : K) :
    constantCoeff (rescale r (expLT K ℓ)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_expLT, mul_zero]

/-- **`ε·log_LT` has no constant term.** -/
theorem constantCoeff_C_mul_logLT {K : Type} [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) (ε : K) :
    constantCoeff (C ε * logLT K ℓ) = 0 := by
  simp [constantCoeff_logLT K hℓ]

/-- **Back to `z`**: `ε·log_LT(e(z/ε)) = z`. -/
theorem subst_C_mul_logLT_rescale_expLT {K : Type} [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) {ε : K} (hε : ε ≠ 0) :
    (C ε * logLT K ℓ).subst (rescale ε⁻¹ (expLT K ℓ)) = X := by
  have hRs := HasSubst.of_constantCoeff_zero' (constantCoeff_rescale_expLT ℓ ε⁻¹)
  rw [subst_mul hRs, subst_C, ← rescale_subst (constantCoeff_expLT K ℓ), logLT_subst_expLT K hℓ, rescale_X]
  change C ε * (C ε⁻¹ * X) = X
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hε, map_one, one_mul]

/-- **Back from Lubin–Tate coordinates**: `P(t(ε·log_LT(T)))` at `T = e(z/ε)` is `P(t(z))`. -/
theorem subst_tSer_eq {K : Type} [Field K] {ℓ : ℕ} (hℓ : 1 < ℓ) {ε : K} (hε : ε ≠ 0) (a b : K) (P : K⟦X⟧) :
    PowerSeries.subst (rescale ε⁻¹ (expLT K ℓ)) (P.subst ((tSer a b).subst (C ε * logLT K ℓ))) =
      P.subst (tSer a b) := by
  have hLs := HasSubst.of_constantCoeff_zero' (constantCoeff_C_mul_logLT hℓ ε)
  have hA0 : constantCoeff ((tSer a b).subst (C ε * logLT K ℓ)) = 0 :=
    constantCoeff_subst_eq_zero (constantCoeff_C_mul_logLT hℓ ε) _ (constantCoeff_tSer a b)
  have hAs := HasSubst.of_constantCoeff_zero' hA0
  have hRs := HasSubst.of_constantCoeff_zero' (constantCoeff_rescale_expLT ℓ ε⁻¹)
  rw [subst_comp_subst_apply hAs hRs, subst_comp_subst_apply hLs hRs, subst_C_mul_logLT_rescale_expLT hℓ hε,
    X_subst]

/-- **The formal logarithm** `z(t)` of the model: the compositional inverse of `t(z)`. -/
def logE {K : Type} [Field K] (a b : K) : K⟦X⟧ :=
  (tSer a b).substInvOfIsUnit (by rw [coeff_one_tSer]; exact isUnit_one)

/-- **Lubin–Tate coordinates** (CM-b): if `t(T) = t(ε·log_LT(T))` is integral with `‖ε‖ = 1`, its inverse `T(t)`
is integral with `T = ε⁻¹t + O(t²)`, and the formal logarithm of the model is `z(t) = ε·log_LT(T(t))`. -/
theorem exists_ltCoord {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {a b ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer a b).subst (C ε * logLT ℂ_[ℓ] ℓ))) :
    ∃ Tt : ℂ_[ℓ]⟦X⟧, IsInt Tt ∧ constantCoeff Tt = 0 ∧ coeff 1 Tt = ε⁻¹ ∧
      logE a b = (C ε * logLT ℂ_[ℓ] ℓ).subst Tt := by
  have hℓ := hℓp.out.one_lt
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  set L := C ε * logLT ℂ_[ℓ] ℓ with hL
  set A : ℂ_[ℓ]⟦X⟧ := (tSer a b).subst L with hA
  have hL0 := constantCoeff_C_mul_logLT hℓ ε
  have hA0 : constantCoeff A = 0 := constantCoeff_subst_eq_zero hL0 _ (constantCoeff_tSer a b)
  have hA1 : coeff 1 A = ε := by
    rw [hA, coeff_one_subst hL0, coeff_one_tSer, coeff_C_mul, coeff_one_logLT, one_mul, mul_one]
  have hu : IsUnit (coeff 1 A) := by rw [hA1]; exact hε0.isUnit
  refine ⟨A.substInvOfIsUnit hu, ht.substInv hA0 (by rw [hA1, hε]) hu, constantCoeff_substInvOfIsUnit _ _, ?_, ?_⟩
  · rw [coeff_one_substInvOfIsUnit]
    simp [hA1]
  · have hTs := HasSubst.substInvOfIsUnit A hu
    symm
    apply eq_substInvOfIsUnit_of_subst_eq_X _ (constantCoeff_tSer a b)
    · exact HasSubst.of_constantCoeff_zero' (constantCoeff_subst_eq_zero (constantCoeff_substInvOfIsUnit _ _) _ hL0)
    · rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hL0) hTs, ← hA,
        subst_substInvOfIsUnit_right _ hA0]

/-- **The formal parameter's jets** in `ℂ_ℓ`: if `t(ε·log_LT(T))` is integral with `‖ε‖ = 1`, then for every series
`P` integral in `t` the `z`-expansion `P(t(z))` has `v([z^N]) ≥ −(N − 1)/(ℓ² − 1)` (`N ≥ 1`). -/
theorem norm_coeff_subst_tSer_le {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {a b ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer a b).subst (C ε * logLT ℂ_[ℓ] ℓ))) {P : ℂ_[ℓ]⟦X⟧} (hP : IsInt P) {N : ℕ} (hN : 1 ≤ N) :
    ‖coeff N (P.subst (tSer a b))‖ ≤ (ℓ : ℝ) ^ (((N : ℝ) - 1) / ((ℓ : ℝ) ^ 2 - 1)) := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hA0 := constantCoeff_subst_eq_zero (constantCoeff_C_mul_logLT hℓp.out.one_lt ε) _ (constantCoeff_tSer a b)
  rw [← subst_tSer_eq hℓp.out.one_lt hε0 a b P]
  exact norm_coeff_subst_expLT_le (hP.subst ht hA0) (by rw [norm_inv, hε, inv_one]) hN

/-- **The formal parameter's jets, divided-power form**: under the hypotheses of `norm_coeff_subst_tSer_le`,
`v(N!·[z^N] P(t(z))) ≥ N·γ_ℓ − s_ℓ(N)/(ℓ − 1) + 1/(ℓ² − 1)` (`N ≥ 1`, `γ_ℓ = ℓ/(ℓ² − 1)`). -/
theorem norm_factorial_mul_coeff_subst_tSer_le {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {a b ε : ℂ_[ℓ]} (hε : ‖ε‖ = 1)
    (ht : IsInt ((tSer a b).subst (C ε * logLT ℂ_[ℓ] ℓ))) {P : ℂ_[ℓ]⟦X⟧} (hP : IsInt P) {N : ℕ} (hN : 1 ≤ N) :
    ‖(N.factorial : ℂ_[ℓ]) * coeff N (P.subst (tSer a b))‖ ≤
      (ℓ : ℝ) ^ (-(N * ℓ / ((ℓ : ℝ) ^ 2 - 1) - ((ℓ.digits N).sum : ℝ) / ((ℓ : ℝ) - 1) +
        1 / ((ℓ : ℝ) ^ 2 - 1))) := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hA0 := constantCoeff_subst_eq_zero (constantCoeff_C_mul_logLT hℓp.out.one_lt ε) _ (constantCoeff_tSer a b)
  rw [← subst_tSer_eq hℓp.out.one_lt hε0 a b P]
  exact norm_factorial_mul_coeff_subst_expLT_le (hP.subst ht hA0) (by rw [norm_inv, hε, inv_one]) hN

/-- **The CM curve at an inert prime** (CM-b): for the `Δ = 1` model of a CM lattice and an inert `ℓ ≥ 5`, there
are Lubin–Tate coordinates (`exists_ltCoord`), and for every series `P` integral in the formal parameter `t` the
`z`-expansion `P(t(z))` has `v([z^N]) ≥ −(N − 1)/(ℓ² − 1)` and
`v(N!·[z^N]) ≥ N·γ_ℓ − s_ℓ(N)/(ℓ − 1) + 1/(ℓ² − 1)` for `N ≥ 1`. -/
theorem cm_inert_jets (hb : CMInertLubinTate) {d : ℕ} {Λ : PeriodPair} (hd : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : HasCM d Λ) (hΔ : Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2 = 1) {ℓ : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (hdℓ : ¬ ℓ ∣ d)
    (hin : ¬ ∃ x : ZMod ℓ, x ^ 2 = -(d : ZMod ℓ)) (ι : ℂ ≃+* ℂ_[ℓ]) {P : ℂ_[ℓ]⟦X⟧} (hP : IsInt P) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖coeff N (P.subst (tSer (ι Λ.g₂) (ι Λ.g₃)))‖ ≤ (ℓ : ℝ) ^ (((N : ℝ) - 1) / ((ℓ : ℝ) ^ 2 - 1)) ∧
      ‖(N.factorial : ℂ_[ℓ]) * coeff N (P.subst (tSer (ι Λ.g₂) (ι Λ.g₃)))‖ ≤
        (ℓ : ℝ) ^ (-(N * ℓ / ((ℓ : ℝ) ^ 2 - 1) - ((ℓ.digits N).sum : ℝ) / ((ℓ : ℝ) - 1) +
          1 / ((ℓ : ℝ) ^ 2 - 1))) := by
  obtain ⟨ε, -, hε, ht⟩ := hb d Λ hd hd4 hcm hΔ ℓ h5 hdℓ hin ι
  exact ⟨norm_coeff_subst_tSer_le hε (fun n => (ht n).2) hP hN,
    norm_factorial_mul_coeff_subst_tSer_le hε (fun n => (ht n).2) hP hN⟩

end Curve

/-! ## `exp` of series without constant term -/

section ExpHom

variable {A : Type} [CommRing A] [Algebra ℚ A] {σ : Type}

omit [Algebra ℚ A] in
/-- **Order of powers**: powers of a series without constant term vanish below their exponent. -/
theorem coeff_pow_eq_zero {f : MvPowerSeries σ A} (hf : MvPowerSeries.constantCoeff f = 0) {α : σ →₀ ℕ}
    {k : ℕ} (hk : (α.sum fun _ e => e) < k) : MvPowerSeries.coeff α (f ^ k) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf)
  exact_mod_cast hk

/-- **The coefficients of `exp(f)`**: `[X^α] exp(f) = Σ_{k ≤ |α|} [X^α] f^k/k!`. -/
theorem coeff_exp_subst {f : MvPowerSeries σ A} (hf : MvPowerSeries.constantCoeff f = 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α ((PowerSeries.exp A).subst f) = ∑ k ∈ Finset.range ((α.sum fun _ e => e) + 1),
      MvPowerSeries.coeff α (f ^ k) * algebraMap ℚ A (1 / (k.factorial : ℚ)) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ e => e) + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul, mul_comm]
  · intro k hk
    simp only [Function.mem_support, ne_eq, Finset.coe_range, Set.mem_Iio] at hk ⊢
    by_contra hlt
    exact hk (by rw [coeff_pow_eq_zero hf (by omega), smul_zero])

/-- **The functional equation of `exp`** in two variables: `exp(X₀ + X₁) = exp(X₀)·exp(X₁)`. -/
theorem exp_subst_add_two :
    (PowerSeries.exp A).subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) =
      (PowerSeries.exp A).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A) *
        (PowerSeries.exp A).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) := by
  ext e
  rw [PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  simp only [PowerSeries.coeff_exp]
  have h := Nat.add_choose_mul_factorial_mul_factorial (e 0) (e 1)
  rw [← Nat.choose_symm_add] at h
  have h' : ((e 0 + e 1).choose (e 0) : ℚ) * (e 0).factorial * (e 1).factorial = (e 0 + e 1).factorial := by
    exact_mod_cast h
  have hf0 : ((e 0).factorial : ℚ) ≠ 0 := by positivity
  have hf1 : ((e 1).factorial : ℚ) ≠ 0 := by positivity
  have hc : ((e 0 + e 1).choose (e 0) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (Nat.le_add_right _ _)).ne'
  have hq : ((e 0 + e 1).choose (e 0) : ℚ) * (1 / (e 0 + e 1).factorial) =
      1 / (e 0).factorial * (1 / (e 1).factorial) := by
    rw [← h']
    field_simp
  rw [← map_mul, ← hq, map_mul, map_natCast]

/-- **`exp` is additive**: `exp(f + g) = exp(f)·exp(g)` for `f, g` without constant term. -/
theorem exp_subst_add {f g : MvPowerSeries σ A} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    (PowerSeries.exp A).subst (f + g) = (PowerSeries.exp A).subst f * (PowerSeries.exp A).subst g := by
  have hb : MvPowerSeries.HasSubst ![f, g] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hf, hg]
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) A) :=
    fun i => PowerSeries.HasSubst.X i
  have hXX : PowerSeries.HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have key := congrArg (MvPowerSeries.subst ![f, g]) (exp_subst_add_two (A := A))
  rw [MvPowerSeries.subst_mul hb] at key
  simp only [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (hXX.const) hb,
    MvPowerSeries.subst_comp_subst_apply ((hX 0).const) hb, MvPowerSeries.subst_comp_subst_apply ((hX 1).const) hb,
    MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb] at key
  simp only [PowerSeries.subst]
  simpa using key

/-- **Powers of `exp`**: `exp(n·f) = exp(f)^n`. -/
theorem exp_subst_nsmul {f : MvPowerSeries σ A} (hf : MvPowerSeries.constantCoeff f = 0) (n : ℕ) :
    (PowerSeries.exp A).subst (n • f) = (PowerSeries.exp A).subst f ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero, PowerSeries.subst_zero_eq_C_constantCoeff]
    simp
  | succ n ih =>
    rw [succ_nsmul, exp_subst_add (by rw [map_nsmul, hf, smul_zero]) hf, ih, pow_succ]

end ExpHom

/-! ## Integral multivariate series -/

section MvInt

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type}

/-- **Integrality** of a multivariate series over a nonarchimedean field: every coefficient in the unit ball. -/
def IsIntK (f : MvPowerSeries σ K) : Prop := ∀ n, ‖MvPowerSeries.coeff n f‖ ≤ 1

/-- **Integral series are the series over the unit ball.** -/
theorem isIntK_iff (f : MvPowerSeries σ K) :
    IsIntK f ↔ ∃ g : MvPowerSeries σ (ball1 K), MvPowerSeries.map (ball1 K).subtype g = f := by
  constructor
  · intro h
    exact ⟨fun n => ⟨MvPowerSeries.coeff n f, h n⟩, by ext n; rfl⟩
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

/-- **Products of integral series are integral.** -/
theorem IsIntK.mul {f g : MvPowerSeries σ K} (hf : IsIntK f) (hg : IsIntK g) : IsIntK (f * g) := by
  obtain ⟨f', rfl⟩ := (isIntK_iff f).1 hf
  obtain ⟨g', rfl⟩ := (isIntK_iff g).1 hg
  exact (isIntK_iff _).2 ⟨f' * g', map_mul _ _ _⟩

/-- **`1` is integral.** -/
theorem isIntK_one : IsIntK (1 : MvPowerSeries σ K) :=
  (isIntK_iff _).2 ⟨1, map_one _⟩

/-- **Inverses**: the inverse of an integral series with constant term `1` is integral. -/
theorem IsIntK.inv {f : MvPowerSeries σ K} (hf : IsIntK f) (h1 : MvPowerSeries.constantCoeff f = 1) :
    IsIntK f⁻¹ := by
  obtain ⟨g, rfl⟩ := (isIntK_iff f).1 hf
  have hg1 : MvPowerSeries.constantCoeff g = ((1 : (ball1 K)ˣ) : ball1 K) := by
    rw [Units.val_one]
    apply Subtype.ext
    have := h1
    rw [MvPowerSeries.constantCoeff_map] at this
    exact this
  refine (isIntK_iff _).2 ⟨MvPowerSeries.invOfUnit g 1, ?_⟩
  rw [MvPowerSeries.eq_inv_iff_mul_eq_one (by rw [h1]; exact one_ne_zero), ← map_mul,
    MvPowerSeries.invOfUnit_mul g 1 hg1, map_one]

/-- **Integral substitution keeps integrality**. -/
theorem IsIntK.subst {τ : Type} [Finite σ] {f : MvPowerSeries σ K} (hf : IsIntK f)
    {ψ : σ → MvPowerSeries τ K} (hψ : ∀ s, IsIntK (ψ s)) (hψ0 : ∀ s, MvPowerSeries.constantCoeff (ψ s) = 0) :
    IsIntK (f.subst ψ) := by
  obtain ⟨f', rfl⟩ := (isIntK_iff f).1 hf
  choose ψ' hψ' using fun s => (isIntK_iff (ψ s)).1 (hψ s)
  have h0 : ∀ s, MvPowerSeries.constantCoeff (ψ' s) = 0 := fun s => by
    apply Subtype.ext
    have := hψ0 s
    rw [← hψ' s, MvPowerSeries.constantCoeff_map] at this
    exact this
  refine (isIntK_iff _).2 ⟨f'.subst ψ', ?_⟩
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)]
  simp_rw [hψ']

/-- **Powers of integral series are integral.** -/
theorem IsIntK.pow {f : MvPowerSeries σ K} (hf : IsIntK f) (n : ℕ) : IsIntK (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact isIntK_one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

end MvInt

/-! ## Dwork's lemma -/

section DworkBasic

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type}

/-- **`ℓ`-divisibility** of a series: every coefficient of norm at most `‖ℓ‖`. -/
def IsDivK (ℓ : ℕ) (f : MvPowerSeries σ K) : Prop := ∀ n, ‖MvPowerSeries.coeff n f‖ ≤ ‖(ℓ : K)‖

variable {ℓ : ℕ}

/-- **Sums of `ℓ`-divisible series are `ℓ`-divisible.** -/
theorem IsDivK.add {f g : MvPowerSeries σ K} (hf : IsDivK ℓ f) (hg : IsDivK ℓ g) : IsDivK ℓ (f + g) :=
  fun n => by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

omit [IsUltrametricDist K] in
/-- **Negatives of `ℓ`-divisible series are `ℓ`-divisible.** -/
theorem IsDivK.neg {f : MvPowerSeries σ K} (hf : IsDivK ℓ f) : IsDivK ℓ (-f) := fun n => by
  rw [map_neg, norm_neg]
  exact hf n

/-- **Differences of `ℓ`-divisible series are `ℓ`-divisible.** -/
theorem IsDivK.sub {f g : MvPowerSeries σ K} (hf : IsDivK ℓ f) (hg : IsDivK ℓ g) : IsDivK ℓ (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- **Finite sums of `ℓ`-divisible series are `ℓ`-divisible.** -/
theorem IsDivK.sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries σ K} (hf : ∀ i ∈ s, IsDivK ℓ (f i)) :
    IsDivK ℓ (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i hi => hf i hi n

/-- **`ℓ`-divisible times integral is `ℓ`-divisible.** -/
theorem IsDivK.mul_isInt {f g : MvPowerSeries σ K} (hf : IsDivK ℓ f) (hg : IsIntK g) : IsDivK ℓ (f * g) :=
  fun n => by
    classical
    rw [MvPowerSeries.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun p _ => ?_
    rw [norm_mul]
    calc _ ≤ ‖(ℓ : K)‖ * 1 := mul_le_mul (hf _) (hg _) (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _

/-- **Multiples of `ℓ`** have norm at most `‖ℓ‖`. -/
theorem norm_natCast_le_of_dvd {k : ℕ} (hk : ℓ ∣ k) : ‖(k : K)‖ ≤ ‖(ℓ : K)‖ := by
  obtain ⟨t, rfl⟩ := hk
  rw [Nat.cast_mul, norm_mul]
  calc _ ≤ ‖(ℓ : K)‖ * 1 := mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one K t) (norm_nonneg _)
    _ = _ := mul_one _

end DworkBasic

section Dwork

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **The Frobenius** `F ↦ F^φ(X^ℓ)` on series, for a ring endomorphism `φ` of the coefficients. -/
def frobS (ℓ : ℕ) [Fact ℓ.Prime] (φ : K →+* K) : MvPowerSeries σ K →+* MvPowerSeries σ K :=
  ((MvPowerSeries.expand ℓ (Fact.out : ℓ.Prime).ne_zero : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) :
    MvPowerSeries σ K →+* MvPowerSeries σ K).comp (MvPowerSeries.map φ)

omit [IsUltrametricDist K] in
/-- **The coefficients of the Frobenius**: `[X^{ℓβ}] F^φ(X^ℓ) = φ([X^β] F)`. -/
theorem coeff_frobS_smul (φ : K →+* K) (F : MvPowerSeries σ K) (β : σ →₀ ℕ) :
    MvPowerSeries.coeff (ℓ • β) (frobS ℓ φ F) = φ (MvPowerSeries.coeff β F) := by
  simp [frobS, MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map]

omit [IsUltrametricDist K] in
/-- **The coefficients of the Frobenius** at exponents not divisible by `ℓ` vanish. -/
theorem coeff_frobS_of_not_dvd (φ : K →+* K) (F : MvPowerSeries σ K) {γ : σ →₀ ℕ} {i : σ} (h : ¬ ℓ ∣ γ i) :
    MvPowerSeries.coeff γ (frobS ℓ φ F) = 0 :=
  MvPowerSeries.coeff_expand_of_not_dvd ℓ hℓp.out.ne_zero _ h

omit [IsUltrametricDist K] in
/-- **The Frobenius of a monomial**: `(cX^β)^φ(X^ℓ) = φ(c)X^{ℓβ}`. -/
theorem frobS_monomial (φ : K →+* K) (β : σ →₀ ℕ) (c : K) :
    frobS ℓ φ (MvPowerSeries.monomial β c) = MvPowerSeries.monomial (ℓ • β) (φ c) := by
  simp [frobS, MvPowerSeries.map_monomial, MvPowerSeries.expand_monomial]

omit [IsUltrametricDist K] in
/-- **The constant term of the Frobenius** is `φ` of the constant term. -/
theorem constantCoeff_frobS (φ : K →+* K) (F : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (frobS ℓ φ F) = φ (MvPowerSeries.constantCoeff F) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← smul_zero ℓ, coeff_frobS_smul,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- **Frobenius is additive mod `ℓ`**: `(M + Q)^ℓ ≡ M^ℓ + Q^ℓ (mod ℓ)` for integral `M`, `Q`. -/
theorem isDivK_add_pow_sub {M Q : MvPowerSeries σ K} (hM : IsIntK M) (hQ : IsIntK Q) :
    IsDivK ℓ ((M + Q) ^ ℓ - M ^ ℓ - Q ^ ℓ) := by
  have hℓ := hℓp.out
  obtain ⟨m, hm⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  have e : (M + Q) ^ ℓ - M ^ ℓ - Q ^ ℓ =
      ∑ i ∈ Finset.range (m + 1), M ^ (i + 1) * Q ^ (ℓ - (i + 1)) * (ℓ.choose (i + 1) : MvPowerSeries σ K) := by
    rw [add_pow, hm, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.choose_self, Nat.sub_self, pow_zero, mul_one, Nat.cast_one, Nat.choose_zero_right,
      one_mul, Nat.sub_zero]
    ring
  rw [e]
  refine IsDivK.sum _ fun i hi => ?_
  have hdvd : ℓ ∣ ℓ.choose (i + 1) := hℓ.dvd_choose_self (by omega) (by rw [Finset.mem_range] at hi; omega)
  intro n
  rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)), MvPowerSeries.coeff_mul_C, norm_mul, mul_comm]
  calc _ ≤ ‖(ℓ : K)‖ * 1 :=
        mul_le_mul (norm_natCast_le_of_dvd hdvd) (((hM.pow _).mul (hQ.pow _)) n) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

/-- **The Frobenius congruence** `P^φ(X^ℓ) ≡ P^ℓ (mod ℓ)` for a finite sum `P` of integral monomials, when `φ` lifts
Frobenius on the unit ball. -/
theorem isDivK_frobS_sub_pow {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖)
    (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → K) (hc : ∀ β ∈ s, ‖c β‖ ≤ 1) :
    IsDivK ℓ (frobS ℓ φ (∑ β ∈ s, MvPowerSeries.monomial β (c β)) -
      (∑ β ∈ s, MvPowerSeries.monomial β (c β)) ^ ℓ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp [zero_pow hℓp.out.ne_zero]
  | insert β s hβ ih =>
    rw [Finset.sum_insert hβ]
    set M := MvPowerSeries.monomial β (c β)
    set Q := ∑ β ∈ s, MvPowerSeries.monomial β (c β)
    have hM : IsIntK M := fun n => by
      rw [MvPowerSeries.coeff_monomial]
      split_ifs
      · exact hc β (Finset.mem_insert_self _ _)
      · simp
    have hQ : IsIntK Q := fun n => by
      rw [map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b hb => ?_
      rw [MvPowerSeries.coeff_monomial]
      split_ifs
      · exact hc b (Finset.mem_insert_of_mem hb)
      · simp
    have e : frobS ℓ φ (M + Q) - (M + Q) ^ ℓ =
        (frobS ℓ φ M - M ^ ℓ) + (frobS ℓ φ Q - Q ^ ℓ) - ((M + Q) ^ ℓ - M ^ ℓ - Q ^ ℓ) := by
      rw [map_add]
      ring
    rw [e]
    refine (IsDivK.add ?_ (ih fun b hb => hc b (Finset.mem_insert_of_mem hb))).sub (isDivK_add_pow_sub hM hQ)
    intro n
    rw [frobS_monomial, MvPowerSeries.monomial_pow, ← map_sub, MvPowerSeries.coeff_monomial]
    split_ifs
    · exact hφ _ (hc β (Finset.mem_insert_self _ _))
    · simp

/-- **Dwork's main lemma**: if `F(0) = 1` and `F^φ(X^ℓ) = F^ℓ·V` with `V ≡ 1 (mod ℓ)`, then `F` is integral. -/
theorem isIntK_of_frobS_eq [CharZero K] [Finite σ] {φ : K →+* K} (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖)
    {F V : MvPowerSeries σ K} (hF0 : MvPowerSeries.constantCoeff F = 1) (hV : IsDivK ℓ (V - 1))
    (hFV : frobS ℓ φ F = F ^ ℓ * V) : IsIntK F := by
  classical
  have hℓ := hℓp.out
  have hn0 : (0 : ℝ) < ‖(ℓ : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hℓ.ne_zero)
  have hV0 : MvPowerSeries.constantCoeff V = 1 := by
    have h := congrArg MvPowerSeries.constantCoeff hFV
    rw [constantCoeff_frobS, hF0, map_one, map_mul, map_pow, hF0, one_pow, one_mul] at h
    exact h.symm
  suffices H : ∀ n : ℕ, ∀ α : σ →₀ ℕ, α.degree < n → ‖MvPowerSeries.coeff α F‖ ≤ 1 from
    fun α => H _ α (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro α h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro α hα
    rcases Nat.lt_succ_iff_lt_or_eq.1 hα with h | hdeg
    · exact ih α h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hdeg
      subst this
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0, norm_one]
    set F' : MvPowerSeries σ K := ((MvPowerSeries.truncTotal n F : MvPolynomial σ K) : MvPowerSeries σ K)
      with hF'def
    have hF'c : ∀ β, MvPowerSeries.coeff β F' = if β.degree < n then MvPowerSeries.coeff β F else 0 :=
      fun β => by rw [hF'def, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
    have hF'i : IsIntK F' := fun β => by
      rw [hF'c]
      split_ifs with hb
      · exact ih β hb
      · simp
    have hF'0 : MvPowerSeries.constantCoeff F' = 1 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF'c, ite_eq_left (by simpa using hn),
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0]
    have hpow : ∀ (m : ℕ) (β : σ →₀ ℕ), β.degree < n →
        MvPowerSeries.coeff β (F ^ m) = MvPowerSeries.coeff β (F' ^ m) := fun m β hb => by
      rw [hF'def, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_pow _ hb]
    have hlow : ∀ a b : σ →₀ ℕ, a + b = α → b ≠ 0 → a.degree < n := fun a b hab hb => by
      have h := congrArg Finsupp.degree hab
      rw [map_add] at h
      have hb' : b.degree ≠ 0 := fun h' => hb ((Finsupp.degree_eq_zero_iff _).1 h')
      omega
    -- the coefficient `α` of `F^ℓ − F'^ℓ = G·(F − F')` is `ℓ·F_α`
    have hc : MvPowerSeries.coeff α (F ^ ℓ) - MvPowerSeries.coeff α (F' ^ ℓ) = ℓ * MvPowerSeries.coeff α F := by
      rw [← map_sub, ← geom_sum₂_mul F F' ℓ, MvPowerSeries.coeff_mul, Finset.sum_eq_single (0, α)]
      · rw [map_sub, hF'c α, ite_eq_right (by omega), sub_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          map_sum]
        simp [hF0, hF'0]
      · intro p hp hne
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have h1 : p.1 ≠ 0 := by
          intro h1
          apply hne
          rw [h1, zero_add] at hp
          rw [← hp, ← h1]
        rw [map_sub, hF'c p.2, ite_eq_left (hlow p.2 p.1 (by rw [add_comm]; exact hp) h1), sub_self, mul_zero]
      · intro h
        exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add α)) h
    -- the correction `F^ℓ·(V − 1)` is `≡ 0 (mod ℓ)` at `α`
    have hd : ‖MvPowerSeries.coeff α (F ^ ℓ * (V - 1))‖ ≤ ‖(ℓ : K)‖ := by
      rw [MvPowerSeries.coeff_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h2 : p.2 = 0
      · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hV0, map_one, sub_self, mul_zero,
          norm_zero]
        exact norm_nonneg _
      · rw [norm_mul, hpow ℓ p.1 (hlow p.1 p.2 hp h2)]
        calc _ ≤ 1 * ‖(ℓ : K)‖ := mul_le_mul ((hF'i.pow ℓ) p.1) (hV p.2) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    -- the Frobenius term only sees `F'`
    have he : MvPowerSeries.coeff α (frobS ℓ φ F) = MvPowerSeries.coeff α (frobS ℓ φ F') := by
      by_cases hdiv : ∀ i, ℓ ∣ α i
      · obtain ⟨β, rfl⟩ : ∃ β, α = ℓ • β :=
          ⟨α.mapRange (· / ℓ) (by simp), by ext i; simp [Nat.mul_div_cancel' (hdiv i)]⟩
        rw [coeff_frobS_smul, coeff_frobS_smul, hF'c β, ite_eq_left]
        rw [map_nsmul, smul_eq_mul] at hdeg
        have h2 : β.degree * 2 ≤ β.degree * ℓ := Nat.mul_le_mul_left _ hℓ.two_le
        have h3 : 0 < β.degree := by
          rcases Nat.eq_zero_or_pos β.degree with h0 | h0
          · rw [h0, mul_zero] at hdeg; omega
          · exact h0
        rw [mul_comm] at hdeg
        omega
      · push Not at hdiv
        obtain ⟨i, hi⟩ := hdiv
        rw [coeff_frobS_of_not_dvd _ _ hi, coeff_frobS_of_not_dvd _ _ hi]
    -- the Frobenius congruence for the polynomial `F'`
    have hF'sum : F' = ∑ β ∈ (MvPowerSeries.truncTotal n F).support,
        MvPowerSeries.monomial β (MvPowerSeries.coeff β F') := by
      ext γ
      rw [map_sum]
      simp only [MvPowerSeries.coeff_monomial]
      rw [Finset.sum_ite_eq]
      split_ifs with hγ
      · rfl
      · rw [hF'def, MvPolynomial.coeff_coe]
        exact MvPolynomial.notMem_support_iff.1 hγ
    have hf : ‖MvPowerSeries.coeff α (frobS ℓ φ F' - F' ^ ℓ)‖ ≤ ‖(ℓ : K)‖ := by
      have := isDivK_frobS_sub_pow hφ (MvPowerSeries.truncTotal n F).support
        (fun β => MvPowerSeries.coeff β F') (fun β _ => hF'i β)
      rw [← hF'sum] at this
      exact this α
    have key : (ℓ : K) * MvPowerSeries.coeff α F =
        MvPowerSeries.coeff α (frobS ℓ φ F' - F' ^ ℓ) - MvPowerSeries.coeff α (F ^ ℓ * (V - 1)) := by
      have h1 : MvPowerSeries.coeff α (frobS ℓ φ F) =
          MvPowerSeries.coeff α (F ^ ℓ) + MvPowerSeries.coeff α (F ^ ℓ * (V - 1)) := by
        rw [hFV, mul_sub, mul_one, map_sub]
        ring
      rw [map_sub, ← he, h1, ← hc]
      ring
    have hk : ‖(ℓ : K) * MvPowerSeries.coeff α F‖ ≤ ‖(ℓ : K)‖ := by
      rw [key]
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hf (by rw [norm_neg]; exact hd))
    rw [norm_mul] at hk
    exact (mul_le_iff_le_one_right hn0).1 hk

omit hℓp in
/-- **Powers of an `ℓ`-divisible series**: `‖[X^α] g^k‖ ≤ ‖ℓ‖^k`. -/
theorem norm_coeff_pow_le_of_isDivK {g : MvPowerSeries σ K} (hg : IsDivK ℓ g) (k : ℕ) (α : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff α (g ^ k)‖ ≤ ‖(ℓ : K)‖ ^ k := by
  classical
  induction k generalizing α with
  | zero =>
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, MvPowerSeries.coeff_mul, pow_succ]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p _ => ?_
    rw [norm_mul]
    exact mul_le_mul (ih _) (hg _) (norm_nonneg _) (by positivity)

/-- **Legendre's bound** `v_ℓ(m!) ≤ m − 1` for `m ≥ 1`. -/
theorem padicValNat_factorial_le_sub_one {m : ℕ} (hm : 1 ≤ m) : padicValNat ℓ m.factorial ≤ m - 1 := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := ℓ) (by omega : m ≠ 0)
  have h1 : 1 ≤ ℓ - 1 := by have := hℓp.out.two_le; omega
  have := Nat.le_mul_of_pos_left (padicValNat ℓ m.factorial) h1
  omega

/-- **The norm of an integer in `ℚ_ℓ`** is `ℓ^{−v_ℓ(n)}`. -/
theorem norm_natCast_padic (n : ℕ) (hn : n ≠ 0) : ‖(n : ℚ_[ℓ])‖ = (ℓ : ℝ) ^ (-(padicValNat ℓ n : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn), Padic.valuation_natCast]

/-- **`exp(ℓ·integral) ≡ 1 (mod ℓ)`**: for `g` without constant term and `ℓ`-divisible, `exp(g) − 1` is
`ℓ`-divisible (the norm on `ℕ` being `ℓ`-adic). -/
theorem isDivK_exp_sub_one [CharZero K] (hK : ∀ n : ℕ, ‖(n : K)‖ = ‖(n : ℚ_[ℓ])‖) {g : MvPowerSeries σ K}
    (hg : IsDivK ℓ g) (hg0 : MvPowerSeries.constantCoeff g = 0) :
    IsDivK ℓ ((PowerSeries.exp K).subst g - 1) := by
  classical
  intro α
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.out.one_le
  have hℓn : ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ := by rw [hK, Padic.norm_p]
  rw [map_sub, coeff_exp_subst hg0, Finset.sum_range_succ', pow_zero, MvPowerSeries.coeff_one]
  have h0 : (if α = 0 then (1 : K) else 0) * algebraMap ℚ K (1 / (Nat.factorial 0 : ℚ)) =
      if α = 0 then 1 else 0 := by simp
  rw [h0, add_sub_cancel_right]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k _ => ?_
  rw [norm_mul, map_div₀, map_one, map_natCast, norm_div, norm_one, hK _,
    norm_natCast_padic _ (Nat.factorial_ne_zero _)]
  have hv := padicValNat_factorial_le_sub_one (ℓ := ℓ) (m := k + 1) (by omega)
  calc ‖MvPowerSeries.coeff α (g ^ (k + 1))‖ * (1 / (ℓ : ℝ) ^ (-(padicValNat ℓ (k + 1).factorial : ℤ)))
      ≤ ‖(ℓ : K)‖ ^ (k + 1) * (ℓ : ℝ) ^ (padicValNat ℓ (k + 1).factorial) := by
        rw [zpow_neg, one_div, inv_inv, zpow_natCast]
        exact mul_le_mul_of_nonneg_right (norm_coeff_pow_le_of_isDivK hg _ _) (by positivity)
    _ ≤ ‖(ℓ : K)‖ ^ (k + 1) * (ℓ : ℝ) ^ k := by
        gcongr
        omega
    _ = ‖(ℓ : K)‖ := by
        rw [hℓn, pow_succ, inv_pow]
        field_simp

omit [IsUltrametricDist K] in
/-- **Frobenius commutes with `exp`**. -/
theorem frobS_exp_subst (φ : K →+* K) [CharZero K] {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    frobS ℓ φ ((PowerSeries.exp K).subst f) = (PowerSeries.exp K).subst (frobS ℓ φ f) := by
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  have hmf : PowerSeries.HasSubst (MvPowerSeries.map φ f) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [MvPowerSeries.constantCoeff_map, hf, map_zero])
  change MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ ((PowerSeries.exp K).subst f)) =
    (PowerSeries.exp K).subst (MvPowerSeries.expand ℓ hℓp.out.ne_zero (MvPowerSeries.map φ f))
  rw [PowerSeries.map_subst hfs, PowerSeries.map_exp, PowerSeries.expand_subst _ _ hmf]

/-- **Dwork's lemma**: if `f` has no constant term and its Dwork defect `f^φ(X^ℓ) − ℓf` is `ℓ`-divisible, then
`exp(f)` is integral (`φ` a Frobenius lift, the norm on `ℕ` `ℓ`-adic). -/
theorem dwork [CharZero K] [Finite σ] (hK : ∀ n : ℕ, ‖(n : K)‖ = ‖(n : ℚ_[ℓ])‖) {φ : K →+* K}
    (hφ : ∀ x : K, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : K)‖) {f : MvPowerSeries σ K}
    (hf0 : MvPowerSeries.constantCoeff f = 0) (hD : IsDivK ℓ (frobS ℓ φ f - ℓ • f)) :
    IsIntK ((PowerSeries.exp K).subst f) := by
  have hfr0 : MvPowerSeries.constantCoeff (frobS ℓ φ f) = 0 := by rw [constantCoeff_frobS, hf0, map_zero]
  have hnf0 : MvPowerSeries.constantCoeff (ℓ • f) = 0 := by rw [map_nsmul, hf0, smul_zero]
  have hD0 : MvPowerSeries.constantCoeff (frobS ℓ φ f - ℓ • f) = 0 := by rw [map_sub, hfr0, hnf0, sub_zero]
  refine isIntK_of_frobS_eq hφ (V := (PowerSeries.exp K).subst (frobS ℓ φ f - ℓ • f)) ?_
    (isDivK_exp_sub_one hK hD hD0) ?_
  · rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hf0]
    simp
  · rw [frobS_exp_subst φ hf0, ← exp_subst_nsmul hf0, ← exp_subst_add hnf0 hD0, add_sub_cancel]

end Dwork

/-! ## The Gaussian equivalence `≃` -/

section Gauss

variable {σ : Type} {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **Integrality** of a multivariate series over `ℂ_ℓ`: every coefficient in the unit ball (D1Spec's `IntS`). -/
def IntS (f : MvPowerSeries σ ℂ_[ℓ]) : Prop :=
  ∀ n, ‖MvPowerSeries.coeff n f‖ ≤ 1

/-- **The exponential** of a power series without constant term, as `Σ f^k/k!` (coefficientwise finite;
D1Spec's `expMv`). -/
def expMv (f : MvPowerSeries σ ℂ_[ℓ]) : MvPowerSeries σ ℂ_[ℓ] :=
  fun α => ∑ k ∈ Finset.range ((α.sum fun _ e => e) + 1), MvPowerSeries.coeff α (f ^ k) / (k.factorial : ℂ_[ℓ])

/-- **The Gaussian equivalence** `f ≃ g`: equal constant terms and `exp(f − g)` integral (D1Spec's `Simeq`). -/
def Simeq (f g : MvPowerSeries σ ℂ_[ℓ]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntS (expMv (f - g))

/-- **The coefficients of `expMv`**, by definition. -/
theorem coeff_expMv (f : MvPowerSeries σ ℂ_[ℓ]) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (expMv f) =
      ∑ k ∈ Finset.range ((α.sum fun _ e => e) + 1), MvPowerSeries.coeff α (f ^ k) / (k.factorial : ℂ_[ℓ]) :=
  rfl

/-- **`expMv` is `exp`**: `expMv f = exp(f)` as a substitution, for `f` without constant term. -/
theorem expMv_eq_subst {f : MvPowerSeries σ ℂ_[ℓ]} (hf : MvPowerSeries.constantCoeff f = 0) :
    expMv f = (PowerSeries.exp ℂ_[ℓ]).subst f := by
  ext α
  rw [coeff_exp_subst hf, coeff_expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_inv_mul, mul_comm]
  congr 1
  simp

/-- **`exp` is additive**: `exp(f + g) = exp(f)·exp(g)` for `f, g` without constant term. -/
theorem expMv_add {f g : MvPowerSeries σ ℂ_[ℓ]} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
  have hfg : MvPowerSeries.constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  rw [expMv_eq_subst hfg, expMv_eq_subst hf, expMv_eq_subst hg, exp_subst_add hf hg]

/-- **`exp(0) = 1`.** -/
theorem expMv_zero : expMv (0 : MvPowerSeries σ ℂ_[ℓ]) = 1 := by
  rw [expMv_eq_subst (map_zero _), PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

/-- **`exp(f)` has constant term `1`** for `f` without constant term. -/
theorem constantCoeff_expMv {f : MvPowerSeries σ ℂ_[ℓ]} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (expMv f) = 1 := by
  rw [expMv_eq_subst hf, PowerSeries.constantCoeff_subst_of_constantCoeff_zero hf]
  simp

/-- **`exp(−f) = exp(f)^{−1}`** for `f` without constant term. -/
theorem expMv_neg {f : MvPowerSeries σ ℂ_[ℓ]} (hf : MvPowerSeries.constantCoeff f = 0) :
    expMv (-f) = (expMv f)⁻¹ := by
  have hn : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  rw [MvPowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_expMv hf]; exact one_ne_zero),
    ← expMv_add hn hf, neg_add_cancel, expMv_zero]

/-- **`≃` is reflexive.** -/
theorem Simeq.refl (f : MvPowerSeries σ ℂ_[ℓ]) : Simeq f f := by
  refine ⟨by simp, ?_⟩
  rw [sub_self, expMv_zero]
  exact isIntK_one

/-- **`≃` is symmetric.** -/
theorem Simeq.symm {f g : MvPowerSeries σ ℂ_[ℓ]} (h : Simeq f g) : Simeq g f := by
  refine ⟨by rw [← neg_sub, map_neg, h.1, neg_zero], ?_⟩
  rw [← neg_sub, expMv_neg h.1]
  exact IsIntK.inv h.2 (constantCoeff_expMv h.1)

/-- **`≃` is transitive.** -/
theorem Simeq.trans {f g h : MvPowerSeries σ ℂ_[ℓ]} (h₁ : Simeq f g) (h₂ : Simeq g h) : Simeq f h := by
  have e : f - h = (f - g) + (g - h) := by ring
  refine ⟨by rw [e, map_add, h₁.1, h₂.1, add_zero], ?_⟩
  rw [e, expMv_add h₁.1 h₂.1]
  exact IsIntK.mul h₁.2 h₂.2

/-- **`≃` is additive.** -/
theorem Simeq.add {f g f' g' : MvPowerSeries σ ℂ_[ℓ]} (h₁ : Simeq f g) (h₂ : Simeq f' g') :
    Simeq (f + f') (g + g') := by
  have e : f + f' - (g + g') = (f - g) + (f' - g') := by ring
  refine ⟨by rw [e, map_add, h₁.1, h₂.1, add_zero], ?_⟩
  rw [e, expMv_add h₁.1 h₂.1]
  exact IsIntK.mul h₁.2 h₂.2

/-- **`≃` is stable under negation.** -/
theorem Simeq.neg {f g : MvPowerSeries σ ℂ_[ℓ]} (h : Simeq f g) : Simeq (-f) (-g) := by
  have e : -f - -g = -(f - g) := by ring
  refine ⟨by rw [e, map_neg, h.1, neg_zero], ?_⟩
  rw [e, expMv_neg h.1]
  exact IsIntK.inv h.2 (constantCoeff_expMv h.1)

/-- **`f ≃ g` iff `f − g ≃ 0`.** -/
theorem simeq_iff_sub {f g : MvPowerSeries σ ℂ_[ℓ]} : Simeq f g ↔ Simeq (f - g) 0 := by
  simp [Simeq]

/-- **`≃` is stable under integral substitution** (with zero constant terms). -/
theorem Simeq.subst {τ : Type} [Finite σ] {f g : MvPowerSeries σ ℂ_[ℓ]} (h : Simeq f g)
    {ψ : σ → MvPowerSeries τ ℂ_[ℓ]} (hψ : ∀ s, IntS (ψ s)) (hψ0 : ∀ s, MvPowerSeries.constantCoeff (ψ s) = 0) :
    Simeq (f.subst ψ) (g.subst ψ) := by
  have hb : MvPowerSeries.HasSubst ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0
  have e : f.subst ψ - g.subst ψ = (f - g).subst ψ := (MvPowerSeries.subst_sub hb f g).symm
  have h0 : MvPowerSeries.constantCoeff ((f - g).subst ψ) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hb hψ0 h.1
  refine ⟨by rw [e, h0], ?_⟩
  have key : expMv ((f - g).subst ψ) = (expMv (f - g)).subst ψ := by
    rw [expMv_eq_subst h0, expMv_eq_subst h.1, PowerSeries.subst_def, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero h.1).const hb]
  rw [e, key]
  exact IsIntK.subst h.2 hψ hψ0

/-- **Legendre's bound** `v_ℓ(k!) ≤ k`. -/
theorem padicValNat_factorial_le (k : ℕ) : padicValNat ℓ k.factorial ≤ k := by
  have h := sub_one_mul_padicValNat_factorial (p := ℓ) k
  have h1 : 1 ≤ ℓ - 1 := by have := hℓp.out.two_le; omega
  calc padicValNat ℓ k.factorial ≤ (ℓ - 1) * padicValNat ℓ k.factorial := Nat.le_mul_of_pos_left _ h1
    _ ≤ k := by rw [h]; exact Nat.sub_le _ _

/-- **Divided powers of `ℓ`**: `‖ℓ^k/k!‖ ≤ 1`. -/
theorem norm_pow_div_factorial_le (k : ℕ) : ‖(ℓ : ℂ_[ℓ]) ^ k / (k.factorial : ℂ_[ℓ])‖ ≤ 1 := by
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.out.one_le
  rw [norm_div, norm_pow, norm_ell_padicC, norm_natCast_padicC _ (Nat.factorial_ne_zero k), div_le_one
    (by positivity), inv_pow, ← zpow_natCast, ← zpow_neg]
  exact zpow_le_zpow_right₀ hℓ1 (by have := padicValNat_factorial_le (ℓ := ℓ) k; omega)

/-- **`ℓ·(integral) ≃ 0`**: `exp(ℓf)` is integral for integral `f` without constant term. -/
theorem simeq_smul_ell {f : MvPowerSeries σ ℂ_[ℓ]} (hf : IntS f) (h0 : MvPowerSeries.constantCoeff f = 0) :
    Simeq ((ℓ : ℂ_[ℓ]) • f) 0 := by
  refine ⟨by simp [h0], fun α => ?_⟩
  rw [sub_zero, coeff_expMv]
  apply (ball1 ℂ_[ℓ]).sum_mem
  intro k _
  change ‖_‖ ≤ 1
  rw [smul_pow, MvPowerSeries.coeff_smul, mul_div_right_comm, norm_mul]
  obtain ⟨f', rfl⟩ := (isIntK_iff f).1 hf
  exact mul_le_one_of_le (norm_pow_div_factorial_le k) (by
    rw [← map_pow, MvPowerSeries.coeff_map]; exact (MvPowerSeries.coeff α (f' ^ k)).2)

/-- **Dwork's criterion for `≃`** in `ℂ_ℓ`: for a series with coefficients in a subfield `k` carrying a Frobenius
lift `φ` (on the unit ball, `‖φ x − x^ℓ‖ ≤ ‖ℓ‖`), `f ≃ 0` as soon as `f` has no constant term and its Dwork defect
`f^φ(X^ℓ) − ℓf` is `ℓ`-divisible. -/
theorem simeq_zero_of_dwork [Finite σ] (k : Subfield ℂ_[ℓ]) {φ : k →+* k}
    (hφ : ∀ x : k, ‖x‖ ≤ 1 → ‖φ x - x ^ ℓ‖ ≤ ‖(ℓ : k)‖) {f : MvPowerSeries σ k}
    (hf0 : MvPowerSeries.constantCoeff f = 0) (hD : IsDivK ℓ (frobS ℓ φ f - ℓ • f)) :
    Simeq (MvPowerSeries.map k.subtype f) 0 := by
  have hK : ∀ n : ℕ, ‖(n : k)‖ = ‖(n : ℚ_[ℓ])‖ := fun n => by
    change ‖((n : k) : ℂ_[ℓ])‖ = _
    have e1 : ((n : k) : ℂ_[ℓ]) = (n : ℂ_[ℓ]) := map_natCast k.subtype n
    have e2 : ((n : ℚ_[ℓ]) : ℂ_[ℓ]) = (n : ℂ_[ℓ]) := by norm_cast
    rw [e1, ← e2, PadicComplex.norm_extends']
  have hm0 : MvPowerSeries.constantCoeff (MvPowerSeries.map k.subtype f) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hf0, map_zero]
  refine ⟨by rw [sub_zero, hm0], ?_⟩
  have hint := dwork hK hφ hf0 hD
  rw [sub_zero, expMv_eq_subst hm0, ← PowerSeries.map_exp k.subtype,
    ← PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf0)]
  intro α
  rw [MvPowerSeries.coeff_map]
  exact hint α

end Gauss

/-! ## The explicit Gaussian pairing `serAB` -/

section SerAB

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

open Classical in
/-- **The explicit Gaussian pairing** on the height-2 Lubin–Tate group in LT coordinates (D1Spec's `serAB`):
`serAB(X, Y) = Σ_{i ≤ j} (X^{ℓ^{2i}}Y^{ℓ^{2j+1}} + Y^{ℓ^{2i}}X^{ℓ^{2j+1}})/ℓ^{i+j+1}`. -/
def serAB (ℓ : ℕ) [Fact ℓ.Prime] : MvPowerSeries (Fin 2) ℂ_[ℓ] :=
  fun n => ∑ i ∈ Finset.range (n 0 + n 1 + 1), ∑ j ∈ Finset.range (n 0 + n 1 + 1),
    if i ≤ j ∧ ((n 0 = ℓ ^ (2 * i) ∧ n 1 = ℓ ^ (2 * j + 1)) ∨ (n 1 = ℓ ^ (2 * i) ∧ n 0 = ℓ ^ (2 * j + 1)))
    then ((ℓ : ℂ_[ℓ]) ^ (i + j + 1))⁻¹ else 0

/-- **The support of `serAB`**: `X^aY^b` with `(a, b) = (ℓ^{2i}, ℓ^{2j+1})` or `(ℓ^{2j+1}, ℓ^{2i})`, `i ≤ j`. -/
def SupAB (ℓ a b i j : ℕ) : Prop :=
  i ≤ j ∧ ((a = ℓ ^ (2 * i) ∧ b = ℓ ^ (2 * j + 1)) ∨ (b = ℓ ^ (2 * i) ∧ a = ℓ ^ (2 * j + 1)))

/-- **Powers of `ℓ` are injective.** -/
theorem pow_inj {m m' : ℕ} (h : ℓ ^ m = ℓ ^ m') : m = m' :=
  Nat.pow_right_injective hℓp.out.two_le h

/-- **The support pair of `serAB` is unique.** -/
theorem supAB_unique {a b i j i' j' : ℕ} (h : SupAB ℓ a b i j) (h' : SupAB ℓ a b i' j') : i = i' ∧ j = j' := by
  rcases h with ⟨-, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩ <;> rcases h' with ⟨-, ⟨ha', hb'⟩ | ⟨hb', ha'⟩⟩
  · have h1 := pow_inj (ha.symm.trans ha')
    have h2 := pow_inj (hb.symm.trans hb')
    omega
  · have := pow_inj (ha.symm.trans ha'); omega
  · have := pow_inj (ha.symm.trans ha'); omega
  · have h1 := pow_inj (hb.symm.trans hb')
    have h2 := pow_inj (ha.symm.trans ha')
    omega

/-- **The coefficients of `serAB` on its support**: `S = ℓ^{−(i+j+1)}`. -/
theorem coeff_serAB_of {n : Fin 2 →₀ ℕ} {i j : ℕ} (h : SupAB ℓ (n 0) (n 1) i j) :
    MvPowerSeries.coeff n (serAB ℓ) = ((ℓ : ℂ_[ℓ]) ^ (i + j + 1))⁻¹ := by
  have hlt : ∀ m : ℕ, m < ℓ ^ m := fun m => Nat.lt_pow_self hℓp.out.one_lt
  have hi : i ∈ Finset.range (n 0 + n 1 + 1) := by
    rcases h with ⟨-, ⟨ha, -⟩ | ⟨hb, -⟩⟩
    · have := hlt (2 * i); rw [Finset.mem_range]; omega
    · have := hlt (2 * i); rw [Finset.mem_range]; omega
  have hj : j ∈ Finset.range (n 0 + n 1 + 1) := by
    rcases h with ⟨-, ⟨-, hb⟩ | ⟨-, ha⟩⟩
    · have := hlt (2 * j + 1); rw [Finset.mem_range]; omega
    · have := hlt (2 * j + 1); rw [Finset.mem_range]; omega
  change serAB ℓ n = _
  simp only [serAB]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · exact ite_eq_left h
  · intro j' _ hj'
    exact ite_eq_right fun h' => hj' (supAB_unique h h').2.symm
  · intro hj'; exact absurd hj hj'
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun j' _ => ite_eq_right fun h' => hi' (supAB_unique h h').1.symm
  · intro hi'; exact absurd hi hi'

/-- **The coefficients of `serAB` off its support** vanish. -/
theorem coeff_serAB_of_not {n : Fin 2 →₀ ℕ} (h : ∀ i j, ¬ SupAB ℓ (n 0) (n 1) i j) :
    MvPowerSeries.coeff n (serAB ℓ) = 0 := by
  change serAB ℓ n = 0
  simp only [serAB]
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ite_eq_right (h i j)

/-- **`serAB` is symmetric**: its coefficient depends symmetrically on the two exponents. -/
theorem coeff_serAB_swap {n n' : Fin 2 →₀ ℕ} (h0 : n' 0 = n 1) (h1 : n' 1 = n 0) :
    MvPowerSeries.coeff n' (serAB ℓ) = MvPowerSeries.coeff n (serAB ℓ) := by
  change serAB ℓ n' = serAB ℓ n
  simp only [serAB]
  rw [h0, h1, add_comm (n 1)]
  simp only [or_comm]

/-- **Teichmüller points**: `ζ^{ℓ²} = ζ` gives `ζ^{ℓ^{2i}} = ζ`. -/
theorem pow_pow_two_mul {ζ : ℂ_[ℓ]} (hζ : ζ ^ (ℓ ^ 2) = ζ) (i : ℕ) : ζ ^ (ℓ ^ (2 * i)) = ζ := by
  induction i with
  | zero => simp
  | succ i ih => rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, pow_mul, ih, hζ]

/-- **`serAB` is hermitian** for the Teichmüller action: `ζ^a·s_{a,b} = (ζ^ℓ)^b·s_{a,b}` when `ζ^{ℓ²} = ζ`, i.e.
`serAB(ζX, Y) = serAB(X, ζ̄Y)` with `ζ̄ = ζ^ℓ`. -/
theorem coeff_serAB_herm {ζ : ℂ_[ℓ]} (hζ : ζ ^ (ℓ ^ 2) = ζ) (n : Fin 2 →₀ ℕ) :
    ζ ^ (n 0) * MvPowerSeries.coeff n (serAB ℓ) = (ζ ^ ℓ) ^ (n 1) * MvPowerSeries.coeff n (serAB ℓ) := by
  by_cases h : ∃ i j, SupAB ℓ (n 0) (n 1) i j
  · obtain ⟨i, j, hij⟩ := h
    congr 1
    rcases hij with ⟨-, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
    · rw [ha, hb, pow_pow_two_mul hζ, ← pow_mul, ← pow_succ', show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
        pow_pow_two_mul hζ]
    · rw [ha, hb, pow_succ, pow_mul, pow_pow_two_mul hζ, pow_right_comm, pow_pow_two_mul hζ]
  · push Not at h
    rw [coeff_serAB_of_not h, mul_zero, mul_zero]

/-- **The coefficient** `S_{a,b}` of `X^aY^b` in `serAB`. -/
abbrev sAB (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℕ) : ℂ_[ℓ] :=
  MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) (serAB ℓ)

/-- **`S_{a,b}` on the support**: `ℓ^{−(i+j+1)}`. -/
theorem sAB_of {a b i j : ℕ} (h : SupAB ℓ a b i j) : sAB ℓ a b = ((ℓ : ℂ_[ℓ]) ^ (i + j + 1))⁻¹ :=
  coeff_serAB_of (by simpa using h)

/-- **`S_{a,b}` off the support** vanishes. -/
theorem sAB_of_not {a b : ℕ} (h : ∀ i j, ¬ SupAB ℓ a b i j) : sAB ℓ a b = 0 :=
  coeff_serAB_of_not (by simpa using h)

/-- **`S` is symmetric**: `S_{a,b} = S_{b,a}`. -/
theorem sAB_swap (a b : ℕ) : sAB ℓ a b = sAB ℓ b a :=
  coeff_serAB_swap (by simp) (by simp)

/-- **The coefficients of `log_LT(T^ℓ)`**: `L(a/ℓ)` if `ℓ ∣ a`, else `0`. -/
def lcF (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) : ℂ_[ℓ] := if ℓ ∣ a then coeff (a / ℓ) (logLT ℂ_[ℓ] ℓ) else 0

/-- **`L_{ℓ^{2k}} = ℓ^{−k}`.** -/
theorem lc_pow (k : ℕ) : coeff (ℓ ^ (2 * k)) (logLT ℂ_[ℓ] ℓ) = ((ℓ : ℂ_[ℓ]) ^ k)⁻¹ :=
  coeff_logLT_pow _ hℓp.out.one_lt k

/-- **`L_a = 0`** off the even powers of `ℓ`. -/
theorem lc_of_not {a : ℕ} (h : ∀ k, a ≠ ℓ ^ (2 * k)) : coeff a (logLT ℂ_[ℓ] ℓ) = 0 :=
  coeff_logLT_of_ne _ h

/-- **`L^F_{ℓ^{2k+1}} = ℓ^{−k}`.** -/
theorem lcF_pow (k : ℕ) : lcF ℓ (ℓ ^ (2 * k + 1)) = ((ℓ : ℂ_[ℓ]) ^ k)⁻¹ := by
  rw [lcF, ite_eq_left (dvd_pow_self ℓ (by omega)), pow_succ, Nat.mul_div_cancel _ hℓp.out.pos, lc_pow]

/-- **`L^F_a = 0`** off the odd powers of `ℓ`. -/
theorem lcF_of_not {a : ℕ} (h : ∀ k, a ≠ ℓ ^ (2 * k + 1)) : lcF ℓ a = 0 := by
  rw [lcF]
  split_ifs with hd
  · refine lc_of_not fun k hk => h k ?_
    rw [pow_succ, ← hk, Nat.div_mul_cancel hd]
  · rfl

/-- **Even and odd powers of `ℓ` differ.** -/
theorem pow_even_ne_odd (k k' : ℕ) : ℓ ^ (2 * k) ≠ ℓ ^ (2 * k' + 1) := fun h => by
  have := pow_inj h; omega

/-- **`ℓ^{m+1}/ℓ = ℓ^m`.** -/
theorem pow_succ_div_ell (m : ℕ) : ℓ ^ (m + 1) / ℓ = ℓ ^ m := by
  rw [pow_succ, Nat.mul_div_cancel _ hℓp.out.pos]

/-- **The Frobenius term** `[ℓ ∣ a, b]·S_{a/ℓ, b/ℓ}`: the coefficient of `X^aY^b` in `serAB(X^ℓ, Y^ℓ)`. -/
def frobT (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℕ) : ℂ_[ℓ] := if ℓ ∣ a ∧ ℓ ∣ b then sAB ℓ (a / ℓ) (b / ℓ) else 0

/-- **The Frobenius term is symmetric.** -/
theorem frobT_swap (a b : ℕ) : frobT ℓ a b = frobT ℓ b a := by
  unfold frobT
  by_cases h : ℓ ∣ a ∧ ℓ ∣ b
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩, sAB_swap]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.2, h'.1⟩]

/-- **The defect identity at `(ℓ^{2k}, ℓ^{2k'+1})`**: one of the two terms carries `ℓ^{−k−k'}`. -/
theorem serAB_frob_evenOdd (k k' : ℕ) :
    frobT ℓ (ℓ ^ (2 * k)) (ℓ ^ (2 * k' + 1)) + ℓ * sAB ℓ (ℓ ^ (2 * k)) (ℓ ^ (2 * k' + 1)) =
      lcF ℓ (ℓ ^ (2 * k)) * coeff (ℓ ^ (2 * k' + 1)) (logLT ℂ_[ℓ] ℓ) +
        coeff (ℓ ^ (2 * k)) (logLT ℂ_[ℓ] ℓ) * lcF ℓ (ℓ ^ (2 * k' + 1)) := by
  have hℓ0 : (ℓ : ℂ_[ℓ]) ≠ 0 := by exact_mod_cast hℓp.out.ne_zero
  rw [lcF_of_not fun m => pow_even_ne_odd k m, lc_pow, lcF_pow, zero_mul, zero_add, ← mul_inv, ← pow_add]
  rcases Nat.lt_or_ge k' k with hk | hk
  · -- `k' < k`: the Frobenius term carries everything
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e1 : ℓ ^ (2 * (m + 1)) / ℓ = ℓ ^ (2 * m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ_div_ell]
    have hS : sAB ℓ (ℓ ^ (2 * (m + 1))) (ℓ ^ (2 * k' + 1)) = 0 := sAB_of_not fun i j h => by
      rcases h with ⟨hij, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
      · have := pow_inj ha; have := pow_inj hb; omega
      · exact pow_even_ne_odd _ _ hb.symm
    rw [frobT, ite_eq_left ⟨dvd_pow_self ℓ (by omega), dvd_pow_self ℓ (by omega)⟩, e1, pow_succ_div_ell,
      sAB_of (i := k') (j := m) ⟨by omega, Or.inr ⟨rfl, rfl⟩⟩, hS, mul_zero, add_zero]
    congr 2
    ring
  · -- `k ≤ k'`: the `ℓ·S` term carries everything
    rw [sAB_of (i := k) (j := k') ⟨hk, Or.inl ⟨rfl, rfl⟩⟩]
    have hfrob : frobT ℓ (ℓ ^ (2 * k)) (ℓ ^ (2 * k' + 1)) = 0 := by
      unfold frobT
      split_ifs with hd
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · have h1 : ℓ ∣ 1 := by simpa using hd.1
          exact absurd h1 hℓp.out.not_dvd_one
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ_div_ell, pow_succ_div_ell]
          refine sAB_of_not fun i j h => ?_
          rcases h with ⟨hij, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
          · exact pow_even_ne_odd _ _ ha.symm
          · have := pow_inj ha; have := pow_inj hb; omega
      · rfl
    rw [hfrob, zero_add, pow_succ, mul_inv]
    field_simp

/-- **The Frobenius defect of `serAB`**, coefficientwise:
`[ℓ ∣ a, b]·S_{a/ℓ,b/ℓ} + ℓ·S_{a,b} = L^F_a·L_b + L_a·L^F_b`, with `L` the coefficients of `log_LT` and `L^F` those
of `log_LT(T^ℓ)`. Hence for `c̄ = −c` the Dwork defect `c̄·serAB(X^ℓ, Y^ℓ) − ℓc·serAB` of `c·serAB` is
`−c·(log_LT(X^ℓ)log_LT(Y) + log_LT(X)log_LT(Y^ℓ))`. -/
theorem serAB_frob (a b : ℕ) :
    frobT ℓ a b + ℓ * sAB ℓ a b = lcF ℓ a * coeff b (logLT ℂ_[ℓ] ℓ) + coeff a (logLT ℂ_[ℓ] ℓ) * lcF ℓ b := by
  by_cases hA : ∃ k k', a = ℓ ^ (2 * k) ∧ b = ℓ ^ (2 * k' + 1)
  · obtain ⟨k, k', rfl, rfl⟩ := hA
    exact serAB_frob_evenOdd k k'
  by_cases hB : ∃ k k', a = ℓ ^ (2 * k + 1) ∧ b = ℓ ^ (2 * k')
  · obtain ⟨k, k', rfl, rfl⟩ := hB
    have := serAB_frob_evenOdd (ℓ := ℓ) k' k
    rw [frobT_swap, sAB_swap, this]
    ring
  push Not at hA hB
  have hS : ∀ a b : ℕ, (∀ k k', a = ℓ ^ (2 * k) → b ≠ ℓ ^ (2 * k' + 1)) →
      (∀ k k', a = ℓ ^ (2 * k + 1) → b ≠ ℓ ^ (2 * k')) → sAB ℓ a b = 0 := fun a b hA hB =>
    sAB_of_not fun i j h => by
      rcases h with ⟨-, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
      · exact hA i j ha hb
      · exact hB j i ha hb
  rw [hS a b hA hB, mul_zero, add_zero]
  have hR1 : lcF ℓ a * coeff b (logLT ℂ_[ℓ] ℓ) = 0 := by
    by_cases ha : ∃ k, a = ℓ ^ (2 * k + 1)
    · obtain ⟨k, rfl⟩ := ha
      rw [lc_of_not fun k' hb => hB k k' rfl hb, mul_zero]
    · push Not at ha; rw [lcF_of_not ha, zero_mul]
  have hR2 : coeff a (logLT ℂ_[ℓ] ℓ) * lcF ℓ b = 0 := by
    by_cases ha : ∃ k, a = ℓ ^ (2 * k)
    · obtain ⟨k, rfl⟩ := ha
      rw [lcF_of_not fun k' hb => hA k k' rfl hb, mul_zero]
    · push Not at ha; rw [lc_of_not ha, zero_mul]
  rw [hR1, hR2, add_zero]
  unfold frobT
  split_ifs with hd
  · obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hd
    rw [Nat.mul_div_cancel_left _ hℓp.out.pos, Nat.mul_div_cancel_left _ hℓp.out.pos]
    refine hS a' b' (fun k k' ha hb => hB k (k' + 1) ?_ ?_) (fun k k' ha hb => hA (k + 1) k' ?_ ?_)
    · rw [ha]; ring
    · rw [hb]; ring
    · rw [ha]; ring
    · rw [hb]; ring
  · rfl

/-- **The twisted logarithm** `log_LT(T^ℓ)`. -/
def logLTF (ℓ : ℕ) [Fact ℓ.Prime] : ℂ_[ℓ]⟦X⟧ := PowerSeries.subst (X ^ ℓ : ℂ_[ℓ]⟦X⟧) (logLT ℂ_[ℓ] ℓ)

/-- **The coefficients of `log_LT(T^ℓ)`** are `L^F`. -/
theorem coeff_logLTF (a : ℕ) : coeff a (logLTF ℓ) = lcF ℓ a := by
  rw [logLTF, coeff_subst_X_pow hℓp.out.ne_zero, lcF]
  rfl

/-- **Products of series in separate variables**: `[X^aY^b] f(X)g(Y) = f_a·g_b`. -/
theorem coeff_subst_X0_mul_subst_X1 (f g : ℂ_[ℓ]⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
      g.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ])) = coeff (e 0) f * coeff (e 1) g := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1)) ?_ ?_]
  · grind [coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq, ite_eq_right_iff, not_forall, exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff, ← Finset.HasAntidiagonal.mem_antidiagonal.mp hb, h0.1, h1.1]
    simp
  · intro he
    have he' : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
      ext i
      fin_cases i <;> simp
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr he') he

/-- **Exponents in two variables** split as `a·e₀ + b·e₁`. -/
theorem eq_single_add_single (n : Fin 2 →₀ ℕ) : n = Finsupp.single 0 (n 0) + Finsupp.single 1 (n 1) := by
  ext i
  fin_cases i <;> simp

/-- **The coefficients of `serAB(X^ℓ, Y^ℓ)`** are the Frobenius terms. -/
theorem coeff_expand_serAB (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.expand ℓ hℓp.out.ne_zero (serAB ℓ)) = frobT ℓ (n 0) (n 1) := by
  unfold frobT
  split_ifs with hd
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hd
    have hn : n = ℓ • (Finsupp.single 0 a + Finsupp.single 1 b) := by
      rw [eq_single_add_single n, ha, hb]
      ext i
      fin_cases i <;> simp
    rw [ha, hb, Nat.mul_div_cancel_left _ hℓp.out.pos, Nat.mul_div_cancel_left _ hℓp.out.pos]
    conv_lhs => rw [hn]
    rw [MvPowerSeries.coeff_expand_smul]
  · rcases not_and_or.1 hd with h | h
    · exact MvPowerSeries.coeff_expand_of_not_dvd ℓ hℓp.out.ne_zero (serAB ℓ) h
    · exact MvPowerSeries.coeff_expand_of_not_dvd ℓ hℓp.out.ne_zero (serAB ℓ) h

/-- **The Frobenius defect of `serAB`** as a series identity:
`serAB(X^ℓ, Y^ℓ) + ℓ·serAB(X, Y) = log_LT(X^ℓ)·log_LT(Y) + log_LT(X)·log_LT(Y^ℓ)`. -/
theorem expand_serAB_add_smul :
    MvPowerSeries.expand ℓ hℓp.out.ne_zero (serAB ℓ) + (ℓ : ℂ_[ℓ]) • serAB ℓ =
      (logLTF ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
          (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) +
        (logLT ℂ_[ℓ] ℓ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[ℓ]) *
          (logLTF ℓ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[ℓ]) := by
  ext n
  rw [map_add, map_add, coeff_expand_serAB, MvPowerSeries.coeff_smul, coeff_subst_X0_mul_subst_X1,
    coeff_subst_X0_mul_subst_X1, coeff_logLTF, coeff_logLTF]
  have := serAB_frob (ℓ := ℓ) (n 0) (n 1)
  rwa [sAB, ← eq_single_add_single] at this

end SerAB

end

end CMFormalInert
