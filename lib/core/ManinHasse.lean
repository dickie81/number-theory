/-
# Hasse's bound for every elliptic curve over a finite field of odd characteristic: Manin's proof

Plain statement. Let `𝔽_q` be a finite field of characteristic not `2`, and `E` an elliptic curve over `𝔽_q`: a
`WeierstrassCurve` with `[E.IsElliptic]` (nonzero discriminant), in any Weierstrass form
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. Count its points `E.toAffine.Point` with the point at infinity. Then
`|q + 1 − #E(𝔽_q)| ≤ 2√q` (`abs_trace_le`), that is `(q + 1 − #E(𝔽_q))² ≤ 4q` (`trace_sq_le`). No hypothesis
beyond these.

Completing the square, `y ↦ y + (a₁x + a₃)/2`, matches the points of `E` with those of
`y² = x³ + (b₂/4)x² + (b₄/2)x + b₆/4` (`cubicEquiv`), whose discriminant is `E`'s (`dsc_mul_eq_Δ`). For a curve
`y² = f(x)` with `f = x³ + a₂x² + a₄x + a₆` without double roots, this is Manin's elementary proof (1956), with no
isogenies (`cubic_trace_sq_le`). Let `s = f(t)`. Over `𝔽_q(t)`, the twist `E'`: `y² = x³ + a₂sx² + a₄s²x + a₆s³`
carries `P₀ = (st, s²)` and the Frobenius point `P₁ = (st^q, s^{(q+3)/2})` (`P1`). Write `deg P` for the degree of the
rational function `x(P)/s` (`ManinTwist`).
* `d(n) = deg(P₁ + nP₀)` satisfies `d(n + 1) + d(n − 1) = 2d(n) + 2` (`ManinTwist.pdeg_add_add_pdeg_sub`). So
  `d(n) = n² + cn + d(0)` (`quadratic_of_second_difference`).
* `d(0) = q` (`pdeg_P1`).
* `d(−1) = #E(𝔽_q)` (`pdeg_P1_sub_P0`).
  - `x(P₁ − P₀)/s = U/(t^q − t)²` with `U = f(f^m + 1)² − (t^q + t + a₂)(t^q − t)²` and `m = (q − 1)/2`.
  - At `c ∈ 𝔽_q`, `U(c) = f(c)(f(c)^m + 1)²`. So `t − c` divides `U` at least twice if `f(c)` is not a square
    (`f(c)^m = −1`). It divides `U` exactly once if `f(c) = 0`, as `f` has no double root. It does not divide `U` if
    `f(c)` is a nonzero square (`mult`).
  - In lowest terms, `U/(t^q − t)²` has degree `2q + 1 − Σ mult(c) = 1 + Σ (2 − mult(c))` (`rdeg_div_prod`). Here
    `2 − mult(c)` counts the `y` with `y² = f(c)`, so this degree is `#E(𝔽_q)`.
* So `c = q + 1 − #E(𝔽_q)`. Since `n² + cn + q ≥ 0` for every integer `n` and `q` is odd, `c² ≤ 4q`
  (`sq_le_of_forall_nonneg`).

`HasseEisenstein` proves the same bound for `y² = x³ + D` with Jacobi sums. That is the rank-two case of the research
direction in `docs/ball-conjecture.md`.
-/
import ManinTwist

open Polynomial ManinDegree Finset

namespace ManinHasse

/-! ## Integer sequences with second difference `2` -/

lemma eq_zero_of_second_difference {e : ℤ → ℤ} (h : ∀ n, e (n + 1) + e (n - 1) = 2 * e n) (h0 : e 0 = 0)
    (h1 : e 1 = 0) (n : ℤ) : e n = 0 := by
  have up : ∀ k : ℕ, e k = 0 ∧ e (k + 1) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using h0, by simpa using h1⟩
    | succ k ih =>
      have hk := h (k + 1)
      rw [add_sub_cancel_right, ih.1, ih.2] at hk
      rw [Nat.cast_succ]
      exact ⟨ih.2, by linarith⟩
  have down : ∀ k : ℕ, e (-k) = 0 ∧ e (-k + 1) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using h0, by simpa using h1⟩
    | succ k ih =>
      have hk := h (-k)
      rw [ih.1, ih.2] at hk
      rw [Nat.cast_succ, show -((k : ℤ) + 1) = -k - 1 by ring, sub_add_cancel]
      exact ⟨by linarith, ih.1⟩
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact (up k).1
  · exact (down k).1

/-- **A sequence with constant second difference `2` is `n² + cn + d(0)`.** -/
lemma quadratic_of_second_difference {d : ℤ → ℤ} (h : ∀ n, d (n + 1) + d (n - 1) = 2 * d n + 2) (n : ℤ) :
    d n = n ^ 2 + (d 1 - d 0 - 1) * n + d 0 := by
  have := eq_zero_of_second_difference (e := fun n => d n - (n ^ 2 + (d 1 - d 0 - 1) * n + d 0))
    (fun n => by linear_combination h n) (by ring) (by ring) n
  beta_reduce at this
  linarith

/-- **If `n² + cn + Q ≥ 0` for every integer `n` and `Q` is odd, then `c² ≤ 4Q`.** -/
lemma sq_le_of_forall_nonneg {c Q : ℤ} (hQ : Q % 2 = 1) (h : ∀ n : ℤ, 0 ≤ n ^ 2 + c * n + Q) : c ^ 2 ≤ 4 * Q := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r : ℤ, (r = 0 ∨ r = 1) ∧ c = 2 * k + r :=
    ⟨c / 2, c % 2, Int.emod_two_eq_zero_or_one c, by omega⟩
  have hk := h (-k)
  rcases hr with rfl | rfl
  · nlinarith
  · obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
    have h1 : j + j ≤ Q := by nlinarith
    have h2 : j ≤ Q / 2 := by omega
    have h3 : Q = 2 * (Q / 2) + 1 := by omega
    nlinarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "ι" => algebraMap F[X] (RatFunc F)

/-! ## The degree of `U/V` from the multiplicities of the roots -/

omit [DecidableEq F] in
lemma X_pow_card_sub_X_eq_prod : (X ^ Fintype.card F - X : F[X]) = ∏ c : F, (X - C c) := by
  have hmon : (X ^ Fintype.card F - X : F[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast Fintype.one_lt_card)
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]; rfl)
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  exact h.symm

omit [DecidableEq F] in
/-- **The degree of `U/∏(X − c)²` in lowest terms.** If `(X − c)^{e(c)}` divides `U`, and `(X − c)^{e(c)+1}` does not
when `e(c) < 2`, then `U/∏_c (X − c)²` is `A/B` in lowest terms with `deg A = deg U − Σ e` and `deg B = Σ (2 − e)`. -/
lemma rdeg_div_prod {U : F[X]} (hU : U ≠ 0) (e : F → ℕ) (he : ∀ c, e c ≤ 2)
    (hdvd : ∀ c, (X - C c) ^ e c ∣ U) (hndvd : ∀ c, e c < 2 → ¬(X - C c) ^ (e c + 1) ∣ U) :
    rdeg (ι U / ι (∏ c : F, (X - C c) ^ 2)) = max (U.natDegree - ∑ c, e c) (∑ c, (2 - e c)) := by
  have hcop : Pairwise (Function.onFun IsCoprime fun c : F => (X - C c) ^ e c) := fun c c' hcc' => by
    simp only [Function.onFun]
    exact (pairwise_coprime_X_sub_C (s := id) Function.injective_id hcc').pow
  obtain ⟨A, hA⟩ := Fintype.prod_dvd_of_coprime hcop hdvd
  have hGB : ∏ c : F, (X - C c) ^ 2 = (∏ c : F, (X - C c) ^ e c) * ∏ c : F, (X - C c) ^ (2 - e c) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun c _ => ?_
    rw [← pow_add, Nat.add_sub_cancel' (he c)]
  have hG0 : ∏ c : F, (X - C c) ^ e c ≠ 0 := prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (X_sub_C_ne_zero c)
  have hB0 : ∏ c : F, (X - C c) ^ (2 - e c) ≠ 0 :=
    prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (X_sub_C_ne_zero c)
  have hA0 : A ≠ 0 := by rintro rfl; rw [mul_zero] at hA; exact hU hA
  have hAB : IsCoprime A (∏ c : F, (X - C c) ^ (2 - e c)) := by
    refine IsCoprime.prod_right fun c _ => ?_
    by_cases hc : e c < 2
    · refine IsCoprime.pow_right ?_
      refine ((irreducible_X_sub_C c).coprime_iff_not_dvd.2 fun h => hndvd c hc ?_).symm
      rw [hA, pow_succ]
      exact mul_dvd_mul (dvd_prod_of_mem (fun c : F => (X - C c) ^ e c) (mem_univ c)) h
    · rw [show 2 - e c = 0 by omega, pow_zero]; exact isCoprime_one_right
  have hι : ι (∏ c : F, (X - C c) ^ e c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 hG0
  have hdG : (∏ c : F, (X - C c) ^ e c).natDegree = ∑ c, e c := by
    rw [natDegree_prod_of_monic _ _ fun c _ => (monic_X_sub_C c).pow _]
    simp [natDegree_pow]
  have hdB : (∏ c : F, (X - C c) ^ (2 - e c)).natDegree = ∑ c, (2 - e c) := by
    rw [natDegree_prod_of_monic _ _ fun c _ => (monic_X_sub_C c).pow _]
    simp [natDegree_pow]
  rw [hGB, hA, map_mul, map_mul, mul_div_mul_left _ _ hι, rdeg_div hAB hB0, natDegree_mul hG0 hA0, hdG, hdB,
    Nat.add_sub_cancel_left]

/-! ## The numerator `U` and its roots in `𝔽_q` -/

variable {a₂ a₄ a₆ : F}

omit [Fintype F] [DecidableEq F] in
lemma eval_fpol (c : F) : (fpol a₂ a₄ a₆).eval c = c ^ 3 + a₂ * c ^ 2 + a₄ * c + a₆ := by
  simp [fpol]

omit [DecidableEq F] in
lemma X_sub_C_dvd_X_pow_card_sub_X (c : F) : X - C c ∣ X ^ Fintype.card F - X := by
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_pow, eval_X, FiniteField.pow_card, sub_self]

variable (a₂ a₄ a₆) in
/-- The numerator of `x(P₁ − P₀)/s`: `U = f(f^m + 1)² − (X^q + X + a₂)(X^q − X)²`, with `m = (q − 1)/2`. -/
noncomputable def Unum : F[X] :=
  fpol a₂ a₄ a₆ * (fpol a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1) ^ 2 -
    (X ^ Fintype.card F + X + C a₂) * (X ^ Fintype.card F - X) ^ 2

omit [DecidableEq F] in
lemma eval_Unum (c : F) : (Unum a₂ a₄ a₆).eval c =
    (fpol a₂ a₄ a₆).eval c * ((fpol a₂ a₄ a₆).eval c ^ (Fintype.card F / 2) + 1) ^ 2 := by
  simp only [Unum, eval_sub, eval_mul, eval_pow, eval_add, eval_one, eval_X, eval_C, FiniteField.pow_card, sub_self]
  ring

variable (a₂ a₄ a₆) in
/-- The multiplicity of `X − c` in `gcd(U, (X^q − X)²)`: `2` if `f(c)` is not a square, `1` if `f(c) = 0`, and `0`
if `f(c)` is a nonzero square. -/
noncomputable def mult (c : F) : ℕ :=
  if (fpol a₂ a₄ a₆).eval c = 0 then 1 else if (fpol a₂ a₄ a₆).eval c ^ (Fintype.card F / 2) = 1 then 0 else 2

lemma mult_le (c : F) : mult a₂ a₄ a₆ c ≤ 2 := by
  unfold mult; split_ifs <;> omega

lemma pow_mult_dvd_Unum (hF : ringChar F ≠ 2) (c : F) : (X - C c) ^ mult a₂ a₄ a₆ c ∣ Unum a₂ a₄ a₆ := by
  unfold mult
  split_ifs with h0 h1
  · rw [pow_one]
    exact dvd_sub (dvd_mul_of_dvd_left (dvd_iff_isRoot.2 h0) _)
      (dvd_mul_of_dvd_right (dvd_pow (X_sub_C_dvd_X_pow_card_sub_X c) two_ne_zero) _)
  · rw [pow_zero]; exact one_dvd _
  · have hm1 : (fpol a₂ a₄ a₆).eval c ^ (Fintype.card F / 2) = -1 :=
      (FiniteField.pow_dichotomy hF h0).resolve_left h1
    have h1' : X - C c ∣ fpol a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1 := by
      rw [dvd_iff_isRoot, IsRoot.def, eval_add, eval_pow, eval_one, hm1, neg_add_cancel]
    exact dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd h1' 2) _)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (X_sub_C_dvd_X_pow_card_sub_X c) 2) _)

lemma not_pow_mult_succ_dvd_Unum (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (c : F)
    (hc : mult a₂ a₄ a₆ c < 2) : ¬(X - C c) ^ (mult a₂ a₄ a₆ c + 1) ∣ Unum a₂ a₄ a₆ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hm : Fintype.card F / 2 ≠ 0 := by
    have := Fintype.one_lt_card (α := F); have := FiniteField.odd_card_of_char_ne_two hF; omega
  unfold mult at hc ⊢
  split_ifs at hc ⊢ with h0 h1
  · -- `f(c) = 0`: `f = (X − c)Q` with `Q(c) = f'(c) ≠ 0`, and `(f^m + 1)(c) = 1`
    intro hdvd
    have hfac : fpol a₂ a₄ a₆ = (X - C c) * (X ^ 2 + C (c + a₂) * X + C (c ^ 2 + a₂ * c + a₄)) := by
      have e : fpol a₂ a₄ a₆ = (X - C c) * (X ^ 2 + C (c + a₂) * X + C (c ^ 2 + a₂ * c + a₄)) +
          C ((fpol a₂ a₄ a₆).eval c) := by
        rw [eval_fpol]; simp only [fpol, map_add, map_mul, map_pow]; ring
      rw [e, h0, C_0, add_zero]
    have hdvd' : (X - C c) ^ 2 ∣ fpol a₂ a₄ a₆ * (fpol a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1) ^ 2 := by
      have := dvd_add (show (X - C c) ^ 2 ∣ Unum a₂ a₄ a₆ from hdvd) (dvd_mul_of_dvd_right
        (pow_dvd_pow_of_dvd (X_sub_C_dvd_X_pow_card_sub_X c) 2) (X ^ Fintype.card F + X + C a₂))
      rwa [Unum, sub_add_cancel] at this
    have e : fpol a₂ a₄ a₆ * (fpol a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1) ^ 2 = (X - C c) *
        ((X ^ 2 + C (c + a₂) * X + C (c ^ 2 + a₂ * c + a₄)) * (fpol a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1) ^ 2) := by
      calc fpol a₂ a₄ a₆ * (fpol a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1) ^ 2 =
          ((X - C c) * (X ^ 2 + C (c + a₂) * X + C (c ^ 2 + a₂ * c + a₄))) *
            (fpol a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1) ^ 2 := by rw [← hfac]
        _ = _ := by ring
    rw [e, pow_two] at hdvd'
    have h3 := (mul_dvd_mul_iff_left (X_sub_C_ne_zero c)).1 hdvd'
    rw [dvd_iff_isRoot, IsRoot.def] at h3
    simp only [eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_one, h0, zero_pow hm, zero_add, one_pow,
      mul_one] at h3
    have h4 := h0
    rw [eval_fpol] at h4
    exact hD (by
      unfold dsc
      linear_combination (4 * a₂ ^ 3 - 18 * a₂ * a₄ - 27 * a₂ * c ^ 2 - 27 * a₄ * c + 27 * a₆ - 27 * c ^ 3) * h4 +
        (-2 * a₂ ^ 3 * c - a₂ ^ 2 * a₄ + a₂ ^ 2 * c ^ 2 + 10 * a₂ * a₄ * c + 12 * a₂ * c ^ 3 + 4 * a₄ ^ 2 +
          15 * a₄ * c ^ 2 + 9 * c ^ 4) * h3)
  · -- `f(c)` a nonzero square: `U(c) = 4f(c) ≠ 0`
    rw [zero_add, pow_one, dvd_iff_isRoot, IsRoot.def, eval_Unum, h1]
    exact mul_ne_zero h0 (pow_ne_zero 2 (by rw [one_add_one_eq_two]; exact h2))
  · omega

omit [DecidableEq F] in
lemma natDegree_Unum (hF : ringChar F ≠ 2) : (Unum a₂ a₄ a₆).natDegree = 2 * Fintype.card F + 1 := by
  obtain ⟨m, hdiv, hm⟩ : ∃ m, Fintype.card F / 2 = m ∧ Fintype.card F = 2 * m + 1 :=
    ⟨_, rfl, by have := FiniteField.odd_card_of_char_ne_two hF; omega⟩
  have hm1 : 1 ≤ m := by have := Fintype.one_lt_card (α := F); omega
  have hfq : fpol a₂ a₄ a₆ ^ Fintype.card F = X ^ (3 * Fintype.card F) + C a₂ * X ^ (2 * Fintype.card F) +
      C a₄ * X ^ Fintype.card F + C a₆ := by
    rw [← FiniteField.Polynomial.expand_card]
    simp only [fpol, map_add, map_mul, map_pow, expand_X, expand_C]
    ring
  have e : Unum a₂ a₄ a₆ = X ^ (2 * Fintype.card F + 1) + (X ^ (Fintype.card F + 2) - X ^ 3 +
      2 * C a₂ * X ^ (Fintype.card F + 1) - C a₂ * X ^ 2 + C a₄ * X ^ Fintype.card F + C a₆ +
      2 * fpol a₂ a₄ a₆ ^ (m + 1) + fpol a₂ a₄ a₆) := by
    rw [Unum, hdiv]
    rw [hm] at hfq ⊢
    linear_combination hfq
  have b1 : (X ^ (Fintype.card F + 2) : F[X]).natDegree ≤ 2 * Fintype.card F := by
    rw [natDegree_X_pow]; omega
  have b2 : (C a₄ * X ^ Fintype.card F).natDegree ≤ 2 * Fintype.card F :=
    (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
  have b3 : (C a₆).natDegree ≤ 2 * Fintype.card F := by rw [natDegree_C]; omega
  have b4 : (2 * fpol a₂ a₄ a₆ ^ (m + 1)).natDegree ≤ 2 * Fintype.card F := by
    refine natDegree_mul_le.trans ?_
    have h5 := natDegree_pow_le (p := fpol a₂ a₄ a₆) (n := m + 1)
    rw [natDegree_fpol] at h5
    rw [natDegree_ofNat]
    omega
  have b5 : (fpol a₂ a₄ a₆).natDegree ≤ 2 * Fintype.card F := by rw [natDegree_fpol]; omega
  have b6 : (X ^ 3 : F[X]).natDegree ≤ 2 * Fintype.card F := by rw [natDegree_X_pow]; omega
  have b7 : (2 * C a₂ * X ^ (Fintype.card F + 1) : F[X]).natDegree ≤ 2 * Fintype.card F := by
    rw [show (2 * C a₂ * X ^ (Fintype.card F + 1) : F[X]) = C (2 * a₂) * X ^ (Fintype.card F + 1) by
      rw [map_mul, map_ofNat]]
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
  have b8 : (C a₂ * X ^ 2).natDegree ≤ 2 * Fintype.card F :=
    (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
  have hR : (X ^ (Fintype.card F + 2) - X ^ 3 + 2 * C a₂ * X ^ (Fintype.card F + 1) - C a₂ * X ^ 2 +
      C a₄ * X ^ Fintype.card F + C a₆ + 2 * fpol a₂ a₄ a₆ ^ (m + 1) + fpol a₂ a₄ a₆ : F[X]).natDegree <
        (X ^ (2 * Fintype.card F + 1) : F[X]).natDegree := by
    rw [natDegree_X_pow]
    refine Nat.lt_succ_of_le ((natDegree_add_le _ _).trans (max_le ?_ b5))
    refine (natDegree_add_le _ _).trans (max_le ?_ b4)
    refine (natDegree_add_le _ _).trans (max_le ?_ b3)
    refine (natDegree_add_le _ _).trans (max_le ?_ b2)
    refine (natDegree_sub_le _ _).trans (max_le ?_ b8)
    refine (natDegree_add_le _ _).trans (max_le ?_ b7)
    exact (natDegree_sub_le _ _).trans (max_le b1 b6)
  rw [e, natDegree_add_eq_left_of_natDegree_lt hR, natDegree_X_pow]

omit [DecidableEq F] in
lemma Unum_ne_zero (hF : ringChar F ≠ 2) : Unum a₂ a₄ a₆ ≠ 0 := fun h => by
  have := natDegree_Unum (a₂ := a₂) (a₄ := a₄) (a₆ := a₆) hF
  rw [h, natDegree_zero] at this
  omega

/-! ## The points of `y² = x³ + a₂x² + a₄x + a₆` -/

variable (a₂ a₄ a₆) in
/-- The curve `y² = x³ + a₂x² + a₄x + a₆`. -/
def cubic : WeierstrassCurve F := { a₁ := 0, a₂ := a₂, a₃ := 0, a₄ := a₄, a₆ := a₆ }

omit [Fintype F] [DecidableEq F] in
lemma cubic_nonsingular_iff (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (x y : F) :
    (cubic a₂ a₄ a₆).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hΔ : (cubic a₂ a₄ a₆).Δ ≠ 0 := by
    rw [cubic, Δ_cubic]
    refine mul_ne_zero ?_ hD
    have e : (-16 : F) = -(2 ^ 4) := by norm_num
    rw [e]; exact neg_ne_zero.2 (pow_ne_zero 4 h2)
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := (cubic a₂ a₄ a₆).toAffine) hΔ,
    WeierstrassCurve.Affine.equation_iff]
  simp [cubic]

omit [Fintype F] [DecidableEq F] in
/-- The points of `y² = x³ + a₂x² + a₄x + a₆`: the point at infinity, and the solutions. -/
def pointEquiv (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    (cubic a₂ a₄ a₆).toAffine.Point ≃
      Option {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + a₂ * xy.1 ^ 2 + a₄ * xy.1 + a₆} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), (cubic_nonsingular_iff hF hD x y).1 h⟩
  invFun
    | none => .zero
    | some xy => .some xy.1.1 xy.1.2 ((cubic_nonsingular_iff hF hD _ _).2 xy.2)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl

lemma card_points (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    Nat.card (cubic a₂ a₄ a₆).toAffine.Point =
      (univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 + a₂ * xy.1 ^ 2 + a₄ * xy.1 + a₆)).card + 1 := by
  rw [Nat.card_congr (pointEquiv hF hD), Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_subtype]

/-- The affine points counted with the quadratic character. -/
lemma card_solutions (hF : ringChar F ≠ 2) :
    ((univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 + a₂ * xy.1 ^ 2 + a₄ * xy.1 + a₆)).card : ℤ) =
      ∑ x : F, (quadraticChar F (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) + 1) := by
  rw [card_filter, ← univ_product_univ, sum_product]
  push_cast
  refine sum_congr rfl fun x _ => ?_
  rw [← quadraticChar_card_sqrts hF, Set.toFinset_ofPred, card_filter]
  push_cast
  rfl

/-- `2 − mult(c)` is the number of square roots of `f(c)`. -/
lemma two_sub_mult (hF : ringChar F ≠ 2) (c : F) :
    ((2 - mult a₂ a₄ a₆ c : ℕ) : ℤ) = quadraticChar F (c ^ 3 + a₂ * c ^ 2 + a₄ * c + a₆) + 1 := by
  rw [← eval_fpol]
  unfold mult
  split_ifs with h0 h1
  · rw [h0, quadraticChar_zero]; norm_num
  · rw [quadraticChar_eq_pow_of_char_ne_two hF h0, ite_eq_left h1]; norm_num
  · rw [quadraticChar_eq_pow_of_char_ne_two hF h0, ite_eq_right h1]; norm_num

/-- **`#E(𝔽_q) = 1 + Σ_c (2 − mult(c))`.** -/
lemma sum_two_sub_mult (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    ∑ c : F, (2 - mult a₂ a₄ a₆ c) + 1 = Nat.card (cubic a₂ a₄ a₆).toAffine.Point := by
  rw [card_points hF hD]
  congr 1
  have h := card_solutions (a₂ := a₂) (a₄ := a₄) (a₆ := a₆) hF
  rw [← sum_congr rfl fun c _ => two_sub_mult (a₂ := a₂) (a₄ := a₄) (a₆ := a₆) hF c] at h
  exact_mod_cast h.symm

/-- **The count as a degree**: in lowest terms, `U/(X^q − X)²` has degree `#E(𝔽_q)`. -/
lemma rdeg_Unum (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    rdeg (ι (Unum a₂ a₄ a₆) / ι ((X ^ Fintype.card F - X) ^ 2)) = Nat.card (cubic a₂ a₄ a₆).toAffine.Point := by
  have hsum : ∑ c : F, mult a₂ a₄ a₆ c + ∑ c : F, (2 - mult a₂ a₄ a₆ c) = 2 * Fintype.card F := by
    rw [← sum_add_distrib, sum_congr rfl fun c _ => Nat.add_sub_cancel' (mult_le c), sum_const, card_univ,
      smul_eq_mul, mul_comm]
  rw [X_pow_card_sub_X_eq_prod, ← prod_pow, rdeg_div_prod (Unum_ne_zero hF) (mult a₂ a₄ a₆) mult_le
    (pow_mult_dvd_Unum hF) (not_pow_mult_succ_dvd_Unum hF hD), natDegree_Unum hF, ← sum_two_sub_mult hF hD]
  omega

/-! ## The Frobenius point -/

section twist

variable [DecidableEq (RatFunc F)]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma sf_pow_card : sf a₂ a₄ a₆ ^ Fintype.card F = ι X ^ (3 * Fintype.card F) +
    ι (C a₂) * ι X ^ (2 * Fintype.card F) + ι (C a₄) * ι X ^ Fintype.card F + ι (C a₆) := by
  rw [sf, ← map_pow, ← FiniteField.Polynomial.expand_card]
  simp only [fpol, map_add, map_mul, map_pow, expand_X, expand_C]
  ring

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma P1_equation (hF : ringChar F ≠ 2) :
    (sf a₂ a₄ a₆ ^ (Fintype.card F / 2 + 2)) ^ 2 = (sf a₂ a₄ a₆ * ι X ^ Fintype.card F) ^ 3 +
      ι (C a₂) * sf a₂ a₄ a₆ * (sf a₂ a₄ a₆ * ι X ^ Fintype.card F) ^ 2 +
        ι (C a₄) * sf a₂ a₄ a₆ ^ 2 * (sf a₂ a₄ a₆ * ι X ^ Fintype.card F) + ι (C a₆) * sf a₂ a₄ a₆ ^ 3 := by
  obtain ⟨m, hdiv, hm⟩ : ∃ m, Fintype.card F / 2 = m ∧ Fintype.card F = 2 * m + 1 :=
    ⟨_, rfl, by have := FiniteField.odd_card_of_char_ne_two hF; omega⟩
  have e : (sf a₂ a₄ a₆ ^ (Fintype.card F / 2 + 2)) ^ 2 = sf a₂ a₄ a₆ ^ Fintype.card F * sf a₂ a₄ a₆ ^ 3 := by
    rw [hdiv, hm]; ring
  rw [e, sf_pow_card]
  ring

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The Frobenius point `P₁ = (st^q, s^{(q+3)/2})`, the point `(t^q, f(t)^{(q−1)/2})` of `sY² = f(X)`. -/
noncomputable def P1 (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) : (twist a₂ a₄ a₆).toAffine.Point :=
  .some _ _ ((twist_nonsingular (Ring.two_ne_zero hF) hD _ _).2 (P1_equation hF))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- **`deg P₁ = q`.** -/
lemma pdeg_P1 (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) : pdeg a₂ a₄ a₆ (P1 hF hD) = Fintype.card F := by
  simp only [P1, pdeg]
  rw [mul_div_cancel_left₀ _ (sf_ne_zero a₂ a₄ a₆), ← map_pow, rdeg_algebraMap, natDegree_X_pow]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma X_pow_card_ne_X : (ι X ^ Fintype.card F : RatFunc F) ≠ ι X := by
  rw [← map_pow]
  intro h
  have := congrArg natDegree (IsFractionRing.injective F[X] (RatFunc F) h)
  rw [natDegree_X_pow, natDegree_X] at this
  exact (Fintype.one_lt_card (α := F)).ne' this

/-- **`deg(P₁ − P₀) = #E(𝔽_q)`.** -/
lemma pdeg_P1_sub_P0 (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    pdeg a₂ a₄ a₆ (P1 hF hD - P0 (Ring.two_ne_zero hF) hD) = Nat.card (cubic a₂ a₄ a₆).toAffine.Point := by
  have hs0 := sf_ne_zero a₂ a₄ a₆
  have hx : sf a₂ a₄ a₆ * ι X ^ Fintype.card F ≠ sf a₂ a₄ a₆ * ι X := fun h =>
    X_pow_card_ne_X (mul_left_cancel₀ hs0 h)
  have hY : sf a₂ a₄ a₆ ^ (Fintype.card F / 2 + 2) / sf a₂ a₄ a₆ ^ 2 = sf a₂ a₄ a₆ ^ (Fintype.card F / 2) := by
    rw [pow_add, mul_div_cancel_right₀ _ (pow_ne_zero 2 hs0)]
  have hV : (ι X ^ Fintype.card F - ι X) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 X_pow_card_ne_X)
  have hfrac : sf a₂ a₄ a₆ * (sf a₂ a₄ a₆ ^ (Fintype.card F / 2) + 1) ^ 2 / (ι X ^ Fintype.card F - ι X) ^ 2 -
      (ι X ^ Fintype.card F + ι X + ι (C a₂)) = ι (Unum a₂ a₄ a₆) / ι ((X ^ Fintype.card F - X) ^ 2) := by
    rw [div_sub' hV]
    congr 1
    · simp only [Unum, sf, map_sub, map_mul, map_pow, map_add, map_one]; ring
    · simp only [map_pow, map_sub]
  unfold P1
  rw [pdeg_some_sub_P0 _ hD _ hx, mul_div_cancel_left₀ _ hs0, hY, hfrac, rdeg_Unum hF hD]

end twist

/-! ## Hasse's bound for `y² = x³ + a₂x² + a₄x + a₆` -/

/-- **Hasse's bound** for `y² = x³ + a₂x² + a₄x + a₆`, in the form `(q + 1 − #E(𝔽_q))² ≤ 4q`. -/
theorem cubic_trace_sq_le (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) :
    ((Fintype.card F : ℤ) + 1 - Nat.card (cubic a₂ a₄ a₆).toAffine.Point) ^ 2 ≤ 4 * Fintype.card F := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set P₀ := P0 (a₂ := a₂) (a₄ := a₄) (a₆ := a₆) h2 hD
  set P₁ := P1 (a₂ := a₂) (a₄ := a₄) (a₆ := a₆) hF hD
  set d : ℤ → ℤ := fun n => (pdeg a₂ a₄ a₆ (P₁ + n • P₀) : ℤ) with hd
  have hrec : ∀ n, d (n + 1) + d (n - 1) = 2 * d n + 2 := by
    intro n
    have h := pdeg_add_add_pdeg_sub h2 hD (P₁ + n • P₀)
    have e1 : P₁ + (n + 1) • P₀ = P₁ + n • P₀ + P₀ := by rw [add_zsmul, one_zsmul, add_assoc]
    have e2 : P₁ + (n - 1) • P₀ = P₁ + n • P₀ - P₀ := by rw [sub_zsmul, one_zsmul]; abel
    simp only [hd]
    rw [e1, e2]
    exact_mod_cast h
  have h0 : d 0 = Fintype.card F := by
    simp only [hd, zero_zsmul, add_zero]
    exact_mod_cast pdeg_P1 hF hD
  have hm1 : d (-1) = Nat.card (cubic a₂ a₄ a₆).toAffine.Point := by
    simp only [hd, neg_one_zsmul, ← sub_eq_add_neg]
    exact_mod_cast pdeg_P1_sub_P0 hF hD
  have hnonneg : ∀ n : ℤ, 0 ≤ n ^ 2 + ((Fintype.card F : ℤ) + 1 - Nat.card (cubic a₂ a₄ a₆).toAffine.Point) * n +
      Fintype.card F := by
    intro n
    have h1 := quadratic_of_second_difference hrec n
    have h2 := quadratic_of_second_difference hrec (-1)
    rw [h0] at h1 h2
    rw [hm1] at h2
    have hc : d 1 - Fintype.card F - 1 =
        (Fintype.card F : ℤ) + 1 - Nat.card (cubic a₂ a₄ a₆).toAffine.Point := by
      linear_combination h2
    rw [← hc, ← h1]
    exact Int.natCast_nonneg _
  exact sq_le_of_forall_nonneg (by have := FiniteField.odd_card_of_char_ne_two hF; omega) hnonneg

/-! ## Every elliptic curve -/

section general

variable (W : WeierstrassCurve F)

omit [Fintype F] [DecidableEq F] in
/-- **Completing the square**: in `y' = y + (a₁x + a₃)/2`, `W` has the equation
`y'² = x³ + (b₂/4)x² + (b₄/2)x + b₆/4`. -/
lemma equation_iff_cubic (hF : ringChar F ≠ 2) (x y : F) :
    W.toAffine.Equation x y ↔
      (y + (W.a₁ * x + W.a₃) / 2) ^ 2 = x ^ 3 + W.b₂ / 4 * x ^ 2 + W.b₄ / 2 * x + W.b₆ / 4 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have e : (4 : F) = 2 * 2 := by norm_num
    rw [e]; exact mul_ne_zero h2 h2
  have e : (y + (W.a₁ * x + W.a₃) / 2) ^ 2 - (x ^ 3 + W.b₂ / 4 * x ^ 2 + W.b₄ / 2 * x + W.b₆ / 4) =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    field_simp
    ring
  rw [WeierstrassCurve.Affine.equation_iff]
  constructor <;> intro h
  · linear_combination e + h
  · linear_combination h - e

omit [Fintype F] [DecidableEq F] in
/-- The discriminant of `y² = x³ + (b₂/4)x² + (b₄/2)x + b₆/4` is that of `W`. -/
lemma dsc_mul_eq_Δ (hF : ringChar F ≠ 2) : -16 * dsc (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) = W.Δ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have e : (4 : F) = 2 * 2 := by norm_num
    rw [e]; exact mul_ne_zero h2 h2
  simp only [dsc, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  field_simp
  ring

omit [Fintype F] [DecidableEq F] in
lemma dsc_ne_zero (hF : ringChar F ≠ 2) (hΔ : W.Δ ≠ 0) : dsc (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) ≠ 0 := fun h =>
  hΔ (by rw [← dsc_mul_eq_Δ W hF, h, mul_zero])

omit [Fintype F] [DecidableEq F] in
/-- The points of `W` and of `y² = x³ + (b₂/4)x² + (b₄/2)x + b₆/4` correspond by `(x, y) ↦ (x, y + (a₁x + a₃)/2)`. -/
def cubicEquiv (hF : ringChar F ≠ 2) (hΔ : W.Δ ≠ 0) :
    W.toAffine.Point ≃ (cubic (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).toAffine.Point where
  toFun
    | .zero => .zero
    | .some x y h => .some x (y + (W.a₁ * x + W.a₃) / 2)
        ((cubic_nonsingular_iff hF (dsc_ne_zero W hF hΔ) _ _).2 ((equation_iff_cubic W hF x y).1
          ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := W.toAffine) hΔ).2 h)))
  invFun
    | .zero => .zero
    | .some x y h => .some x (y - (W.a₁ * x + W.a₃) / 2)
        ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := W.toAffine) hΔ).1
          ((equation_iff_cubic W hF x _).2 (by
            rw [sub_add_cancel]; exact (cubic_nonsingular_iff hF (dsc_ne_zero W hF hΔ) _ _).1 h)))
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp only [add_sub_cancel_right]
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp only [sub_add_cancel]

omit [DecidableEq F] in
/-- **Hasse's bound for every elliptic curve over a finite field of odd characteristic**, in the form
`(q + 1 − #E(𝔽_q))² ≤ 4q`. -/
theorem trace_sq_le [W.IsElliptic] (hF : ringChar F ≠ 2) :
    ((Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point) ^ 2 ≤ 4 * Fintype.card F := by
  classical
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [Nat.card_congr (cubicEquiv W hF hΔ)]
  exact cubic_trace_sq_le hF (dsc_ne_zero W hF hΔ)

omit [DecidableEq F] in
/-- **Hasse's bound for every elliptic curve over a finite field of odd characteristic**: `|q + 1 − #E(𝔽_q)| ≤ 2√q`,
the Riemann hypothesis for its zeta function. -/
theorem abs_trace_le [W.IsElliptic] (hF : ringChar F ≠ 2) :
    |(Fintype.card F : ℝ) + 1 - Nat.card W.toAffine.Point| ≤ 2 * Real.sqrt (Fintype.card F) := by
  have h := trace_sq_le W hF
  have h4q : 2 * Real.sqrt (Fintype.card F) = Real.sqrt (4 * Fintype.card F) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [h4q]
  refine Real.abs_le_sqrt ?_
  exact_mod_cast h

end general

end ManinHasse

#print axioms ManinHasse.trace_sq_le
#print axioms ManinHasse.abs_trace_le
