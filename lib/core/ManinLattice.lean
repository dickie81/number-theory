/-
# The Frobenius lattice: the Riemann hypothesis for an elliptic curve in every degree, from a definite form

Plain statement. Let `𝔽_q` be a finite field of characteristic not `2` and `E` an elliptic curve over `𝔽_q`: a
`WeierstrassCurve` with `[E.IsElliptic]`. For each `d ≥ 1` let `L_d` be a finite field extension of `𝔽_q` with `q^d`
elements, and `N_d = #E(L_d)` the number of Mathlib's points of `E` over `L_d`, the point at infinity included. Put
`c_d = (q^d + 1 − N_d)/(2q^{d/2})` and `c_0 = 1`. Then `d ↦ c_{|d|}` is a positive-definite function on `ℤ`: for all
`K` and all real `x_0, …, x_{K−1}`, `Σ_{i,j} x_i x_j c_{|i−j|} ≥ 0` (`toeplitz_nonneg`). No hypothesis beyond these.

This is the Riemann hypothesis for `E` in every degree at once: with `q^d + 1 − N_d = α^d + β^d` and `αβ = q`, it is
equivalent to `|α| = |β| = √q`. Here it comes from a definite lattice, with no use of the zeta function.
* The degree of `x/s` is a quadratic form on the points of Manin's twist over `𝔽_q(t)`
  (`ManinTwist.pdeg_parallelogram`). Its polar form is biadditive, and
  `2 deg(Σ nᵢPᵢ) = Σ nᵢnⱼ B(Pᵢ, Pⱼ)` (`two_mul_sum_eq`). So the Gram matrix of any points is positive
  semidefinite on integer vectors (`gram_nonneg`), and so on real ones (`quadratic_nonneg_of_int`).
* The Frobenius points `P_k = (st^{q^k}, s^{(q^k+3)/2})` (`Pk`) have `deg P_k = q^k` and, for `j < i`,
  `deg(P_i − P_j) = q^j·N_{i−j}` (`pdeg_Pk_sub_Pk`). The `x`-coordinate of `P_i − P_j` is that of `P_{i−j} − P_0` at
  `t^{q^j}`, which multiplies degrees by `q^j` (`rdeg_expand`). Over `L_d` that of `P_d − P_0` has degree `N_d`, as in
  `ManinHasse.rdeg_Unum`, and the degree does not change from `𝔽_q(t)` to `L_d(t)` (`rdeg_map`).
* So the vectors `P_k/q^{k/2}` lie on the unit sphere of a definite form, with inner products `c_{|i−j|}`.

This is the third of the first steps in `docs/ball-conjecture.md`.
-/
import ManinHasse

open Polynomial ManinDegree Finset

namespace ManinHasse

/-! ## Quadratic forms on an abelian group -/

section quadratic

variable {G : Type*} [AddCommGroup G]

/-- The polar form `B(P, R) = Q(P + R) − Q(P) − Q(R)` of a function `Q` on an abelian group. -/
def polar (Q : G → ℤ) (P R : G) : ℤ := Q (P + R) - Q P - Q R

variable {Q : G → ℤ} (hQ : ∀ P R, Q (P + R) + Q (P - R) = 2 * Q P + 2 * Q R)
include hQ

lemma Q_zero_of_parallelogram : Q 0 = 0 := by
  have := hQ 0 0
  rw [add_zero, sub_zero] at this
  linarith

lemma Q_neg_of_parallelogram (P : G) : Q (-P) = Q P := by
  have := hQ 0 P
  rw [zero_add, zero_sub, Q_zero_of_parallelogram hQ] at this
  linarith

omit hQ in
lemma polar_comm (P R : G) : polar Q P R = polar Q R P := by
  unfold polar; rw [add_comm P R]; ring

/-- **The polar form is additive.** -/
lemma polar_add_left (P R T : G) : polar Q (P + R) T = polar Q P T + polar Q R T := by
  have h1 : ∀ P R : G, polar Q (P + R) T + polar Q (P - R) T = 2 * polar Q P T := fun P R => by
    have e1 := hQ (P + T) R
    have e2 := hQ P R
    rw [show P + T + R = P + R + T by abel, show P + T - R = P - R + T by abel] at e1
    unfold polar; linarith
  have h2 : ∀ P : G, polar Q (-P) T = -polar Q P T := fun P => by
    have e := hQ T P
    have hn := Q_neg_of_parallelogram hQ P
    unfold polar
    rw [show -P + T = T - P by abel, hn, show P + T = T + P by abel]
    linarith
  have e1 := h1 P R
  have e2 := h1 R P
  rw [show R - P = -(P - R) by abel, h2, add_comm R P] at e2
  linarith

lemma polar_self (P : G) : polar Q P P = 2 * Q P := by
  have := hQ P P
  rw [sub_self, Q_zero_of_parallelogram hQ] at this
  unfold polar; linarith

lemma polar_eq_sub (P R : G) : polar Q P R = Q P + Q R - Q (P - R) := by
  have := hQ P R
  unfold polar; linarith

/-- `P ↦ B(P, R)`, an additive map. -/
def polarLeft (R : G) : G →+ ℤ := AddMonoidHom.mk' (fun P => polar Q P R) fun P T => polar_add_left hQ P T R

lemma polar_sum_left {ι : Type*} (s : Finset ι) (n : ι → ℤ) (P : ι → G) (R : G) :
    polar Q (∑ i ∈ s, n i • P i) R = ∑ i ∈ s, n i * polar Q (P i) R := by
  have := map_sum (polarLeft hQ R) (fun i => n i • P i) s
  simp only [map_zsmul, smul_eq_mul] at this
  exact this

/-- **`2Q(Σ nᵢPᵢ) = Σ nᵢnⱼ B(Pᵢ, Pⱼ)`.** -/
lemma two_mul_sum_eq {ι : Type*} (s : Finset ι) (n : ι → ℤ) (P : ι → G) :
    2 * Q (∑ i ∈ s, n i • P i) = ∑ i ∈ s, ∑ j ∈ s, n i * n j * polar Q (P i) (P j) := by
  rw [← polar_self hQ, polar_sum_left hQ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polar_comm, polar_sum_left hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [polar_comm]; ring

end quadratic

/-! ## From integer to real vectors -/

/-- A quadratic form with integer coefficients that is nonnegative on integer vectors is nonnegative on real ones. -/
lemma quadratic_nonneg_of_int {K : ℕ} (G : Fin K → Fin K → ℤ)
    (h : ∀ n : Fin K → ℤ, 0 ≤ ∑ i, ∑ j, n i * n j * G i j) (y : Fin K → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * (G i j : ℝ) := by
  -- rational vectors, by clearing denominators
  have hq : ∀ r : Fin K → ℚ, 0 ≤ ∑ i, ∑ j, r i * r j * (G i j : ℚ) := by
    intro r
    set d : ℕ := ∏ i, (r i).den with hd
    have hd0 : (0 : ℚ) < d := by
      rw [hd]; exact_mod_cast Finset.prod_pos fun i _ => (r i).den_pos
    have hdiv : ∀ i, (r i).den ∣ d := fun i => Finset.dvd_prod_of_mem _ (mem_univ i)
    set n : Fin K → ℤ := fun i => (r i).num * (d / (r i).den : ℕ) with hn
    have hnr : ∀ i, (n i : ℚ) = d * r i := fun i => by
      obtain ⟨c, hc⟩ := hdiv i
      have hc0 : (r i).den ≠ 0 := (r i).den_nz
      rw [hn]
      simp only
      rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hc0)]
      push_cast
      rw [← Rat.mul_den_eq_num (r i)]
      ring
    have := h n
    have hcast : (0 : ℚ) ≤ ∑ i, ∑ j, (n i : ℚ) * n j * G i j := by exact_mod_cast this
    simp only [hnr] at hcast
    have e : ∑ i, ∑ j, (d * r i) * (d * r j) * (G i j : ℚ) = (d : ℚ) ^ 2 * ∑ i, ∑ j, r i * r j * (G i j : ℚ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e] at hcast
    exact (mul_nonneg_iff_of_pos_left (pow_pos hd0 2)).1 hcast
  -- real vectors, by density
  have hdense : DenseRange (Pi.map fun _ : Fin K => ((↑) : ℚ → ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
  have hcont : Continuous fun y : Fin K → ℝ => ∑ i, ∑ j, y i * y j * (G i j : ℝ) := by fun_prop
  refine hdense.induction_on (p := fun y => 0 ≤ ∑ i, ∑ j, y i * y j * (G i j : ℝ)) y
    (isClosed_le continuous_const hcont) fun r => ?_
  have := hq r
  have hc : (0 : ℝ) ≤ ((∑ i, ∑ j, r i * r j * (G i j : ℚ) : ℚ) : ℝ) := by exact_mod_cast this
  simpa [Pi.map] using hc

/-! ## Degrees under `t ↦ t^m` and under base change -/

section degree

variable {k : Type*} [Field k]

local notation "ι" => algebraMap k[X] (RatFunc k)

lemma max_mul_right (a b m : ℕ) : max (a * m) (b * m) = m * max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right (Nat.mul_le_mul_right m h), max_eq_right h, mul_comm]
  · rw [max_eq_left (Nat.mul_le_mul_right m h), max_eq_left h, mul_comm]

/-- **Substituting `t^m` for `t` multiplies the degree by `m`.** -/
lemma rdeg_expand {m : ℕ} (hm : 0 < m) {p r : k[X]} (hr : r ≠ 0) :
    rdeg (ι (expand k m p) / ι (expand k m r)) = m * rdeg (ι p / ι r) := by
  have hinj := IsFractionRing.injective k[X] (RatFunc k)
  obtain ⟨x, hxdef⟩ : ∃ x, x = ι p / ι r := ⟨_, rfl⟩
  rw [← hxdef]
  have hx : x.num * r = p * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hr).2 hxdef
  have hd := RatFunc.denom_ne_zero x
  have hed : expand k m x.denom ≠ 0 := by rwa [Ne, expand_eq_zero hm]
  have her : expand k m r ≠ 0 := by rwa [Ne, expand_eq_zero hm]
  have hx' : expand k m p * expand k m x.denom = expand k m x.num * expand k m r := by
    rw [← map_mul, ← map_mul, hx]
  have e : ι (expand k m p) / ι (expand k m r) = ι (expand k m x.num) / ι (expand k m x.denom) := by
    rw [div_eq_div_iff ((map_ne_zero_iff _ hinj).2 her) ((map_ne_zero_iff _ hinj).2 hed)]
    simpa only [map_mul] using congrArg ι hx'
  have hc : IsCoprime (expand k m x.num) (expand k m x.denom) := by
    obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom x
    exact ⟨expand k m u, expand k m v, by rw [← map_mul, ← map_mul, ← map_add, huv, map_one]⟩
  rw [e, rdeg_div hc hed, natDegree_expand, natDegree_expand, max_mul_right]
  rfl

/-- **The degree of a rational function does not change under an extension of the field of constants.** -/
lemma rdeg_map {L : Type*} [Field L] (φ : k →+* L) {p r : k[X]} (hr : r ≠ 0) :
    rdeg (algebraMap L[X] (RatFunc L) (p.map φ) / algebraMap L[X] (RatFunc L) (r.map φ)) = rdeg (ι p / ι r) := by
  have hinjL := IsFractionRing.injective L[X] (RatFunc L)
  obtain ⟨x, hxdef⟩ : ∃ x, x = ι p / ι r := ⟨_, rfl⟩
  rw [← hxdef]
  have hx : x.num * r = p * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hr).2 hxdef
  have hd := RatFunc.denom_ne_zero x
  have hmd : x.denom.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).2 hd
  have hmr : r.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).2 hr
  have hx' : p.map φ * x.denom.map φ = x.num.map φ * r.map φ := by
    rw [← Polynomial.map_mul, ← Polynomial.map_mul, hx]
  have e : algebraMap L[X] (RatFunc L) (p.map φ) / algebraMap L[X] (RatFunc L) (r.map φ) =
      algebraMap L[X] (RatFunc L) (x.num.map φ) / algebraMap L[X] (RatFunc L) (x.denom.map φ) := by
    rw [div_eq_div_iff ((map_ne_zero_iff _ hinjL).2 hmr) ((map_ne_zero_iff _ hinjL).2 hmd)]
    simpa only [map_mul] using congrArg (algebraMap L[X] (RatFunc L)) hx'
  have hc : IsCoprime (x.num.map φ) (x.denom.map φ) := (RatFunc.isCoprime_num_denom x).map (Polynomial.mapRingHom φ)
  rw [e, rdeg_div hc hmd, natDegree_map_eq_of_injective φ.injective, natDegree_map_eq_of_injective φ.injective]
  rfl

end degree

/-! ## The Frobenius points -/

section frobenius

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a₂ a₄ a₆ : F}

local notation "ι" => algebraMap F[X] (RatFunc F)

omit [DecidableEq F] in
lemma fpol_pow_card_pow (n : ℕ) :
    fpol a₂ a₄ a₆ ^ (Fintype.card F ^ n) = expand F (Fintype.card F ^ n) (fpol a₂ a₄ a₆) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, ih, ← FiniteField.Polynomial.expand_card, expand_expand, mul_comm (Fintype.card F)]

omit [DecidableEq F] in
lemma card_pow_odd (hF : ringChar F ≠ 2) (n : ℕ) : Fintype.card F ^ n % 2 = 1 := by
  rw [Nat.pow_mod, FiniteField.odd_card_of_char_ne_two hF, one_pow]
  rfl

variable (a₂ a₄ a₆) in
/-- The numerator of `x(P_d − P_0)/s`: `U_d = f(f^{m_d} + 1)² − (X^{q^d} + X + a₂)(X^{q^d} − X)²`, with
`m_d = (q^d − 1)/2`. Over a field with `q^d` elements it is `ManinHasse.Unum`. -/
noncomputable def Ud (n : ℕ) : F[X] :=
  fpol a₂ a₄ a₆ * (fpol a₂ a₄ a₆ ^ (n / 2) + 1) ^ 2 - (X ^ n + X + C a₂) * (X ^ n - X) ^ 2

section twist

variable [DecidableEq (RatFunc F)]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma sf_pow_card_pow (n : ℕ) : sf a₂ a₄ a₆ ^ (Fintype.card F ^ n) = ι X ^ (3 * Fintype.card F ^ n) +
    ι (C a₂) * ι X ^ (2 * Fintype.card F ^ n) + ι (C a₄) * ι X ^ (Fintype.card F ^ n) + ι (C a₆) := by
  rw [sf, ← map_pow, fpol_pow_card_pow]
  simp only [fpol, map_add, map_mul, map_pow, expand_X, expand_C]
  ring

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma Pk_equation (hF : ringChar F ≠ 2) (n : ℕ) :
    (sf a₂ a₄ a₆ ^ (Fintype.card F ^ n / 2 + 2)) ^ 2 = (sf a₂ a₄ a₆ * ι X ^ (Fintype.card F ^ n)) ^ 3 +
      ι (C a₂) * sf a₂ a₄ a₆ * (sf a₂ a₄ a₆ * ι X ^ (Fintype.card F ^ n)) ^ 2 +
        ι (C a₄) * sf a₂ a₄ a₆ ^ 2 * (sf a₂ a₄ a₆ * ι X ^ (Fintype.card F ^ n)) + ι (C a₆) * sf a₂ a₄ a₆ ^ 3 := by
  obtain ⟨m, hdiv, hm⟩ : ∃ m, Fintype.card F ^ n / 2 = m ∧ Fintype.card F ^ n = 2 * m + 1 :=
    ⟨_, rfl, by have := card_pow_odd hF n; omega⟩
  have e : (sf a₂ a₄ a₆ ^ (Fintype.card F ^ n / 2 + 2)) ^ 2 =
      sf a₂ a₄ a₆ ^ (Fintype.card F ^ n) * sf a₂ a₄ a₆ ^ 3 := by
    rw [hdiv, hm]; ring
  rw [e, sf_pow_card_pow]
  ring

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The Frobenius point `P_k = (st^{q^k}, s^{(q^k+3)/2})`, the point `(t^{q^k}, f(t)^{(q^k−1)/2})` of `sY² = f(X)`. -/
noncomputable def Pk (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (n : ℕ) : (twist a₂ a₄ a₆).toAffine.Point :=
  .some _ _ ((twist_nonsingular (Ring.two_ne_zero hF) hD _ _).2 (Pk_equation hF n))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- **`deg P_k = q^k`.** -/
lemma pdeg_Pk (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (n : ℕ) :
    pdeg a₂ a₄ a₆ (Pk hF hD n) = Fintype.card F ^ n := by
  simp only [Pk, pdeg]
  rw [mul_div_cancel_left₀ _ (sf_ne_zero a₂ a₄ a₆), ← map_pow, rdeg_algebraMap, natDegree_X_pow]

omit [DecidableEq F] in
/-- **`deg(P_i − P_j) = q^j·deg(U_{q^{i−j}}/(X^{q^{i−j}} − X)²)`** for `j < i`: the `x`-coordinate of `P_i − P_j` is
that of `P_{i−j} − P_0` at `t^{q^j}`. -/
lemma pdeg_Pk_sub_Pk (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) {i j : ℕ} (hij : j < i) :
    pdeg a₂ a₄ a₆ (Pk hF hD i - Pk hF hD j) = Fintype.card F ^ j *
      rdeg (ι (Ud a₂ a₄ a₆ (Fintype.card F ^ (i - j))) / ι ((X ^ (Fintype.card F ^ (i - j)) - X) ^ 2)) := by
  have hs0 := sf_ne_zero a₂ a₄ a₆
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
  have hd0 : 0 < d := by omega
  rw [show j + d - j = d by omega]
  set Qj := Fintype.card F ^ j with hQj
  set Qd := Fintype.card F ^ d with hQd
  have hQi : Fintype.card F ^ (j + d) = Qj * Qd := by rw [pow_add]
  obtain ⟨mj, hmj⟩ : ∃ mj, Qj = 2 * mj + 1 := ⟨Qj / 2, by have := card_pow_odd hF j; omega⟩
  obtain ⟨md, hmd⟩ : ∃ md, Qd = 2 * md + 1 := ⟨Qd / 2, by have := card_pow_odd hF d; omega⟩
  have hdivj : Qj / 2 = mj := by omega
  have hdivd : Qd / 2 = md := by omega
  have hdivi : Fintype.card F ^ (j + d) / 2 = Qj * md + mj := by
    rw [hQi]
    have e : Qj * Qd = 2 * (Qj * md + mj) + 1 := by rw [hmd, hmj]; ring
    omega
  have hXne : ∀ a b : ℕ, a ≠ b → (ι X ^ a : RatFunc F) ≠ ι X ^ b := fun a b hab h => by
    rw [← map_pow, ← map_pow] at h
    have := congrArg natDegree (IsFractionRing.injective F[X] (RatFunc F) h)
    rw [natDegree_X_pow, natDegree_X_pow] at this
    exact hab this
  have hQne : Qj * Qd ≠ Qj := by
    have : 1 < Qd := Nat.one_lt_pow hd0.ne' hq1
    have : 0 < Qj := Nat.pos_of_ne_zero (by rw [hmj]; omega)
    nlinarith
  have hx : sf a₂ a₄ a₆ * ι X ^ (Fintype.card F ^ (j + d)) ≠ sf a₂ a₄ a₆ * ι X ^ Qj := fun h =>
    hXne _ _ (by rw [hQi]; exact hQne) (mul_left_cancel₀ hs0 h)
  unfold Pk
  rw [pdeg_some_sub_some _ _ hx, mul_div_cancel_left₀ _ hs0, mul_div_cancel_left₀ _ hs0, pow_add (sf a₂ a₄ a₆) _ 2,
    mul_div_cancel_right₀ _ (pow_ne_zero 2 hs0), pow_add (sf a₂ a₄ a₆) (Qj / 2) 2,
    mul_div_cancel_right₀ _ (pow_ne_zero 2 hs0), hdivi, hdivj, hQi]
  have hV : (ι X ^ (Qj * Qd) - ι X ^ Qj) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (hXne _ _ hQne))
  have hQj0 : 0 < Qj := by rw [hmj]; omega
  have hVd : (X ^ Qd - X : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => by
    have := congrArg natDegree (sub_eq_zero.1 h)
    rw [natDegree_X_pow, natDegree_X] at this
    exact (Nat.one_lt_pow hd0.ne' hq1).ne' this)
  have hfrac : sf a₂ a₄ a₆ * (sf a₂ a₄ a₆ ^ (Qj * md + mj) + sf a₂ a₄ a₆ ^ mj) ^ 2 /
      (ι X ^ (Qj * Qd) - ι X ^ Qj) ^ 2 - (ι X ^ (Qj * Qd) + ι X ^ Qj + ι (C a₂)) =
        ι (expand F Qj (Ud a₂ a₄ a₆ Qd)) / ι (expand F Qj ((X ^ Qd - X) ^ 2)) := by
    rw [div_sub' hV]
    congr 1
    · simp only [Ud, hdivd, map_sub, map_mul, map_pow, map_add, map_one, expand_X, expand_C]
      rw [← fpol_pow_card_pow, ← hQj]
      simp only [sf, map_pow]
      rw [hmj]
      ring
    · simp only [map_pow, map_sub, expand_X]
      ring
  rw [hfrac, rdeg_expand hQj0 hVd]

end twist

end frobenius

/-! ## The count over the extensions -/

section counts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "ι" => algebraMap F[X] (RatFunc F)

omit [Fintype F] [DecidableEq F] in
lemma Ud_map {L : Type*} [Field L] (φ : F →+* L) (a₂ a₄ a₆ : F) (n : ℕ) :
    (Ud a₂ a₄ a₆ n).map φ = Ud (φ a₂) (φ a₄) (φ a₆) n := by
  simp [Ud, fpol, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add]

omit [DecidableEq F] in
/-- **Over a field with `q^d` elements, `x(P_d − P_0)/s` has degree `#E(𝔽_{q^d})`.** -/
lemma rdeg_Ud_eq_card {a₂ a₄ a₆ : F} (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) {L : Type*} [Field L]
    [Fintype L] [DecidableEq L] [Algebra F L] {d : ℕ} (hL : Fintype.card L = Fintype.card F ^ d) :
    rdeg (ι (Ud a₂ a₄ a₆ (Fintype.card F ^ d)) / ι ((X ^ (Fintype.card F ^ d) - X) ^ 2)) =
      Nat.card (cubic (algebraMap F L a₂) (algebraMap F L a₄) (algebraMap F L a₆)).toAffine.Point := by
  have hLq : 1 < Fintype.card F ^ d := hL ▸ Fintype.one_lt_card
  have hV : ((X ^ (Fintype.card F ^ d) - X) ^ 2 : F[X]) ≠ 0 := pow_ne_zero 2 fun h => by
    have := congrArg natDegree (sub_eq_zero.1 h)
    rw [natDegree_X_pow, natDegree_X] at this
    omega
  have hFL : ringChar L ≠ 2 := by rwa [← Algebra.ringChar_eq F L]
  have hDL : dsc (algebraMap F L a₂) (algebraMap F L a₄) (algebraMap F L a₆) ≠ 0 := by
    have e : dsc (algebraMap F L a₂) (algebraMap F L a₄) (algebraMap F L a₆) = algebraMap F L (dsc a₂ a₄ a₆) := by
      simp only [dsc, map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [e]
    exact (map_ne_zero (algebraMap F L)).2 hD
  rw [← rdeg_map (algebraMap F L) hV, Ud_map, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, ← hL]
  exact rdeg_Unum hFL hDL

omit [DecidableEq F] in
/-- **The points of `E` over a field with `q^d` elements, as a degree over `𝔽_q(t)`.** -/
lemma card_baseChange_eq (W : WeierstrassCurve F) [W.IsElliptic] (hF : ringChar F ≠ 2) {L : Type*} [Field L]
    [Fintype L] [DecidableEq L] [Algebra F L] {d : ℕ} (hL : Fintype.card L = Fintype.card F ^ d) :
    Nat.card (W.baseChange L).toAffine.Point =
      rdeg (ι (Ud (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) (Fintype.card F ^ d)) / ι ((X ^ (Fintype.card F ^ d) - X) ^ 2)) := by
  have hFL : ringChar L ≠ 2 := by rwa [← Algebra.ringChar_eq F L]
  have : (W.baseChange L).IsElliptic := inferInstanceAs (W.map (algebraMap F L)).IsElliptic
  have hΔL : (W.baseChange L).Δ ≠ 0 := (W.baseChange L).isUnit_Δ.ne_zero
  have hb₂ : (W.baseChange L).b₂ / 4 = algebraMap F L (W.b₂ / 4) := by
    change (W.map (algebraMap F L)).b₂ / 4 = _
    rw [WeierstrassCurve.map_b₂, map_div₀, map_ofNat]
  have hb₄ : (W.baseChange L).b₄ / 2 = algebraMap F L (W.b₄ / 2) := by
    change (W.map (algebraMap F L)).b₄ / 2 = _
    rw [WeierstrassCurve.map_b₄, map_div₀, map_ofNat]
  have hb₆ : (W.baseChange L).b₆ / 4 = algebraMap F L (W.b₆ / 4) := by
    change (W.map (algebraMap F L)).b₆ / 4 = _
    rw [WeierstrassCurve.map_b₆, map_div₀, map_ofNat]
  rw [Nat.card_congr (cubicEquiv (W.baseChange L) hFL hΔL), hb₂, hb₄, hb₆,
    rdeg_Ud_eq_card hF (dsc_ne_zero W hF W.isUnit_Δ.ne_zero) hL]

end counts

/-! ## The Gram matrix of the Frobenius points -/

section gram

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [DecidableEq (RatFunc F)] {a₂ a₄ a₆ : F}

local notation "ι" => algebraMap F[X] (RatFunc F)

variable (a₂ a₄ a₆) in
/-- The degree of a point of the twist, as an integer. -/
noncomputable def degZ (P : (twist a₂ a₄ a₆).toAffine.Point) : ℤ := pdeg a₂ a₄ a₆ P

omit [Fintype F] [DecidableEq F] in
lemma degZ_parallelogram (h2 : (2 : F) ≠ 0) (hD : dsc a₂ a₄ a₆ ≠ 0) (P R : (twist a₂ a₄ a₆).toAffine.Point) :
    degZ a₂ a₄ a₆ (P + R) + degZ a₂ a₄ a₆ (P - R) = 2 * degZ a₂ a₄ a₆ P + 2 * degZ a₂ a₄ a₆ R := by
  have := pdeg_parallelogram h2 hD P R
  unfold degZ
  exact_mod_cast this

omit [DecidableEq F] in
/-- **The Gram matrix of the Frobenius points is positive semidefinite**: for every integer vector `n`,
`Σ nᵢnⱼ B(P_i, P_j) = 2 deg(Σ nᵢP_i) ≥ 0`. -/
theorem gram_nonneg (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) {K : ℕ} (n : Fin K → ℤ) :
    0 ≤ ∑ i, ∑ j, n i * n j * polar (degZ a₂ a₄ a₆) (Pk hF hD i) (Pk hF hD j) := by
  have := two_mul_sum_eq (degZ_parallelogram (Ring.two_ne_zero hF) hD) univ n (fun i : Fin K => Pk hF hD i)
  rw [← this]
  exact mul_nonneg (by norm_num) (Int.natCast_nonneg _)

omit [DecidableEq F] in
lemma gram_self (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) (i : ℕ) :
    polar (degZ a₂ a₄ a₆) (Pk hF hD i) (Pk hF hD i) = 2 * (Fintype.card F : ℤ) ^ i := by
  rw [polar_self (degZ_parallelogram (Ring.two_ne_zero hF) hD), degZ, pdeg_Pk]
  push_cast
  ring

omit [DecidableEq F] in
lemma gram_lt (hF : ringChar F ≠ 2) (hD : dsc a₂ a₄ a₆ ≠ 0) {i j : ℕ} (hij : j < i) :
    polar (degZ a₂ a₄ a₆) (Pk hF hD i) (Pk hF hD j) = (Fintype.card F : ℤ) ^ i + (Fintype.card F : ℤ) ^ j -
      (Fintype.card F : ℤ) ^ j * (rdeg (ι (Ud a₂ a₄ a₆ (Fintype.card F ^ (i - j))) /
        ι ((X ^ (Fintype.card F ^ (i - j)) - X) ^ 2)) : ℤ) := by
  rw [polar_eq_sub (degZ_parallelogram (Ring.two_ne_zero hF) hD), degZ, degZ, degZ, pdeg_Pk, pdeg_Pk,
    pdeg_Pk_sub_Pk hF hD hij]
  push_cast
  ring

end gram

/-! ## The Riemann hypothesis for `E` in every degree -/

section toeplitz

variable {F : Type*} [Field F] [Fintype F]

/-- The normalised trace `c_d = (q^d + 1 − #E(L_d))/(2q^{d/2})` of `E` over the extension `L_d`, and `c_0 = 1`. -/
noncomputable def ctrace (W : WeierstrassCurve F) (L : ℕ → Type*) [∀ d, Field (L d)] [∀ d, Algebra F (L d)]
    (d : ℕ) : ℝ :=
  if d = 0 then 1 else
    ((Fintype.card F : ℝ) ^ d + 1 - Nat.card (W.baseChange (L d)).toAffine.Point) /
      (2 * Real.sqrt (Fintype.card F) ^ d)

/-- **The Riemann hypothesis for an elliptic curve in every degree, from a definite form.** The normalised traces
`c_d = (q^d + 1 − #E(L_d))/(2q^{d/2})` form a positive-definite function on `ℤ`: `Σ_{i,j} x_i x_j c_{|i−j|} ≥ 0`. -/
theorem toeplitz_nonneg (W : WeierstrassCurve F) [W.IsElliptic] (hF : ringChar F ≠ 2) (L : ℕ → Type*)
    [∀ d, Field (L d)] [∀ d, Fintype (L d)] [∀ d, Algebra F (L d)]
    (hL : ∀ d, 0 < d → Fintype.card (L d) = Fintype.card F ^ d) (K : ℕ) (x : Fin K → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * ctrace W L (Nat.dist i j) := by
  classical
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hD := dsc_ne_zero W hF W.isUnit_Δ.ne_zero
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact_mod_cast (by omega : 0 < Fintype.card F)
  set s : ℝ := Real.sqrt q with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hq0
  have hsq : s ^ 2 = q := Real.sq_sqrt hq0.le
  set G : Fin K → Fin K → ℤ := fun i j => polar (degZ (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)) (Pk hF hD i) (Pk hF hD j)
    with hG
  have hreal := quadratic_nonneg_of_int G (gram_nonneg hF hD) (fun i => x i / s ^ (i : ℕ))
  -- the entries `G_ij = 2q^{(i+j)/2} c_{|i−j|}`
  have hlt : ∀ i j : ℕ, j < i → (polar (degZ (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)) (Pk hF hD i) (Pk hF hD j) : ℝ) =
      2 * s ^ i * s ^ j * ctrace W L (i - j) := fun i j hij => by
    obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    have hd0 : 0 < d := by omega
    have hN := card_baseChange_eq W hF (L := L d) (hL d hd0)
    rw [gram_lt hF hD hij, show j + d - j = d by omega, ← hN]
    simp only [ctrace, ite_eq_right hd0.ne']
    push_cast
    rw [← hqdef]
    have hsj : s ^ j ≠ 0 := pow_ne_zero _ hs.ne'
    have hsd : s ^ d ≠ 0 := pow_ne_zero _ hs.ne'
    have hqj : q ^ j = s ^ j * s ^ j := by rw [← mul_pow, ← sq, hsq]
    have hqd : q ^ d = s ^ d * s ^ d := by rw [← mul_pow, ← sq, hsq]
    rw [pow_add, pow_add, hqj, hqd]
    field_simp
    ring
  have hentry : ∀ i j : Fin K, (G i j : ℝ) = 2 * s ^ (i : ℕ) * s ^ (j : ℕ) * ctrace W L (Nat.dist i j) := by
    intro i j
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [hG]
      simp only
      rw [polar_comm, hlt j i h, Nat.dist_eq_sub_of_le h.le]
      ring
    · rw [hG]
      simp only
      rw [show i = j from Fin.ext h, gram_self hF hD, Nat.dist_self]
      simp only [ctrace]
      push_cast
      rw [← hqdef, mul_one, mul_assoc, ← pow_add, ← two_mul, pow_mul, hsq]
    · rw [hG]
      simp only
      rw [hlt i j h, Nat.dist_eq_sub_of_le_right h.le]
  have e : ∑ i, ∑ j, x i * x j * ctrace W L (Nat.dist i j) =
      (1 / 2) * ∑ i, ∑ j, (x i / s ^ (i : ℕ)) * (x j / s ^ (j : ℕ)) * (G i j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hentry]
    have hi : s ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hs.ne'
    have hj : s ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hs.ne'
    field_simp
  rw [e]
  exact mul_nonneg (by norm_num) hreal

/-- **A constraint between `#E(𝔽_q)` and `#E(𝔽_{q²})`**, from definiteness alone. With `a_d = q^d + 1 − #E(L_d)`,
`a₁² − 2q ≤ a₂`: twice the degree of `qP₀ − a₁P₁ + P₂` is `2q(2q + a₂ − a₁²) ≥ 0`. (The zeta function of `E` gives
`a₂ = a₁² − 2q`; the lattice gives the inequality without it, and Hasse's bound field by field does not.) -/
theorem trace_two_ge (W : WeierstrassCurve F) [W.IsElliptic] (hF : ringChar F ≠ 2) {L₁ L₂ : Type*} [Field L₁]
    [Fintype L₁] [Algebra F L₁] [Field L₂] [Fintype L₂] [Algebra F L₂] (h₁ : Fintype.card L₁ = Fintype.card F)
    (h₂ : Fintype.card L₂ = Fintype.card F ^ 2) :
    ((Fintype.card F : ℤ) + 1 - Nat.card (W.baseChange L₁).toAffine.Point) ^ 2 - 2 * Fintype.card F ≤
      (Fintype.card F : ℤ) ^ 2 + 1 - Nat.card (W.baseChange L₂).toAffine.Point := by
  classical
  have hD := dsc_ne_zero W hF W.isUnit_Δ.ne_zero
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hN₁ := card_baseChange_eq W hF (L := L₁) (d := 1) (by rw [h₁, pow_one])
  have hN₂ := card_baseChange_eq W hF (L := L₂) (d := 2) h₂
  set Q := degZ (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)
  set q : ℤ := (Fintype.card F : ℤ) with hq
  set a : ℤ := q + 1 - Nat.card (W.baseChange L₁).toAffine.Point with ha
  set b : ℤ := q ^ 2 + 1 - Nat.card (W.baseChange L₂).toAffine.Point with hb
  have p00 : polar Q (Pk hF hD 0) (Pk hF hD 0) = 2 := by rw [gram_self hF hD 0, pow_zero, mul_one]
  have p11 : polar Q (Pk hF hD 1) (Pk hF hD 1) = 2 * q := by rw [gram_self hF hD 1, pow_one]
  have p22 : polar Q (Pk hF hD 2) (Pk hF hD 2) = 2 * q ^ 2 := gram_self hF hD 2
  have p10 : polar Q (Pk hF hD 1) (Pk hF hD 0) = a := by
    rw [gram_lt hF hD (show 0 < 1 by norm_num), show 1 - 0 = 1 from rfl, ← hN₁, ha, hq]
    ring
  have p20 : polar Q (Pk hF hD 2) (Pk hF hD 0) = b := by
    rw [gram_lt hF hD (show 0 < 2 by norm_num), show 2 - 0 = 2 from rfl, ← hN₂, hb, hq]
    ring
  have p21 : polar Q (Pk hF hD 2) (Pk hF hD 1) = q * a := by
    rw [gram_lt hF hD (show 1 < 2 by norm_num), show 2 - 1 = 1 from rfl, ← hN₁, ha, hq]
    ring
  have key := gram_nonneg hF hD (K := 3) ![q, -a, 1]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.val_two] at key
  rw [polar_comm (P := Pk hF hD 0) (R := Pk hF hD 1), polar_comm (P := Pk hF hD 0) (R := Pk hF hD 2),
    polar_comm (P := Pk hF hD 1) (R := Pk hF hD 2), p00, p11, p22, p10, p20, p21] at key
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast (by omega : 0 < Fintype.card F)
  nlinarith

end toeplitz

end ManinHasse

#print axioms ManinHasse.toeplitz_nonneg
#print axioms ManinHasse.trace_two_ge
