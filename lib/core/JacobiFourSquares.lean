import Mathlib

/-! # Jacobi's four-square theorem

For `n ≥ 1` the number `r₄(n)` of points `v ∈ ℤ⁴` with `v₁² + v₂² + v₃² + v₄² = n` is eight times
the sum of the divisors of `n` that are not divisible by `4` (`r4_eq`), and `r₄(0) = 1`
(`r4_zero`).

The proof is Hirschhorn's (Proc. AMS 101 (1987)), in the purely formal version of Klazar's note,
carried out in the ring `ℤ⟦X⟧` of formal power series with the coefficientwise topology.

* **The triple product** (`jtp`). For power series `a`, `b` with `X ∣ a`,
  `∏ (1 - (ab)^(k+1)) (1 + a^(k+1) b^k) (1 + a^k b^(k+1)) = ∑_{j ∈ ℤ} a^T(j) b^T(j-1)`, where
  `T(j) = j(j+1)/2`. It is the limit of the finite identity `finite_jtp`, which holds in every
  commutative ring, with Gaussian binomial coefficients `gauss` on the right; the limit uses the
  congruence `[2N, i]_q ∏_{k<N} (1 - q^(k+1)) ≡ 1` modulo `X^(min(i, 2N-i)+1)`
  (`gauss_mul_euler`).
* **Jacobi's cube** (`jacobi_cube`): `(∏ (1 - X^(k+1)))³ = ∑_{j ∈ ℤ} j (-1)^j X^T(j)`. This is
  the `ε`-part of the finite identity over the dual numbers `ℤ⟦X⟧[ε]` at `a = -(1+ε)X`,
  `b = -(1-ε)`, where the factor `1 + b` is `ε`.
* **Squaring.** The square of `∑ (2j+1) (-1)^j X^T(j)` regroups, through the bijection
  `parityEquiv` between `ℤ² ⊕ ℤ²` and `ℤ²`, into `2 ∑_{r,s} ((2r+1)² - (2s)²) X^(r²+r+s²)`, which
  is `2 ((B + 4 D B) θ - 4 B D θ)` with `θ = ∑ X^(s²)`, `B = ∑ X^(r²+r)` and `D = X d/dX`.
* **Products.** The triple product writes `θ`, `B` and `θ(-X)` as infinite products. The
  logarithmic derivative (`D_ratio`) turns `θ D B - B D θ` into a Lambert series `L`, and Euler's
  identity `∏ (1 + X^k) (1 - X^(2k-1)) = 1` gives `θ(-X)⁴ = 1 + 8 L`.
* **Coefficients.** Substituting `X ↦ -X` and collecting divisors (`coeff_L`,
  `sum_sign_eq_sigma4`) gives `theta_pow_four`: `θ⁴ = 1 + 8 ∑ σ₄(n) Xⁿ`. The coefficient of `Xⁿ`
  in `θ⁴` counts the lattice points (`coeff_theta_pow_four`).
-/

open PowerSeries PowerSeries.WithPiTopology Filter Topology

namespace JacobiFourSquares

/-! ## Triangular numbers -/

/-- The triangular number `T j = j (j + 1) / 2` of an integer `j`. -/
def T (j : ℤ) : ℕ := (j * (j + 1) / 2).toNat

theorem two_mul_T (j : ℤ) : 2 * (T j : ℤ) = j * (j + 1) := by
  have h2 : (2 : ℤ) ∣ j * (j + 1) := (Int.even_mul_succ_self j).two_dvd
  have h0 : 0 ≤ j * (j + 1) := by
    rcases le_or_gt 0 j with h | h <;> nlinarith
  rw [T, Int.toNat_of_nonneg (Int.ediv_nonneg h0 (by norm_num)), Int.mul_ediv_cancel' h2]

theorem T_succ (j : ℤ) : (T (j + 1) : ℤ) = T j + j + 1 := by
  have h := two_mul_T (j + 1)
  have h' := two_mul_T j
  have : 2 * (T (j + 1) : ℤ) = 2 * (T j + j + 1) := by linear_combination h - h'
  omega

theorem T_neg (j : ℤ) : T (-1 - j) = T j := by
  have h := two_mul_T (-1 - j)
  have h' := two_mul_T j
  have : 2 * (T (-1 - j) : ℤ) = 2 * T j := by rw [h, h']; ring
  omega

theorem le_T (j : ℤ) : j ≤ T j := by
  have h := two_mul_T j
  rcases le_or_gt j 0 with hj | hj
  · exact hj.trans (Int.natCast_nonneg _)
  · nlinarith

theorem neg_le_T (j : ℤ) : -j - 1 ≤ T j := by
  have h := two_mul_T j
  rcases le_or_gt (-1) j with hj | hj
  · linarith [Int.natCast_nonneg (T j)]
  · nlinarith

theorem finite_T (n : ℕ) : {j : ℤ | T j ≤ n}.Finite :=
  (Set.finite_Icc (-(n : ℤ) - 1) n).subset fun j hj => by
    have := le_T j
    have := neg_le_T j
    have hj' : T j ≤ n := hj
    simp only [Set.mem_Icc]
    omega

theorem T_add_T_sub_one (j : ℤ) : T j + T (j - 1) = j.natAbs ^ 2 := by
  have h : (2 : ℤ) * ((T j + T (j - 1) : ℕ) : ℤ) = 2 * ((j.natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs]
    linear_combination two_mul_T j + two_mul_T (j - 1)
  generalize j.natAbs ^ 2 = s at h ⊢
  omega

theorem T_le_sq (j : ℤ) : T j ≤ j.natAbs ^ 2 := by
  rw [← T_add_T_sub_one]
  omega

/-! ## Gaussian binomials and the finite triple product -/

section FiniteTripleProduct

variable {K : Type*} [CommRing K]

/-- The term `a ^ T j * b ^ T (j - 1)` of the triple product series. -/
def jt (a b : K) (j : ℤ) : K := a ^ T j * b ^ T (j - 1)

/-- The Gaussian binomial coefficient `[n, k]` at `q`, by the `q`-Pascal rule. -/
def gauss (q : K) : ℕ → ℕ → K
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gauss q n k + q ^ (k + 1) * gauss q n (k + 1)

@[simp] theorem gauss_zero (q : K) (n : ℕ) : gauss q n 0 = 1 := by cases n <;> rfl

theorem gauss_succ (q : K) (n k : ℕ) :
    gauss q (n + 1) (k + 1) = gauss q n k + q ^ (k + 1) * gauss q n (k + 1) := rfl

theorem gauss_of_lt (q : K) {n k : ℕ} (h : n < k) : gauss q n k = 0 := by
  induction n generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [gauss_succ, ih (by omega), ih (by omega)]
    ring

theorem gauss_ratio (q : K) (n k : ℕ) :
    (1 - q ^ (n - k)) * gauss q n k = (1 - q ^ (k + 1)) * gauss q n (k + 1) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gauss]
  | succ n ih =>
    cases k with
    | zero =>
      have h := ih 0
      simp only [Nat.sub_zero, gauss_zero, zero_add, pow_one, mul_one] at h ⊢
      rw [gauss_succ, gauss_zero]
      linear_combination q * h
    | succ k =>
      rw [gauss_succ, gauss_succ]
      rcases lt_or_ge k n with hk | hk
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
        have h1 := ih k
        have h2 := ih (k + 1)
        rw [show k + m + 1 - k = m + 1 by omega] at h1
        rw [show k + m + 1 - (k + 1) = m by omega] at h2
        rw [show k + m + 1 + 1 - (k + 1) = m + 1 by omega]
        linear_combination h1 + q ^ (k + 1 + 1) * h2
      · rw [gauss_of_lt q (show n < k + 1 by omega), gauss_of_lt q (show n < k + 1 + 1 by omega),
          Nat.sub_eq_zero_of_le (show n + 1 ≤ k + 1 by omega)]
        ring

theorem gauss_succ' (q : K) (n k : ℕ) :
    gauss q (n + 1) (k + 1) = q ^ (n - k) * gauss q n k + gauss q n (k + 1) := by
  rw [gauss_succ]
  linear_combination gauss_ratio q n k

theorem gauss_mul_prod (q : K) (n k : ℕ) :
    gauss q n k * ∏ i ∈ Finset.range k, (1 - q ^ (i + 1)) =
      ∏ i ∈ Finset.range k, (1 - q ^ (n - i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih]
    linear_combination -(∏ i ∈ Finset.range k, (1 - q ^ (i + 1))) * gauss_ratio q n k

theorem map_gauss {L : Type*} [CommRing L] (f : K →+* L) (q : K) (n k : ℕ) :
    f (gauss q n k) = gauss (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gauss]
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [gauss_succ, ih]

theorem gauss_two (q : K) (N : ℕ) :
    gauss q (2 * N + 1 + 1) (0 + 1) = (1 + q ^ (2 * N + 1)) + q * gauss q (2 * N) 1 := by
  rw [gauss_succ', gauss_succ]
  simp only [gauss_zero, Nat.sub_zero, zero_add, pow_one]
  ring

theorem gauss_two_step (q : K) (N i : ℕ) :
    gauss q (2 * N + 1 + 1) (i + 1 + 1) = q ^ (2 * N - i) * gauss q (2 * N) i +
      (1 + q ^ (2 * N + 1)) * gauss q (2 * N) (i + 1) + q ^ (i + 2) * gauss q (2 * N) (i + 2) := by
  rw [gauss_succ, gauss_succ', gauss_succ']
  rcases lt_or_ge i (2 * N) with h | h
  · have e : q ^ (i + 1 + 1) * q ^ (2 * N - (i + 1)) = q ^ (2 * N + 1) := by
      rw [← pow_add]; congr 1; omega
    linear_combination gauss q (2 * N) (i + 1) * e
  · rw [gauss_of_lt q (show 2 * N < i + 1 by omega)]
    ring

theorem jt_succ (a b : K) (N : ℕ) (j : ℤ) (hj : j ≤ N) :
    a ^ (N + 1) * b ^ N * jt a b j = (a * b) ^ (N - j).toNat * jt a b (j + 1) := by
  have h1 := T_succ j
  have h2 := T_succ (j - 1)
  rw [sub_add_cancel] at h2
  have hm : ((N - j).toNat : ℤ) = N - j := Int.toNat_of_nonneg (by omega)
  simp only [jt, add_sub_cancel_right]
  calc a ^ (N + 1) * b ^ N * (a ^ T j * b ^ T (j - 1))
      = a ^ (N + 1 + T j) * b ^ (N + T (j - 1)) := by ring
    _ = a ^ ((N - j).toNat + T (j + 1)) * b ^ ((N - j).toNat + T j) := by
        rw [show N + 1 + T j = (N - j).toNat + T (j + 1) by omega,
          show N + T (j - 1) = (N - j).toNat + T j by omega]
    _ = (a * b) ^ (N - j).toNat * (a ^ T (j + 1) * b ^ T j) := by ring

theorem jt_pred (a b : K) (N : ℕ) (j : ℤ) (hj : -N ≤ j) :
    a ^ N * b ^ (N + 1) * jt a b j = (a * b) ^ (N + j).toNat * jt a b (j - 1) := by
  have h1 := T_succ (j - 1)
  have h2 := T_succ (j - 1 - 1)
  rw [sub_add_cancel] at h1 h2
  have hm : ((N + j).toNat : ℤ) = N + j := Int.toNat_of_nonneg (by omega)
  simp only [jt]
  calc a ^ N * b ^ (N + 1) * (a ^ T j * b ^ T (j - 1))
      = a ^ (N + T j) * b ^ (N + 1 + T (j - 1)) := by ring
    _ = a ^ ((N + j).toNat + T (j - 1)) * b ^ ((N + j).toNat + T (j - 1 - 1)) := by
        rw [show N + T j = (N + j).toNat + T (j - 1) by omega,
          show N + 1 + T (j - 1) = (N + j).toNat + T (j - 1 - 1) by omega]
    _ = (a * b) ^ (N + j).toNat * (a ^ T (j - 1) * b ^ T (j - 1 - 1)) := by ring

theorem finite_jtp (a b : K) (N : ℕ) :
    ∏ k ∈ Finset.range N, ((1 + a ^ (k + 1) * b ^ k) * (1 + a ^ k * b ^ (k + 1))) =
      ∑ i ∈ Finset.range (2 * N + 1), jt a b ((i : ℤ) - N) * gauss (a * b) (2 * N) i := by
  induction N with
  | zero => simp [jt, T]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_mul]
    have hG1 : gauss (a * b) (2 * N) (2 * N + 1) = 0 := gauss_of_lt _ (by omega)
    have hG2 : gauss (a * b) (2 * N) (2 * N + 1 + 1) = 0 := gauss_of_lt _ (by omega)
    have hL : ∀ i ∈ Finset.range (2 * N + 1), jt a b ((i : ℤ) - N) * gauss (a * b) (2 * N) i *
        ((1 + a ^ (N + 1) * b ^ N) * (1 + a ^ N * b ^ (N + 1))) =
        (1 + (a * b) ^ (2 * N + 1)) * (jt a b ((i : ℤ) - N) * gauss (a * b) (2 * N) i) +
        (a * b) ^ (2 * N - i) * jt a b ((i : ℤ) - N + 1) * gauss (a * b) (2 * N) i +
        (a * b) ^ i * jt a b ((i : ℤ) - N - 1) * gauss (a * b) (2 * N) i := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have e1 := jt_succ a b N ((i : ℤ) - N) (by omega)
      have e2 := jt_pred a b N ((i : ℤ) - N) (by omega)
      rw [show ((N : ℤ) - ((i : ℤ) - N)).toNat = 2 * N - i by omega] at e1
      rw [show ((N : ℤ) + ((i : ℤ) - N)).toNat = i by omega] at e2
      linear_combination gauss (a * b) (2 * N) i * e1 + gauss (a * b) (2 * N) i * e2
    rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- the shifted sums
    have I1 : ∑ i ∈ Finset.range (2 * N + 1),
        (1 + (a * b) ^ (2 * N + 1)) * (jt a b ((i : ℤ) - N) * gauss (a * b) (2 * N) i) =
        ∑ i ∈ Finset.range (2 * N + 1),
          (1 + (a * b) ^ (2 * N + 1)) * (jt a b ((i : ℤ) - N + 1) * gauss (a * b) (2 * N) (i + 1)) +
        (1 + (a * b) ^ (2 * N + 1)) * jt a b (-N) := by
      have h1 := Finset.sum_range_succ (fun i : ℕ =>
        (1 + (a * b) ^ (2 * N + 1)) * (jt a b ((i : ℤ) - N) * gauss (a * b) (2 * N) i)) (2 * N + 1)
      have h2 := Finset.sum_range_succ' (fun i : ℕ =>
        (1 + (a * b) ^ (2 * N + 1)) * (jt a b ((i : ℤ) - N) * gauss (a * b) (2 * N) i)) (2 * N + 1)
      simp only [hG1, mul_zero, add_zero] at h1
      rw [← h1, h2]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub, gauss_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (i : ℤ) + 1 - N = i - N + 1 by ring]
    have I2 : ∑ i ∈ Finset.range (2 * N + 1),
        (a * b) ^ i * jt a b ((i : ℤ) - N - 1) * gauss (a * b) (2 * N) i =
        ∑ i ∈ Finset.range (2 * N + 1),
          (a * b) ^ (i + 2) * jt a b ((i : ℤ) - N + 1) * gauss (a * b) (2 * N) (i + 2) +
        (a * b) * jt a b (-N) * gauss (a * b) (2 * N) 1 + jt a b (-N - 1) := by
      have h1 := Finset.sum_range_succ (fun i : ℕ =>
        (a * b) ^ i * jt a b ((i : ℤ) - N - 1) * gauss (a * b) (2 * N) i) (2 * N + 1 + 1)
      have h1' := Finset.sum_range_succ (fun i : ℕ =>
        (a * b) ^ i * jt a b ((i : ℤ) - N - 1) * gauss (a * b) (2 * N) i) (2 * N + 1)
      have h2 := Finset.sum_range_succ' (fun i : ℕ =>
        (a * b) ^ i * jt a b ((i : ℤ) - N - 1) * gauss (a * b) (2 * N) i) (2 * N + 1 + 1)
      have h2' := Finset.sum_range_succ' (fun i : ℕ =>
        (a * b) ^ (i + 1) * jt a b (((i + 1 : ℕ) : ℤ) - N - 1) * gauss (a * b) (2 * N) (i + 1))
        (2 * N + 1)
      simp only [hG1, hG2, mul_zero, add_zero] at h1 h1'
      rw [← h1', ← h1, h2, h2']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub, gauss_zero, mul_one, pow_zero,
        one_mul, zero_add, pow_one]
      congr 2
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (i : ℤ) + 1 + 1 - N - 1 = i - N + 1 by ring]
      · rw [show (1 : ℤ) - N - 1 = -N by ring]
    have hR : ∀ i ∈ Finset.range (2 * N + 1), jt a b (((i + 1 + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ)) *
        gauss (a * b) (2 * N + 1 + 1) (i + 1 + 1) =
        (a * b) ^ (2 * N - i) * jt a b ((i : ℤ) - N + 1) * gauss (a * b) (2 * N) i +
        (1 + (a * b) ^ (2 * N + 1)) * (jt a b ((i : ℤ) - N + 1) * gauss (a * b) (2 * N) (i + 1)) +
        (a * b) ^ (i + 2) * jt a b ((i : ℤ) - N + 1) * gauss (a * b) (2 * N) (i + 2) := by
      intro i _
      rw [gauss_two_step,
        show ((i + 1 + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = i - N + 1 by push_cast; ring]
      ring
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_congr rfl hR,
      Finset.sum_add_distrib, Finset.sum_add_distrib, gauss_two, gauss_zero,
      show ((0 + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = -N by push_cast; ring,
      show ((0 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = -N - 1 by push_cast; ring]
    linear_combination I1 + I2

end FiniteTripleProduct

/-! ## Power series over `ℤ` -/

theorem coeff_eq_of_dvd {f g : ℤ⟦X⟧} {N m : ℕ} (h : X ^ N ∣ f - g) (hm : m < N) :
    coeff m f = coeff m g := by
  have := X_pow_dvd_iff.mp h m hm
  rwa [map_sub, sub_eq_zero] at this

theorem dvd_prod_sub_one {ι : Type*} (s : Finset ι) (f : ι → ℤ⟦X⟧) (c : ℕ)
    (h : ∀ i ∈ s, X ^ c ∣ f i - 1) : X ^ c ∣ (∏ i ∈ s, f i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have : f i * ∏ j ∈ s, f j - 1 = f i * (∏ j ∈ s, f j - 1) + (f i - 1) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) h1

theorem summable_of_dvd {ι : Type*} {f : ι → ℤ⟦X⟧} (e : ι → ℕ) (he : ∀ i, X ^ e i ∣ f i)
    (hfin : ∀ n, {i | e i ≤ n}.Finite) : Summable f := by
  rw [summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  refine (hfin n).subset fun i hi => ?_
  by_contra h
  exact hi (X_pow_dvd_iff.mp (he i) n (by simpa using h))

theorem coeff_of_hasSum {ι : Type*} {f : ι → ℤ⟦X⟧} {F : ℤ⟦X⟧} (hF : HasSum f F) (n : ℕ)
    (s : Finset ι) (hs : ∀ i ∉ s, coeff n (f i) = 0) : coeff n F = ∑ i ∈ s, coeff n (f i) :=
  ((hasSum_iff_hasSum_coeff ℤ).mp hF n).unique (hasSum_sum_of_ne_finset_zero hs)

theorem hasSum_mul_of_dvd {ι κ : Type*} {f : ι → ℤ⟦X⟧} {g : κ → ℤ⟦X⟧} {F G : ℤ⟦X⟧}
    (e : ι → ℕ) (e' : κ → ℕ) (hf : HasSum f F) (hg : HasSum g G)
    (hfe : ∀ i, X ^ e i ∣ f i) (hge : ∀ j, X ^ e' j ∣ g j)
    (he : ∀ n, {i | e i ≤ n}.Finite) (he' : ∀ n, {j | e' j ≤ n}.Finite) :
    HasSum (fun p : ι × κ => f p.1 * g p.2) (F * G) :=
  hf.mul hg <| summable_of_dvd (fun p => e p.1 + e' p.2)
    (fun p => by rw [pow_add]; exact mul_dvd_mul (hfe _) (hge _))
    fun n => ((he n).prod (he' n)).subset fun p (hp : e p.1 + e' p.2 ≤ n) =>
      ⟨(by omega : e p.1 ≤ n), (by omega : e' p.2 ≤ n)⟩

theorem multipliable_of_dvd {f : ℕ → ℤ⟦X⟧} (h : ∀ k, X ^ k ∣ f k - 1) : Multipliable f := by
  have := multipliable_one_add_of_tendsto_order_atTop_nhds_top ℤ (f := fun k => f k - 1) ?_
  · simpa using this
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [eventually_gt_atTop n] with k hk
  exact (Nat.cast_lt.mpr hk).trans_le (nat_le_order _ _ fun i hi => X_pow_dvd_iff.mp (h k) i hi)

theorem constantCoeff_of_hasProd {f : ℕ → ℤ⟦X⟧} {P : ℤ⟦X⟧} (hP : HasProd f P)
    (h : ∀ k, constantCoeff (f k) = 1) : constantCoeff P = 1 := by
  have := hP.map (constantCoeff (R := ℤ)) (continuous_constantCoeff ℤ)
  simp only [Function.comp_def, h] at this
  exact this.unique hasProd_one

theorem X_pow_dvd_one_sub_pow_sub_one {q : ℤ⟦X⟧} (hq : X ∣ q) {c e : ℕ} (h : c ≤ e) :
    X ^ c ∣ (1 - q ^ e) - 1 := by
  rw [sub_sub_cancel_left]
  exact dvd_neg.mpr ((pow_dvd_pow X h).trans (pow_dvd_pow_of_dvd hq e))

theorem monomial_eq (n : ℕ) (c : ℤ) : (monomial n c : ℤ⟦X⟧) = C c * X ^ n := by
  rw [X_pow_eq, ← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]

theorem C_ne_zero {c : ℤ} (hc : c ≠ 0) : (C c : ℤ⟦X⟧) ≠ 0 :=
  fun h => hc (by simpa using congrArg (coeff 0) h)

theorem X_pow_dvd_monomial {n e : ℕ} (h : n ≤ e) (c : ℤ) : X ^ n ∣ (monomial e c : ℤ⟦X⟧) :=
  X_pow_dvd_iff.mpr fun m hm => by
    rw [coeff_monomial]
    split_ifs <;> omega

theorem hasSum_rescale {ι : Type*} {f : ι → ℤ⟦X⟧} {F : ℤ⟦X⟧} (a : ℤ) (h : HasSum f F) :
    HasSum (fun i => rescale a (f i)) (rescale a F) := by
  rw [hasSum_iff_hasSum_coeff] at h ⊢
  intro n
  simpa only [coeff_rescale] using (h n).mul_left (a ^ n)

/-! ## The triple product -/

theorem gauss_mul_euler {q : ℤ⟦X⟧} (hq : X ∣ q) {n k M : ℕ} (hk : k ≤ n) :
    X ^ (min (min k (n - k)) M + 1) ∣
      gauss q n k * ∏ l ∈ Finset.range M, (1 - q ^ (l + 1)) - 1 := by
  have hP := gauss_mul_prod q n k
  have hM := Finset.prod_range_mul_prod_Ico (fun l => 1 - q ^ (l + 1)) (min_le_right k M)
  have hK := Finset.prod_range_mul_prod_Ico (fun l => 1 - q ^ (l + 1)) (min_le_left k M)
  have hR1 : X ^ (min k M + 1) ∣ ∏ l ∈ Finset.Ico (min k M) M, (1 - q ^ (l + 1)) - 1 :=
    dvd_prod_sub_one _ _ _ fun l hl =>
      X_pow_dvd_one_sub_pow_sub_one hq (by simp only [Finset.mem_Ico] at hl; omega)
  have hR2 : X ^ (min k M + 1) ∣ ∏ l ∈ Finset.Ico (min k M) k, (1 - q ^ (l + 1)) - 1 :=
    dvd_prod_sub_one _ _ _ fun l hl =>
      X_pow_dvd_one_sub_pow_sub_one hq (by simp only [Finset.mem_Ico] at hl; omega)
  have hPi : X ^ (n - k + 1) ∣ ∏ l ∈ Finset.range k, (1 - q ^ (n - l)) - 1 :=
    dvd_prod_sub_one _ _ _ fun l hl =>
      X_pow_dvd_one_sub_pow_sub_one hq (by simp only [Finset.mem_range] at hl; omega)
  have key : gauss q n k * ∏ l ∈ Finset.range M, (1 - q ^ (l + 1)) - 1 =
      gauss q n k * (∏ l ∈ Finset.range (min k M), (1 - q ^ (l + 1))) *
        ((∏ l ∈ Finset.Ico (min k M) M, (1 - q ^ (l + 1)) - 1) -
          (∏ l ∈ Finset.Ico (min k M) k, (1 - q ^ (l + 1)) - 1)) +
      (∏ l ∈ Finset.range k, (1 - q ^ (n - l)) - 1) := by
    rw [← hP, ← hM, ← hK]
    ring
  rw [key]
  exact dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow X (by omega)).trans (dvd_sub hR1 hR2)) _)
    ((pow_dvd_pow X (by omega)).trans hPi)

theorem tendsto_jtp {q : ℤ⟦X⟧} (hq : X ∣ q) {u : ℤ → ℤ⟦X⟧} (hu : ∀ j, X ^ T j ∣ u j)
    {S : ℤ⟦X⟧} (hS : HasSum u S) :
    Tendsto (fun N : ℕ => (∏ k ∈ Finset.range N, (1 - q ^ (k + 1))) *
      ∑ i ∈ Finset.range (2 * N + 1), u ((i : ℤ) - N) * gauss q (2 * N) i) atTop (𝓝 S) := by
  rw [tendsto_iff_coeff_tendsto]
  intro m
  refine tendsto_atTop_of_eventually_const (i₀ := m + 1) fun N hN => ?_
  have h1 : X ^ N ∣ (∏ k ∈ Finset.range N, (1 - q ^ (k + 1))) *
      ∑ i ∈ Finset.range (2 * N + 1), u ((i : ℤ) - N) * gauss q (2 * N) i -
      ∑ i ∈ Finset.range (2 * N + 1), u ((i : ℤ) - N) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hg := gauss_mul_euler hq (n := 2 * N) (k := i) (M := N) (by omega)
    have e1 := le_T ((i : ℤ) - N)
    have e2 := neg_le_T ((i : ℤ) - N)
    have : (∏ k ∈ Finset.range N, (1 - q ^ (k + 1))) * (u ((i : ℤ) - N) * gauss q (2 * N) i) -
        u ((i : ℤ) - N) =
        u ((i : ℤ) - N) * (gauss q (2 * N) i * ∏ k ∈ Finset.range N, (1 - q ^ (k + 1)) - 1) := by
      ring
    have hN : N ≤ T ((i : ℤ) - N) + (min (min i (2 * N - i)) N + 1) := by omega
    rw [this]
    exact (pow_dvd_pow X hN).trans (by rw [pow_add]; exact mul_dvd_mul (hu _) hg)
  have h2 : coeff m S = ∑ i ∈ Finset.range (2 * N + 1), coeff m (u ((i : ℤ) - N)) := by
    rw [coeff_of_hasSum hS m ((Finset.range (2 * N + 1)).image fun i : ℕ => (i : ℤ) - N),
      Finset.sum_image]
    · intro i _ j _ h
      simpa using h
    · intro j hj
      have hj' : ¬ ((-N : ℤ) ≤ j ∧ j ≤ N) := fun h => hj (Finset.mem_image.mpr
        ⟨(j + N).toNat, Finset.mem_range.mpr (by omega), by omega⟩)
      have e1 := le_T j
      have e2 := neg_le_T j
      exact X_pow_dvd_iff.mp (hu j) m (by omega)
  rw [coeff_eq_of_dvd h1 (by omega), map_sum, h2]

/-- **Jacobi's triple product identity**, in the form
`∏ (1 - (ab)^(k+1)) (1 + a^(k+1) b^k) (1 + a^k b^(k+1)) = ∑_{j ∈ ℤ} a^T(j) b^T(j-1)`,
for power series `a`, `b` with `X ∣ a`. -/
theorem jtp {a b S : ℤ⟦X⟧} (ha : X ∣ a) (hS : HasSum (jt a b) S) :
    HasProd (fun k : ℕ => (1 - (a * b) ^ (k + 1)) *
      ((1 + a ^ (k + 1) * b ^ k) * (1 + a ^ k * b ^ (k + 1)))) S := by
  have hq : X ∣ a * b := dvd_mul_of_dvd_left ha b
  have hmul : Multipliable (fun k : ℕ => (1 - (a * b) ^ (k + 1)) *
      ((1 + a ^ (k + 1) * b ^ k) * (1 + a ^ k * b ^ (k + 1)))) := by
    refine multipliable_of_dvd fun k => ?_
    have hx : X ^ k ∣ (a * b) ^ (k + 1) :=
      (pow_dvd_pow X (Nat.le_succ k)).trans (pow_dvd_pow_of_dvd hq _)
    have hy : X ^ k ∣ a ^ (k + 1) * b ^ k :=
      dvd_mul_of_dvd_left ((pow_dvd_pow X (Nat.le_succ k)).trans (pow_dvd_pow_of_dvd ha _)) _
    have hz : X ^ k ∣ a ^ k * b ^ (k + 1) := dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd ha _) _
    have : (1 - (a * b) ^ (k + 1)) * ((1 + a ^ (k + 1) * b ^ k) * (1 + a ^ k * b ^ (k + 1))) - 1 =
        -((a * b) ^ (k + 1)) * ((1 + a ^ (k + 1) * b ^ k) * (1 + a ^ k * b ^ (k + 1))) +
          a ^ (k + 1) * b ^ k * (1 + a ^ k * b ^ (k + 1)) + a ^ k * b ^ (k + 1) := by ring
    rw [this]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr hx) _) (dvd_mul_of_dvd_left hy _)) hz
  have h1 := hmul.tendsto_prod_tprod_nat
  have h2 := tendsto_jtp hq (fun j => dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd ha _) _) hS
  have h3 : (fun N : ℕ => ∏ k ∈ Finset.range N, (1 - (a * b) ^ (k + 1)) *
      ((1 + a ^ (k + 1) * b ^ k) * (1 + a ^ k * b ^ (k + 1)))) = fun N =>
      (∏ k ∈ Finset.range N, (1 - (a * b) ^ (k + 1))) *
        ∑ i ∈ Finset.range (2 * N + 1), jt a b ((i : ℤ) - N) * gauss (a * b) (2 * N) i := by
    funext N
    rw [Finset.prod_mul_distrib, finite_jtp]
  rw [h3] at h1
  rw [← tendsto_nhds_unique h1 h2]
  exact hmul.hasProd

/-! ## Jacobi's identity for the cube of the Euler product -/

/-- The term `j (-1)^j X^T(j)` of Jacobi's series for the cube of the Euler product. -/
noncomputable def cubeTerm (j : ℤ) : ℤ⟦X⟧ := monomial (T j) (j * j.negOnePow)

section Dual

open DualNumber TrivSqZeroExt

theorem one_add_eps_pow (m : ℕ) :
    (1 + ε : DualNumber ℤ⟦X⟧) ^ m = 1 + (m : DualNumber ℤ⟦X⟧) * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (m : DualNumber ℤ⟦X⟧) * (eps_mul_eps (R := ℤ⟦X⟧))

theorem one_sub_eps_pow (m : ℕ) :
    (1 - ε : DualNumber ℤ⟦X⟧) ^ m = 1 - (m : DualNumber ℤ⟦X⟧) * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (m : DualNumber ℤ⟦X⟧) * (eps_mul_eps (R := ℤ⟦X⟧))

theorem snd_jt (j : ℤ) :
    snd (jt (inl (-X : ℤ⟦X⟧) * (1 + ε)) (inl (-1 : ℤ⟦X⟧) * (1 - ε)) j) = cubeTerm j := by
  have hT := T_succ (j - 1)
  rw [sub_add_cancel] at hT
  have e : jt (inl (-X : ℤ⟦X⟧) * (1 + ε)) (inl (-1 : ℤ⟦X⟧) * (1 - ε)) j =
      inl ((-X : ℤ⟦X⟧) ^ T j * (-1) ^ T (j - 1)) *
        (1 + ((T j : DualNumber ℤ⟦X⟧) - (T (j - 1) : DualNumber ℤ⟦X⟧)) * ε) := by
    simp only [jt, mul_pow, one_add_eps_pow, one_sub_eps_pow, inl_pow, inl_mul]
    linear_combination (-(T j : DualNumber ℤ⟦X⟧) * (T (j - 1) : DualNumber ℤ⟦X⟧) *
      inl ((-X : ℤ⟦X⟧) ^ T j) * inl ((-1 : ℤ⟦X⟧) ^ T (j - 1))) * (eps_mul_eps (R := ℤ⟦X⟧))
  rw [e]
  simp only [inl_mul, TrivSqZeroExt.snd_mul, fst_mul, fst_inl, snd_add, snd_one, fst_sub,
    fst_natCast, snd_eps, smul_eq_mul, mul_one, fst_eps, MulOpposite.op_zero, snd_sub, snd_natCast,
    sub_self, smul_zero, add_zero, zero_add, fst_add, fst_one, mul_zero, MulOpposite.op_one,
    snd_inl, MulOpposite.op_pow, MulOpposite.op_neg]
  have hc : ((T j : ℤ⟦X⟧) - (T (j - 1) : ℤ⟦X⟧)) = C (j : ℤ) := by
    rw [← map_natCast C, ← map_natCast C, ← map_sub]
    congr 1
    omega
  have hs : (-1 : ℤ⟦X⟧) ^ T j * (-1) ^ T (j - 1) = C (j.negOnePow : ℤ) := by
    rw [← pow_add, show (-1 : ℤ⟦X⟧) = C (-1) by simp, ← map_pow, ← Int.coe_negOnePow_natCast,
      show ((T j + T (j - 1) : ℕ) : ℤ) = j + 2 * (T (j - 1) : ℤ) by push_cast; omega,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  rw [cubeTerm, monomial_eq, neg_pow, hc, map_mul, ← hs]
  ring

theorem neg_X_pow_mul (m : ℕ) : (-X : ℤ⟦X⟧) ^ (m + 1) * (-1) ^ m = -X ^ (m + 1) := by
  have h : ((-1 : ℤ⟦X⟧) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  rw [neg_pow]
  linear_combination (-X ^ (m + 1) : ℤ⟦X⟧) * h

theorem neg_X_pow_mul' (m : ℕ) : (-X : ℤ⟦X⟧) ^ m * (-1) ^ (m + 1) = -X ^ m := by
  have h : ((-1 : ℤ⟦X⟧) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  rw [neg_pow]
  linear_combination (-X ^ m : ℤ⟦X⟧) * h

theorem finite_cube (N : ℕ) :
    (∏ k ∈ Finset.range (N + 1), (1 - (X : ℤ⟦X⟧) ^ (k + 1))) *
      ∏ k ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (k + 1)) =
      ∑ i ∈ Finset.range (2 * (N + 1) + 1),
        cubeTerm ((i : ℤ) - (N + 1 : ℕ)) * gauss X (2 * (N + 1)) i := by
  have hab : ((inl (-X : ℤ⟦X⟧) * (1 + ε)) * (inl (-1 : ℤ⟦X⟧) * (1 - ε)) : DualNumber ℤ⟦X⟧) =
      inl X := by
    have : (1 + ε : DualNumber ℤ⟦X⟧) * (1 - ε) = 1 := by
      linear_combination -(eps_mul_eps (R := ℤ⟦X⟧))
    calc ((inl (-X : ℤ⟦X⟧) * (1 + ε)) * (inl (-1 : ℤ⟦X⟧) * (1 - ε)) : DualNumber ℤ⟦X⟧)
        = inl ((-X) * (-1)) * ((1 + ε) * (1 - ε)) := by rw [inl_mul]; ring
      _ = inl X := by rw [this, mul_one]; congr 1; ring
  have hg : ∀ n k, gauss (inl X : DualNumber ℤ⟦X⟧) n k = inl (gauss X n k) :=
    fun n k => (map_gauss (inlHom ℤ⟦X⟧ ℤ⟦X⟧) X n k).symm
  have h := congrArg snd (finite_jtp (inl (-X : ℤ⟦X⟧) * (1 + ε) : DualNumber ℤ⟦X⟧)
    (inl (-1 : ℤ⟦X⟧) * (1 - ε)) (N + 1))
  rw [hab, snd_sum] at h
  simp only [hg, DualNumber.snd_mul, fst_inl, snd_inl, mul_zero, zero_add, snd_jt] at h
  rw [← h]
  conv_rhs => rw [Finset.prod_range_succ']
  have h1b : (1 + inl (-1 : ℤ⟦X⟧) * (1 - ε) : DualNumber ℤ⟦X⟧) = ε := by
    rw [inl_neg, inl_one]
    ring
  rw [pow_zero, pow_zero, zero_add, pow_one, pow_one, mul_one, one_mul, h1b, ← mul_assoc,
    DualNumber.snd_mul, snd_eps, fst_eps, mul_one, mul_zero, add_zero, fst_mul]
  rw [show ∀ x : DualNumber ℤ⟦X⟧, fst x = fstHom ℤ⟦X⟧ ℤ⟦X⟧ ℤ⟦X⟧ x from fun _ => rfl, map_prod]
  simp only [fstHom_apply, fst_mul, fst_add, fst_sub, fst_one, fst_pow, fst_inl,
    DualNumber.fst_eps, add_zero, sub_zero, mul_one, neg_X_pow_mul, neg_X_pow_mul',
    ← sub_eq_add_neg]
  rw [Finset.prod_range_succ' (fun k => 1 - (X : ℤ⟦X⟧) ^ (k + 1)), Finset.prod_mul_distrib]
  ring

end Dual

/-- **Jacobi's identity** `(∏ (1 - X^(k+1)))^3 = ∑_{j ∈ ℤ} j (-1)^j X^T(j)`. -/
theorem jacobi_cube {C3 S : ℤ⟦X⟧} (hC : HasProd (fun k : ℕ => 1 - X ^ (k + 1)) C3)
    (hS : HasSum cubeTerm S) : C3 ^ 3 = S := by
  have h1 := tendsto_jtp (q := X) (u := cubeTerm) dvd_rfl
    (fun j => X_pow_dvd_monomial le_rfl _) hS
  have h2 := h1.comp (tendsto_add_atTop_nat 1)
  have ht := hC.tendsto_prod_nat
  have h3 := (ht.comp (tendsto_add_atTop_nat 1)).mul ((ht.comp (tendsto_add_atTop_nat 1)).mul ht)
  have h4 : ((fun N : ℕ => (∏ k ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (k + 1))) *
      ∑ i ∈ Finset.range (2 * N + 1), cubeTerm ((i : ℤ) - N) * gauss X (2 * N) i) ∘
        fun n => n + 1) = fun N =>
      (∏ k ∈ Finset.range (N + 1), (1 - (X : ℤ⟦X⟧) ^ (k + 1))) *
        ((∏ k ∈ Finset.range (N + 1), (1 - (X : ℤ⟦X⟧) ^ (k + 1))) *
          ∏ k ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (k + 1))) := by
    funext N
    simp only [Function.comp_apply, finite_cube]
  rw [h4] at h2
  rw [show C3 ^ 3 = C3 * (C3 * C3) by ring]
  exact tendsto_nhds_unique h3 h2

/-! ## The Euler operator `X d/dX` and logarithmic derivatives -/

/-- The Euler operator `X d/dX`: it multiplies the `n`-th coefficient by `n`. -/
noncomputable def D (f : ℤ⟦X⟧) : ℤ⟦X⟧ := mk fun n => n * coeff n f

theorem coeff_D (f : ℤ⟦X⟧) (n : ℕ) : coeff n (D f) = n * coeff n f := coeff_mk _ _

theorem D_mul (f g : ℤ⟦X⟧) : D (f * g) = D f * g + f * D g := by
  ext n
  simp only [coeff_D, map_add, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  push_cast
  ring

theorem D_monomial (e : ℕ) (c : ℤ) : D (monomial e c) = monomial e (e * c) := by
  ext n
  simp only [coeff_D, coeff_monomial]
  split_ifs with h
  · rw [h]
  · ring

theorem D_C (c : ℤ) : D (C c) = 0 := by
  ext n
  rw [coeff_D, coeff_C]
  split_ifs with h <;> simp [h]

theorem hasSum_D {ι : Type*} {f : ι → ℤ⟦X⟧} {F : ℤ⟦X⟧} (h : HasSum f F) :
    HasSum (fun i => D (f i)) (D F) := by
  rw [hasSum_iff_hasSum_coeff] at h ⊢
  intro n
  simpa only [coeff_D] using (h n).mul_left (n : ℤ)

theorem tendsto_D {s : ℕ → ℤ⟦X⟧} {F : ℤ⟦X⟧} (h : Tendsto s atTop (𝓝 F)) :
    Tendsto (fun N => D (s N)) atTop (𝓝 (D F)) := by
  rw [tendsto_iff_coeff_tendsto] at h ⊢
  intro n
  simpa only [coeff_D] using (h n).const_mul (n : ℤ)

theorem D_prod {f ℓ : ℕ → ℤ⟦X⟧} (h : ∀ k, D (f k) = f k * ℓ k) (N : ℕ) :
    D (∏ k ∈ Finset.range N, f k) = (∏ k ∈ Finset.range N, f k) * ∑ k ∈ Finset.range N, ℓ k := by
  induction N with
  | zero =>
    ext n
    simp [coeff_D, coeff_one]
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, D_mul, ih, h]
    ring

/-- The logarithmic derivative `X (1 + X^d)' / (1 + X^d) = ∑_{j ≥ 1} (-1)^(j+1) d X^(dj)`. -/
noncomputable def lam (d : ℕ) : ℤ⟦X⟧ := mk fun n => if d ∣ n ∧ 0 < n then -(-1) ^ (n / d) * d else 0

theorem D_one_add_X_pow (d : ℕ) : D (1 + X ^ d) = (1 + X ^ d) * lam d := by
  ext n
  rw [coeff_D, add_mul, one_mul, map_add, map_add, coeff_X_pow_mul', lam, coeff_mk, coeff_one,
    coeff_X_pow]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [zero_dvd_iff, zero_le, ite_true, Nat.sub_zero, coeff_mk]
    split_ifs <;> simp_all
  rcases lt_trichotomy n d with h | rfl | h
  · have h1 : ¬ (d ∣ n ∧ 0 < n) := fun ⟨h2, h3⟩ => absurd (Nat.le_of_dvd h3 h2) (by omega)
    rw [ite_eq_right h1, ite_eq_right (show ¬ d ≤ n by omega), ite_eq_right (show n ≠ d by omega)]
    split_ifs <;> simp_all
  · rw [ite_eq_left (show n ∣ n ∧ 0 < n from ⟨dvd_refl n, hd⟩), ite_eq_left (le_refl n),
      ite_eq_left rfl, ite_eq_right (show n ≠ 0 by omega), Nat.sub_self, coeff_mk,
      ite_eq_right (show ¬ (n ∣ 0 ∧ 0 < 0) by simp), Nat.div_self hd]
    ring
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [ite_eq_left (show d ≤ d + m + 1 by omega), show d + m + 1 - d = m + 1 by omega, coeff_mk,
      ite_eq_right (show d + m + 1 ≠ 0 by omega), ite_eq_right (show d + m + 1 ≠ d by omega)]
    simp only [show d + m + 1 = d + (m + 1) by ring, Nat.dvd_add_right (dvd_refl d),
      show 0 < d + (m + 1) by omega, show 0 < m + 1 by omega, and_true]
    split_ifs
    · rw [Nat.add_div_of_dvd_right (dvd_refl d), Nat.div_self hd]
      ring
    · ring

theorem X_pow_dvd_lam (d : ℕ) : X ^ d ∣ lam d :=
  X_pow_dvd_iff.mpr fun m hm => by
    rw [lam, coeff_mk, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact absurd (Nat.le_of_dvd h2 h1) (by omega)

/-- The derivative of a quotient of two infinite products, without division:
`P Q' - P' Q = P Q ∑ (ℓg - ℓf)` when `f' = f ℓf` and `g' = g ℓg` factorwise. -/
theorem D_ratio {f g ℓf ℓg : ℕ → ℤ⟦X⟧} {P Q L : ℤ⟦X⟧} (hP : HasProd f P) (hQ : HasProd g Q)
    (hf : ∀ k, D (f k) = f k * ℓf k) (hg : ∀ k, D (g k) = g k * ℓg k)
    (hL : HasSum (fun k => ℓg k - ℓf k) L) : P * D Q - D P * Q = P * Q * L := by
  have tP := hP.tendsto_prod_nat
  have tQ := hQ.tendsto_prod_nat
  have h1 := (tP.mul (tendsto_D tQ)).sub ((tendsto_D tP).mul tQ)
  have h2 := (tP.mul tQ).mul hL.tendsto_sum_nat
  have h3 : (fun N => (∏ k ∈ Finset.range N, f k) * D (∏ k ∈ Finset.range N, g k) -
      D (∏ k ∈ Finset.range N, f k) * ∏ k ∈ Finset.range N, g k) = fun N =>
      (∏ k ∈ Finset.range N, f k) * (∏ k ∈ Finset.range N, g k) *
        ∑ k ∈ Finset.range N, (ℓg k - ℓf k) := by
    funext N
    rw [D_prod hf, D_prod hg, Finset.sum_sub_distrib]
    ring
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-! ## The square of Jacobi's series -/

/-- The parity bijection `ℤ² ⊕ ℤ² ≃ ℤ²`: `(r, s) ↦ (r + s, r - s)` on the first copy and
`(r, s) ↦ (r + s, s - r - 1)` on the second. -/
def parityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun p => (p.1 + p.2, p.1 - p.2)) (fun p => (p.1 + p.2, p.2 - p.1 - 1))
  invFun p := if (p.1 + p.2) % 2 = 0 then Sum.inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
    else Sum.inr ((p.1 - p.2 - 1) / 2, (p.1 + p.2 + 1) / 2)
  left_inv := by
    rintro (⟨r, s⟩ | ⟨r, s⟩) <;> dsimp only [Sum.elim_inl, Sum.elim_inr]
    · rw [ite_eq_left (by omega)]
      simp only [Sum.inl.injEq, Prod.mk.injEq]
      omega
    · rw [ite_eq_right (by omega)]
      simp only [Sum.inr.injEq, Prod.mk.injEq]
      omega
  right_inv := by
    rintro ⟨m, n⟩
    dsimp only
    by_cases h : (m + n) % 2 = 0
    · rw [ite_eq_left h]
      dsimp only [Sum.elim_inl]
      simp only [Prod.mk.injEq]
      omega
    · rw [ite_eq_right h]
      dsimp only [Sum.elim_inr]
      simp only [Prod.mk.injEq]
      omega

theorem v_mul_v_inl (r s : ℤ) :
    (monomial (T (r + s)) ((2 * (r + s) + 1) * ((r + s).negOnePow : ℤ)) : ℤ⟦X⟧) *
      monomial (T (r - s)) ((2 * (r - s) + 1) * ((r - s).negOnePow : ℤ)) =
    monomial (2 * T r + s.natAbs ^ 2) ((2 * r + 1) ^ 2 - 4 * s ^ 2) := by
  have he : T (r + s) + T (r - s) = 2 * T r + s.natAbs ^ 2 := by
    have h : (2 : ℤ) * ((T (r + s) + T (r - s) : ℕ) : ℤ) =
        2 * ((2 * T r + s.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      linear_combination two_mul_T (r + s) + two_mul_T (r - s) - 2 * two_mul_T r
    generalize s.natAbs ^ 2 = t at h ⊢
    omega
  have hσ : ((r + s).negOnePow : ℤ) * ((r - s).negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, show r + s + (r - s) = 2 * r by ring,
      Int.negOnePow_two_mul, Units.val_one]
  rw [monomial_mul_monomial, he]
  congr 1
  linear_combination ((2 * (r + s) + 1) * (2 * (r - s) + 1)) * hσ

theorem v_mul_v_inr (r s : ℤ) :
    (monomial (T (r + s)) ((2 * (r + s) + 1) * ((r + s).negOnePow : ℤ)) : ℤ⟦X⟧) *
      monomial (T (s - r - 1)) ((2 * (s - r - 1) + 1) * ((s - r - 1).negOnePow : ℤ)) =
    monomial (2 * T r + s.natAbs ^ 2) ((2 * r + 1) ^ 2 - 4 * s ^ 2) := by
  have he : T (r + s) + T (s - r - 1) = 2 * T r + s.natAbs ^ 2 := by
    have h : (2 : ℤ) * ((T (r + s) + T (s - r - 1) : ℕ) : ℤ) =
        2 * ((2 * T r + s.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      linear_combination two_mul_T (r + s) + two_mul_T (s - r - 1) - 2 * two_mul_T r
    generalize s.natAbs ^ 2 = t at h ⊢
    omega
  have hσ : ((r + s).negOnePow : ℤ) * ((s - r - 1).negOnePow : ℤ) = -1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, show r + s + (s - r - 1) = 2 * (s - 1) + 1 by ring,
      Int.negOnePow_two_mul_add_one, Units.val_neg, Units.val_one]
  rw [monomial_mul_monomial, he]
  congr 1
  linear_combination ((2 * (r + s) + 1) * (2 * (s - r - 1) + 1)) * hσ

theorem w_eq (r s : ℤ) :
    (monomial (2 * T r) 1 + C 4 * D (monomial (2 * T r) 1)) * monomial (s.natAbs ^ 2) 1 -
      C 4 * (monomial (2 * T r) 1 * D (monomial (s.natAbs ^ 2) 1)) =
    (monomial (2 * T r + s.natAbs ^ 2) ((2 * r + 1) ^ 2 - 4 * s ^ 2) : ℤ⟦X⟧) := by
  simp only [D_monomial, ← monomial_zero_eq_C_apply, add_mul, monomial_mul_monomial, zero_add,
    mul_one, one_mul]
  rw [← map_add, ← map_sub]
  congr 1
  push_cast
  rw [sq_abs]
  linear_combination 4 * two_mul_T r

theorem neg_X_pow_succ_mul (k : ℕ) : (-X : ℤ⟦X⟧) ^ (k + 1) * (-X) ^ k = -X ^ (2 * k + 1) := by
  rw [← pow_add, show k + 1 + k = 2 * k + 1 by ring, pow_succ, pow_mul, neg_sq]
  ring

/-! ## Divisor sums -/

/-- `Σ_{d ∣ n, 4 ∤ d} d`. -/
def sigma4 (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ 4 ∣ d, d

theorem sign_eq (d e : ℕ) :
    (-1 : ℤ) ^ (d * e) * ((-1) ^ d * (-(-1) ^ e)) = if 2 ∣ d ∧ 2 ∣ e then -1 else 1 := by
  rcases Nat.even_or_odd d with hd | hd <;> rcases Nat.even_or_odd e with he | he
  · rw [(hd.mul_right e).neg_one_pow, hd.neg_one_pow, he.neg_one_pow,
      ite_eq_left ⟨hd.two_dvd, he.two_dvd⟩]
    ring
  · rw [(hd.mul_right e).neg_one_pow, hd.neg_one_pow, he.neg_one_pow,
      ite_eq_right fun h => Nat.not_even_iff_odd.mpr he (even_iff_two_dvd.mpr h.2)]
    ring
  · rw [(he.mul_left d).neg_one_pow, hd.neg_one_pow, he.neg_one_pow,
      ite_eq_right fun h => Nat.not_even_iff_odd.mpr hd (even_iff_two_dvd.mpr h.1)]
    ring
  · rw [(hd.mul he).neg_one_pow, hd.neg_one_pow, he.neg_one_pow,
      ite_eq_right fun h => Nat.not_even_iff_odd.mpr hd (even_iff_two_dvd.mpr h.1)]
    ring

theorem sum_four_dvd (n : ℕ) :
    ∑ d ∈ n.divisors with 4 ∣ d, d = ∑ d ∈ n.divisors with (2 ∣ d ∧ 2 ∣ n / d), 2 * d := by
  symm
  apply Finset.sum_nbij' (fun d => 2 * d) (fun d => d / 2)
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨hdn, hn⟩, ⟨a, rfl⟩, ⟨b, hb⟩⟩ := hd
    have : n = 2 * a * (2 * b) := by rw [← hb, Nat.mul_div_cancel' hdn]
    exact ⟨⟨⟨b, by rw [this]; ring⟩, hn⟩, ⟨a, by ring⟩⟩
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨⟨m, hm⟩, hn⟩, ⟨c, rfl⟩⟩ := hd
    rw [show 4 * c / 2 = 2 * c by omega]
    refine ⟨⟨⟨2 * m, by rw [hm]; ring⟩, hn⟩, ⟨c, rfl⟩, ⟨m, ?_⟩⟩
    rw [hm, show 4 * c * m = 2 * c * (2 * m) by ring, Nat.mul_div_cancel_left _ (by
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp at hm; exact absurd hm hn
      · omega)]
  · intro d _
    simp
  · intro d hd
    obtain ⟨c, rfl⟩ := (Finset.mem_filter.mp hd).2
    omega
  · intro d _
    rfl

theorem sum_sign_eq_sigma4 {n : ℕ} :
    ∑ d ∈ n.divisors, (-1 : ℤ) ^ n * ((-1) ^ d * (-(-1) ^ (n / d) * d)) = sigma4 n := by
  have h1 : ∀ d ∈ n.divisors, (-1 : ℤ) ^ n * ((-1) ^ d * (-(-1) ^ (n / d) * d)) =
      if 2 ∣ d ∧ 2 ∣ n / d then -(d : ℤ) else d := by
    intro d hd
    have := sign_eq d (n / d)
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] at this
    split_ifs at this ⊢ <;> linear_combination (d : ℤ) * this
  rw [Finset.sum_congr rfl h1, Finset.sum_ite, sigma4, Nat.cast_sum, Finset.sum_neg_distrib]
  have h2 := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 4 ∣ d) (fun d => (d : ℤ))
  have h3 := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 2 ∣ d ∧ 2 ∣ n / d)
    (fun d => (d : ℤ))
  have h4 := congrArg (Nat.cast : ℕ → ℤ) (sum_four_dvd n)
  push_cast at h4
  rw [← Finset.mul_sum] at h4
  linear_combination h3 - h2 + h4

theorem sum_regroup (μ : ℕ → ℤ) (K : ℕ) :
    ∑ k ∈ Finset.range K, (μ (2 * k + 2) - μ (2 * k + 1)) =
      ∑ d ∈ Finset.range (2 * K), (-1) ^ (d + 1) * μ (d + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, (show Odd (2 * K + 1) from ⟨K, rfl⟩).neg_one_pow,
      (show Even (2 * K + 1 + 1) from ⟨K + 1, by ring⟩).neg_one_pow,
      show 2 * K + 1 + 1 = 2 * K + 2 by ring]
    ring

theorem sum_range_eq_sum_divisors {n : ℕ} (hn : n ≠ 0) (g : ℕ → ℤ) (hg : ∀ e, ¬ e ∣ n → g e = 0) :
    ∑ d ∈ Finset.range (2 * n), g (d + 1) = ∑ d ∈ n.divisors, g d := by
  have h1 : ∑ d ∈ Finset.range (2 * n), g (d + 1) = ∑ e ∈ Finset.range (2 * n + 1), g e := by
    rw [Finset.sum_range_succ', hg 0 (by simpa using hn), add_zero]
  rw [h1]
  symm
  apply Finset.sum_subset
  · intro e he
    rw [Finset.mem_range]
    have := Nat.divisor_le he
    omega
  · intro e _ he
    exact hg e fun h => he (Nat.mem_divisors.mpr ⟨h, hn⟩)

theorem coeff_L {L : ℤ⟦X⟧} (hL : HasSum (fun k : ℕ => lam (2 * k + 2) - lam (2 * k + 1)) L)
    (n : ℕ) : coeff n L = ∑ d ∈ n.divisors, (-1 : ℤ) ^ d * (-(-1) ^ (n / d) * (d : ℤ)) := by
  rw [coeff_of_hasSum hL n (Finset.range n) fun k hk => X_pow_dvd_iff.mp
    (dvd_sub ((pow_dvd_pow X (by omega)).trans (X_pow_dvd_lam _)) (X_pow_dvd_lam _)) n
    (by rw [Finset.mem_range] at hk; omega)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  simp only [map_sub]
  rw [sum_regroup (fun d => coeff n (lam d)) n,
    sum_range_eq_sum_divisors hn.ne' (fun d => (-1) ^ d * coeff n (lam d)) fun e he => by
      rw [lam, coeff_mk, ite_eq_right fun h => he h.1, mul_zero]]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [lam, coeff_mk, ite_eq_left ⟨Nat.dvd_of_mem_divisors hd, hn⟩]

/-! ## The fourth power of the theta series -/

theorem summable_theta : Summable fun j : ℤ => (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2) :=
  summable_of_dvd T (fun j => pow_dvd_pow X (T_le_sq j)) finite_T

/-- The theta series `θ = ∑_{j ∈ ℤ} X^(j²)`. -/
noncomputable def theta : ℤ⟦X⟧ := ∑' j : ℤ, X ^ (j.natAbs ^ 2)

theorem hasSum_theta : HasSum (fun j : ℤ => (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2)) theta :=
  summable_theta.hasSum

/-- **Jacobi's four-square identity** for power series: `θ⁴ = 1 + 8 ∑ σ₄(n) Xⁿ`. -/
theorem theta_pow_four : theta ^ 4 = 1 + 8 * mk fun n => (sigma4 n : ℤ) := by
  -- the five infinite products
  obtain ⟨E, hE⟩ : Multipliable fun k : ℕ => (1 : ℤ⟦X⟧) - X ^ (2 * k + 2) :=
    multipliable_of_dvd fun k => X_pow_dvd_one_sub_pow_sub_one dvd_rfl (by omega)
  obtain ⟨O, hO⟩ : Multipliable fun k : ℕ => (1 : ℤ⟦X⟧) - X ^ (2 * k + 1) :=
    multipliable_of_dvd fun k => X_pow_dvd_one_sub_pow_sub_one dvd_rfl (by omega)
  obtain ⟨Qo, hQo⟩ : Multipliable fun k : ℕ => (1 : ℤ⟦X⟧) + X ^ (2 * k + 1) :=
    multipliable_of_dvd fun k => by rw [add_sub_cancel_left]; exact pow_dvd_pow X (by omega)
  obtain ⟨Qe, hQe⟩ : Multipliable fun k : ℕ => (1 : ℤ⟦X⟧) + X ^ (2 * k + 2) :=
    multipliable_of_dvd fun k => by rw [add_sub_cancel_left]; exact pow_dvd_pow X (by omega)
  obtain ⟨C3, hC3⟩ : Multipliable fun k : ℕ => (1 : ℤ⟦X⟧) - X ^ (k + 1) :=
    multipliable_of_dvd fun k => X_pow_dvd_one_sub_pow_sub_one dvd_rfl (by omega)
  have hE0 : E ≠ 0 := fun h => by
    have := constantCoeff_of_hasProd hE fun k => by simp
    rw [h, map_zero] at this
    exact zero_ne_one this
  -- Euler: split the products of `1 ∓ X^(k+1)` into odd and even parts
  have hC : C3 = O * E :=
    hC3.unique (HasProd.even_mul_odd (f := fun k => (1 : ℤ⟦X⟧) - X ^ (k + 1)) hO hE)
  have hEu : Qo * Qe * O = 1 := by
    have h1 : HasProd (fun k : ℕ => (1 : ℤ⟦X⟧) - X ^ (2 * k + 2)) (Qo * Qe * C3) := by
      convert (HasProd.even_mul_odd (f := fun k => (1 : ℤ⟦X⟧) + X ^ (k + 1)) hQo hQe).mul hC3
        using 1
      funext k
      ring
    have h2 := h1.unique hE
    rw [hC] at h2
    have h3 : (Qo * Qe * O - 1) * E = 0 := by linear_combination h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hE0)
  -- the triple product at `a = b = X`, at `a = b = -X` and at `a = X², b = 1`
  have hθ : theta = E * (Qo * Qo) := by
    have h := jtp (a := X) (b := X) dvd_rfl (S := theta) (by
      convert hasSum_theta using 1
      funext j
      rw [jt, ← pow_add, T_add_T_sub_one])
    refine h.unique ?_
    convert hE.mul (hQo.mul hQo) using 1
    funext k
    ring
  have hG : rescale (-1) theta = E * (O * O) := by
    have h := jtp (a := -X) (b := -X) (dvd_neg.mpr dvd_rfl) (S := rescale (-1) theta) (by
      convert hasSum_rescale (-1) hasSum_theta using 1
      funext j
      rw [jt, ← pow_add, T_add_T_sub_one, map_pow, rescale_neg_one_X])
    refine h.unique ?_
    convert hE.mul (hO.mul hO) using 1
    funext k
    rw [neg_X_pow_succ_mul, mul_comm ((-X) ^ k), neg_X_pow_succ_mul]
    ring
  obtain ⟨B, hB'⟩ : Summable fun j : ℤ => (X : ℤ⟦X⟧) ^ (2 * T j) :=
    summable_of_dvd T (fun j => pow_dvd_pow X (by omega)) finite_T
  have hB : B = E * (Qe * (2 * Qe)) := by
    have h := jtp (a := X ^ 2) (b := 1) (dvd_pow_self X two_ne_zero) (S := B) (by
      convert hB' using 1
      funext j
      rw [jt, one_pow, mul_one, ← pow_mul])
    have h2 : HasProd (fun k : ℕ => (1 : ℤ⟦X⟧) + X ^ (2 * k)) (2 * Qe) := by
      have := HasProd.zero_mul (f := fun k : ℕ => (1 : ℤ⟦X⟧) + X ^ (2 * k)) hQe
      convert this using 1
      norm_num
    refine h.unique ?_
    convert hE.mul (hQe.mul h2) using 1
    funext k
    ring
  -- Jacobi's cube identity gives `2 C3³ = ∑ (2j + 1) (-1)^j X^T(j)`
  obtain ⟨S3, hS3⟩ : Summable cubeTerm :=
    summable_of_dvd T (fun j => X_pow_dvd_monomial le_rfl _) finite_T
  have hcube := jacobi_cube hC3 hS3
  have hz : HasSum (fun j : ℤ => (monomial (T j) (j.negOnePow : ℤ) : ℤ⟦X⟧)) 0 := by
    obtain ⟨Z, hZ⟩ : Summable fun j : ℤ => (monomial (T j) (j.negOnePow : ℤ) : ℤ⟦X⟧) :=
      summable_of_dvd T (fun j => X_pow_dvd_monomial le_rfl _) finite_T
    have h1 : HasSum (fun j : ℤ => (monomial (T j) (j.negOnePow : ℤ) : ℤ⟦X⟧)) (-Z) := by
      convert ((Equiv.subLeft (-1 : ℤ)).hasSum_iff.mpr hZ).neg using 1
      funext j
      simp only [Function.comp_apply, Equiv.subLeft_apply, T_neg]
      rw [Int.negOnePow_sub, Int.negOnePow_neg, Int.negOnePow_one]
      simp only [neg_mul, one_mul, Units.val_neg, map_neg, neg_neg]
    have h2 := hZ.unique h1
    have h3 : (2 : ℤ⟦X⟧) * Z = 0 := by linear_combination h2
    rwa [(mul_eq_zero.mp h3).resolve_left (by rw [← map_ofNat C 2]; exact C_ne_zero two_ne_zero)]
      at hZ
  have hV : HasSum (fun j : ℤ => (monomial (T j) ((2 * j + 1) * (j.negOnePow : ℤ)) : ℤ⟦X⟧))
      (2 * C3 ^ 3) := by
    rw [hcube]
    convert (hS3.mul_left 2).add hz using 1
    · funext j
      rw [cubeTerm, monomial_eq, monomial_eq, monomial_eq]
      simp only [map_mul, map_add, map_ofNat, map_one]
      ring
    · ring
  -- the double sum: `V² = 2 W` with `W = (B + 4 D B) θ - 4 B D θ`
  have hVV := hasSum_mul_of_dvd T T hV hV (fun j => X_pow_dvd_monomial le_rfl _)
    (fun j => X_pow_dvd_monomial le_rfl _) finite_T finite_T
  have hα : HasSum (fun j : ℤ => (monomial (j.natAbs ^ 2) 1 : ℤ⟦X⟧)) theta := by
    convert hasSum_theta using 1
    funext j
    rw [X_pow_eq]
  have hβ : HasSum (fun j : ℤ => (monomial (2 * T j) 1 : ℤ⟦X⟧)) B := by
    convert hB' using 1
    funext j
    rw [X_pow_eq]
  have hw1 := hasSum_mul_of_dvd T T (hβ.add ((hasSum_D hβ).mul_left (C 4))) hα
    (fun j => dvd_add (X_pow_dvd_monomial (by omega) _)
      (dvd_mul_of_dvd_right (by rw [D_monomial]; exact X_pow_dvd_monomial (by omega) _) _))
    (fun j => X_pow_dvd_monomial (T_le_sq j) _) finite_T finite_T
  have hw2 := hasSum_mul_of_dvd T T hβ (hasSum_D hα) (fun j => X_pow_dvd_monomial (by omega) _)
    (fun j => by rw [D_monomial]; exact X_pow_dvd_monomial (T_le_sq j) _) finite_T finite_T
  have hW : HasSum (fun p : ℤ × ℤ =>
      (monomial (2 * T p.1 + p.2.natAbs ^ 2) ((2 * p.1 + 1) ^ 2 - 4 * p.2 ^ 2) : ℤ⟦X⟧))
      ((B + C 4 * D B) * theta - C 4 * (B * D theta)) := by
    convert hw1.sub (hw2.mul_left (C 4)) using 1
    funext p
    rw [w_eq]
  have hVW := (parityEquiv.hasSum_iff.mpr hVV).unique (HasSum.sum
    (by convert hW using 1; funext p; exact v_mul_v_inl p.1 p.2)
    (by convert hW using 1; funext p; exact v_mul_v_inr p.1 p.2))
  -- the logarithmic derivative of `∏ (1 + X^(2k+2)) / ∏ (1 + X^(2k+1))`
  obtain ⟨L, hL⟩ : Summable fun k : ℕ => lam (2 * k + 2) - lam (2 * k + 1) :=
    summable_of_dvd (fun k => k)
      (fun k => dvd_sub ((pow_dvd_pow X (by omega)).trans (X_pow_dvd_lam _))
        ((pow_dvd_pow X (by omega)).trans (X_pow_dvd_lam _))) fun n => Set.finite_Iic n
  have hLD := D_ratio hQo hQe (fun k => D_one_add_X_pow (2 * k + 1))
    (fun k => D_one_add_X_pow (2 * k + 2)) hL
  have hDθ : D theta = D E * (Qo * Qo) + E * (D Qo * Qo + Qo * D Qo) := by rw [hθ, D_mul, D_mul]
  have hDB : D B = D E * (Qe * (2 * Qe)) + E * (D Qe * (2 * Qe) + Qe * (2 * D Qe)) := by
    rw [hB, D_mul, D_mul, D_mul, ← map_ofNat C 2, D_C]
    ring
  -- assemble: `(rescale (-1) θ)⁴ = 1 + 8 L`
  have hmain : rescale (-1) theta ^ 4 = 1 + 8 * L := by
    rw [hDθ, hDB, hθ, hB, hC, map_ofNat C 4] at hVW
    have key : 4 * E ^ 2 * (rescale (-1) theta ^ 4 - (1 + 8 * L)) = 0 := by
      rw [hG]
      linear_combination O ^ 2 * hVW + (4 * E ^ 2 + 32 * E ^ 2 * L) * (Qo * Qe * O + 1) * hEu +
        32 * E ^ 2 * O ^ 2 * Qo * Qe * hLD
    have h4 : (4 : ℤ⟦X⟧) * E ^ 2 ≠ 0 :=
      mul_ne_zero (by rw [← map_ofNat C 4]; exact C_ne_zero four_ne_zero) (pow_ne_zero 2 hE0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left h4)
  -- back to `θ` by `X ↦ -X`, and read off the coefficients
  have hθθ : theta = rescale (-1) (rescale (-1) theta) := by
    rw [rescale_rescale, show (-1 : ℤ) * -1 = 1 by norm_num, rescale_one, RingHom.id_apply]
  rw [hθθ, ← map_pow, hmain]
  ext n
  rw [coeff_rescale, map_add, map_add, show (8 : ℤ⟦X⟧) = C 8 by simp, coeff_C_mul, coeff_C_mul,
    coeff_mk, coeff_L hL]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sigma4]
  rw [coeff_one, ite_eq_right hn.ne', ← sum_sign_eq_sigma4]
  simp only [zero_add, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-! ## Counting the lattice points -/

/-- `r₄(n)`: the integer points of `ℤ⁴` on the sphere `x₁² + x₂² + x₃² + x₄² = n`. -/
def r4 (n : ℕ) : ℕ :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i ^ 2 = (n : ℤ)) |>.card

/-- The `n`-th coefficient of `θ⁴` counts the points of `ℤ⁴` on the sphere of radius `√n`. -/
theorem coeff_theta_pow_four (n : ℕ) : coeff n (theta ^ 4) = (r4 n : ℤ) := by
  have h1 : X ^ (n + 1) ∣
      theta - ∑ j ∈ Finset.Icc (-(n : ℤ)) n, (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, sub_eq_zero, coeff_of_hasSum hasSum_theta m (Finset.Icc (-(n : ℤ)) n), map_sum]
    intro j hj
    rw [coeff_X_pow, ite_eq_right]
    intro h
    apply hj
    have := Nat.le_self_pow two_ne_zero j.natAbs
    rw [Finset.mem_Icc]
    omega
  rw [coeff_eq_of_dvd (h1.trans (sub_dvd_pow_sub_pow _ _ 4)) (Nat.lt_succ_self n),
    show (∑ j ∈ Finset.Icc (-(n : ℤ)) n, (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2)) ^ 4 =
      ∏ _i : Fin 4, ∑ j ∈ Finset.Icc (-(n : ℤ)) n, (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2) by simp,
    Finset.prod_univ_sum]
  simp only [Finset.prod_pow_eq_pow_sum, map_sum, coeff_X_pow]
  rw [Finset.sum_boole, r4]
  congr 2
  refine Finset.filter_congr fun v _ => ?_
  rw [eq_comm, ← Nat.cast_inj (R := ℤ)]
  push_cast
  simp only [sq_abs]

/-- `r₄(0) = 1`: only the origin. -/
theorem r4_zero : r4 0 = 1 := by
  have h := coeff_theta_pow_four 0
  rw [theta_pow_four] at h
  simp [sigma4] at h
  exact_mod_cast h.symm

/-- **Jacobi's four-square theorem** (C. G. J. Jacobi, *Fundamenta nova*, 1829). -/
theorem r4_eq {n : ℕ} (hn : n ≠ 0) : r4 n = 8 * sigma4 n := by
  have h := coeff_theta_pow_four n
  rw [theta_pow_four, map_add, coeff_one, ite_eq_right hn, zero_add,
    show (8 : ℤ⟦X⟧) = C 8 by simp, coeff_C_mul, coeff_mk] at h
  exact_mod_cast h.symm

end JacobiFourSquares

#print axioms JacobiFourSquares.jtp
#print axioms JacobiFourSquares.jacobi_cube
#print axioms JacobiFourSquares.theta_pow_four
#print axioms JacobiFourSquares.r4_zero
#print axioms JacobiFourSquares.r4_eq
