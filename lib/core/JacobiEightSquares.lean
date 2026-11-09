import Mathlib
import JacobiFourSquares

/-! # Jacobi's eight-square theorem

For `n ≥ 1` the number `r₈(n)` of points `v ∈ ℤ⁸` with `v₁² + ⋯ + v₈² = n` is
`16 Σ_{d ∣ n} (-1)^(n+d) d³` (`r8_eq`), and `r₈(0) = 1` (`r8_zero`).

The proof is the heat-equation method, carried out formally: the finite triple product
`JacobiFourSquares.finite_jtp` at `z = e^(at)`, expanded in `t`, in the ring `K = ℚ⟦q⟧⟦t⟧`. The four-square
theorem `JacobiFourSquares.theta_pow_four` is an input.

* **Exponential moments** (`tendsto_mom`). For the finite products `Pr α β s a N`, `m!` times the
  `t^m`-coefficient tends, `q`-adically, to `Σ_j (s + ja)^m q^(αT(j)+βT(j-1))`, by
  `JacobiFourSquares.tendsto_jtp` (`Pr_eq`, `tendsto_Pr`).
* **Logarithmic derivatives.** The factor `1 + q^e e^(at)` has logarithmic derivative `a G_e(at)`, where the
  Lambert series `G_e = q^e e^t / (1 + q^e e^t)` is given coefficientwise (`one_add_mul_G`,
  `derivative_factor`); the factor `e^t + e^(-t)` has `τ = tanh t`, whose first coefficients are `0, 1, 0, -1/3`
  (`mul_τ`, `coeff_τ`). The derivative of a product is handled by `derivative_prod`.
* **The recursion** (`recursion`). If `P_N' = P_N L_N` and the exponential moments of `P_N` and `L_N` converge
  to `M` and `ℓ`, then `M (m+1) = Σ_i (m choose i) M i ℓ (m-i)`.
* **Heat equations.** For `θ(q, e^t) = Σ q^(j²) e^(jt)` the moments of order `0, 2, 4` are `θ, Dθ, D²θ` with
  `D = q d/dq` (`mom_theta`), and the recursion at `m = 1, 3` leaves `4μ₁² = Dμ₁ - μ₃` (`theta_heat`) for the
  Lambert series `μ_m` of the divisor sums `Σ_{d ∣ N, N/d odd} (-1)^(d+1) d^m` (`lamb`, `tendsto_sum_gq`). For
  `Σ q^(cT(j)) e^((2j+1)t)` (`derivative_PU`, `tendsto_LU`, `mom_U`) it leaves `4cλ₁² = 2Dλ₁ - cλ₁ - cλ₃`
  (`U_heat`) for the sums over the divisors `d` with `c ∣ N/d`.
* **Assembly** (`theta_pow_eight`). The four-square theorem reads `θ⁴ = 1 + 8 (λ₁⁽²⁾ - μ₁(-q))`
  (`theta_pow_four_lamb`), and `λ₁⁽²⁾ + μ₁(-q) = λ₁⁽¹⁾(-q)` (`lamb_add_rescale`); the heat equations make the
  square of `λ₁⁽²⁾ - μ₁(-q)` linear, and `θ⁸ = 1 - 32 λ₃⁽²⁾ - 32 μ₃(-q) + 16 λ₃⁽¹⁾(-q)`. Its coefficients are
  the divisor sums (`coeff_theta_pow_eight`), and the coefficients of `θ⁸` count the lattice points
  (`coeff_theta_pow_eight_int`).
-/

open PowerSeries PowerSeries.WithPiTopology Filter Topology
open scoped Nat

namespace JacobiEightSquares

open JacobiFourSquares (T jt gauss)

/-- Power series in `q` over `ℚ`. -/
abbrev Q := PowerSeries ℚ

/-- Power series in `t` over `Q`. -/
abbrev K := PowerSeries Q

instance : CharZero Q := charZero_of_injective_algebraMap (algebraMap ℚ Q).injective

/-- `e^(at)`. -/
noncomputable def E (a : Q) : K := rescale a (exp Q)

theorem E_mul_E (a b : Q) : E a * E b = E (a + b) := exp_mul_exp_eq_exp_add a b

theorem E_zero : E 0 = 1 := by
  rw [E, rescale_zero, RingHom.comp_apply, constantCoeff_exp, map_one]

theorem E_pow (a : Q) (n : ℕ) : E a ^ n = E (n * a) := by
  induction n with
  | zero => simp [E_zero]
  | succ n ih =>
    rw [pow_succ, ih, E_mul_E]
    push_cast
    ring_nf

theorem rescale_E (a b : Q) : rescale a (E b) = E (b * a) := rescale_rescale _ _ _

theorem rescale_C (a r : Q) : rescale a (C r : K) = C r := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

theorem coeff_E (a : Q) (m : ℕ) : coeff m (E a) = a ^ m * C ((m ! : ℚ)⁻¹) := by
  rw [E, coeff_rescale, coeff_exp, one_div]
  rfl

theorem fact_mul_coeff_E (a : Q) (m : ℕ) : (m ! : Q) * coeff m (E a) = a ^ m := by
  rw [coeff_E, mul_left_comm, ← map_natCast (C (R := ℚ)), ← map_mul,
    mul_inv_cancel₀ (by positivity), map_one, mul_one]

theorem derivative_E (a : Q) : d⁄dX (E a) = C a * E a := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_derivative, coeff_C_mul, coeff_E, coeff_E, pow_succ, Nat.factorial_succ,
    show (n + 1 : Q) = C ((n + 1 : ℕ) : ℚ) by simp]
  rw [show C (((n + 1) * n ! : ℕ) : ℚ)⁻¹ = C ((n + 1 : ℕ) : ℚ)⁻¹ * C ((n ! : ℚ)⁻¹) by
    rw [← map_mul]; push_cast; rw [mul_inv]]
  have : C ((n + 1 : ℕ) : ℚ)⁻¹ * C ((n + 1 : ℕ) : ℚ) = (1 : Q) := by
    rw [← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  linear_combination (a ^ n * a * C ((n ! : ℚ)⁻¹)) * this

/-! ## Lambert series -/

theorem binom_exp (b : ℚ) (j : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, (p.1 ! : ℚ)⁻¹ * ((p.2 ! : ℚ)⁻¹ * b ^ p.2) =
      (j ! : ℚ)⁻¹ * (1 + b) ^ j := by
  have h := congrArg (coeff j) (exp_mul_exp_eq_exp_add (A := ℚ) 1 b)
  simp only [coeff_mul, coeff_rescale, coeff_exp, one_pow, one_mul, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  rw [Finset.sum_congr rfl fun p _ => show (p.1 ! : ℚ)⁻¹ * ((p.2 ! : ℚ)⁻¹ * b ^ p.2) =
    1 / p.1 ! * (b ^ p.2 * (1 / p.2 !)) by ring, h]
  ring

/-- The `N`-th coefficient of `∑_{n ≥ 1} (-1)^(n+1) n^j q^(ne)`. -/
def gc (e j N : ℕ) : ℚ := if e ∣ N ∧ N ≠ 0 then (-1) ^ (N / e + 1) * ((N / e : ℕ) : ℚ) ^ j else 0

theorem gc_mul {e : ℕ} (he : 0 < e) (j : ℕ) {n : ℕ} (hn : 0 < n) :
    gc e j (e * n) = (-1) ^ (n + 1) * (n : ℚ) ^ j := by
  rw [gc, ite_eq_left ⟨dvd_mul_right e n, by positivity⟩, Nat.mul_div_cancel_left _ he]

theorem gc_of_not_dvd {e N : ℕ} (h : ¬ e ∣ N) (j : ℕ) : gc e j N = 0 :=
  ite_eq_right fun h' => h h'.1

theorem gc_zero (e j : ℕ) : gc e j 0 = 0 := ite_eq_right fun h => h.2 rfl

/-- `∑_{n ≥ 1} (-1)^(n+1) n^j q^(ne)`. -/
noncomputable def gq (e j : ℕ) : Q := mk (gc e j)

/-- `q^e e^t / (1 + q^e e^t)`, whose `t^j` coefficient is `gq e j / j!`. -/
noncomputable def G (e : ℕ) : K := mk fun j => C ((j ! : ℚ)⁻¹) * gq e j

/-- `G_e (1 + q^e e^t) = q^e e^t`, coefficient by coefficient. -/
theorem one_add_mul_G {e : ℕ} (he : 0 < e) : (1 + C (X ^ e) * E 1) * G e = C (X ^ e) * E 1 := by
  refine PowerSeries.ext fun j => ?_
  rw [add_mul, one_mul, mul_assoc, map_add, coeff_C_mul, coeff_mul, coeff_C_mul, coeff_E]
  simp only [G, coeff_mk, coeff_E, one_pow, one_mul]
  refine PowerSeries.ext fun N => ?_
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul', map_sum, gq, coeff_mk, coeff_C]
  by_cases hd : e ∣ N
  · obtain ⟨n, rfl⟩ := hd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [gc_zero, show ¬ e ≤ 0 by omega]
    have hle := Nat.le_mul_of_pos_right e hn
    rw [gc_mul he j hn, ite_eq_left hle, ite_eq_left hle, ← Nat.mul_sub_one]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      simp [gc_zero]
    have hn1 : 0 < n - 1 := by omega
    have hb : (1 : ℚ) + ((n - 1 : ℕ) : ℚ) = n := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    have hs : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j,
        (p.1 ! : ℚ)⁻¹ * ((p.2 ! : ℚ)⁻¹ * gc e p.2 (e * (n - 1))) =
        (-1) ^ n * ((j ! : ℚ)⁻¹ * (n : ℚ) ^ j) := by
      rw [← hb, ← binom_exp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [gc_mul he _ hn1, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      ring
    rw [hs, ite_eq_right (Nat.mul_ne_zero he.ne' hn1.ne')]
    ring
  · rw [gc_of_not_dvd hd]
    split_ifs with h1 h2
    · exact absurd (by rw [show N = e by omega]) hd
    · rw [Finset.sum_eq_zero fun p _ => by
        rw [gc_of_not_dvd fun h => hd (by rw [show N = N - e + e by omega]; exact dvd_add h dvd_rfl)]
        ring]
      ring
    · ring

theorem rescale_factor (a : Q) (e : ℕ) : rescale a (1 + C (X ^ e) * E 1) = 1 + C (X ^ e) * E a := by
  rw [map_add, map_one, map_mul, rescale_C, rescale_E, one_mul]

/-- The product rule for `d/dt` on `K`, coefficientwise. -/
theorem derivative_mul (f g : K) : d⁄dX (f * g) = d⁄dX f * g + f * d⁄dX g := by
  refine PowerSeries.ext fun n => ?_
  have h1 := Finset.Nat.sum_antidiagonal_succ (n := n)
    (f := fun p => (p.1 : Q) * (coeff p.1 f * coeff p.2 g))
  have h2 := Finset.Nat.sum_antidiagonal_succ' (n := n)
    (f := fun p => (p.2 : Q) * (coeff p.1 f * coeff p.2 g))
  simp only [Nat.cast_zero, zero_mul, zero_add] at h1 h2
  have h3 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), coeff p.1 f * coeff p.2 g * ((n : Q) + 1) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), (p.1 : Q) * (coeff p.1 f * coeff p.2 g) +
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), (p.2 : Q) * (coeff p.1 f * coeff p.2 g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have h' : (n : Q) + 1 = p.1 + p.2 := by rw [← Nat.cast_add, h, Nat.cast_add_one]
    rw [h']
    ring
  rw [coeff_derivative, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.sum_mul, h3, h1, h2]
  simp only [coeff_derivative]
  congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_ <;> push_cast <;> ring

/-- The logarithmic derivative of `1 + q^e e^(at)` is `a G_e(at)`. -/
theorem derivative_factor (a : Q) {e : ℕ} (he : 0 < e) :
    d⁄dX (1 + C (X ^ e) * E a) = (1 + C (X ^ e) * E a) * (C a * rescale a (G e)) := by
  have h := congrArg (rescale a) (one_add_mul_G he)
  rw [map_mul, rescale_factor, map_mul, rescale_C, rescale_E, one_mul] at h
  rw [map_add, derivative_one, zero_add, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_E, mul_left_comm (1 + C (X ^ e) * E a), h]
  ring

theorem fact_mul_inv (m : ℕ) : (m ! : Q) * C ((m ! : ℚ)⁻¹) = 1 := by
  rw [← map_natCast (C (R := ℚ)), ← map_mul, mul_inv_cancel₀ (by positivity), map_one]

theorem fact_mul_coeff_G (a : Q) (e m : ℕ) :
    (m ! : Q) * coeff m (C a * rescale a (G e)) = a ^ (m + 1) * gq e m := by
  rw [coeff_C_mul, coeff_rescale, G, coeff_mk]
  linear_combination (a ^ (m + 1) * gq e m) * fact_mul_inv m

/-- Exponential generating functions multiply by binomial convolution. -/
theorem fact_mul_coeff_mul (f g : K) (m : ℕ) :
    (m ! : Q) * coeff m (f * g) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      (m.choose p.1 : Q) * (((p.1 ! : Q) * coeff p.1 f) * ((p.2 ! : Q) * coeff p.2 g)) := by
  rw [coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  have h := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
  rw [← Nat.choose_symm_add] at h
  rw [← h]
  push_cast
  ring

theorem derivative_mul_of {f g a b : K} (hf : d⁄dX f = f * a) (hg : d⁄dX g = g * b) :
    d⁄dX (f * g) = f * g * (a + b) := by
  rw [derivative_mul, hf, hg]
  ring

/-- The logarithmic derivative of a finite product is the sum of the factors' ones. -/
theorem derivative_prod {f g : ℕ → K} (h : ∀ k, d⁄dX (f k) = f k * g k) (N : ℕ) :
    d⁄dX (∏ k ∈ Finset.range N, f k) = (∏ k ∈ Finset.range N, f k) * ∑ k ∈ Finset.range N, g k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, derivative_mul_of ih (h N)]

/-- The heat-equation recursion: if `P_N' = P_N L_N` and the exponential moments of `P_N` and
`L_N` converge to `M` and `ℓ`, then `M (m+1) = Σ_i (m choose i) M i ℓ (m-i)`. -/
theorem recursion {P L : ℕ → K} {M l : ℕ → Q} (hD : ∀ N, d⁄dX (P N) = P N * L N)
    (hM : ∀ i, Tendsto (fun N => (i ! : Q) * coeff i (P N)) atTop (𝓝 (M i)))
    (hl : ∀ j, Tendsto (fun N => (j ! : Q) * coeff j (L N)) atTop (𝓝 (l j))) (m : ℕ) :
    M (m + 1) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (m.choose p.1 : Q) * (M p.1 * l p.2) := by
  have key : ∀ N, ((m + 1) ! : Q) * coeff (m + 1) (P N) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      (m.choose p.1 : Q) * (((p.1 ! : Q) * coeff p.1 (P N)) * ((p.2 ! : Q) * coeff p.2 (L N))) := by
    intro N
    rw [← fact_mul_coeff_mul, ← hD, coeff_derivative, Nat.factorial_succ]
    push_cast
    ring
  refine tendsto_nhds_unique (hM (m + 1)) ?_
  simp_rw [key]
  exact tendsto_finsetSum _ fun p _ => ((hM p.1).mul (hl p.2)).const_mul _

/-! ## Lambert series -/

/-- The Lambert series `Σ_N (Σ_{d ∣ N, P(N/d)} (-1)^(d+1) d^m) q^N`. -/
noncomputable def lamb (P : ℕ → Prop) [DecidablePred P] (m : ℕ) : Q :=
  mk fun N => ∑ d ∈ N.divisors with P (N / d), (-1) ^ (d + 1) * (d : ℚ) ^ m

/-- The partial sums of `Σ_k gq (e k) m` over an injective enumeration `e` of the cofactors in `P` converge
to the Lambert series `lamb P m`. -/
theorem tendsto_sum_gq {e : ℕ → ℕ} (hinj : e.Injective) (hlt : ∀ k, k < e k)
    {P : ℕ → Prop} [DecidablePred P] (hP : ∀ n, P n ↔ ∃ k, e k = n) (m : ℕ) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, gq (e k) m) atTop (𝓝 (lamb P m)) := by
  rw [tendsto_iff_coeff_tendsto]
  intro M
  refine tendsto_atTop_of_eventually_const (i₀ := M + 1) fun N hN => ?_
  simp only [map_sum, lamb, gq, coeff_mk]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [gc_zero]
  rw [← Finset.sum_filter_of_ne (p := fun k => e k ∣ M) fun k _ h =>
    by_contra fun h' => h (gc_of_not_dvd h' m)]
  refine Finset.sum_nbij (fun k => M / e k) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hk', hM.ne'⟩, ?_⟩
    rw [Nat.div_div_self hk' hM.ne']
    exact (hP _).mpr ⟨k, rfl⟩
  · intro k₁ hk₁ k₂ hk₂ h
    have h₁ := (Finset.mem_filter.mp hk₁).2
    have h₂ := (Finset.mem_filter.mp hk₂).2
    apply hinj
    simp only at h
    rw [← Nat.div_div_self h₁ hM.ne', h, Nat.div_div_self h₂ hM.ne']
  · intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
    have hdM := Nat.dvd_of_mem_divisors hd1
    obtain ⟨k, hk⟩ := (hP _).mp hd2
    have hle : e k ≤ M := hk ▸ Nat.div_le_self M d
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hk ▸ Nat.div_dvd_of_dvd hdM⟩, ?_⟩
    · have := hlt k
      omega
    · simp only
      rw [hk, Nat.div_div_self hdM hM.ne']
  · intro k hk
    rw [gc, ite_eq_left ⟨(Finset.mem_filter.mp hk).2, hM.ne'⟩]

/-! ## The Euler operator `q d/dq` -/

/-- The Euler operator `q d/dq` on `Q`: it multiplies the `n`-th coefficient by `n`. -/
noncomputable def D (f : Q) : Q := mk fun n => n * coeff n f

theorem coeff_D (f : Q) (n : ℕ) : coeff n (D f) = n * coeff n f := coeff_mk _ _

theorem D_mul (f g : Q) : D (f * g) = D f * g + f * D g := by
  ext n
  simp only [coeff_D, map_add, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  push_cast
  ring

theorem D_add (f g : Q) : D (f + g) = D f + D g := by
  ext n
  simp only [coeff_D, map_add]
  ring

theorem D_rescale (f : Q) : D (rescale (-1) f) = rescale (-1) (D f) := by
  ext n
  simp only [coeff_D, coeff_rescale]
  ring

/-- The coefficientwise map `ℤ⟦X⟧ → ℚ⟦X⟧`. -/
noncomputable def toQ : ℤ⟦X⟧ →+* Q := PowerSeries.map (Int.castRingHom ℚ)

theorem toQ_D (f : ℤ⟦X⟧) : toQ (JacobiFourSquares.D f) = D (toQ f) := by
  ext n
  simp [toQ, coeff_D, JacobiFourSquares.coeff_D]

theorem tendsto_toQ {s : ℕ → ℤ⟦X⟧} {S : ℤ⟦X⟧} (h : Tendsto s atTop (𝓝 S)) :
    Tendsto (fun N => toQ (s N)) atTop (𝓝 (toQ S)) := by
  rw [tendsto_iff_coeff_tendsto] at h ⊢
  intro n
  have := ((continuous_of_discreteTopology (f := (Int.cast : ℤ → ℚ))).tendsto _).comp (h n)
  simpa [toQ, Function.comp_def] using this

/-! ## The triple product at `z = e^(at)` -/

theorem CE_mul (x y a b : Q) : C x * E a * (C y * E b) = C (x * y) * E (a + b) := by
  rw [map_mul, ← E_mul_E]
  ring

theorem CE_pow (x a : Q) (n : ℕ) : (C x * E a) ^ n = C (x ^ n) * E (n * a) := by
  rw [mul_pow, ← map_pow, E_pow]

theorem CE_pow_mul_pow (α β : ℕ) (a : Q) (i j : ℕ) :
    (C (X ^ α) * E a) ^ i * (C (X ^ β) * E (-a)) ^ j =
      C (X ^ (α * i + β * j)) * E ((i - j : Q) * a) := by
  rw [CE_pow, CE_pow, CE_mul, ← pow_mul, ← pow_mul, pow_add]
  congr 2
  ring

theorem T_sub (j : ℤ) : ((T j : ℕ) : Q) - (T (j - 1) : ℕ) = j := by
  have h := JacobiFourSquares.T_succ (j - 1)
  rw [sub_add_cancel] at h
  have h' := congrArg (Int.cast : ℤ → Q) h
  push_cast at h'
  rw [h']
  ring

/-- `e^(st) ∏_{k<N} (1 - q^((α+β)(k+1))) (1 + q^(α(k+1)+βk) e^(at)) (1 + q^(αk+β(k+1)) e^(-at))`. -/
noncomputable def Pr (α β : ℕ) (s a : ℤ) (N : ℕ) : K :=
  C (∏ k ∈ Finset.range N, (1 - X ^ ((α + β) * (k + 1)))) * E s *
    ∏ k ∈ Finset.range N, ((1 + C (X ^ (α * (k + 1) + β * k)) * E a) *
      (1 + C (X ^ (α * k + β * (k + 1))) * E (-a)))

theorem Pr_eq (α β : ℕ) (s a : ℤ) (N : ℕ) :
    Pr α β s a N = C (∏ k ∈ Finset.range N, (1 - X ^ ((α + β) * (k + 1)))) *
      ∑ i ∈ Finset.range (2 * N + 1), C (X ^ (α * T (i - N) + β * T (i - N - 1)) *
        gauss (X ^ (α + β)) (2 * N) i) * E ((s + ((i : ℤ) - N) * a : ℤ) : Q) := by
  have h := JacobiFourSquares.finite_jtp (C (X ^ α) * E (a : Q)) (C (X ^ β) * E (-a)) N
  have hab : C (X ^ α) * E (a : Q) * (C (X ^ β) * E (-a)) = C (X ^ (α + β)) := by
    rw [CE_mul, add_neg_cancel, E_zero, mul_one, pow_add]
  rw [hab] at h
  simp only [CE_pow_mul_pow, jt, T_sub, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
    sub_add_cancel_left, one_mul, neg_mul, ← JacobiFourSquares.map_gauss (C : Q →+* K)] at h
  rw [Pr, mul_assoc, h, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [map_mul, ← E_mul_E]
  ring

theorem T_le {α : ℕ} (hα : 0 < α) (β : ℕ) (j : ℤ) : T j ≤ α * T j + β * T (j - 1) := by
  have := Nat.le_mul_of_pos_left (T j) hα
  omega

/-- The exponential moments of the finite products converge, by `JacobiFourSquares.tendsto_jtp`. -/
theorem tendsto_Pr {α : ℕ} (hα : 0 < α) (β : ℕ) (s a : ℤ) (m : ℕ) {S : ℤ⟦X⟧}
    (hS : HasSum (fun j : ℤ => monomial (α * T j + β * T (j - 1)) ((s + j * a) ^ m)) S) :
    Tendsto (fun N => (m ! : Q) * coeff m (Pr α β s a N)) atTop (𝓝 (toQ S)) := by
  refine Tendsto.congr (fun N => ?_) (tendsto_toQ (JacobiFourSquares.tendsto_jtp
    (dvd_pow_self X (by omega : α + β ≠ 0))
    (fun j => JacobiFourSquares.X_pow_dvd_monomial (T_le hα β j) _) hS))
  conv_lhs => rw [map_mul, map_sum, Finset.mul_sum]
  conv_rhs => rw [Pr_eq, coeff_C_mul, map_sum, Finset.mul_sum, Finset.mul_sum]
  have key : ∀ p y x : Q, (m ! : Q) * (p * (y * coeff m (E x))) = p * (y * x ^ m) := fun p y x => by
    rw [← fact_mul_coeff_E]
    ring
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_C_mul, key, JacobiFourSquares.monomial_eq]
  simp only [toQ, map_mul, map_prod, map_sub, map_one, map_pow, map_X,
    JacobiFourSquares.map_gauss, ← pow_mul]
  push_cast
  simp only [map_add, map_sub, map_mul, map_natCast, eq_intCast, map_intCast]
  ring

/-- The logarithmic derivative of `Pr α β s a N`. -/
noncomputable def LPr (α β : ℕ) (s a : ℤ) (N : ℕ) : K :=
  C (s : Q) + ∑ k ∈ Finset.range N, (C (a : Q) * rescale (a : Q) (G (α * (k + 1) + β * k)) +
    C (-a : Q) * rescale (-a : Q) (G (α * k + β * (k + 1))))

theorem derivative_Pr {α β : ℕ} (hα : 0 < α) (hβ : 0 < β) (s a : ℤ) (N : ℕ) :
    d⁄dX (Pr α β s a N) = Pr α β s a N * LPr α β s a N := by
  have h1 : d⁄dX (C (∏ k ∈ Finset.range N, (1 - X ^ ((α + β) * (k + 1)))) * E s) =
      C (∏ k ∈ Finset.range N, (1 - X ^ ((α + β) * (k + 1)))) * E s * (0 + C (s : Q)) :=
    derivative_mul_of (by rw [derivative_C, mul_zero]) (by rw [derivative_E, mul_comm])
  have h2 := derivative_prod (f := fun k => (1 + C (X ^ (α * (k + 1) + β * k)) * E a) *
    (1 + C (X ^ (α * k + β * (k + 1))) * E (-a))) (fun k => derivative_mul_of
      (derivative_factor _ (by positivity)) (derivative_factor _ (by positivity))) N
  rw [Pr, derivative_mul_of h1 h2, zero_add, LPr]

theorem fact_mul_coeff_LPr (α β : ℕ) (a : ℤ) (N j : ℕ) :
    (j ! : Q) * coeff j (LPr α β 0 a N) = ∑ k ∈ Finset.range N,
      ((a : Q) ^ (j + 1) * gq (α * (k + 1) + β * k) j + (-a : Q) ^ (j + 1) * gq (α * k + β * (k + 1)) j) := by
  rw [LPr, map_add, map_sum, mul_add, Finset.mul_sum, Int.cast_zero, map_zero, map_zero, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_add, mul_add, fact_mul_coeff_G, fact_mul_coeff_G]

/-- The `m`-th exponential moment `Σ_j (s + ja)^m q^(αT(j)+βT(j-1))` of the triple product. -/
noncomputable def mom (α β : ℕ) (s a : ℤ) (m : ℕ) : Q :=
  toQ (∑' j : ℤ, monomial (α * T j + β * T (j - 1)) ((s + j * a) ^ m))

theorem summable_mom {α : ℕ} (hα : 0 < α) (β : ℕ) (s a : ℤ) (m : ℕ) :
    Summable fun j : ℤ => (monomial (α * T j + β * T (j - 1)) ((s + j * a) ^ m) : ℤ⟦X⟧) :=
  JacobiFourSquares.summable_of_dvd T
    (fun j => JacobiFourSquares.X_pow_dvd_monomial (T_le hα β j) _) JacobiFourSquares.finite_T

theorem tendsto_mom {α : ℕ} (hα : 0 < α) (β : ℕ) (s a : ℤ) (m : ℕ) :
    Tendsto (fun N => (m ! : Q) * coeff m (Pr α β s a N)) atTop (𝓝 (mom α β s a m)) :=
  tendsto_Pr hα β s a m (summable_mom hα β s a m).hasSum

/-! ## The theta series -/

/-- The theta series `θ = Σ_{j ∈ ℤ} q^(j²)` over `ℚ`. -/
noncomputable def θ : Q := toQ JacobiFourSquares.theta

theorem hasSum_theta_mom (r : ℕ) :
    HasSum (fun j : ℤ => (monomial (1 * T j + 1 * T (j - 1)) ((0 + j * 1) ^ (2 * r)) : ℤ⟦X⟧))
      (JacobiFourSquares.D^[r] JacobiFourSquares.theta) := by
  induction r with
  | zero =>
    rw [Function.iterate_zero_apply]
    convert JacobiFourSquares.hasSum_theta using 1
    funext j
    rw [one_mul, one_mul, JacobiFourSquares.T_add_T_sub_one, mul_zero, pow_zero, X_pow_eq]
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    convert JacobiFourSquares.hasSum_D ih using 1
    funext j
    rw [JacobiFourSquares.D_monomial, one_mul, one_mul, JacobiFourSquares.T_add_T_sub_one]
    congr 1
    push_cast
    rw [sq_abs]
    ring

/-- The even moments of `θ(q, e^t)` are the iterates `D^r θ`. -/
theorem mom_theta (r : ℕ) : mom 1 1 0 1 (2 * r) = D^[r] θ := by
  rw [mom, (hasSum_theta_mom r).tsum_eq, θ]
  exact Function.Semiconj.iterate_right toQ_D r _

theorem θ_ne_zero : θ ≠ 0 := by
  intro h
  have h0 : coeff 0 (JacobiFourSquares.theta ^ 4) = 1 := by
    rw [JacobiFourSquares.theta_pow_four, map_add, coeff_one, ite_eq_left rfl,
      show (8 : ℤ⟦X⟧) = C 8 by simp, coeff_C_mul, coeff_mk]
    simp [JacobiFourSquares.sigma4]
  have h1 : coeff 0 (θ ^ 4) = 1 := by
    rw [θ, ← map_pow, toQ, coeff_map, h0, map_one]
  rw [h, zero_pow four_ne_zero, map_zero] at h1
  exact zero_ne_one h1

theorem tendsto_LPr_theta (j : ℕ) :
    Tendsto (fun N => (j ! : Q) * coeff j (LPr 1 1 0 1 N)) atTop
      (𝓝 ((1 + (-1) ^ (j + 1)) * lamb (fun n => n % 2 = 1) j)) := by
  have h := (tendsto_sum_gq (e := fun k => 2 * k + 1) (fun a b h => by simp only at h; omega)
    (fun k => by omega) (P := fun n => n % 2 = 1)
    (fun n => ⟨fun h => ⟨n / 2, by omega⟩, fun ⟨k, hk⟩ => by omega⟩) j).const_mul
      (1 + (-1) ^ (j + 1) : Q)
  refine h.congr fun N => ?_
  rw [fact_mul_coeff_LPr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 1 * (k + 1) + 1 * k = 2 * k + 1 by ring, show 1 * k + 1 * (k + 1) = 2 * k + 1 by ring]
  push_cast
  ring

theorem D_C_mul (r : ℚ) (f : Q) : D (C r * f) = C r * D f := by
  ext n
  simp only [coeff_D, coeff_C_mul]
  ring

/-- **The heat equation for `θ`**: `4 μ₁² = D μ₁ - μ₃` for the odd-cofactor Lambert series. -/
theorem theta_heat :
    4 * lamb (fun n => n % 2 = 1) 1 ^ 2 =
      D (lamb (fun n => n % 2 = 1) 1) - lamb (fun n => n % 2 = 1) 3 := by
  have hrec := recursion (fun N => derivative_Pr one_pos one_pos 0 1 N) (tendsto_mom one_pos 1 0 1)
    tendsto_LPr_theta
  have h1 := hrec 1
  have h3 := hrec 3
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h1 h3
  simp [Finset.sum_range_succ, Nat.choose] at h1 h3
  have m0 : mom 1 1 0 1 0 = θ := by simpa using mom_theta 0
  have m2 : mom 1 1 0 1 2 = D θ := by simpa using mom_theta 1
  have m4 : mom 1 1 0 1 4 = D (D θ) := by simpa using mom_theta 2
  rw [m0, m2] at h1
  rw [m0, m2, m4] at h3
  set μ := lamb (fun n => n % 2 = 1) 1
  have hD2 : D (D θ) = D θ * ((1 + 1) * μ) + θ * ((1 + 1) * D μ) := by
    conv_lhs => rw [h1, D_mul, add_mul, one_mul, D_add]
    ring
  have key : θ * (2 * (D μ - lamb (fun n => n % 2 = 1) 3 - 4 * μ ^ 2)) = 0 := by
    linear_combination h3 - hD2 + 4 * μ * h1
  have hx := (mul_eq_zero.mp ((mul_eq_zero.mp key).resolve_left θ_ne_zero)).resolve_left two_ne_zero
  linear_combination -hx

/-! ## The series `Σ q^(cT(j)) e^((2j+1)t)` -/

/-- `2` as a unit of `Q`. -/
noncomputable def two : Qˣ :=
  ⟨2, C (1 / 2), by rw [← map_ofNat C 2, ← map_mul]; norm_num,
    by rw [← map_ofNat C 2, ← map_mul]; norm_num⟩

/-- `tanh t = (e^t - e^(-t)) / (e^t + e^(-t))`. -/
noncomputable def τ : K := (E 1 - E (-1)) * invOfUnit (E 1 + E (-1)) two

theorem constantCoeff_E (a : Q) : constantCoeff (E a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_E, pow_zero, one_mul, Nat.factorial_zero,
    Nat.cast_one, inv_one, map_one]

theorem mul_τ : (E 1 + E (-1)) * τ = E 1 - E (-1) := by
  rw [τ, mul_left_comm, mul_invOfUnit _ _ (by
    rw [map_add, constantCoeff_E, constantCoeff_E]; exact one_add_one_eq_two), mul_one]

theorem derivative_cosh : d⁄dX (E 1 + E (-1)) = (E 1 + E (-1)) * τ := by
  rw [mul_τ, map_add, derivative_E, derivative_E, map_neg, map_one]
  ring

/-- The first coefficients of `tanh t`: `0, 1, 0, -1/3`. -/
theorem coeff_τ : coeff 0 τ = 0 ∧ coeff 1 τ = 1 ∧ coeff 2 τ = 0 ∧ 6 * coeff 3 τ = -2 := by
  have h : ∀ m, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (m.choose p.1 : Q) *
      ((1 + (-1) ^ p.1) * ((p.2 ! : Q) * coeff p.2 τ)) = 1 - (-1) ^ m := by
    intro m
    have h1 := fact_mul_coeff_mul (E 1 + E (-1)) τ m
    rw [mul_τ, map_sub, mul_sub, fact_mul_coeff_E, fact_mul_coeff_E, one_pow] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_add, mul_add, fact_mul_coeff_E, fact_mul_coeff_E, one_pow]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h0 h1 h2 h3
  simp [Finset.sum_range_succ, Nat.choose, Nat.factorial] at h0 h1 h2 h3
  have h4 : (4 : Q) * coeff 2 τ = 0 := by linear_combination h2 - 2 * h0
  have h5 : (2 : Q) * (6 * coeff 3 τ + 2) = 0 := by linear_combination h3 - 6 * h1
  refine ⟨by rw [coeff_zero_eq_constantCoeff_apply]; exact h0, h1,
    (mul_eq_zero.mp h4).resolve_left (by norm_num), ?_⟩
  linear_combination (mul_eq_zero.mp h5).resolve_left two_ne_zero

/-- The logarithmic derivative of `Pr c 0 1 2 (N + 1)`. -/
noncomputable def LU (c N : ℕ) : K :=
  τ + ∑ k ∈ Finset.range (N + 1), C 2 * rescale 2 (G (c * (k + 1))) +
    ∑ k ∈ Finset.range N, C (-2) * rescale (-2) (G (c * (k + 1)))

theorem derivative_PU {c : ℕ} (hc : 0 < c) (N : ℕ) :
    d⁄dX (Pr c 0 1 2 (N + 1)) = Pr c 0 1 2 (N + 1) * LU c N := by
  have hP : Pr c 0 1 2 (N + 1) = C (∏ k ∈ Finset.range (N + 1), (1 - X ^ (c * (k + 1)))) *
      (E 1 + E (-1)) * (∏ k ∈ Finset.range (N + 1), (1 + C (X ^ (c * (k + 1))) * E 2)) *
      ∏ k ∈ Finset.range N, (1 + C (X ^ (c * (k + 1))) * E (-2)) := by
    rw [Pr, Finset.prod_mul_distrib, Finset.prod_range_succ'
      (fun k => 1 + C (X ^ (c * k + 0 * (k + 1))) * E _)]
    simp only [zero_mul, add_zero, mul_zero, pow_zero, map_one, one_mul, Int.cast_one,
      Int.cast_ofNat]
    rw [show E 1 + E (-1) = E 1 * (1 + E (-2)) by rw [mul_add, mul_one, E_mul_E]; norm_num]
    ring
  have h0 : d⁄dX (C (∏ k ∈ Finset.range (N + 1), (1 - X ^ (c * (k + 1)))) : K) =
      C (∏ k ∈ Finset.range (N + 1), (1 - X ^ (c * (k + 1)))) * 0 := by
    rw [derivative_C, mul_zero]
  have hf := derivative_prod (f := fun k => 1 + C (X ^ (c * (k + 1))) * E 2)
    (fun k => derivative_factor 2 (by positivity)) (N + 1)
  have hg := derivative_prod (f := fun k => 1 + C (X ^ (c * (k + 1))) * E (-2))
    (fun k => derivative_factor (-2) (by positivity)) N
  rw [hP, derivative_mul_of (derivative_mul_of (derivative_mul_of h0 derivative_cosh) hf) hg, LU]
  ring

theorem tendsto_LU {c : ℕ} (hc : 0 < c) (j : ℕ) :
    Tendsto (fun N => (j ! : Q) * coeff j (LU c N)) atTop (𝓝 ((j ! : Q) * coeff j τ +
      2 ^ (j + 1) * lamb (fun n => c ∣ n ∧ 0 < n) j +
        (-2) ^ (j + 1) * lamb (fun n => c ∣ n ∧ 0 < n) j)) := by
  have hL := tendsto_sum_gq (e := fun k => c * (k + 1))
    (fun a b h => by simpa [hc.ne'] using h) (fun k => by nlinarith)
    (P := fun n => c ∣ n ∧ 0 < n)
    (fun n => ⟨fun ⟨⟨m, hm⟩, h⟩ => ⟨m - 1, by
      rw [hm]
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · simp at hm; omega
      · rw [Nat.sub_add_cancel hm']⟩,
      fun ⟨k, hk⟩ => ⟨⟨k + 1, hk.symm⟩, by rw [← hk]; positivity⟩⟩) j
  refine Tendsto.congr (fun N => ?_) ((tendsto_const_nhds.add
    ((hL.comp (tendsto_add_atTop_nat 1)).const_mul (2 ^ (j + 1)))).add (hL.const_mul ((-2) ^ (j + 1))))
  simp only [Function.comp_apply, LU, map_add, mul_add, map_sum, Finset.mul_sum, fact_mul_coeff_G]

/-- The moments of order `2` and `4` of `Σ q^(cT(j)) e^((2j+1)t)`, from `(2j + 1)² = 8T(j) + 1`. -/
theorem mom_U (c : ℕ) (hc : 0 < c) :
    (c : Q) * mom c 0 1 2 2 = 8 * D (mom c 0 1 2 0) + c * mom c 0 1 2 0 ∧
      (c : Q) ^ 2 * mom c 0 1 2 4 =
        64 * D (D (mom c 0 1 2 0)) + 16 * c * D (mom c 0 1 2 0) + c ^ 2 * mom c 0 1 2 0 := by
  have hS := fun m => (summable_mom hc 0 1 2 m).hasSum
  have hJD := JacobiFourSquares.hasSum_D (hS 0)
  have h2 := ((hS 2).mul_left (C (c : ℤ))).unique (by
    convert (hJD.mul_left (C 8)).add ((hS 0).mul_left (C (c : ℤ))) using 1
    funext j
    rw [JacobiFourSquares.D_monomial, JacobiFourSquares.monomial_eq,
      JacobiFourSquares.monomial_eq, JacobiFourSquares.monomial_eq]
    simp only [← mul_assoc, ← map_mul, ← add_mul, ← map_add]
    congr 2
    push_cast
    linear_combination (-4 * c : ℤ) * JacobiFourSquares.two_mul_T j)
  have h4 := ((hS 4).mul_left (C ((c : ℤ) ^ 2))).unique (by
    convert ((((JacobiFourSquares.hasSum_D hJD).mul_left (C 64)).add (hJD.mul_left (C (16 * (c : ℤ))))).add
      ((hS 0).mul_left (C ((c : ℤ) ^ 2)))) using 1
    funext j
    rw [JacobiFourSquares.D_monomial, JacobiFourSquares.D_monomial, JacobiFourSquares.monomial_eq,
      JacobiFourSquares.monomial_eq, JacobiFourSquares.monomial_eq, JacobiFourSquares.monomial_eq]
    simp only [← mul_assoc, ← map_mul, ← add_mul, ← map_add]
    congr 2
    push_cast
    linear_combination (-4 * (c : ℤ) ^ 2 * ((1 + j * 2) ^ 2 + 1 + 8 * T j)) *
      JacobiFourSquares.two_mul_T j)
  constructor
  · have := congrArg toQ h2
    simp only [map_mul, map_add, toQ_D] at this
    simpa [toQ, mom, map_ofNat] using this
  · have := congrArg toQ h4
    simp only [map_mul, map_add, toQ_D] at this
    simpa [toQ, mom, map_ofNat] using this

theorem mom_U_ne_zero {c : ℕ} (hc : 0 < c) : mom c 0 1 2 0 ≠ 0 := by
  intro h
  have h0 := JacobiFourSquares.coeff_of_hasSum (summable_mom hc 0 1 2 0).hasSum 0 {0, -1}
    (fun j hj => by
      rw [coeff_monomial, ite_eq_right]
      intro h'
      have hT : T j = 0 := (Nat.mul_eq_zero.mp (by simpa using h'.symm)).resolve_left hc.ne'
      have h1 := JacobiFourSquares.le_T j
      have h2 := JacobiFourSquares.neg_le_T j
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      omega)
  rw [Finset.sum_pair (by norm_num)] at h0
  have h1 := congrArg (coeff 0) h
  rw [mom, toQ, coeff_map, h0, map_zero] at h1
  simp [JacobiFourSquares.T] at h1

/-- **The heat equation for `Σ q^(cT(j))`**: `4c λ₁² = 2 D λ₁ - c λ₁ - c λ₃` for the Lambert series
over the divisors with cofactor divisible by `c`. -/
theorem U_heat {c : ℕ} (hc : 0 < c) :
    4 * c * lamb (fun n => c ∣ n ∧ 0 < n) 1 ^ 2 = 2 * D (lamb (fun n => c ∣ n ∧ 0 < n) 1) -
      c * lamb (fun n => c ∣ n ∧ 0 < n) 1 - c * lamb (fun n => c ∣ n ∧ 0 < n) 3 := by
  have hrec := recursion (P := fun N => Pr c 0 1 2 (N + 1)) (fun N => derivative_PU hc N)
    (fun i => (tendsto_mom hc 0 1 2 i).comp (tendsto_add_atTop_nat 1)) (tendsto_LU hc)
  have h1 := hrec 1
  have h3 := hrec 3
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h1 h3
  simp [Finset.sum_range_succ, Nat.choose, Nat.factorial] at h1 h3
  obtain ⟨t0, t1, t2, t3⟩ := coeff_τ
  rw [coeff_zero_eq_constantCoeff_apply] at t0
  obtain ⟨m2, m4⟩ := mom_U c hc
  set U := mom c 0 1 2 0
  set l := lamb (fun n => c ∣ n ∧ 0 < n) 1
  have hDU8 : (8 : Q) * (D U - c * U * l) = 0 := by
    linear_combination -m2 + c * h1 + c * U * t1 + c * mom c 0 1 2 1 * t0
  have hDU : D U = c * U * l := by
    linear_combination (mul_eq_zero.mp hDU8).resolve_left (by norm_num)
  have hD2U : D (D U) = c * (D U * l + U * D l) := by
    conv_lhs => rw [hDU, mul_assoc, ← map_natCast (C (R := ℚ)) c, D_C_mul, D_mul, map_natCast]
  have key : (c : Q) * U * (32 * (4 * c * l ^ 2 - 2 * D l + c * l +
      c * lamb (fun n => c ∣ n ∧ 0 < n) 3)) = 0 := by
    linear_combination (-(c : Q) ^ 2) * h3 + m4 - (c : Q) ^ 2 * U * t3 -
      6 * (c : Q) ^ 2 * mom c 0 1 2 1 * t2 - (c : Q) ^ 2 * mom c 0 1 2 3 * t0 -
      3 * (c : Q) ^ 2 * mom c 0 1 2 2 * t1 - 3 * c * (1 + 8 * l) * m2 + 64 * hD2U -
      (8 * c + 128 * c * l) * hDU
  have hcU : (c : Q) * U ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') (mom_U_ne_zero hc)
  linear_combination (mul_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hcU)).resolve_left
    (by norm_num)

/-! ## The eighth power of `θ` -/

theorem coeff_lamb (P : ℕ → Prop) [DecidablePred P] (m N : ℕ) :
    coeff N (lamb P m) = ∑ d ∈ N.divisors, if P (N / d) then (-1) ^ (d + 1) * (d : ℚ) ^ m else 0 := by
  rw [lamb, coeff_mk, Finset.sum_filter]

theorem neg_one_pow_mul_of_even {d e : ℕ} (he : Even e) : (-1 : ℚ) ^ (d * e) = 1 := by
  rw [mul_comm, pow_mul, he.neg_one_pow, one_pow]

theorem neg_one_pow_mul_of_odd {d e : ℕ} (he : Odd e) : (-1 : ℚ) ^ (d * e) = (-1) ^ d := by
  rw [mul_comm, pow_mul, he.neg_one_pow]

theorem even_cond {e : ℕ} (he0 : 0 < e) (h : Even e) : 2 ∣ e ∧ 0 < e := ⟨h.two_dvd, he0⟩

theorem even_cond' {e : ℕ} (h : Odd e) : ¬ (2 ∣ e ∧ 0 < e) :=
  fun h' => Nat.not_even_iff_odd.mpr h (even_iff_two_dvd.mpr h'.1)

theorem odd_cond {e : ℕ} (h : Odd e) : e % 2 = 1 := Nat.odd_iff.mp h

theorem odd_cond' {e : ℕ} (h : Even e) : ¬ e % 2 = 1 := Nat.odd_iff.not.mp (Nat.not_odd_iff_even.mpr h)

theorem exists_eq_mul_of_mem_divisors {N d : ℕ} (hd : d ∈ N.divisors) :
    ∃ e, 0 < e ∧ N = d * e ∧ N / d = e := by
  obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
  have hN := (Nat.mem_divisors.mp hd).2
  refine ⟨e, Nat.pos_of_ne_zero fun h => hN (by rw [he, h, mul_zero]), he, ?_⟩
  rw [he, Nat.mul_div_cancel_left _ (Nat.pos_of_mem_divisors hd)]

/-- The four-square theorem in terms of the Lambert series. -/
theorem theta_pow_four_lamb : θ ^ 4 = 1 + 8 * (lamb (fun n => 2 ∣ n ∧ 0 < n) 1 -
    rescale (-1) (lamb (fun n => n % 2 = 1) 1)) := by
  have h := congrArg toQ JacobiFourSquares.theta_pow_four
  rw [map_pow, ← θ, map_add, map_one, map_mul, map_ofNat] at h
  rw [h]
  congr 2
  ext N
  rw [toQ, coeff_map, coeff_mk, map_sub, coeff_rescale, coeff_lamb, coeff_lamb, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← JacobiFourSquares.sum_sign_eq_sigma4, eq_intCast]
  push_cast
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨e, he0, hN, hNd⟩ := exists_eq_mul_of_mem_divisors hd
  rw [hNd, hN]
  rcases Nat.even_or_odd e with h2 | h2
  · rw [neg_one_pow_mul_of_even h2, ite_eq_left (even_cond he0 h2), ite_eq_right (odd_cond' h2),
      h2.neg_one_pow]
    ring
  · rw [neg_one_pow_mul_of_odd h2, ite_eq_right (even_cond' h2), ite_eq_left (odd_cond h2),
      h2.neg_one_pow]
    ring

/-- `λ₁⁽²⁾ + μ₁(-q) = λ₁⁽¹⁾(-q)`, divisor by divisor. -/
theorem lamb_add_rescale : lamb (fun n => 2 ∣ n ∧ 0 < n) 1 + rescale (-1) (lamb (fun n => n % 2 = 1) 1) =
    rescale (-1) (lamb (fun n => 1 ∣ n ∧ 0 < n) 1) := by
  ext N
  rw [map_add, coeff_rescale, coeff_rescale, coeff_lamb, coeff_lamb, coeff_lamb, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨e, he0, hN, hNd⟩ := exists_eq_mul_of_mem_divisors hd
  rw [hNd, hN, ite_eq_left (show 1 ∣ e ∧ 0 < e from ⟨one_dvd e, he0⟩)]
  rcases Nat.even_or_odd e with h2 | h2
  · rw [neg_one_pow_mul_of_even h2, ite_eq_left (even_cond he0 h2), ite_eq_right (odd_cond' h2)]
    ring
  · rw [ite_eq_right (even_cond' h2), ite_eq_left (odd_cond h2)]
    ring

/-- `θ⁸` as a combination of three Lambert series of cubes. -/
theorem theta_pow_eight : θ ^ 8 = 1 - 32 * lamb (fun n => 2 ∣ n ∧ 0 < n) 3 -
    32 * rescale (-1) (lamb (fun n => n % 2 = 1) 3) +
      16 * rescale (-1) (lamb (fun n => 1 ∣ n ∧ 0 < n) 3) := by
  have h4 := theta_pow_four_lamb
  have hV := lamb_add_rescale
  have hx := U_heat two_pos
  have hv := congrArg (rescale (-1 : ℚ)) (U_heat one_pos)
  have hz := congrArg (rescale (-1 : ℚ)) theta_heat
  simp only [map_mul, map_sub, map_pow, map_ofNat, map_natCast] at hv hz
  push_cast at hx hv
  have hDv := congrArg D hV
  rw [D_add, D_rescale, D_rescale] at hDv
  linear_combination (θ ^ 4 + 1 + 8 * (lamb (fun n => 2 ∣ n ∧ 0 < n) 1 -
      rescale (-1) (lamb (fun n => n % 2 = 1) 1))) * h4 -
    (64 * (lamb (fun n => 2 ∣ n ∧ 0 < n) 1 + rescale (-1) (lamb (fun n => n % 2 = 1) 1) +
      rescale (-1) (lamb (fun n => 1 ∣ n ∧ 0 < n) 1)) + 16) * hV + 16 * hx + 32 * hz - 16 * hv +
    32 * hDv

/-- The coefficients of `θ⁸`: `16 Σ_{d ∣ N} (-1)^(N+d) d³` for `N ≥ 1`. -/
theorem coeff_theta_pow_eight {N : ℕ} (hN : N ≠ 0) :
    coeff N (θ ^ 8) = 16 * ∑ d ∈ N.divisors, (-1) ^ (N + d) * (d : ℚ) ^ 3 := by
  rw [theta_pow_eight, map_add, map_sub, map_sub, coeff_one, ite_eq_right hN,
    ← map_ofNat C 32, ← map_ofNat C 16, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_rescale, coeff_rescale, coeff_lamb, coeff_lamb, coeff_lamb]
  simp only [Finset.mul_sum, zero_sub, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨e, he0, hN', hNd⟩ := exists_eq_mul_of_mem_divisors hd
  rw [hNd, hN', ite_eq_left (show 1 ∣ e ∧ 0 < e from ⟨one_dvd e, he0⟩), pow_add (-1 : ℚ) (d * e) d]
  rcases Nat.even_or_odd e with h2 | h2
  · rw [neg_one_pow_mul_of_even h2, ite_eq_left (even_cond he0 h2), ite_eq_right (odd_cond' h2)]
    ring
  · rw [neg_one_pow_mul_of_odd h2, ite_eq_right (even_cond' h2), ite_eq_left (odd_cond h2)]
    ring

/-! ## Counting the lattice points -/

/-- `r₈(n)`: the integer points of `ℤ⁸` on the sphere `x₁² + ⋯ + x₈² = n`. -/
def r8 (n : ℕ) : ℕ :=
  (Fintype.piFinset fun _ : Fin 8 => Finset.Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i ^ 2 = (n : ℤ)) |>.card

/-- The `n`-th coefficient of `θ⁸` counts the points of `ℤ⁸` on the sphere of radius `√n`. -/
theorem coeff_theta_pow_eight_int (n : ℕ) :
    coeff n (JacobiFourSquares.theta ^ 8) = (r8 n : ℤ) := by
  have h1 : X ^ (n + 1) ∣
      JacobiFourSquares.theta - ∑ j ∈ Finset.Icc (-(n : ℤ)) n, (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, sub_eq_zero, JacobiFourSquares.coeff_of_hasSum JacobiFourSquares.hasSum_theta m
      (Finset.Icc (-(n : ℤ)) n), map_sum]
    intro j hj
    rw [coeff_X_pow, ite_eq_right]
    intro h
    apply hj
    have := Nat.le_self_pow two_ne_zero j.natAbs
    rw [Finset.mem_Icc]
    omega
  rw [JacobiFourSquares.coeff_eq_of_dvd (h1.trans (sub_dvd_pow_sub_pow _ _ 8)) (Nat.lt_succ_self n),
    show (∑ j ∈ Finset.Icc (-(n : ℤ)) n, (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2)) ^ 8 =
      ∏ _i : Fin 8, ∑ j ∈ Finset.Icc (-(n : ℤ)) n, (X : ℤ⟦X⟧) ^ (j.natAbs ^ 2) by simp,
    Finset.prod_univ_sum]
  simp only [Finset.prod_pow_eq_pow_sum, map_sum, coeff_X_pow]
  rw [Finset.sum_boole, r8]
  congr 2
  refine Finset.filter_congr fun v _ => ?_
  rw [eq_comm, ← Nat.cast_inj (R := ℤ)]
  push_cast
  simp only [sq_abs]

/-- `r₈(0) = 1`: only the origin. -/
theorem r8_zero : r8 0 = 1 := by
  have h := coeff_theta_pow_eight_int 0
  rw [show JacobiFourSquares.theta ^ 8 = (JacobiFourSquares.theta ^ 4) ^ 2 by ring,
    JacobiFourSquares.theta_pow_four] at h
  simp [JacobiFourSquares.sigma4] at h
  exact_mod_cast h.symm

/-- **Jacobi's eight-square theorem**: `r₈(n) = 16 Σ_{d ∣ n} (−1)^{n+d} d³` for `n ≥ 1`. -/
theorem r8_eq {n : ℕ} (hn : n ≠ 0) :
    (r8 n : ℤ) = 16 * ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℤ) ^ 3 := by
  have h := coeff_theta_pow_eight hn
  rw [θ, ← map_pow, toQ, coeff_map, coeff_theta_pow_eight_int, eq_intCast] at h
  exact_mod_cast h

end JacobiEightSquares

#print axioms JacobiEightSquares.r8_zero
#print axioms JacobiEightSquares.r8_eq
