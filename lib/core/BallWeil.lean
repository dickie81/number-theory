/-
# The Riemann hypothesis in Weil's form: Castelnuovo–Severi for divisors built from the primes

Plain statement. Weil's proof of the Riemann hypothesis for a curve `C` of genus `g` over `𝔽_q` intersects divisors
on `C × C`: the fibres `e₁ = pt × C` and `e₂ = C × pt`, and the graphs `Γ_k` of the powers of Frobenius. Their
intersection numbers are `e₁² = e₂² = 0`, `e₁·e₂ = 1`, `Γ_k·e₁ = 1`, `Γ_k·e₂ = q^k` and, with the eigenvalues
`α_1, …, α_{2g}` of Frobenius, `Γ_j·Γ_k = q^j + q^k − √(q^j q^k)·Σ_i (α_i/√q)^{j − k}` for `j ≥ k`. The Hodge index
theorem on `C × C` gives the Castelnuovo–Severi inequality `D² ≤ 2(D·e₁)(D·e₂)`, and that gives RH for `C`.

For `ζ`, put a positive integer `n` for `q^k` and `K_H` for the sum over the eigenvalues. So take formal classes `e₁`,
`e₂`, `D_1, D_2, …` with `e₁² = e₂² = 0`, `e₁·e₂ = 1`, `D_n·e₁ = 1`, `D_n·e₂ = n` and
`D_m·D_n = m + n − √(mn)·K_H(m/n)` (`inter`), where `K_H` is computed from the primes (`BallPsi.kerHψ`, through `ψ`).
For the divisors `D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n D_n` with integer coefficients:
* Mathlib's `RiemannHypothesis` holds if and only if every such `D` has `D² ≤ 2(D·e₁)(D·e₂)`
  (`rh_iff_castelnuovo_severi`), and if and only if `D² ≤ 0` whenever `D·e₁ = D·e₂ = 0` (`rh_iff_hodge_index`);
* under RH, `|D_m·D_n − m − n| ≤ (2 − D_1²)·√(mn)` (`weil_bound`). Here `D_1² = 2 − K_H(1)` plays `Δ² = 2 − 2g`,
  so `2 − D_1² = K_H(1) = 2 + γ − log 4π` plays `2g` (`inter_one`), and for `n = 1` this is the Hasse–Weil bound for
  `D_m·D_1`, the analogue of `#C(𝔽_{q^k}) = Γ_k·Δ`;
* the upper bound alone, `D_m·D_n ≤ m + n + (2 − D_1²)·√(mn)` for all `m, n ≥ 1`, gives RH (`rh_iff_weil_bound`).
  For a curve the upper bound on the point counts that Stepanov's method gives is not enough by itself, and Bombieri
  derives the lower bound from upper bounds on a Galois cover. For `ζ` it is enough because no zero of `ζ` is real:
  the poles of the twin form of `TwinLandau` are off the real axis;
* `D_{km}·D_{kn} = k·(D_m·D_n)` (`inter_mul`), as `Γ_{i+j}·Γ_{i+k} = q^i·(Γ_j·Γ_k)`: multiplication by `k` acts like a
  Frobenius of degree `k`.

The quadratic form `Q(x) = Σ_{m,n ≤ N} x_m x_n √(mn)·K_H(m/n)` (`form`) of the Gram matrix of the orbit is
`‖Σ_n x_n w_n‖²` in every realization of `K_H` (`form_eq_norm_sq`). If `Q(δ_k − Σ_{n < k} c_n δ_n) ≥ Q(δ_1)` for every
`k` and all real `c`, the orbit-lattice conjecture of `docs/ball-conjecture.md` without the vectors, then RH holds
(`rh_of_pivots`).

* The fibres cancel: `2(D·e₁)(D·e₂) − D² = Q(c)` (`two_deg_sub_selfInt`), the form on the primitive part.
* Under RH, `Q(x)` is a squared norm in the realization `BallHadamard.realizationH`.
* Conversely, the divisor `q·D_{p²} + p·D_{q²}` has `Q = 2p²q²(K_H(1) + K_H((p/q)²))` (`form_two`, `gram_sq`): the
  `2 × 2` minor of `BallKernel.minor_nonneg` at `r = (p/q)²`, with integer coefficients. These `r` are enough for the
  Landau argument (`BallKernel.re_eq_zero_of_dense`, `rh_of_minors`), since the `log(p/q)` are dense.

Like Weil's criterion, these equivalences are reformulations. What is missing is a space on which these numbers are
intersection numbers and a Hodge index theorem holds there. The numbers are real, not integers: `D_1² ≈ 1.9538`, as for
the Arakelov intersection numbers of an arithmetic surface.
-/
import Mathlib
import BallPsi

open Real Complex Finset ComplexConjugate WeilForm WeilTest
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace BallWeil

open BallKernel BallLattice BallHadamard BallPsi

/-! ## The kernel from the primes and the intersection numbers -/

/-- **`K_H` from the primes, as a real function**: `kψ(x) = Re kerHψ(x)`, and `kerHψ` is real (`kerHψ_eq`). -/
def kψ (x : ℝ) : ℝ := (kerHψ x).re

lemma kerHψ_eq (x : ℝ) : kerHψ x = (kψ x : ℂ) := by
  unfold kψ kerHψ
  rw [Complex.ofReal_re]

lemma kerH_eq_kψ {x : ℝ} (hx : 0 < x) : kerH x = (kψ x : ℂ) := by
  rw [kerH_eq_kerHψ hx, kerHψ_eq]

lemma kψ_inv (x : ℝ) : kψ x⁻¹ = kψ x := by
  unfold kψ kerHψ
  rw [inv_inv, max_comm]

/-- `K_H(1) = 2 + γ − log 4π`, Hadamard's constant. -/
theorem kψ_one : kψ 1 = 2 + eulerMascheroniConstant - Real.log (4 * π) := by
  have h := kerH_eq_kψ one_pos
  rw [kerH_one] at h
  exact_mod_cast h.symm

lemma kψ_one_pos : 0 < kψ 1 := kψ_one ▸ PsiOmega.hadamard_const_pos

/-- **The Gram matrix of the orbit**, `G(m, n) = √(mn)·K_H(m/n)`: in a realization of `K_H` it is `⟨w_m, w_n⟩`
(`inner_w`). -/
def gram (m n : ℕ) : ℝ := Real.sqrt ((m : ℝ) * n) * kψ ((m : ℝ) / n)

lemma gram_comm (m n : ℕ) : gram m n = gram n m := by
  unfold gram
  rw [mul_comm (m : ℝ), ← kψ_inv, inv_div]

lemma gram_self (n : ℕ) : gram n n = n * kψ 1 := by
  unfold gram
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Real.sqrt_mul_self (Nat.cast_nonneg n), div_self (by exact_mod_cast hn.ne')]

lemma gram_sq (p q : ℕ) : gram (p ^ 2) (q ^ 2) = p * q * kψ (((p : ℝ) / q) ^ 2) := by
  unfold gram
  push_cast
  rw [div_pow, ← mul_pow, Real.sqrt_sq (by positivity)]

/-- **The intersection number** `D_m·D_n = m + n − √(mn)·K_H(m/n)`, with `K_H` computed from the primes. -/
def inter (m n : ℕ) : ℝ := m + n - gram m n

/-- **`D_1² = 2 − K_H(1)`**, the analogue of `Δ² = 2 − 2g`: so `K_H(1) = 2 + γ − log 4π` plays `2g`. -/
theorem inter_one : inter 1 1 = 2 - (2 + eulerMascheroniConstant - Real.log (4 * π)) := by
  unfold inter
  rw [gram_self, kψ_one]
  push_cast
  ring

/-- **Multiplication by `k` acts like a Frobenius of degree `k`**: `D_{km}·D_{kn} = k·(D_m·D_n)`. -/
theorem inter_mul (k m n : ℕ) : inter (k * m) (k * n) = k * inter m n := by
  unfold inter gram
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    push_cast
    rw [mul_div_mul_left _ _ hk0.ne', show (k : ℝ) * m * (k * n) = k ^ 2 * (m * n) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hk0.le]
    ring

/-! ## Divisors -/

/-- **The self-intersection** of `D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n D_n`, from `e₁² = e₂² = 0`, `e₁·e₂ = 1`,
`D_n·e₁ = 1`, `D_n·e₂ = n` and `D_m·D_n = inter m n`. -/
def selfInt (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  2 * a * b + 2 * a * ∑ n ∈ Icc 1 N, c n + 2 * b * ∑ n ∈ Icc 1 N, c n * n +
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * inter m n

/-- `D·e₁ = b + Σ_n c_n`. -/
def deg₁ (b : ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ := b + ∑ n ∈ Icc 1 N, c n

/-- `D·e₂ = a + Σ_n c_n·n`. -/
def deg₂ (a : ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ := a + ∑ n ∈ Icc 1 N, c n * n

/-- **The form of the Gram matrix of the orbit**, `Q(x) = Σ_{m,n ≤ N} x_m x_n G(m, n)`. -/
def form (N : ℕ) (x : ℕ → ℝ) : ℝ := ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * gram m n

/-- **The fibres cancel**: `2(D·e₁)(D·e₂) − D² = Q(c)`, the form of the Gram matrix on the coefficients of the
`D_n`. -/
theorem two_deg_sub_selfInt (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) :
    2 * deg₁ b N c * deg₂ a N c - selfInt a b N c = form N c := by
  unfold deg₁ deg₂ selfInt form inter
  have e : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * ((m : ℝ) + n - gram m n) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * m * c n + ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * (c n * n) -
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * gram m n := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [e, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
  ring

/-! ## The form on a realization -/

/-- In a realization of `K_H`, `⟨w_m, w_n⟩ = G(m, n)`. -/
lemma inner_w (R : Realization kerH) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ⟪R.w (m : ℚ), R.w (n : ℚ)⟫_ℂ = (gram m n : ℂ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := R.gram (n : ℚ) (m : ℚ) (by exact_mod_cast hn) (by exact_mod_cast hm)
  simp only [Rat.cast_natCast] at h
  rw [h, kerH_eq_kψ (div_pos hn0 hm0), gram_comm, gram, Complex.ofReal_mul]

/-- **The form is a squared norm in every realization of `K_H`**: `Q(x) = ‖Σ_{n ≤ N} x_n w_n‖²`. -/
theorem form_eq_norm_sq (R : Realization kerH) (N : ℕ) (x : ℕ → ℝ) :
    form N x = ‖∑ n ∈ Icc 1 N, (x n : ℂ) • R.w (n : ℚ)‖ ^ 2 := by
  set v := ∑ n ∈ Icc 1 N, (x n : ℂ) • R.w (n : ℚ) with hv
  have h : ⟪v, v⟫_ℂ = (form N x : ℂ) := by
    rw [hv, sum_inner, form, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [inner_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hm1 : 0 < m := (Finset.mem_Icc.1 hm).1
    have hn1 : 0 < n := (Finset.mem_Icc.1 hn).1
    rw [inner_smul_left, inner_smul_right, inner_w R hm1 hn1, Complex.conj_ofReal]
    push_cast
    ring
  have h2 : ((form N x : ℝ) : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rfl
  exact_mod_cast h2

/-- **Under RH the form is nonnegative**, for all real coefficients. -/
theorem form_nonneg (hRH : RiemannHypothesis) (N : ℕ) (x : ℕ → ℝ) : 0 ≤ form N x := by
  rw [form_eq_norm_sq (realizationH hRH)]
  positivity

/-! ## The form on two points -/

lemma form_eq_sum {N : ℕ} {x : ℕ → ℝ} {T : Finset ℕ} (hT : T ⊆ Icc 1 N)
    (hx : ∀ n ∈ Icc 1 N, n ∉ T → x n = 0) :
    form N x = ∑ m ∈ T, ∑ n ∈ T, x m * x n * gram m n := by
  unfold form
  rw [← Finset.sum_subset hT fun m hm hmT => by simp [hx m hm hmT]]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact (Finset.sum_subset hT fun n hn hnT => by simp [hx n hn hnT]).symm

/-- **The form on two points**: for `m ≠ n` in `[1, N]`, `Q(aδ_m + bδ_n) = a²G(m, m) + 2abG(m, n) + b²G(n, n)`. -/
theorem form_two {m n N : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hmn : m ≠ n) (a b : ℝ) :
    form N (fun i => if i = m then a else if i = n then b else 0) =
      a ^ 2 * gram m m + 2 * a * b * gram m n + b ^ 2 * gram n n := by
  have hT : ({m, n} : Finset ℕ) ⊆ Icc 1 N := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hm
    · rw [Finset.mem_singleton.1 hi]; exact hn
  rw [form_eq_sum hT fun i _ hi => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [hi.1, hi.2]]
  rw [Finset.sum_pair hmn, Finset.sum_pair hmn, Finset.sum_pair hmn]
  simp only [↓reduceIte, Ne.symm hmn]
  rw [gram_comm n m]
  ring

/-! ## From the `2 × 2` minors to the Riemann hypothesis -/

/-- **The minors at squares give the Riemann hypothesis**: if `K_H((p/q)²) ≥ −K_H(1)` for all positive integers `p`,
`q`, then RH. The twin sum at `λ = log(p/q)` is `2K_H(1) + 2K_H((p/q)²)` (`BallHadamard.twin_eq_kerH`), and the
`log(p/q)` are dense, which is all the Landau argument of `BallKernel.re_eq_zero_of_dense` needs. -/
theorem rh_of_minors (h : ∀ p q : ℕ, 0 < p → 0 < q → -kψ 1 ≤ kψ (((p : ℝ) / q) ^ 2)) : RiemannHypothesis := by
  have hW : ∀ r : ℚ, 0 < r → 0 ≤ TwinLandau.Wsum poleP (fun q => hG (poleP q)) (1 * Real.log r) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have e : (1 : ℝ) * Real.log r = Real.log ((r : ℝ) ^ 2) / 2 := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [e, twin_eq_kerH, kerH_inv, kerH_eq_kψ one_pos, kerH_eq_kψ (by positivity)]
    have hnum : 0 < r.num := Rat.num_pos.2 hr
    have hrq : (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by
      rw [Rat.cast_def]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm
    have hm := h r.num.toNat r.den (by omega) r.den_pos
    rw [← hrq] at hm
    have e2 : 2 * (kψ 1 : ℂ) + kψ ((r : ℝ) ^ 2) + kψ ((r : ℝ) ^ 2) =
        ((2 * kψ 1 + 2 * kψ ((r : ℝ) ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e2]
    exact Complex.zero_le_real.2 (by linarith)
  have hline : ∀ q : ZIdx, (zetaZeroFamily q).re = 1 / 2 := fun q => by
    have h := re_eq_zero_of_dense twinPoles_hG (G := hG) (fun _ => rfl) hG_neg (fun p _ => hG_ne p) one_ne_zero hW q
    rw [re_poleP] at h
    linarith
  intro s hs htriv _
  exact hline ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

/-- **Integer coefficients give the minors**: if `Q(x) ≥ 0` for all integer `x`, then `K_H((p/q)²) ≥ −K_H(1)`, from
the divisor `q·D_{p²} + p·D_{q²}`. -/
theorem minor_of_form (h : ∀ (N : ℕ) (x : ℕ → ℤ), 0 ≤ form N (fun n => x n)) {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    -kψ 1 ≤ kψ (((p : ℝ) / q) ^ 2) := by
  rcases eq_or_ne p q with rfl | hpq
  · rw [div_self (by exact_mod_cast hp.ne'), one_pow]
    linarith [kψ_one_pos]
  · have hp2 : 0 < p ^ 2 := pow_pos hp 2
    have hq2 : 0 < q ^ 2 := pow_pos hq 2
    have hne : p ^ 2 ≠ q ^ 2 := fun e => hpq (Nat.pow_left_injective (by norm_num) e)
    have hmN : p ^ 2 ∈ Icc 1 (max (p ^ 2) (q ^ 2)) := Finset.mem_Icc.2 ⟨hp2, le_max_left _ _⟩
    have hnN : q ^ 2 ∈ Icc 1 (max (p ^ 2) (q ^ 2)) := Finset.mem_Icc.2 ⟨hq2, le_max_right _ _⟩
    have hx := h (max (p ^ 2) (q ^ 2)) fun i => if i = p ^ 2 then (q : ℤ) else if i = q ^ 2 then (p : ℤ) else 0
    have e : (fun i => (((if i = p ^ 2 then (q : ℤ) else if i = q ^ 2 then (p : ℤ) else 0 : ℤ)) : ℝ)) =
        fun i => if i = p ^ 2 then (q : ℝ) else if i = q ^ 2 then (p : ℝ) else 0 := by
      funext i
      split_ifs <;> simp
    rw [e, form_two hmN hnN hne, gram_self, gram_self, gram_sq] at hx
    have hpq0 : (0 : ℝ) < (p : ℝ) ^ 2 * q ^ 2 := by positivity
    push_cast at hx
    nlinarith

/-- **RH is the positivity of the form on integer vectors.** -/
theorem rh_iff_form : RiemannHypothesis ↔ ∀ (N : ℕ) (x : ℕ → ℤ), 0 ≤ form N (fun n => x n) :=
  ⟨fun hRH N _ => form_nonneg hRH N _, fun h => rh_of_minors fun _ _ hp hq => minor_of_form h hp hq⟩

/-! ## Weil's form -/

/-- **The Riemann hypothesis is the Castelnuovo–Severi inequality for the divisors `D_n`**: RH holds if and only if
every `D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n D_n` with integer coefficients has `D² ≤ 2(D·e₁)(D·e₂)`. -/
theorem rh_iff_castelnuovo_severi : RiemannHypothesis ↔ ∀ (a b : ℤ) (N : ℕ) (c : ℕ → ℤ),
    selfInt a b N (fun n => c n) ≤ 2 * deg₁ b N (fun n => c n) * deg₂ a N (fun n => c n) := by
  refine rh_iff_form.trans ⟨fun h a b N c => ?_, fun h N x => ?_⟩
  · linarith [two_deg_sub_selfInt a b N (fun n => c n), h N c]
  · have h0 := h 0 0 N x
    have e := two_deg_sub_selfInt 0 0 N (fun n => x n)
    simp only [Int.cast_zero] at h0
    linarith

/-- **The Riemann hypothesis is the Hodge index theorem for the divisors `D_n`**: RH holds if and only if `D² ≤ 0` for
every `D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n D_n` with integer coefficients and `D·e₁ = D·e₂ = 0`. -/
theorem rh_iff_hodge_index : RiemannHypothesis ↔ ∀ (a b : ℤ) (N : ℕ) (c : ℕ → ℤ),
    deg₁ b N (fun n => c n) = 0 → deg₂ a N (fun n => c n) = 0 → selfInt a b N (fun n => c n) ≤ 0 := by
  refine rh_iff_form.trans ⟨fun h a b N c h1 h2 => ?_, fun h N x => ?_⟩
  · have e := two_deg_sub_selfInt a b N (fun n => c n)
    rw [h1, mul_zero, zero_mul, zero_sub] at e
    linarith [h N c]
  · have h1 : deg₁ ((-∑ n ∈ Icc 1 N, x n : ℤ) : ℝ) N (fun n => x n) = 0 := by
      unfold deg₁
      push_cast
      ring
    have h2 : deg₂ ((-∑ n ∈ Icc 1 N, x n * n : ℤ) : ℝ) N (fun n => x n) = 0 := by
      unfold deg₂
      push_cast
      ring
    have hs := h _ _ N x h1 h2
    have e := two_deg_sub_selfInt ((-∑ n ∈ Icc 1 N, x n * n : ℤ) : ℝ) ((-∑ n ∈ Icc 1 N, x n : ℤ) : ℝ) N
      (fun n => x n)
    rw [h1, mul_zero, zero_mul, zero_sub] at e
    linarith

/-- **The Weil bound**: under RH, `|D_m·D_n − m − n| ≤ (2 − D_1²)·√(mn)`, where `2 − D_1² = K_H(1)` plays `2g`.
With `n = 1` it bounds the analogue `D_m·D_1` of the number of points. -/
theorem weil_bound (hRH : RiemannHypothesis) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    |inter m n - m - n| ≤ (2 - inter 1 1) * Real.sqrt ((m : ℝ) * n) := by
  have hk : 2 - inter 1 1 = kψ 1 := by rw [inter_one, kψ_one]; ring
  have hg : inter m n - m - n = -gram m n := by unfold inter; ring
  rw [hk, hg, abs_neg]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 := kψ_one_pos
  have hsq : (kψ 1 * Real.sqrt ((m : ℝ) * n)) ^ 2 = kψ 1 ^ 2 * (m * n) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rcases eq_or_ne m n with rfl | hmn
  · rw [gram_self, Real.sqrt_mul_self hm0.le, abs_of_nonneg (by positivity)]
    ring_nf
    rfl
  · have hmN : m ∈ Icc 1 (max m n) := Finset.mem_Icc.2 ⟨hm, le_max_left _ _⟩
    have hnN : n ∈ Icc 1 (max m n) := Finset.mem_Icc.2 ⟨hn, le_max_right _ _⟩
    have h := form_nonneg hRH (max m n) fun i => if i = m then gram m n else if i = n then -(m * kψ 1) else 0
    rw [form_two hmN hnN hmn, gram_self, gram_self] at h
    have h' : 0 ≤ m * kψ 1 * (kψ 1 ^ 2 * (m * n) - gram m n ^ 2) := by nlinarith
    have hle : gram m n ^ 2 ≤ (kψ 1 * Real.sqrt ((m : ℝ) * n)) ^ 2 := by
      rw [hsq]
      nlinarith [mul_pos hm0 hk0]
    exact abs_le_of_sq_le_sq hle (by positivity)

/-- **The upper Weil bound gives the Riemann hypothesis**: RH holds if and only if
`D_m·D_n ≤ m + n + (2 − D_1²)·√(mn)` for all `m, n ≥ 1`. Only the squares `m = p²`, `n = q²` are used. For a curve
the upper bound on the point counts needs a lower bound as well; here none is needed, as no zero of `ζ` is real. -/
theorem rh_iff_weil_bound : RiemannHypothesis ↔
    ∀ m n : ℕ, 0 < m → 0 < n → inter m n ≤ m + n + (2 - inter 1 1) * Real.sqrt ((m : ℝ) * n) := by
  refine ⟨fun hRH m n hm hn => ?_, fun h => rh_of_minors fun p q hp hq => ?_⟩
  · have := (le_abs_self _).trans (weil_bound hRH hm hn)
    linarith
  · have hb := h (p ^ 2) (q ^ 2) (pow_pos hp 2) (pow_pos hq 2)
    have hk : 2 - inter 1 1 = kψ 1 := by rw [inter_one, kψ_one]; ring
    rw [hk] at hb
    unfold inter at hb
    rw [gram_sq] at hb
    push_cast at hb
    rw [← mul_pow, Real.sqrt_sq (by positivity)] at hb
    have hpq : (0 : ℝ) < p * q := by positivity
    nlinarith

/-! ## The orbit-lattice conjecture implies the Riemann hypothesis -/

lemma form_congr {N : ℕ} {x y : ℕ → ℝ} (h : ∀ n ∈ Icc 1 N, x n = y n) : form N x = form N y := by
  unfold form
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  rw [h m hm, h n hn]

lemma form_smul (N : ℕ) (t : ℝ) (y : ℕ → ℝ) : form N (fun n => t * y n) = t ^ 2 * form N y := by
  unfold form
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma form_succ_of_zero {N : ℕ} {x : ℕ → ℝ} (hx : x (N + 1) = 0) : form (N + 1) x = form N x := by
  unfold form
  rw [Finset.sum_Icc_succ_top (by omega), hx]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_Icc_succ_top (by omega), hx]
  simp

/-- **The orbit-lattice conjecture implies the Riemann hypothesis**: if `Q(δ_k − Σ_{n < k} c_n δ_n) ≥ Q(δ_1)` for
every `k ≥ 1` and all real `c`, where `Q` is the form of the Gram matrix of the orbit, built from the primes, then RH
holds. In a realization `Q(δ_k − Σ_{n < k} c_n δ_n) = ‖w_k − Σ_{n < k} c_n w_n‖²` (`form_eq_norm_sq`), so the
hypothesis is the conjecture `d_k ≥ d_1` of `docs/ball-conjecture.md`. -/
theorem rh_of_pivots (h : ∀ (k : ℕ) (c : ℕ → ℝ), 1 ≤ k → gram 1 1 ≤ form k (fun n => if n = k then 1 else -c n)) :
    RiemannHypothesis := by
  have hg : 0 ≤ gram 1 1 := by
    rw [gram_self]
    simpa using kψ_one_pos.le
  have hall : ∀ (N : ℕ) (x : ℕ → ℝ), 0 ≤ form N x := by
    intro N
    induction N with
    | zero => intro x; simp [form]
    | succ N ih =>
      intro x
      by_cases hx : x (N + 1) = 0
      · rw [form_succ_of_zero hx]
        exact ih x
      · have e : form (N + 1) x =
            x (N + 1) ^ 2 * form (N + 1) (fun n => if n = N + 1 then 1 else -(-(x n / x (N + 1)))) := by
          rw [← form_smul]
          refine form_congr fun n _ => ?_
          split_ifs with hn
          · rw [hn, mul_one]
          · field_simp
        rw [e]
        exact mul_nonneg (sq_nonneg _) (hg.trans (h (N + 1) _ (by omega)))
  exact rh_iff_form.2 fun N x => hall N _

end BallWeil

#print axioms BallWeil.inter_one
#print axioms BallWeil.inter_mul
#print axioms BallWeil.two_deg_sub_selfInt
#print axioms BallWeil.form_eq_norm_sq
#print axioms BallWeil.rh_iff_form
#print axioms BallWeil.rh_iff_castelnuovo_severi
#print axioms BallWeil.rh_iff_hodge_index
#print axioms BallWeil.weil_bound
#print axioms BallWeil.rh_iff_weil_bound
#print axioms BallWeil.rh_of_pivots
