import Mathlib

/-!
# `p`-adic factorial units, Mahler decay and the Gram-window lemma

Module 4 of the L5/L6 plan: the `p`-adic tools T7, N16, B6 and B7, independent of the rest of the library.

**Legendre** (`legendre_lower`, `legendre_upper`): `m/(p − 1) − ⌊log_p m⌋ − 1 ≤ v_p(m!) ≤ m/(p − 1)`, from Mathlib's
`(p − 1)·v_p(m!) = m − s_p(m)` and `s_p(m) ≤ (p − 1)·#digits`.

**Mahler decay.** A function `f : ℕ → ℚ_p` *decays at rate `α` with offset `a`* (`Decay p α a f`) when its Mahler
coefficients satisfy `‖Δ^k f(0)‖ ≤ p^{−(αk + a)}`. By Newton's formula `f(e) = Σ_k C(e, k)·Δ^k f(0)` (`newton`) the
values are then `≤ p^{−a}` (`Decay.norm_le`). The class is closed under sums, `Δ` (gaining `α`, `Decay.diff`), the
shift `e ↦ e + 1` (`Decay.shift`), products (offsets add, `Decay.mul`: `Δ^k(fg)(0)` is an integral combination of
the `Δ^i f(0)·Δ^j g(0)` with `i + j ≥ k`, as `Δ^k` kills the polynomial `C(x, i)·C(x, j)` of degree `i + j`,
`sum_choose_mul_choose_eq_zero`), inverses `(1 + H)⁻¹` for an offset `a > 0` (the geometric series to a large order,
`Decay.inv_one_add`), running products `e ↦ ∏_{i<e}(1 + H(i))` when `H` has offset `α` (`Decay.prod_range`:
`Δ^j F = F·Q_j` with `Q_{j+1} = ΔQ_j + H·Q_j(· + 1)`, `qSeq`), and `∏_z (1 + h_z) − 1`
(`decay_prod_one_add_sub_one`); a linear function `e ↦ u·e` with `‖u‖ ≤ p^{−1}` has rate and offset `1/2`
(`decay_linear`).

**Factorial units** (T7, N16(a)). For `P = p^s` and `ρ < P`, `(ρ + Pe)! = ρ!·e!·(P!)^e·u(e)` (`factorial_eq_unit`)
with `u = c_P·d_{P,ρ}`, `c_P(e) = (Pe)!/((P!)^e e!) = ∏_{i<e} ∏_{1≤y<P}(1 + Pi/y)` (`cUnit`, `factorial_mul_eq`) and
`d_{P,ρ}(e) = C(Pe + ρ, ρ) = ∏_{1≤y≤ρ}(1 + Pe/y)` (`dUnit`). Since `‖P/y‖ ≤ p^{−1}` for `y < P` (`norm_pow_div_le`),
`c_P`, `c_P⁻¹`, `d_{P,ρ}`, `d_{P,ρ}⁻¹`, `u` and `u⁻¹` all decay at rate `1/2` (`decay_cUnit`, …, `decay_fUnit_inv`),
i.e. `v_p(Δ^k f(0)) ≥ k/2` (the spec's `k/4`, `p ≥ 5`, is weaker), and `‖u(e)‖ = 1` (`norm_fUnit`).

**Binomial approximation** (N16(d)): a product `∏_l f_l(e_l)` of functions decaying at rate `α > 0` is, modulo
`p^c`, an integral combination of the `∏_l C(e_l, J_l)` with `Σ_l J_l < D` whenever `αD ≥ c`
(`exists_binomial_approx`); for the factorial units `D = 2c` (the spec's `4c`).

**Jordan splitting** (B6): over a discrete valuation ring in which `2` is a unit (`ℤ_p`, `p` odd), a symmetric
bilinear form on a free module has an orthogonal basis (`exists_orthogonal_basis`: split off a vector `x` with
`B(x, x)` dividing every value, `exists_self_dvd`); in matrix form, `Uᵀ·S·U` is diagonal with `det U` a unit
(`exists_diagonal_congr`).

**The Gram-window lemma** (B7, `gram_window`). Gauss norms `‖P‖_c = max_i ‖P_i‖·c^i` over an ultrametric field `K`
(`gN`, Mathlib's `Polynomial.gaussNorm`, multiplicative by Gauss's lemma). Mahler integrality: `C(a + p^h·u, i)` has
integral coefficients in `u` for `a ∈ ℤ`, `i < p^h` (`gN_choose_comp_le`, by Vandermonde and
`C(P·u, l) = (P/l)·u·∏_{m<l−1}((P/(m+1))·u − 1)`, `choose_C_mul_X`). At `a = t₀ + j`, with the Smith form
`M(a) = U·diag(d)·V`, `N(u) = U⁻¹·M(a + p^h u)·V⁻¹` has integral entries and `N(0) = diag(d)`, so the rows with
`‖d_i‖ ≤ ρ` have Gauss-`ρ` norm `≤ ρ` and `‖det N‖_ρ ≤ ρ^β`; and `‖det N‖_ρ = ‖λ‖·∏_ζ ‖a − ζ + p^h u‖_ρ ≥
‖λ‖·∏_ζ max(‖a − ζ‖, p^{−h}ρ)` (`gram_point`). Taking logarithms with `ρ = p^{−E}`,
`−log max(x, p^{−h−E}) ≤ log p·(#{1 ≤ i ≤ h : x < p^{1−i}} + E·[x ≤ p^{−h}])` (`neg_log_max_le`); the `j < Y₀` with
`‖t₀ + j − ζ‖ < p^{1−i}` are pairwise congruent mod `p^i`, so there are `≤ Y₀/p^i + 1` of them, and at most one with
`‖t₀ + j − ζ‖ ≤ p^{−h}` (`card_le_of_dvd`, `sum_neg_log_le`). Summing over the window and the `≤ nδ` roots gives the
bound.
-/

namespace PadicUnits

open Finset

noncomputable section

/-! ## Legendre bounds -/

section Legendre

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Legendre, lower bound**: `v_p(m!) ≥ m/(p − 1) − ⌊log_p m⌋ − 1` (the base-`p` digit sum is at most
`(p − 1)·#digits`). -/
theorem legendre_lower (m : ℕ) :
    (m : ℝ) / (p - 1) - Nat.log p m - 1 ≤ padicValNat p m.factorial := by
  have h := sub_one_mul_padicValNat_factorial (p := p) m
  have h1 := hp.out.one_lt
  have hd : (p.digits m).sum ≤ (Nat.log p m + 1) * (p - 1) := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rw [← Nat.length_digits p m h1 hm]
    exact List.sum_le_length_nsmul _ _ fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base h1 hd)
  have h2 : (p.digits m).sum ≤ m := Nat.digit_sum_le p m
  have hp1 : (1 : ℝ) < p := by exact_mod_cast h1
  have key : (m : ℝ) ≤ (p - 1) * (padicValNat p m.factorial + Nat.log p m + 1) := by
    have : m ≤ (p - 1) * padicValNat p m.factorial + (Nat.log p m + 1) * (p - 1) := by omega
    have e : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub h1.le]; simp
    have := (Nat.cast_le (α := ℝ)).2 this
    push_cast [e] at this
    linarith
  rw [sub_sub, sub_le_iff_le_add, div_le_iff₀ (by linarith)]
  linarith

/-- **Legendre, upper bound**: `v_p(m!) ≤ m/(p − 1)`. -/
theorem legendre_upper (m : ℕ) : (padicValNat p m.factorial : ℝ) ≤ m / (p - 1) := by
  have h := sub_one_mul_padicValNat_factorial (p := p) m
  have h1 := hp.out.one_lt
  have hp1 : (1 : ℝ) < p := by exact_mod_cast h1
  rw [le_div_iff₀ (by linarith)]
  have : (p - 1) * padicValNat p m.factorial ≤ m := by omega
  have e : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub h1.le]; simp
  have := (Nat.cast_le (α := ℝ)).2 this
  push_cast [e] at this
  linarith

end Legendre

/-! ## Mahler decay -/

section Decay

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Mahler decay** at rate `α` with offset `a`: the Mahler coefficients of `f : ℕ → ℚ_p` satisfy
`‖Δ^k f(0)‖ ≤ p^{−(αk + a)}` for every `k`. -/
def Decay (p : ℕ) [Fact p.Prime] (α a : ℝ) (f : ℕ → ℚ_[p]) : Prop :=
  ∀ k : ℕ, ‖(fwdDiff 1)^[k] f 0‖ ≤ (p : ℝ) ^ (-(α * k + a))

omit hp in
/-- **`p ≥ 1`.** -/
theorem one_le_p (hp : Fact p.Prime) : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

/-- **Monotonicity of `p^{−x}`.** -/
theorem rpow_anti {x y : ℝ} (h : x ≤ y) : (p : ℝ) ^ (-y) ≤ (p : ℝ) ^ (-x) :=
  Real.rpow_le_rpow_of_exponent_le (one_le_p hp) (by linarith)

/-- **The Mahler coefficients** `Δ^k f(0) = Σ_{m ≤ k} (−1)^{k−m} C(k, m) f(m)`. -/
theorem fwdDiff_iter_zero (f : ℕ → ℚ_[p]) (k : ℕ) :
    (fwdDiff 1)^[k] f 0 = ∑ m ∈ range (k + 1), ((-1) ^ (k - m) * (k.choose m : ℤ)) • f m := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp

/-- **Newton's formula** `f(e) = Σ_{k ≤ N} C(e, k)·Δ^k f(0)` for `N ≥ e`. -/
theorem newton (f : ℕ → ℚ_[p]) {e N : ℕ} (h : e ≤ N) :
    f e = ∑ k ∈ range (N + 1), (e.choose k : ℚ_[p]) * (fwdDiff 1)^[k] f 0 := by
  have := shift_eq_sum_fwdDiff_iter (1 : ℕ) f e 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at this
  rw [this]
  refine Finset.sum_subset (range_subset_range.2 (by omega)) fun k hk hk' => ?_
  rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hk hk'; omega), Nat.cast_zero, zero_mul]

/-- **Integer multiples do not increase the norm.** -/
theorem norm_zsmul_le (z : ℤ) (x : ℚ_[p]) : ‖z • x‖ ≤ ‖x‖ := by
  rw [zsmul_eq_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (Padic.norm_int_le_one z)

/-- **Natural multiples do not increase the norm.** -/
theorem norm_natCast_mul_le (n : ℕ) (x : ℚ_[p]) : ‖(n : ℚ_[p]) * x‖ ≤ ‖x‖ := by
  have := norm_zsmul_le (n : ℤ) x
  rwa [zsmul_eq_mul, Int.cast_natCast] at this

/-- **Pointwise bounds bound the Mahler coefficients**: if `‖g(m)‖ ≤ C` for `m ≤ k`, then `‖Δ^k g(0)‖ ≤ C`. -/
theorem norm_fwdDiff_iter_le {g : ℕ → ℚ_[p]} {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hg : ∀ m ≤ k, ‖g m‖ ≤ C) :
    ‖(fwdDiff 1)^[k] g 0‖ ≤ C := by
  rw [fwdDiff_iter_zero]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun m hm => ?_
  exact (norm_zsmul_le _ _).trans (hg m (by simp at hm; omega))

/-- **Decay bounds the values**: `‖f(e)‖ ≤ p^{−a}` (for `α ≥ 0`). -/
theorem Decay.norm_le {α a : ℝ} {f : ℕ → ℚ_[p]} (hf : Decay p α a f) (hα : 0 ≤ α) (e : ℕ) :
    ‖f e‖ ≤ (p : ℝ) ^ (-a) := by
  rw [newton f le_rfl]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  refine (norm_natCast_mul_le _ _).trans ((hf k).trans (rpow_anti ?_))
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- **Weakening** the rate and the offset. -/
theorem Decay.mono {α α' a a' : ℝ} {f : ℕ → ℚ_[p]} (hf : Decay p α a f) (hα : α' ≤ α) (ha : a' ≤ a) :
    Decay p α' a' f := fun k => (hf k).trans (rpow_anti (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))

/-- **Pointwise equal functions.** -/
theorem Decay.congr {α a : ℝ} {f g : ℕ → ℚ_[p]} (hf : Decay p α a f) (h : ∀ e, f e = g e) : Decay p α a g :=
  funext h ▸ hf

/-- **Sums.** -/
theorem Decay.add {α a : ℝ} {f g : ℕ → ℚ_[p]} (hf : Decay p α a f) (hg : Decay p α a g) :
    Decay p α a (f + g) := fun k => by
  rw [fwdDiff_iter_add, Pi.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf k) (hg k))

/-- **Negation.** -/
theorem Decay.neg {α a : ℝ} {f : ℕ → ℚ_[p]} (hf : Decay p α a f) : Decay p α a (-f) := fun k => by
  have : (fwdDiff 1)^[k] (-f) 0 = -(fwdDiff 1)^[k] f 0 := by
    simp only [fwdDiff_iter_zero, Pi.neg_apply, smul_neg, sum_neg_distrib]
  rw [this, norm_neg]
  exact hf k

/-- **Constants**: `c` decays with offset `a` when `‖c‖ ≤ p^{−a}`. -/
theorem decay_const {α a : ℝ} {c : ℚ_[p]} (hc : ‖c‖ ≤ (p : ℝ) ^ (-a)) : Decay p α a fun _ => c := by
  intro k
  rcases k with _ | k
  · simpa using hc
  · rw [Function.iterate_succ_apply, fwdDiff_const, Function.iterate_fixed (by simp)]
    simp only [norm_zero]
    positivity

/-- **Differencing gains `α`.** -/
theorem Decay.diff {α a : ℝ} {f : ℕ → ℚ_[p]} (hf : Decay p α a f) : Decay p α (a + α) (fwdDiff 1 f) :=
  fun k => by
    rw [← Function.iterate_succ_apply]
    refine (hf (k + 1)).trans (le_of_eq ?_)
    push_cast
    ring_nf

/-- **Shifting** `e ↦ f(e + 1)` keeps the decay (`α ≥ 0`): `Δ^k f(1) = Δ^k f(0) + Δ^{k+1} f(0)`. -/
theorem Decay.shift {α a : ℝ} {f : ℕ → ℚ_[p]} (hf : Decay p α a f) (hα : 0 ≤ α) :
    Decay p α a fun e => f (e + 1) := fun k => by
  rw [fwdDiff_iter_comp_add, zero_add]
  have : (fwdDiff 1)^[k] f 1 = (fwdDiff 1)^[k] f 0 + (fwdDiff 1)^[k + 1] f 0 := by
    rw [Function.iterate_succ_apply', fwdDiff]
    simp
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf k) ((hf (k + 1)).trans (rpow_anti ?_)))
  push_cast
  nlinarith

/-- **The binomial product coefficients vanish above the degree**:
`Σ_{m ≤ k} (−1)^{k−m} C(k, m)·C(m, i)·C(m, j) = 0` for `i + j < k` (`Δ^k` kills `C(x, i)·C(x, j)`, a polynomial
of degree `i + j`). -/
theorem sum_choose_mul_choose_eq_zero {i j k : ℕ} (h : i + j < k) :
    ∑ m ∈ range (k + 1), ((-1) ^ (k - m) * (k.choose m : ℤ)) * ((m.choose i : ℤ) * m.choose j) = 0 := by
  set P : Polynomial ℚ :=
    descPochhammer ℚ i * descPochhammer ℚ j * Polynomial.C ((i.factorial * j.factorial : ℚ)⁻¹)
  have hdeg : P.natDegree < k := by
    refine lt_of_le_of_lt (Polynomial.natDegree_mul_C_le _ _) (lt_of_le_of_lt Polynomial.natDegree_mul_le ?_)
    rw [descPochhammer_natDegree, descPochhammer_natDegree]
    exact h
  have h0 := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at h0
  have heval : ∀ m : ℕ, P.eval (m : ℚ) = (m.choose i : ℚ) * m.choose j := by
    intro m
    simp only [P, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  have : ((∑ m ∈ range (k + 1), ((-1) ^ (k - m) * (k.choose m : ℤ)) * ((m.choose i : ℤ) * m.choose j) : ℤ) :
      ℚ) = 0 := by
    rw [← h0]
    push_cast
    refine sum_congr rfl fun m _ => ?_
    rw [zsmul_eq_mul, zero_add, nsmul_eq_mul, mul_one, heval]
    push_cast
    ring
  exact_mod_cast this

/-- **Products** (`α ≥ 0`): offsets add. Expanding `f` and `g` by Newton, `Δ^k(fg)(0) = Σ_{i,j ≤ k} Δ^i f(0)·Δ^j g(0)·γ`
with integers `γ` that vanish for `i + j < k`. -/
theorem Decay.mul {α a b : ℝ} {f g : ℕ → ℚ_[p]} (hf : Decay p α a f) (hg : Decay p α b g) (hα : 0 ≤ α) :
    Decay p α (a + b) (f * g) := fun k => by
  have hexp : (fwdDiff 1)^[k] (f * g) 0 = ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      (fwdDiff 1)^[i] f 0 * (fwdDiff 1)^[j] g 0 * ((∑ m ∈ range (k + 1),
        ((-1) ^ (k - m) * (k.choose m : ℤ)) * ((m.choose i : ℤ) * m.choose j) : ℤ) : ℚ_[p]) := by
    rw [fwdDiff_iter_zero]
    have hm : ∀ m ∈ range (k + 1), ((-1) ^ (k - m) * (k.choose m : ℤ)) • (f * g) m =
        ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), (fwdDiff 1)^[i] f 0 * (fwdDiff 1)^[j] g 0 *
          ((((-1) ^ (k - m) * (k.choose m : ℤ)) * ((m.choose i : ℤ) * m.choose j) : ℤ) : ℚ_[p]) := by
      intro m hm
      have hmk : m ≤ k := by simp only [mem_range] at hm; omega
      rw [Pi.mul_apply, newton f hmk, newton g hmk, sum_mul_sum, smul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [smul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [sum_congr rfl hm, sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sum]
    push_cast
    rfl
  rw [hexp]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  by_cases hij : i + j < k
  · rw [sum_choose_mul_choose_eq_zero hij, Int.cast_zero, mul_zero, norm_zero]
    positivity
  · rw [norm_mul, norm_mul]
    calc _ ≤ ‖(fwdDiff 1)^[i] f 0‖ * ‖(fwdDiff 1)^[j] g 0‖ :=
          mul_le_of_le_one_right (by positivity) (Padic.norm_int_le_one _)
      _ ≤ (p : ℝ) ^ (-(α * i + a)) * (p : ℝ) ^ (-(α * j + b)) :=
          mul_le_mul (hf i) (hg j) (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (-(α * (i + j : ℕ) + (a + b))) := by
          rw [← Real.rpow_add (by have := one_le_p hp; linarith)]
          push_cast
          ring_nf
      _ ≤ _ := rpow_anti (by
          have : (k : ℝ) ≤ (i + j : ℕ) := by exact_mod_cast not_lt.1 hij
          nlinarith)

/-- **The constant `1`.** -/
theorem decay_one {α : ℝ} : Decay p α 0 fun _ => (1 : ℚ_[p]) :=
  decay_const (c := (1 : ℚ_[p])) (by rw [neg_zero, Real.rpow_zero, norm_one])

/-- **Powers** (`α ≥ 0`): `f^n` decays with offset `n·a`. -/
theorem Decay.pow {α a : ℝ} {f : ℕ → ℚ_[p]} (hf : Decay p α a f) (hα : 0 ≤ α) (n : ℕ) :
    Decay p α (n * a) (f ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using decay_one
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hf hα using 1
    push_cast
    ring

/-- **Finite sums.** -/
theorem decay_sum {ι : Type*} (s : Finset ι) {α a : ℝ} {f : ι → ℕ → ℚ_[p]} (hf : ∀ i ∈ s, Decay p α a (f i)) :
    Decay p α a (∑ i ∈ s, f i) := fun k => by
  rw [fwdDiff_iter_finsetSum, Finset.sum_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => hf i hi k

/-- **Inverses** (`α ≥ 0`, `a > 0`): if `H` decays with offset `a`, then `(1 + H)⁻¹` decays with offset `0`
(the geometric series to an order `N` with `aN ≥ αk`; the remainder `(−H)^N/(1 + H)` is pointwise `≤ p^{−aN}`). -/
theorem Decay.inv_one_add {α a : ℝ} {H : ℕ → ℚ_[p]} (hH : Decay p α a H) (hα : 0 ≤ α) (ha : 0 < a) :
    Decay p α 0 fun e => (1 + H e)⁻¹ := fun k => by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, α * k ≤ a * N := by
    obtain ⟨N, hN⟩ := exists_nat_ge (α * k / a)
    exact ⟨N, by rw [div_le_iff₀ ha] at hN; linarith⟩
  have hHn : ∀ e, ‖H e‖ ≤ (p : ℝ) ^ (-a) := hH.norm_le hα
  have hlt : (p : ℝ) ^ (-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.out.one_lt) (by linarith)
  have hunit : ∀ e, ‖1 + H e‖ = 1 := fun e => by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact (lt_of_le_of_lt (hHn e) hlt).ne'),
      norm_one]
    exact max_eq_left (le_trans (hHn e) hlt.le)
  have hne : ∀ e, 1 + H e ≠ 0 := fun e h => by
    have := hunit e
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set S : ℕ → ℚ_[p] := ∑ n ∈ range N, (-H) ^ n
  set R : ℕ → ℚ_[p] := fun e => (-H e) ^ N * (1 + H e)⁻¹
  have hsplit : (fun e => (1 + H e)⁻¹) = S + R := by
    funext e
    simp only [S, R, Pi.add_apply, Finset.sum_apply, Pi.pow_apply, Pi.neg_apply]
    have key : (∑ n ∈ range N, (-H e) ^ n) * (1 + H e) = 1 - (-H e) ^ N := by
      have := geom_sum_mul (-H e) N
      linear_combination -this
    have h1 : (1 + H e) * (1 + H e)⁻¹ = 1 := mul_inv_cancel₀ (hne e)
    linear_combination (-(1 + H e)⁻¹) * key + (∑ n ∈ range N, (-H e) ^ n) * h1
  have hS : Decay p α 0 S := decay_sum _ fun n _ => ((hH.neg.pow hα n).mono le_rfl (by positivity))
  have hR : ‖(fwdDiff 1)^[k] R 0‖ ≤ (p : ℝ) ^ (-(a * N)) := by
    refine norm_fwdDiff_iter_le (by positivity) k fun m _ => ?_
    simp only [R, norm_mul, norm_pow, norm_neg, norm_inv, hunit, inv_one, mul_one]
    rw [show -(a * N) = -a * N by ring, Real.rpow_mul_natCast (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hHn m) N
  rw [hsplit, fwdDiff_iter_add, Pi.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hS k) (hR.trans (rpow_anti ?_)))
  linarith

/-- **The difference quotients of a running product** `F(e) = ∏_{i<e}(1 + H(i))`: `Q_0 = 1`,
`Q_{j+1} = ΔQ_j + H·Q_j(· + 1)`, so that `Δ^j F = F·Q_j` (`fwdDiff_iter_prod`). -/
def qSeq (H : ℕ → ℚ_[p]) : ℕ → ℕ → ℚ_[p]
  | 0 => fun _ => 1
  | j + 1 => _root_.fwdDiff 1 (qSeq H j) + H * fun e => qSeq H j (e + 1)

/-- **`Δ^j F = F·Q_j`** for `F(e) = ∏_{i<e}(1 + H(i))`: `F(e + 1) = F(e)(1 + H(e))`. -/
theorem fwdDiff_iter_prod (H : ℕ → ℚ_[p]) (j e : ℕ) :
    (fwdDiff 1)^[j] (fun e => ∏ i ∈ range e, (1 + H i)) e = (∏ i ∈ range e, (1 + H i)) * qSeq H j e := by
  induction j generalizing e with
  | zero => simp [qSeq]
  | succ j ih =>
    rw [Function.iterate_succ_apply', _root_.fwdDiff, ih, ih, prod_range_succ]
    simp only [qSeq, Pi.add_apply, Pi.mul_apply, _root_.fwdDiff]
    ring

/-- **Running products** (`α ≥ 0`): if `H` decays with offset `α`, then `∏_{i<e}(1 + H(i))` decays with offset `0`
(`Q_j` decays with offset `αj`, and `Δ^j F(0) = Q_j(0)`). -/
theorem Decay.prod_range {α : ℝ} {H : ℕ → ℚ_[p]} (hH : Decay p α α H) (hα : 0 ≤ α) :
    Decay p α 0 fun e => ∏ i ∈ range e, (1 + H i) := fun k => by
  have hq : ∀ j : ℕ, Decay p α (α * j) (qSeq H j) := by
    intro j
    induction j with
    | zero => simpa [qSeq] using decay_one
    | succ j ih =>
      have h1 := ih.diff
      have h2 := hH.mul (ih.shift hα) hα
      exact (h1.mono le_rfl (by push_cast; linarith)).add (h2.mono le_rfl (by push_cast; linarith))
  rw [fwdDiff_iter_prod, prod_range_zero, one_mul]
  refine ((hq k) 0).trans (le_of_eq ?_)
  simp

/-- **Products of `1 + h_z`** (`α, a ≥ 0`): if every `h_z` decays with offset `a`, so does `∏_z (1 + h_z) − 1`. -/
theorem decay_prod_one_add_sub_one {ι : Type*} (s : Finset ι) {α a : ℝ} (hα : 0 ≤ α) (ha : 0 ≤ a)
    {h : ι → ℕ → ℚ_[p]} (hh : ∀ z ∈ s, Decay p α a (h z)) :
    Decay p α a fun e => ∏ z ∈ s, (1 + h z e) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using decay_const (α := α) (c := (0 : ℚ_[p])) (by rw [norm_zero]; positivity)
  | insert z s hz ih =>
    have ih' := ih fun y hy => hh y (mem_insert_of_mem hy)
    have hP : Decay p α 0 fun e => ∏ y ∈ s, (1 + h y e) := by
      have := (ih'.mono le_rfl ha).add decay_one
      convert this using 1
      funext e
      simp
    have := ((hh z (mem_insert_self z s)).mul hP hα).add (ih'.mono le_rfl (by simp))
    convert this using 2
    · simp
    · simp only [Pi.add_apply, Pi.mul_apply, prod_insert hz]
      ring

/-- **Linear functions** `e ↦ u·e` with `‖u‖ ≤ p^{−1}` decay at rate `1/2` with offset `1/2`. -/
theorem decay_linear {u : ℚ_[p]} (hu : ‖u‖ ≤ (p : ℝ)⁻¹) : Decay p (1 / 2) (1 / 2) fun e => u * e := fun k => by
  have h1 : _root_.fwdDiff 1 (fun e : ℕ => u * e) = fun _ => u := by
    funext e
    simp [_root_.fwdDiff]
    ring
  rcases k with _ | _ | k
  · simp only [Function.iterate_zero, id, Nat.cast_zero, mul_zero, norm_zero]
    positivity
  · rw [Function.iterate_one, h1]
    refine hu.trans (le_of_eq ?_)
    norm_num [Real.rpow_neg_one]
  · rw [Function.iterate_succ_apply, h1, Function.iterate_succ_apply, fwdDiff_const,
      Function.iterate_fixed (by simp)]
    simp only [norm_zero]
    positivity

end Decay

/-! ## Factorial units -/

section Units

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The factor of `c_P`**: `g(i) = ∏_{1 ≤ y < P} (1 + P·i/y)`, `P = p^s`. -/
def gFac (s i : ℕ) : ℚ_[p] := ∏ y ∈ range (p ^ s - 1), (1 + (p : ℚ_[p]) ^ s / (y + 1) * i)

/-- **`c_P(e) = (Pe)!/((P!)^e·e!) = ∏_{i<e} g(i)`** (`factorial_mul_eq`). -/
def cUnit (s e : ℕ) : ℚ_[p] := ∏ i ∈ range e, gFac p s i

/-- **`d_{P,ρ}(e) = C(Pe + ρ, ρ) = ∏_{1 ≤ y ≤ ρ} (1 + P·e/y)`**. -/
def dUnit (s ρ e : ℕ) : ℚ_[p] := ∏ y ∈ range ρ, (1 + (p : ℚ_[p]) ^ s / (y + 1) * e)

/-- **The factorial unit** `u(e) = c_P(e)·d_{P,ρ}(e)`: `(ρ + Pe)! = ρ!·e!·(P!)^e·u(e)` (`factorial_eq_unit`). -/
def fUnit (s ρ e : ℕ) : ℚ_[p] := cUnit p s e * dUnit p s ρ e

/-- **Factorials of a sum**: `(n + k)! = n!·∏_{y<k} (n + y + 1)`. -/
theorem factorial_add_eq (n k : ℕ) :
    ((n + k).factorial : ℚ_[p]) = n.factorial * ∏ y ∈ range k, ((n : ℚ_[p]) + y + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, Nat.cast_mul, ih, prod_range_succ]
    push_cast
    ring

/-- **`(y + 1)·(1 + P·x/(y + 1)) = y + 1 + P·x`.** -/
theorem succ_mul_one_add (y : ℕ) (P x : ℚ_[p]) : ((y : ℚ_[p]) + 1) * (1 + P / (y + 1) * x) = y + 1 + P * x := by
  have : (y : ℚ_[p]) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero y
  field_simp

/-- **`(Pe)! = (P!)^e·e!·c_P(e)`.** -/
theorem factorial_mul_eq (s e : ℕ) :
    ((p ^ s * e).factorial : ℚ_[p]) = ((p ^ s).factorial : ℚ_[p]) ^ e * e.factorial * cUnit p s e := by
  have hP : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.out.pos
  induction e with
  | zero => simp [cUnit]
  | succ e ih =>
    have hg : gFac p s e * ((p ^ s - 1).factorial : ℚ_[p]) =
        ∏ y ∈ range (p ^ s - 1), (((p ^ s * e : ℕ) : ℚ_[p]) + y + 1) := by
      rw [gFac, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← prod_mul_distrib]
      refine prod_congr rfl fun y _ => ?_
      rw [mul_comm]
      push_cast
      rw [succ_mul_one_add]
      ring
    have hl : ((p ^ s * e : ℕ) : ℚ_[p]) + ((p ^ s - 1 : ℕ) : ℚ_[p]) + 1 = ((p ^ s : ℕ) : ℚ_[p]) * (e + 1) := by
      rw [Nat.cast_sub hP]
      push_cast
      ring
    have hf : (((p ^ s).factorial : ℕ) : ℚ_[p]) = ((p ^ s : ℕ) : ℚ_[p]) * (p ^ s - 1).factorial := by
      conv_lhs => rw [show p ^ s = p ^ s - 1 + 1 by omega, Nat.factorial_succ, Nat.sub_add_cancel hP]
      push_cast
      ring
    rw [mul_add, mul_one, factorial_add_eq, ih, show range (p ^ s) = range (p ^ s - 1 + 1) by
      rw [Nat.sub_add_cancel hP], prod_range_succ, ← hg, hl]
    unfold cUnit
    rw [prod_range_succ, Nat.factorial_succ, pow_succ, hf]
    push_cast
    ring

/-- **The factorisation** `(ρ + Pe)! = ρ!·e!·(P!)^e·u(e)`. -/
theorem factorial_eq_unit (s ρ e : ℕ) :
    ((ρ + p ^ s * e).factorial : ℚ_[p]) =
      ρ.factorial * e.factorial * ((p ^ s).factorial : ℚ_[p]) ^ e * fUnit p s ρ e := by
  rw [add_comm, factorial_add_eq, factorial_mul_eq, fUnit, dUnit, ← Finset.prod_range_add_one_eq_factorial ρ,
    Nat.cast_prod]
  have : ∏ y ∈ range ρ, (((p ^ s * e : ℕ) : ℚ_[p]) + y + 1) =
      (∏ y ∈ range ρ, ((y + 1 : ℕ) : ℚ_[p])) * ∏ y ∈ range ρ, (1 + (p : ℚ_[p]) ^ s / (y + 1) * e) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun y _ => ?_
    push_cast
    rw [succ_mul_one_add]
    ring
  rw [this]
  ring

/-- **`‖P/y‖ ≤ p^{−1}`** for `1 ≤ y < P = p^s` (`v_p(y) ≤ s − 1`). -/
theorem norm_pow_div_le {s y : ℕ} (hy : y + 1 < p ^ s) : ‖(p : ℚ_[p]) ^ s / (y + 1)‖ ≤ (p : ℝ)⁻¹ := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hlow : (p : ℝ) ^ (-(s : ℤ) + 1) ≤ ‖((y : ℚ_[p]) + 1)‖ := by
    by_contra! hlt
    have h1 := (Padic.norm_le_pow_iff_norm_lt_pow_add_one ((y : ℚ_[p]) + 1) (-(s : ℤ))).2 hlt
    have h2 : ‖(((y + 1 : ℕ) : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(s : ℤ)) := by push_cast; exact h1
    rw [show (-(s : ℤ)) = -((s : ℕ) : ℤ) from rfl, Padic.norm_int_le_pow_iff_dvd] at h2
    have := Int.le_of_dvd (by positivity) h2
    have h3 : ((p ^ s : ℕ) : ℤ) ≤ ((y + 1 : ℕ) : ℤ) := by push_cast; exact this
    omega
  rw [norm_div, Padic.norm_p_pow, div_le_iff₀ (lt_of_lt_of_le (by positivity) hlow)]
  calc (p : ℝ) ^ (-(s : ℤ)) = (p : ℝ)⁻¹ * (p : ℝ) ^ (-(s : ℤ) + 1) := by
        rw [zpow_add_one₀ hpos.ne']
        field_simp
    _ ≤ (p : ℝ)⁻¹ * ‖((y : ℚ_[p]) + 1)‖ := by gcongr

/-- **`g − 1` decays** at rate `1/2` with offset `1/2`. -/
theorem decay_gFac (s : ℕ) : Decay p (1 / 2) (1 / 2) fun i => gFac p s i - 1 :=
  decay_prod_one_add_sub_one _ (by norm_num) (by norm_num) fun y hy =>
    decay_linear (norm_pow_div_le p (by simp only [mem_range] at hy; omega))

/-- **`d − 1` decays** at rate `1/2` with offset `1/2` (`ρ < P`). -/
theorem decay_dUnit_sub {s ρ : ℕ} (hρ : ρ < p ^ s) : Decay p (1 / 2) (1 / 2) fun e => dUnit p s ρ e - 1 :=
  decay_prod_one_add_sub_one _ (by norm_num) (by norm_num) fun y hy =>
    decay_linear (norm_pow_div_le p (by simp only [mem_range] at hy; omega))

/-- **An element within `p^{−1/2}` of `1` is nonzero.** -/
theorem ne_zero_of_decay {f : ℕ → ℚ_[p]} (hf : Decay p (1 / 2) (1 / 2) fun e => f e - 1) (e : ℕ) : f e ≠ 0 := by
  intro h
  have h1 := hf.norm_le (by norm_num) e
  rw [h, zero_sub, norm_neg, norm_one] at h1
  have : (p : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.out.one_lt) (by norm_num)
  linarith

/-- **Inverses of `1 + H`, minus `1`**: `(1 + H)⁻¹ − 1 = −H·(1 + H)⁻¹` decays like `H` (offset `1/2`). -/
theorem decay_inv_sub_one {f : ℕ → ℚ_[p]} (hf : Decay p (1 / 2) (1 / 2) fun e => f e - 1) :
    Decay p (1 / 2) (1 / 2) fun e => (f e)⁻¹ - 1 := by
  have hi := hf.inv_one_add (by norm_num) (by norm_num)
  have := hf.neg.mul hi (by norm_num)
  rw [add_zero] at this
  convert this using 1
  funext e
  have hne := ne_zero_of_decay p hf e
  simp only [Pi.mul_apply, Pi.neg_apply, add_sub_cancel]
  field_simp
  ring

/-- **`c_P` decays** at rate `1/2` (offset `0`). -/
theorem decay_cUnit (s : ℕ) : Decay p (1 / 2) 0 (cUnit p s) :=
  ((decay_gFac p s).prod_range (by norm_num)).congr fun e => by simp [cUnit]

/-- **`c_P⁻¹` decays** at rate `1/2`. -/
theorem decay_cUnit_inv (s : ℕ) : Decay p (1 / 2) 0 fun e => (cUnit p s e)⁻¹ :=
  ((decay_inv_sub_one p (decay_gFac p s)).prod_range (by norm_num)).congr fun e => by
    simp [cUnit, prod_inv_distrib]

/-- **`d_{P,ρ}` decays** at rate `1/2` (`ρ < P`). -/
theorem decay_dUnit {s ρ : ℕ} (hρ : ρ < p ^ s) : Decay p (1 / 2) 0 (dUnit p s ρ) :=
  (((decay_dUnit_sub p hρ).mono le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)).add decay_one).congr fun e => by simp

/-- **`d_{P,ρ}⁻¹` decays** at rate `1/2` (`ρ < P`). -/
theorem decay_dUnit_inv {s ρ : ℕ} (hρ : ρ < p ^ s) : Decay p (1 / 2) 0 fun e => (dUnit p s ρ e)⁻¹ :=
  (((decay_inv_sub_one p (decay_dUnit_sub p hρ)).mono le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
    decay_one).congr fun e => by simp

/-- **The unit `u = c_P·d_{P,ρ}` decays** at rate `1/2` (`ρ < P`): `‖Δ^k u(0)‖ ≤ p^{−k/2}`. -/
theorem decay_fUnit {s ρ : ℕ} (hρ : ρ < p ^ s) : Decay p (1 / 2) 0 (fUnit p s ρ) :=
  (((decay_cUnit p s).mul (decay_dUnit p hρ) (by norm_num)).mono le_rfl (by norm_num)).congr fun e => rfl

/-- **The inverse unit `u⁻¹` decays** at rate `1/2` (`ρ < P`). -/
theorem decay_fUnit_inv {s ρ : ℕ} (hρ : ρ < p ^ s) : Decay p (1 / 2) 0 fun e => (fUnit p s ρ e)⁻¹ :=
  (((decay_cUnit_inv p s).mul (decay_dUnit_inv p hρ) (by norm_num)).mono le_rfl (by norm_num)).congr fun e => by
    simp [fUnit, mul_comm]

/-- **`u(e)` is a `p`-adic unit**: `‖u(e)‖ = 1` (`ρ < P`). -/
theorem norm_fUnit {s ρ : ℕ} (hρ : ρ < p ^ s) (e : ℕ) : ‖fUnit p s ρ e‖ = 1 := by
  have h1 := (decay_fUnit p hρ).norm_le (by norm_num) e
  have h2 := (decay_fUnit_inv p hρ).norm_le (by norm_num) e
  rw [neg_zero, Real.rpow_zero] at h1 h2
  have hne : fUnit p s ρ e ≠ 0 := by
    intro h
    have := factorial_eq_unit p s ρ e
    rw [h, mul_zero] at this
    exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _) this
  rw [norm_inv] at h2
  have hpos : 0 < ‖fUnit p s ρ e‖ := norm_pos_iff.2 hne
  have := (inv_le_one₀ hpos).1 h2
  linarith

/-- **Binomial approximation** (N16(d), T7): a product `∏_l f_l(e_l)` of functions decaying at rate `α > 0` is,
modulo `p^c`, an integral combination of the `∏_l C(e_l, J_l)` with `Σ_l J_l < D`, as soon as `αD ≥ c`
(Newton in each variable; the terms with `Σ_l J_l ≥ D` are `≤ p^{−αD}`). With `decay_fUnit`, `decay_fUnit_inv`:
`α = 1/2`, `D = 2c`. -/
theorem exists_binomial_approx {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ} (hα : 0 < α)
    (f : ι → ℕ → ℚ_[p]) (hf : ∀ l, Decay p α 0 (f l)) {c : ℝ} {D : ℕ} (hD : c ≤ α * D) :
    ∃ q : (ι → ℕ) → ℚ_[p], (∀ J, ‖q J‖ ≤ 1) ∧ ∀ e : ι → ℕ,
      ‖∏ l, f l (e l) - ∑ J ∈ (Fintype.piFinset fun _ : ι => range D).filter (fun J => ∑ l, J l < D),
        q J * ∏ l, ((e l).choose (J l) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-c) := by
  have hA : ∀ l k, ‖(fwdDiff 1)^[k] (f l) 0‖ ≤ (p : ℝ) ^ (-(α * k)) := fun l k => by
    simpa using hf l k
  have hA1 : ∀ l k, ‖(fwdDiff 1)^[k] (f l) 0‖ ≤ 1 := fun l k =>
    (hA l k).trans (Real.rpow_le_one_of_one_le_of_nonpos (one_le_p hp) (by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      nlinarith))
  refine ⟨fun J => ∏ l, (fwdDiff 1)^[J l] (f l) 0, fun J => ?_, fun e => ?_⟩
  · rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun l _ => hA1 l (J l)
  have hle : ∀ (J : ι → ℕ) (l : ι), J l ≤ ∑ l, J l := fun J l =>
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ l)
  set N := D + ∑ l, e l
  have hexp : ∏ l, f l (e l) = ∑ J ∈ Fintype.piFinset (fun _ : ι => range (N + 1)),
      ∏ l, ((e l).choose (J l) : ℚ_[p]) * (fwdDiff 1)^[J l] (f l) 0 := by
    rw [← Finset.prod_univ_sum (fun _ => range (N + 1))
      fun l k => ((e l).choose k : ℚ_[p]) * (fwdDiff 1)^[k] (f l) 0]
    exact prod_congr rfl fun l _ => newton (f l) (by have := hle e l; omega)
  rw [hexp, ← sum_filter_add_sum_filter_not _ (fun J => ∑ l, J l < D)]
  have hfil : (Fintype.piFinset fun _ : ι => range (N + 1)).filter (fun J => ∑ l, J l < D) =
      (Fintype.piFinset fun _ : ι => range D).filter (fun J => ∑ l, J l < D) := by
    ext J
    simp only [mem_filter, Fintype.mem_piFinset, mem_range]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨fun l => lt_of_le_of_lt (hle J l) h, h⟩
    · rintro ⟨-, h⟩
      exact ⟨fun l => by have := hle J l; omega, h⟩
  have hsame : ∑ J ∈ (Fintype.piFinset fun _ : ι => range D).filter (fun J => ∑ l, J l < D),
      ∏ l, ((e l).choose (J l) : ℚ_[p]) * (fwdDiff 1)^[J l] (f l) 0 =
      ∑ J ∈ (Fintype.piFinset fun _ : ι => range D).filter (fun J => ∑ l, J l < D),
        (∏ l, (fwdDiff 1)^[J l] (f l) 0) * ∏ l, ((e l).choose (J l) : ℚ_[p]) := by
    refine sum_congr rfl fun J _ => ?_
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun l _ => mul_comm _ _
  rw [hfil, hsame, add_sub_cancel_left]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun J hJ => ?_
  simp only [mem_filter, not_lt] at hJ
  rw [norm_prod]
  calc ∏ l, ‖((e l).choose (J l) : ℚ_[p]) * (fwdDiff 1)^[J l] (f l) 0‖
      ≤ ∏ l, (p : ℝ) ^ (-(α * J l)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => (norm_natCast_mul_le _ _).trans (hA l (J l))
    _ = (p : ℝ) ^ (-(α * (∑ l, J l : ℕ))) := by
        rw [← Real.rpow_sum_of_pos (by have := one_le_p hp; linarith)]
        push_cast
        rw [mul_sum, ← sum_neg_distrib]
    _ ≤ (p : ℝ) ^ (-c) := rpow_anti (le_trans hD (by
        have : (D : ℝ) ≤ (∑ l, J l : ℕ) := by exact_mod_cast hJ.2
        nlinarith))

end Units

/-! ## Jordan splitting -/

section Jordan

variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M] [Module R M]

/-- **A divisibility-minimal diagonal value** (`2` a unit): a nonzero symmetric form on a free module has a vector
`x` with `B(x, x) ≠ 0` dividing every `B(y, z)`. Take an entry `g = B(b_i, b_j)` of minimal valuation; if no diagonal
entry divides it, then `x = b_i + b_j` has `B(x, x) = g·(a + 2 + c)` with `a, c` in the maximal ideal. -/
theorem exists_self_dvd (h2 : IsUnit (2 : R)) {ι : Type*} [Fintype ι] (b : Module.Basis ι R M)
    {B : LinearMap.BilinForm R M} (hB : B.IsSymm) (hB0 : B ≠ 0) :
    ∃ x, B x x ≠ 0 ∧ ∀ y z, B x x ∣ B y z := by
  classical
  set G : ι × ι → R := fun ij => B (b ij.1) (b ij.2)
  have hne : ∃ ij, G ij ≠ 0 := by
    by_contra! h
    exact hB0 (LinearMap.BilinForm.ext_basis b fun i j => by simpa [G] using h (i, j))
  obtain ⟨ij0, hij0⟩ := hne
  obtain ⟨ij, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun ij => IsDiscreteValuationRing.addVal R (G ij)) ⟨ij0, Finset.mem_univ _⟩
  have hdvd : ∀ ij', G ij ∣ G ij' := fun ij' =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.1 (hmin ij' (Finset.mem_univ _))
  have hg0 : G ij ≠ 0 := fun h => hij0 (zero_dvd_iff.1 (h ▸ hdvd ij0))
  -- every value is a multiple of the entries
  have hall : ∀ g : R, (∀ ij', g ∣ G ij') → ∀ y z, g ∣ B y z := by
    intro g hg y z
    rw [← LinearMap.BilinForm.sum_repr_mul_repr_mul b y z]
    exact Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => by
      simp only [smul_eq_mul]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (hg (i, j)) _) _
  by_cases hd : ∃ i, G (i, i) ∣ G ij
  · obtain ⟨i, hi⟩ := hd
    refine ⟨b i, fun h => hg0 (zero_dvd_iff.1 (h ▸ hi)), hall _ fun ij' => hi.trans (hdvd ij')⟩
  · push Not at hd
    obtain ⟨i, j⟩ := ij
    have hij : i ≠ j := by
      rintro rfl
      exact hd i dvd_rfl
    obtain ⟨a, ha⟩ := hdvd (i, i)
    obtain ⟨c, hc⟩ := hdvd (j, j)
    have hna : ¬ IsUnit a := fun hu => hd i ⟨↑hu.unit⁻¹, by rw [ha, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
    have hnc : ¬ IsUnit c := fun hu => hd j ⟨↑hu.unit⁻¹, by rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
    have hu : IsUnit (a + 2 + c) := by
      by_contra hu
      have h1 : a + 2 + c ∈ IsLocalRing.maximalIdeal R := hu
      have h2' : a + c ∈ IsLocalRing.maximalIdeal R := Ideal.add_mem _ hna hnc
      have : (2 : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ h1 h2'
        rwa [show a + 2 + c - (a + c) = 2 by ring] at this
      exact this h2
    have hxx : B (b i + b j) (b i + b j) = G (i, j) * (a + 2 + c) := by
      have hs : B (b j) (b i) = G (i, j) := hB.eq _ _
      simp only [map_add, LinearMap.add_apply]
      rw [hs]
      simp only [G] at ha hc ⊢
      rw [ha, hc]
      ring
    refine ⟨b i + b j, by rw [hxx]; exact mul_ne_zero hg0 hu.ne_zero, hall _ fun ij' => ?_⟩
    rw [hxx]
    exact (mul_dvd_mul_left _ hu.dvd).trans ((mul_one (G (i, j))).symm ▸ hdvd ij')

/-- **Orthogonal (Jordan) splitting** (B6): over a discrete valuation ring with `2` a unit (`ℤ_p`, `p` odd), a
symmetric bilinear form on a free module of rank `d` has an orthogonal basis. Split off `x` with `B(x, x)` dividing
every value (`exists_self_dvd`): `M = R·x ⊕ x^⊥`, and `x^⊥` is free (a PID) of rank `d − 1`. -/
theorem exists_orthogonal_basis (h2 : IsUnit (2 : R)) (d : ℕ) (b : Module.Basis (Fin d) R M)
    {B : LinearMap.BilinForm R M} (hB : B.IsSymm) :
    ∃ v : Module.Basis (Fin d) R M, ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  induction d generalizing M with
  | zero => exact ⟨b, fun i => i.elim0⟩
  | succ d ih =>
    by_cases hB0 : B = 0
    · exact ⟨b, fun i j _ => by simp [hB0]⟩
    obtain ⟨x, hx0, hx⟩ := exists_self_dvd h2 b hB hB0
    set N := LinearMap.ker (B x)
    have hli : ∀ (c : R), ∀ y ∈ N, c • x + y = 0 → c = 0 := by
      intro c y hy h
      have : B x (c • x + y) = 0 := by rw [h, map_zero]
      rw [map_add, map_smul, LinearMap.mem_ker.1 hy, add_zero, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_right hx0
    have hsp : ∀ z : M, ∃ c : R, z + c • x ∈ N := by
      intro z
      obtain ⟨q, hq⟩ := hx x z
      refine ⟨-q, LinearMap.mem_ker.2 ?_⟩
      rw [map_add, map_smul, hq, smul_eq_mul]
      ring
    obtain ⟨n, bN⟩ := Submodule.basisOfPid b N
    have hn : n = d := by
      have := Fintype.card_congr (b.indexEquiv (Module.Basis.mkFinCons x bN hli hsp))
      simpa using this.symm
    subst hn
    obtain ⟨v', hv'⟩ := ih bN (B := B.restrict N) (hB.restrict N)
    refine ⟨Module.Basis.mkFinCons x v' hli hsp, fun i j => ?_⟩
    rw [Module.Basis.coe_mkFinCons]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
    · exact (hij rfl).elim
    · exact LinearMap.mem_ker.1 (v' j).prop
    · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
      rw [hB.eq]
      exact LinearMap.mem_ker.1 (v' i).prop
    · simp only [Fin.cons_succ, Function.comp_apply]
      exact hv' i j fun h => hij (by rw [h])

/-- **Jordan splitting, matrix form**: a symmetric matrix over a discrete valuation ring with `2` a unit is
congruent to a diagonal matrix, `Uᵀ·S·U = diag(d)` with `det U` a unit. -/
theorem exists_diagonal_congr (h2 : IsUnit (2 : R)) {n : ℕ} (S : Matrix (Fin n) (Fin n) R) (hS : S.IsSymm) :
    ∃ U : Matrix (Fin n) (Fin n) R, IsUnit U.det ∧ ∃ d : Fin n → R, U.transpose * S * U = Matrix.diagonal d := by
  classical
  have hB : (Matrix.toBilin' S).IsSymm := ⟨fun x y => by
    simp only [Matrix.toBilin'_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hS.apply j i]
    ring⟩
  obtain ⟨v, hv⟩ := exists_orthogonal_basis h2 n (Pi.basisFun R (Fin n)) hB
  refine ⟨(Pi.basisFun R (Fin n)).toMatrix v, ?_, fun i => Matrix.toBilin' S (v i) (v i), ?_⟩
  · have := (Pi.basisFun R (Fin n)).invertibleToMatrix v
    exact Matrix.isUnit_det_of_invertible _
  · ext i j
    have key : (((Pi.basisFun R (Fin n)).toMatrix v).transpose * S * (Pi.basisFun R (Fin n)).toMatrix v) i j =
        Matrix.toBilin' S (v i) (v j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
        Matrix.toBilin'_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [key, Matrix.diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact hv i j h

end Jordan

/-! ## Gauss norms -/

section GaussNorm

open Polynomial

variable {K : Type*} [NormedField K]

variable (K) in
/-- **The norm as an absolute value.** -/
def nabs : AbsoluteValue K ℝ := IsAbsoluteValue.toAbsoluteValue (norm : K → ℝ)

/-- **`nabs` is the norm.** -/
theorem nabs_apply (x : K) : nabs K x = ‖x‖ := IsAbsoluteValue.toAbsoluteValue_apply _ x

/-- **The Gauss norm at radius `c`**: `‖P‖_c = max_i ‖P_i‖·c^i`. -/
abbrev gN (c : ℝ) (P : K[X]) : ℝ := P.gaussNorm (nabs K) c

/-- **Gauss norms are nonnegative** (`c ≥ 0`). -/
theorem gN_nonneg {c : ℝ} (hc : 0 ≤ c) (P : K[X]) : 0 ≤ gN c P := P.gaussNorm_nonneg _ hc

/-- **Coefficients bound the Gauss norm below.** -/
theorem coeff_le_gN {c : ℝ} (hc : 0 ≤ c) (P : K[X]) (i : ℕ) : ‖P.coeff i‖ * c ^ i ≤ gN c P := by
  rw [← nabs_apply]
  exact P.le_gaussNorm _ hc i

/-- **Coefficient bounds give Gauss-norm bounds.** -/
theorem gN_le {c B : ℝ} (hB : 0 ≤ B) {P : K[X]} (h : ∀ i, ‖P.coeff i‖ * c ^ i ≤ B) : gN c P ≤ B := by
  show P.gaussNorm (nabs K) c ≤ B
  unfold Polynomial.gaussNorm
  split_ifs with hP
  · exact Finset.sup'_le _ _ fun i _ => by rw [nabs_apply]; exact h i
  · exact hB

/-- **Constants**: `‖a‖_c = ‖a‖`. -/
theorem gN_C (c : ℝ) (a : K) : gN c (C a) = ‖a‖ := by
  show (C a).gaussNorm (nabs K) c = ‖a‖
  rw [gaussNorm_C, nabs_apply]

/-- **Linear polynomials**: `‖a + bX‖_c ≥ max(‖a‖, ‖b‖·c)`. -/
theorem le_gN_linear {c : ℝ} (hc : 0 ≤ c) (a b : K) : max ‖a‖ (‖b‖ * c) ≤ gN c (C a + C b * X) := by
  have h0 : (C a + C b * X).coeff 0 = a := by
    rw [coeff_add, coeff_C_zero, coeff_C_mul_X, ite_eq_right_iff.2 (by norm_num), add_zero]
  have h1 : (C a + C b * X).coeff 1 = b := by
    simp [coeff_C]
  refine max_le ?_ ?_
  · calc ‖a‖ = ‖(C a + C b * X).coeff 0‖ * c ^ 0 := by rw [h0, pow_zero, mul_one]
      _ ≤ _ := coeff_le_gN hc _ 0
  · calc ‖b‖ * c = ‖(C a + C b * X).coeff 1‖ * c ^ 1 := by rw [h1, pow_one]
      _ ≤ _ := coeff_le_gN hc _ 1

/-- **Integral polynomials** (Gauss norm `≤ 1` at radius `1`) have `‖P‖_c ≤ max(‖P(0)‖, c)` for `c ≤ 1`. -/
theorem gN_le_max {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) {P : K[X]} (hP : gN 1 P ≤ 1) :
    gN c P ≤ max ‖P.coeff 0‖ c := by
  refine gN_le (le_trans hc (le_max_right _ _)) fun i => ?_
  have hi : ‖P.coeff i‖ ≤ 1 := by simpa using (coeff_le_gN zero_le_one P i).trans hP
  rcases i with _ | i
  · simp
  · calc ‖P.coeff (i + 1)‖ * c ^ (i + 1) ≤ 1 * c := by
          gcongr
          exact pow_le_of_le_one hc hc1 (by omega)
      _ ≤ _ := by rw [one_mul]; exact le_max_right _ _

variable [IsUltrametricDist K]

/-- **`nabs` is nonarchimedean.** -/
theorem isNonarchimedean_nabs : IsNonarchimedean (nabs K) := fun x y => by
  simpa [nabs_apply] using IsUltrametricDist.norm_add_le_max x y

/-- **The Gauss norm is ultrametric.** -/
theorem gN_add_le {c : ℝ} (hc : 0 ≤ c) (P Q : K[X]) : gN c (P + Q) ≤ max (gN c P) (gN c Q) :=
  isNonarchimedean_gaussNorm _ isNonarchimedean_nabs hc P Q

/-- **The Gauss norm is submultiplicative.** -/
theorem gN_mul_le {c : ℝ} (hc : 0 ≤ c) (P Q : K[X]) : gN c (P * Q) ≤ gN c P * gN c Q :=
  gaussNorm_mul_le _ isNonarchimedean_nabs P Q hc

/-- **Gauss's lemma**: the Gauss norm is multiplicative (`c > 0`; Mathlib's `gaussNorm_mul`). -/
theorem gN_mul {c : ℝ} (hc : 0 < c) (P Q : K[X]) : gN c (P * Q) = gN c P * gN c Q :=
  gaussNorm_mul isNonarchimedean_nabs hc P Q

/-- **Finite sums** (ultrametric). -/
theorem gN_sum_le {ι : Type*} (s : Finset ι) {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) {f : ι → K[X]}
    (h : ∀ i ∈ s, gN c (f i) ≤ B) : gN c (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (gN_add_le hc _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Finite products** (submultiplicative). -/
theorem gN_prod_le {ι : Type*} (s : Finset ι) {c : ℝ} (hc : 0 ≤ c) (f : ι → K[X]) :
    gN c (∏ i ∈ s, f i) ≤ ∏ i ∈ s, gN c (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (gN_C c (1 : K)).le
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (gN_mul_le hc _ _).trans (mul_le_mul_of_nonneg_left ih (gN_nonneg hc _))

end GaussNorm

/-! ## Window counting -/

section Window

variable {p : ℕ} [hp : Fact p.Prime]

/-- **`a·b ≤ 1`** for `a ≤ 1` and `0 ≤ b ≤ 1`. -/
theorem mul_le_one_of_le {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_of_le_one_left hb0 ha).trans hb

/-- **Window counting**: a set of `j < Y₀` that are pairwise congruent modulo `M ≥ 1` has at most `Y₀/M + 1`
elements. -/
theorem card_le_of_dvd {Y₀ M : ℕ} {S : Finset ℕ} (hS : S ⊆ range Y₀)
    (h : ∀ j ∈ S, ∀ j' ∈ S, (M : ℤ) ∣ (j : ℤ) - j') : (S.card : ℝ) ≤ Y₀ / M + 1 := by
  have h1 : S.card ≤ (range (Y₀ / M + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun j => j / M) (fun j hj => ?_) (fun j hj j' hj' he => ?_)
    · have := hS hj
      simp only [mem_range, coe_range, Set.mem_Iio] at this ⊢
      exact Nat.lt_succ_of_le (Nat.div_le_div_right this.le)
    · have hmod : j % M = j' % M := (Nat.modEq_iff_dvd.2 (h j' hj' j hj))
      simp only at he
      rw [← Nat.div_add_mod j M, ← Nat.div_add_mod j' M, he, hmod]
  rw [card_range] at h1
  have h2 : ((Y₀ / M : ℕ) : ℝ) ≤ Y₀ / M := Nat.cast_div_le
  calc (S.card : ℝ) ≤ ((Y₀ / M + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ Y₀ / M + 1 := by push_cast; linarith

/-- **The pointwise digit bound**: for `E ≥ 0`, with `ℓ = log p`,
`−log max(x, p^{−h−E}) ≤ ℓ·(#{1 ≤ i ≤ h : x < p^{1−i}} + E·[x ≤ p^{−h}])`. -/
theorem neg_log_max_le (x : ℝ) (h : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    -Real.log (max x ((p : ℝ) ^ (-(h : ℝ) - E))) ≤ Real.log p *
      (((Icc 1 h).filter fun i : ℕ => x < (p : ℝ) ^ ((1 : ℝ) - i)).card +
        if x ≤ (p : ℝ) ^ (-(h : ℝ)) then E else 0) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  have hpos : ∀ y : ℝ, 0 < (p : ℝ) ^ y := fun y => Real.rpow_pos_of_pos (by linarith) y
  have hlogr : ∀ y : ℝ, Real.log ((p : ℝ) ^ y) = y * Real.log p := fun y => Real.log_rpow (by linarith) y
  by_cases hxh : x ≤ (p : ℝ) ^ (-(h : ℝ))
  · simp only [hxh, ↓reduceIte]
    have hfil : (Icc 1 h).filter (fun i : ℕ => x < (p : ℝ) ^ ((1 : ℝ) - i)) = Icc 1 h := by
      refine Finset.filter_true_of_mem fun i hi => lt_of_le_of_lt hxh ?_
      rw [mem_Icc] at hi
      have : (i : ℝ) ≤ h := by exact_mod_cast hi.2
      exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
    rw [hfil, Nat.card_Icc, Nat.add_sub_cancel]
    have := Real.log_le_log (hpos _) (le_max_right x ((p : ℝ) ^ (-(h : ℝ) - E)))
    rw [hlogr] at this
    nlinarith
  · simp only [hxh, ↓reduceIte, add_zero]
    push Not at hxh
    have hxpos : 0 < x := lt_trans (hpos _) hxh
    have hmax : max x ((p : ℝ) ^ (-(h : ℝ) - E)) = x :=
      max_eq_left (le_of_lt (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)) hxh))
    rw [hmax]
    set v := -Real.log x / Real.log p with hv
    have hlx : Real.log x = -(v * Real.log p) := by rw [hv]; field_simp
    have hvh : v < h := by
      have := Real.log_lt_log (hpos _) hxh
      rw [hlogr, hlx] at this
      nlinarith
    rw [hlx, neg_neg, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hL.le
    rcases le_or_gt v 0 with hv0 | hv0
    · exact hv0.trans (Nat.cast_nonneg _)
    · have hk : ⌈v⌉₊ ≤ h := Nat.ceil_le.2 hvh.le
      have hsub : Icc 1 ⌈v⌉₊ ⊆ (Icc 1 h).filter fun i : ℕ => x < (p : ℝ) ^ ((1 : ℝ) - i) := by
        intro i hi
        rw [mem_Icc] at hi
        rw [mem_filter, mem_Icc]
        refine ⟨⟨hi.1, hi.2.trans hk⟩, ?_⟩
        have hi1 : ((i - 1 : ℕ) : ℝ) < v := Nat.lt_ceil.1 (by omega)
        have hc : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi.1]; simp
        rw [hc] at hi1
        rw [← Real.log_lt_log_iff hxpos (hpos _), hlogr, hlx]
        nlinarith
      calc v ≤ ⌈v⌉₊ := Nat.le_ceil v
        _ = (Icc 1 ⌈v⌉₊).card := by simp
        _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- **The window sum** (B7 step 4): if any two `j < Y₀` with `x_j, x_{j'} < p^{1−r}` are congruent modulo `p^r`, then
`Σ_{j<Y₀} −log max(x_j, p^{−h−E}) ≤ log p·(Y₀/(p − 1) + h + E)` (for `Y₀ ≤ p^h`). -/
theorem sum_neg_log_le {Y₀ h : ℕ} (hYh : Y₀ ≤ p ^ h) {E : ℝ} (hE : 0 ≤ E) {x : ℕ → ℝ}
    (hdvd : ∀ (r : ℕ) (j j' : ℕ), j < Y₀ → j' < Y₀ → x j < (p : ℝ) ^ ((1 : ℝ) - r) →
      x j' < (p : ℝ) ^ ((1 : ℝ) - r) → ((p ^ r : ℕ) : ℤ) ∣ (j : ℤ) - j') :
    ∑ j ∈ range Y₀, -Real.log (max (x j) ((p : ℝ) ^ (-(h : ℝ) - E))) ≤
      Real.log p * (Y₀ / ((p : ℝ) - 1) + h + E) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  refine (Finset.sum_le_sum fun j _ => neg_log_max_le (p := p) (x j) h hE).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hL.le
  rw [Finset.sum_add_distrib]
  -- the digit counts
  have h1 : ∑ j ∈ range Y₀, (((Icc 1 h).filter fun i : ℕ => x j < (p : ℝ) ^ ((1 : ℝ) - i)).card : ℝ) ≤
      Y₀ / ((p : ℝ) - 1) + h := by
    have hswap : ∑ j ∈ range Y₀, (((Icc 1 h).filter fun i : ℕ => x j < (p : ℝ) ^ ((1 : ℝ) - i)).card : ℝ) =
        ∑ i ∈ Icc 1 h, (((range Y₀).filter fun j => x j < (p : ℝ) ^ ((1 : ℝ) - i)).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    rw [hswap]
    have hi : ∀ i ∈ Icc 1 h, (((range Y₀).filter fun j => x j < (p : ℝ) ^ ((1 : ℝ) - i)).card : ℝ) ≤
        Y₀ * (1 / (p : ℝ)) ^ i + 1 := by
      intro i _
      have := card_le_of_dvd (Y₀ := Y₀) (M := p ^ i) (Finset.filter_subset _ _)
        fun j hj j' hj' => by
          simp only [mem_filter, mem_range] at hj hj'
          exact hdvd i j j' hj.1 hj'.1 hj.2 hj'.2
      refine this.trans (le_of_eq ?_)
      push_cast
      rw [div_pow, one_pow]
      ring
    refine (Finset.sum_le_sum hi).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_one]
    have hg : ∑ i ∈ Icc 1 h, (1 / (p : ℝ)) ^ i ≤ 1 / ((p : ℝ) - 1) := by
      have := geom_sum_Ico_le_of_lt_one (x := 1 / (p : ℝ)) (m := 1) (n := h + 1) (by positivity)
        ((div_lt_one (by linarith)).2 hp1)
      rw [Finset.Ico_add_one_right_eq_Icc] at this
      refine this.trans (le_of_eq ?_)
      field_simp
    have := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg Y₀ : (0 : ℝ) ≤ Y₀)
    rw [mul_one_div] at this
    linarith
  -- the deep points
  have h2 : ∑ j ∈ range Y₀, (if x j ≤ (p : ℝ) ^ (-(h : ℝ)) then E else 0) ≤ E := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((range Y₀).filter fun j => x j ≤ (p : ℝ) ^ (-(h : ℝ))).card ≤ 1 := by
      refine Finset.card_le_one.2 fun j hj j' hj' => ?_
      simp only [mem_filter, mem_range] at hj hj'
      have hlt : ∀ y, y ≤ (p : ℝ) ^ (-(h : ℝ)) → y < (p : ℝ) ^ ((1 : ℝ) - h) := fun y hy =>
        lt_of_le_of_lt hy (Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith))
      have hd := hdvd h j j' hj.1 hj'.1 (hlt _ hj.2) (hlt _ hj'.2)
      have : (j : ℤ) - j' = 0 := Int.eq_zero_of_abs_lt_dvd hd (by
        rw [abs_lt]
        push_cast
        constructor <;> linarith [(Nat.cast_le (α := ℤ)).2 hYh, (by omega : ((j : ℕ) : ℤ) < Y₀),
          (by omega : ((j' : ℕ) : ℤ) < Y₀), (Nat.cast_nonneg j : (0 : ℤ) ≤ j),
          (Nat.cast_nonneg j' : (0 : ℤ) ≤ j')])
      omega
    calc (((range Y₀).filter fun j => x j ≤ (p : ℝ) ^ (-(h : ℝ))).card : ℝ) * E ≤ 1 * E := by
          gcongr
          exact_mod_cast hc
      _ = E := one_mul E
  linarith

end Window

/-! ## The Gram-window lemma -/

section GramWindow

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CharZero K]

/-- **Binomial polynomials**: `i!·C(Y, i) = Y(Y − 1)⋯(Y − i + 1)` in `K[X]`. -/
theorem factorial_mul_choose (Y : K[X]) (i : ℕ) :
    (i.factorial : K[X]) * Ring.choose Y i = ∏ m ∈ range i, (Y - (m : K[X])) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose Y i
  rw [← aeval_eq_smeval, aeval_def, ← eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range,
    nsmul_eq_mul] at h
  exact h.symm

/-- **Evaluating binomial polynomials at integers**: `C(X, i)(t) = C(t, i)`. -/
theorem eval_choose_X (t : ℤ) (i : ℕ) : (Ring.choose (X : K[X]) i).eval (t : K) = ((Ring.choose t i : ℤ) : K) := by
  rw [← coe_evalRingHom, Ring.map_choose, coe_evalRingHom, eval_X]
  simpa using (Ring.map_choose (Int.castRingHom K) t i).symm

/-- **Binomial polynomials have degree `≤ i`.** -/
theorem natDegree_choose_X_le (i : ℕ) : (Ring.choose (X : K[X]) i).natDegree ≤ i := by
  have h := factorial_mul_choose (X : K[X]) i
  have hne : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
  have h' : C (i.factorial : K) * Ring.choose (X : K[X]) i = ∏ m ∈ range i, (X - (m : K[X])) := by
    rw [C_eq_natCast]
    exact h
  rw [← natDegree_C_mul hne, h']
  refine (natDegree_prod_le _ _).trans ?_
  have hm : ∀ m ∈ range i, (X - (m : K[X])).natDegree ≤ 1 := fun m _ => by
    rw [← C_eq_natCast, natDegree_X_sub_C]
  calc _ ≤ ∑ m ∈ range i, 1 := Finset.sum_le_sum hm
    _ = i := by simp

/-- **`‖P/m‖ ≤ 1` in `K`** for `1 ≤ m < P = p^h`. -/
theorem norm_pow_div_le_one {h m : ℕ} (hm : m + 1 < p ^ h) : ‖(p : K) ^ h / (m + 1)‖ ≤ 1 := by
  have e : (p : K) ^ h / (m + 1) = algebraMap ℚ_[p] K ((p : ℚ_[p]) ^ h / (m + 1)) := by
    simp [map_div₀]
  rw [e, norm_algebraMap']
  refine (norm_pow_div_le p hm).trans ?_
  exact inv_le_one_of_one_le₀ (one_le_p hp)

/-- **The scaled binomial** `C(P·X, l) = (P/l)·X·∏_{m<l−1} ((P/(m+1))·X − 1)` for `l ≥ 1`. -/
theorem choose_C_mul_X (P : K) (l : ℕ) :
    Ring.choose (C P * X) (l + 1) = C (P / (l + 1)) * X * ∏ m ∈ range l, (C (P / (m + 1)) * X - 1) := by
  have hne : ((l + 1).factorial : K[X]) ≠ 0 := by
    rw [← C_eq_natCast]
    exact C_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  refine mul_left_cancel₀ hne ?_
  rw [factorial_mul_choose, prod_range_succ', Nat.factorial_succ, Nat.cast_mul, ← prod_range_add_one_eq_factorial,
    Nat.cast_prod]
  have h1 : ∀ m : ℕ, ((m + 1 : ℕ) : K[X]) * (C (P / (m + 1)) * X - 1) = C P * X - ((m + 1 : ℕ) : K[X]) := by
    intro m
    have : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [← C_eq_natCast, mul_sub, ← mul_assoc, ← C_mul, mul_one]
    push_cast
    rw [mul_div_cancel₀ _ this]
  have h2 : ((l + 1 : ℕ) : K[X]) * C (P / (l + 1)) = C P := by
    have : ((l : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l
    rw [← C_eq_natCast, ← C_mul]
    push_cast
    rw [mul_div_cancel₀ _ this]
  symm
  calc ((l + 1 : ℕ) : K[X]) * (∏ m ∈ range l, ((m + 1 : ℕ) : K[X])) *
        (C (P / (l + 1)) * X * ∏ m ∈ range l, (C (P / (m + 1)) * X - 1))
      = (((l + 1 : ℕ) : K[X]) * C (P / (l + 1))) * X *
          ∏ m ∈ range l, (((m + 1 : ℕ) : K[X]) * (C (P / (m + 1)) * X - 1)) := by
        rw [prod_mul_distrib]
        ring
    _ = (∏ m ∈ range l, (C P * X - ((m + 1 : ℕ) : K[X]))) * (C P * X - ((0 : ℕ) : K[X])) := by
        rw [h2]
        simp_rw [h1]
        push_cast
        ring

variable [IsUltrametricDist K]

/-- **Mahler integrality** (B7 step 1): `C(a + P·u, i) ∈ O_K[u]` for `a ∈ ℤ` and `i < P = p^h` (Vandermonde, and
`C(P·u, l)` is a product of integral linear factors). -/
theorem gN_choose_comp_le (h : ℕ) (a : ℤ) {i : ℕ} (hi : i < p ^ h) :
    gN 1 ((Ring.choose (X : K[X]) i).comp (C (a : K) + C ((p : K) ^ h) * X)) ≤ 1 := by
  have hX : gN 1 (X : K[X]) ≤ 1 := gN_le zero_le_one fun k => by
    rw [coeff_X]
    split_ifs <;> simp
  rw [← coe_compRingHom_apply, Ring.map_choose, coe_compRingHom_apply, X_comp,
    Ring.add_choose_eq i (Commute.all _ _)]
  refine gN_sum_le _ zero_le_one zero_le_one fun kl hkl => (gN_mul_le zero_le_one _ _).trans ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  have h1 : gN 1 (Ring.choose (C (a : K)) kl.1) ≤ 1 := by
    have e := Ring.map_choose (Int.castRingHom K) a kl.1
    simp only [eq_intCast] at e
    rw [← Ring.map_choose, gN_C, ← e]
    exact IsUltrametricDist.norm_intCast_le_one K _
  have h2 : gN 1 (Ring.choose (C ((p : K) ^ h) * X) kl.2) ≤ 1 := by
    rcases Nat.eq_zero_or_pos kl.2 with h0 | hpos
    · rw [h0, Ring.choose_zero_right, ← C_1, gN_C, norm_one]
    · obtain ⟨l, hl⟩ : ∃ l, kl.2 = l + 1 := ⟨kl.2 - 1, by omega⟩
      rw [hl, choose_C_mul_X]
      have hlP : l + 1 < p ^ h := by omega
      refine (gN_mul_le zero_le_one _ _).trans ?_
      refine mul_le_one_of_le ((gN_mul_le zero_le_one _ _).trans (mul_le_one_of_le ?_ (gN_nonneg zero_le_one _) hX))
        (gN_nonneg zero_le_one _) ((gN_prod_le _ zero_le_one _).trans ?_)
      · rw [gN_C]
        exact_mod_cast norm_pow_div_le_one (p := p) (h := h) (m := l) hlP
      · refine Finset.prod_le_one₀ (fun _ _ => gN_nonneg zero_le_one _) fun m hm => ?_
        rw [mem_range] at hm
        rw [sub_eq_add_neg, ← C_1, ← C_neg]
        refine (gN_add_le zero_le_one _ _).trans (max_le ?_ (by rw [gN_C, norm_neg, norm_one]))
        refine (gN_mul_le zero_le_one _ _).trans (mul_le_one_of_le ?_ (gN_nonneg zero_le_one _) hX)
        rw [gN_C]
        exact_mod_cast norm_pow_div_le_one (p := p) (h := h) (m := m) (by omega)
  exact mul_le_one_of_le h1 (gN_nonneg zero_le_one _) h2

omit [CharZero K] in
/-- **Integral matrices have integral determinants.** -/
theorem norm_det_le_one {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : ∀ a b, ‖A a b‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  exact mul_le_one_of_le (IsUltrametricDist.norm_intCast_le_one K _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _)

omit [CharZero K] in
/-- **Unimodular integral matrices have integral inverses** (`A⁻¹ = det(A)⁻¹·adj A`). -/
theorem norm_inv_le_one {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : ∀ a b, ‖A a b‖ ≤ 1) (hdet : ‖A.det‖ = 1)
    (a b : Fin n) : ‖A⁻¹ a b‖ ≤ 1 := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Ring.inverse_eq_inv', norm_inv, hdet, inv_one,
    one_mul, Matrix.adjugate_apply]
  refine norm_det_le_one fun k l => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact hA k l

omit [CharZero K] in
/-- **The Gauss norm of a multiset product** of polynomials is the product of the Gauss norms (`c > 0`). -/
theorem gN_multiset_prod {c : ℝ} (hc : 0 < c) (s : Multiset K[X]) : gN c s.prod = (s.map (gN c)).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using gN_C c (1 : K)
  | cons a s ih => rw [Multiset.prod_cons, gN_mul hc, ih, Multiset.map_cons, Multiset.prod_cons]

/-- **The pointwise Gram-window inequality** (B7 steps 1–3): with `M(a + P·u) = U·N(u)·V`, `P = p^h`, the rows of
`N(u)` whose value at `0` is `≤ ρ` have Gauss-`ρ` norm `≤ ρ`, so `‖det N‖_ρ ≤ ρ^β`; and
`‖det N‖_ρ = ‖λ‖·∏_ζ ‖a − ζ + P·u‖_ρ ≥ ‖λ‖·∏_ζ max(‖a − ζ‖, p^{−h}ρ)`. -/
theorem gram_point {n δ h : ℕ} {c : Fin (δ + 1) → Matrix (Fin n) (Fin n) K} (hc : ∀ i a b, ‖c i a b‖ ≤ 1)
    {lead : K} {roots : Multiset K} {MP : Matrix (Fin n) (Fin n) K[X]}
    (hMPe : ∀ a b, MP a b = ∑ i, C (c i a b) * Ring.choose (X : K[X]) i)
    (hdet : MP.det = C lead * (roots.map fun ζ => X - C ζ).prod)
    (hδh : δ + 1 ≤ p ^ h) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (a : ℤ) (d : Fin n → K)
    {U V : Matrix (Fin n) (Fin n) K} (hUV : ∀ k l, ‖U k l‖ ≤ 1 ∧ ‖V k l‖ ≤ 1) (hU : ‖U.det‖ = 1)
    (hV : ‖V.det‖ = 1) (hsm : MP.map (eval (a : K)) = U * Matrix.diagonal d * V) :
    ‖lead‖ * (roots.map fun ζ => max ‖(a : K) - ζ‖ ((p : ℝ) ^ (-(h : ℝ)) * ρ)).prod ≤
      ρ ^ (Finset.univ.filter fun i => ‖d i‖ ≤ ρ).card := by
  classical
  set P : K := (p : K) ^ h
  set aff : K[X] := C (a : K) + C P * X
  have hnP : ‖P‖ = (p : ℝ) ^ (-(h : ℝ)) := by
    have e : (p : K) = algebraMap ℚ_[p] K p := by simp
    rw [norm_pow, e, norm_algebraMap', Padic.norm_p, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.2 fun h0 => by rw [h0, norm_zero] at hU; exact zero_ne_one hU
  have hVu : IsUnit V.det := isUnit_iff_ne_zero.2 fun h0 => by rw [h0, norm_zero] at hV; exact zero_ne_one hV
  set A : Matrix (Fin n) (Fin n) K[X] := MP.map fun q => q.comp aff
  have hA : ∀ k l, gN 1 (A k l) ≤ 1 := by
    intro k l
    simp only [A, Matrix.map_apply, hMPe, Polynomial.sum_comp, mul_comp, C_comp]
    refine gN_sum_le _ zero_le_one zero_le_one fun i _ => (gN_mul_le zero_le_one _ _).trans ?_
    rw [gN_C]
    exact mul_le_one_of_le (hc i k l) (gN_nonneg zero_le_one _)
      (gN_choose_comp_le h a (by have := i.isLt; omega))
  set N : Matrix (Fin n) (Fin n) K[X] := U⁻¹.map C * A * V⁻¹.map C
  have hN1 : ∀ k b, gN 1 (N k b) ≤ 1 := by
    intro k b
    simp only [N, Matrix.mul_apply, Matrix.map_apply]
    refine gN_sum_le _ zero_le_one zero_le_one fun l _ => (gN_mul_le zero_le_one _ _).trans ?_
    refine mul_le_one_of_le ?_ (gN_nonneg zero_le_one _)
      (by rw [gN_C]; exact norm_inv_le_one (fun k l => (hUV k l).2) hV l b)
    refine gN_sum_le _ zero_le_one zero_le_one fun m _ => (gN_mul_le zero_le_one _ _).trans ?_
    rw [gN_C]
    exact mul_le_one_of_le (norm_inv_le_one (fun k l => (hUV k l).1) hU k m) (gN_nonneg zero_le_one _) (hA m l)
  have hN0 : ∀ k b, (N k b).coeff 0 = Matrix.diagonal d k b := by
    have hev : N.map (evalRingHom 0) = Matrix.diagonal d := by
      simp only [N, Matrix.map_mul]
      have h1 : (U⁻¹.map C).map (evalRingHom (0 : K)) = U⁻¹ := by ext; simp
      have h2 : (V⁻¹.map C).map (evalRingHom (0 : K)) = V⁻¹ := by ext; simp
      have h3 : A.map (evalRingHom (0 : K)) = MP.map (eval (a : K)) := by
        ext k l
        simp [A, aff, eval_comp]
      rw [h1, h2, h3, hsm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hVu, Matrix.mul_one]
    intro k b
    rw [coeff_zero_eq_eval_zero, ← hev]
    rfl
  set r : Fin n → ℝ := fun k => if ‖d k‖ ≤ ρ then ρ else 1
  have hrow : ∀ k b, gN ρ (N k b) ≤ r k := by
    intro k b
    refine (gN_le_max hρ.le hρ1 (hN1 k b)).trans ?_
    rw [hN0, Matrix.diagonal_apply]
    simp only [r]
    split_ifs with h1 h2 h2
    · subst h1; exact max_le h2 le_rfl
    · subst h1
      have := (coeff_le_gN zero_le_one (N k k) 0).trans (hN1 k k)
      rw [hN0, Matrix.diagonal_apply_eq, pow_zero, mul_one] at this
      exact max_le this hρ1
    · simp [hρ.le]
    · simp [hρ1]
  have hdetle : gN ρ N.det ≤ ρ ^ (Finset.univ.filter fun i => ‖d i‖ ≤ ρ).card := by
    have hprod : ∏ k, r k = ρ ^ (Finset.univ.filter fun i => ‖d i‖ ≤ ρ).card := by
      simp only [r]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [← hprod, Matrix.det_apply]
    refine gN_sum_le _ hρ.le (Finset.prod_nonneg fun k _ => by simp only [r]; split_ifs <;> linarith)
      fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast]
    refine (gN_mul_le hρ.le _ _).trans ?_
    rw [gN_C]
    refine (mul_le_of_le_one_left (gN_nonneg hρ.le _) (IsUltrametricDist.norm_intCast_le_one K _)).trans ?_
    refine (gN_prod_le _ hρ.le _).trans ?_
    calc ∏ i, gN ρ (N (σ i) i) ≤ ∏ i, r (σ i) :=
          Finset.prod_le_prod₀ (fun _ _ => gN_nonneg hρ.le _) fun i _ => hrow _ _
      _ = ∏ k, r k := Equiv.prod_comp σ r
  have hdeteq : N.det = C U⁻¹.det * (C lead * (roots.map fun ζ => C ((a : K) - ζ) + C P * X).prod) *
      C V⁻¹.det := by
    have hA' : A = (compRingHom aff).mapMatrix MP := by
      ext k l
      simp [A]
    simp only [N, Matrix.det_mul]
    rw [hA', ← RingHom.map_det, hdet, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    congr 2
    rw [map_mul, coe_compRingHom_apply, coe_compRingHom_apply, C_comp, multiset_prod_comp, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun ζ _ => ?_)
    simp [aff, sub_comp]
    ring
  have hgeq : ‖lead‖ * (roots.map fun ζ => max ‖(a : K) - ζ‖ ((p : ℝ) ^ (-(h : ℝ)) * ρ)).prod ≤ gN ρ N.det := by
    rw [hdeteq, gN_mul hρ, gN_mul hρ, gN_C, gN_C, gN_mul hρ, gN_C, gN_multiset_prod hρ, Multiset.map_map,
      Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, norm_inv, hU, hV, inv_one,
      one_mul, mul_one]
    refine mul_le_mul_of_nonneg_left (Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => by positivity)
      fun ζ _ => ?_) (norm_nonneg _)
    simp only [Function.comp_apply]
    have := le_gN_linear hρ.le ((a : K) - ζ) P
    rwa [hnP] at this
  exact hgeq.trans hdetle

end GramWindow

/-! ## The Gram-window lemma (B7) -/

open Polynomial in
/-- **Multiset sums with a uniform bound.** -/
theorem multiset_sum_map_le {α : Type*} (s : Multiset α) {g : α → ℝ} {B : ℝ} (h : ∀ x ∈ s, g x ≤ B) :
    (s.map g).sum ≤ s.card * B := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have := h a (Multiset.mem_cons_self a s)
    push_cast
    linarith

/-- **Exchanging a finite sum and a multiset sum.** -/
theorem sum_multiset_map_sum {α ι : Type*} (s : Multiset α) (t : Finset ι) (f : α → ι → ℝ) :
    ∑ j ∈ t, (s.map fun x => f x j).sum = (s.map fun x => ∑ j ∈ t, f x j).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Finset.sum_add_distrib, ih]

open Polynomial in
/-- **The Gram-window lemma** (B7, the form with roots): for `M(t) = Σ_{i ≤ δ} c_i·C(t, i)` with integral `c_i` and
`det M = λ·∏_ζ (X − ζ)` over an ultrametric `K ⊇ ℚ_p`, the mean over a window of `Y₀ ≤ p^h` consecutive integers of
the number of elementary divisors of norm `≤ p^{−E}` is `≤ n·(δ/Y₀ + (La₀ + δh/Y₀)/E)`.

Proof: `M` is the polynomial `Σ_i c_i·C(X, i)` (`eq_of_infinite_eval_eq`), of degree `≤ δ`, so `#roots ≤ nδ`; at each
`a = t₀ + j`, `gram_point` (Mahler integrality, Gauss norms) gives
`E·β_j·log p ≤ −log‖λ‖ + Σ_ζ −log max(‖a − ζ‖, p^{−h−E})`; summing over the window, `sum_neg_log_le` bounds each
root's contribution by `log p·(Y₀/(p − 1) + h + E)`. -/
theorem gram_window (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
    [IsUltrametricDist K] (n δ h : ℕ) (E La₀ : ℝ) (c : Fin (δ + 1) → Matrix (Fin n) (Fin n) K)
    (hc : ∀ i a b, ‖c i a b‖ ≤ 1) (lead : K) (roots : Multiset K) (hlead : lead ≠ 0)
    (MP : Matrix (Fin n) (Fin n) (Polynomial K))
    (hMP : ∀ t : ℤ, MP.map (Polynomial.eval (t : K)) = ∑ i : Fin (δ + 1), ((Ring.choose t i.val : ℤ) : K) • c i)
    (hdet : MP.det = Polynomial.C lead * (roots.map fun ζ => Polynomial.X - Polynomial.C ζ).prod)
    (t₀ : ℤ) (Y₀ : ℕ) (hY : 0 < Y₀) (hYh : Y₀ ≤ p ^ h) (hδh : δ + 1 ≤ p ^ h) (hE : 1 ≤ E)
    (dg : ℤ → Fin n → K)
    (hsmith : ∀ j < Y₀, ∃ U V : Matrix (Fin n) (Fin n) K, (∀ a b, ‖U a b‖ ≤ 1 ∧ ‖V a b‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧
      ‖V.det‖ = 1 ∧ MP.map (Polynomial.eval ((t₀ + j : ℤ) : K)) = U * Matrix.diagonal (dg (t₀ + j)) * V)
    (hLa : -Real.logb p ‖lead‖ + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ n * La₀) :
    (∑ j ∈ Finset.range Y₀, ((Finset.univ.filter fun i => ‖dg (t₀ + j) i‖ ≤ (p : ℝ) ^ (-E)).card : ℝ)) / Y₀ ≤
      n * ((δ : ℝ) / Y₀ + (La₀ + δ * h / Y₀) / E) := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  have hE0 : 0 < E := by linarith
  have hY0 : (0 : ℝ) < Y₀ := by exact_mod_cast hY
  -- `M` is the binomial polynomial
  have hMPe : ∀ a b, MP a b = ∑ i, C (c i a b) * Ring.choose (X : K[X]) i := by
    intro a b
    refine Polynomial.eq_of_infinite_eval_eq _ _ (Set.Infinite.mono ?_
      (Set.infinite_range_of_injective (Int.cast_injective (α := K))))
    rintro _ ⟨t, rfl⟩
    have := congrFun (congrFun (hMP t) a) b
    rw [Matrix.map_apply] at this
    simp only [Set.mem_ofPred_eq, this, eval_finsetSum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      eval_mul, eval_C, eval_choose_X]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- `#roots ≤ nδ`
  have hcard : (roots.card : ℝ) ≤ n * δ := by
    have hentry : ∀ a b, (MP a b).natDegree ≤ δ := by
      intro a b
      rw [hMPe]
      refine natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_choose_X_le _).trans (by have := i.isLt; omega)
    have hdeg : MP.det.natDegree ≤ n * δ := by
      rw [Matrix.det_apply]
      refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast]
      refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
      calc ∑ i, (MP (σ i) i).natDegree ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => hentry _ _
        _ = n * δ := by simp
    have hr : MP.det.natDegree = roots.card := by
      rw [hdet, natDegree_C_mul hlead, natDegree_multiset_prod_X_sub_C_eq_card]
    rw [hr] at hdeg
    exact_mod_cast hdeg
  -- the pointwise inequality, in logarithms
  set ρ : ℝ := (p : ℝ) ^ (-E)
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (by linarith) _
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
  set w : K → ℕ → ℝ := fun ζ j => -Real.log (max ‖((t₀ + j : ℤ) : K) - ζ‖ ((p : ℝ) ^ (-(h : ℝ) - E)))
  set β : ℕ → ℝ := fun j => ((Finset.univ.filter fun i => ‖dg (t₀ + j) i‖ ≤ ρ).card : ℝ)
  have hpt : ∀ j < Y₀, E * Real.log p * β j ≤ -Real.log ‖lead‖ + (roots.map fun ζ => w ζ j).sum := by
    intro j hj
    obtain ⟨U, V, hUV, hU, hV, hsm⟩ := hsmith j hj
    have key := gram_point hc hMPe hdet hδh hρ hρ1 (t₀ + j) (dg (t₀ + j)) hUV hU hV hsm
    have hm : (p : ℝ) ^ (-(h : ℝ)) * ρ = (p : ℝ) ^ (-(h : ℝ) - E) := by
      rw [← Real.rpow_add (by linarith)]
      ring_nf
    simp only [hm] at key
    have hpos : ∀ ζ : K, 0 < max ‖((t₀ + j : ℤ) : K) - ζ‖ ((p : ℝ) ^ (-(h : ℝ) - E)) :=
      fun ζ => lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) (le_max_right _ _)
    have hlpos : 0 < ‖lead‖ := norm_pos_iff.2 hlead
    have hprod : 0 < (roots.map fun ζ => max ‖((t₀ + j : ℤ) : K) - ζ‖ ((p : ℝ) ^ (-(h : ℝ) - E))).prod :=
      Multiset.prod_pos fun x hx => by
        obtain ⟨ζ, -, rfl⟩ := Multiset.mem_map.1 hx
        exact hpos ζ
    have hlog := Real.log_le_log (mul_pos hlpos hprod) key
    rw [Real.log_mul hlpos.ne' hprod.ne', Real.log_multiset_prod (fun x hx => by
      obtain ⟨ζ, -, rfl⟩ := Multiset.mem_map.1 hx
      exact (hpos ζ).ne'), Real.log_pow, Real.log_rpow (by linarith), Multiset.map_map] at hlog
    have hsum : (roots.map fun ζ => w ζ j).sum =
        -(roots.map (Real.log ∘ fun ζ => max ‖((t₀ + j : ℤ) : K) - ζ‖ ((p : ℝ) ^ (-(h : ℝ) - E)))).sum := by
      rw [← Multiset.sum_map_neg]
      rfl
    rw [hsum]
    simp only [β]
    nlinarith
  -- each root contributes at most `log p·(Y₀/(p − 1) + h + E)`
  have hroot : ∀ ζ : K, ∑ j ∈ Finset.range Y₀, w ζ j ≤ Real.log p * (Y₀ / ((p : ℝ) - 1) + h + E) := by
    intro ζ
    refine sum_neg_log_le (p := p) hYh hE0.le fun r j j' hj hj' hx hx' => ?_
    have hn : ‖(((j : ℤ) - j' : ℤ) : K)‖ < (p : ℝ) ^ ((1 : ℝ) - r) := by
      have e : (((j : ℤ) - j' : ℤ) : K) = (((t₀ + j : ℤ) : K) - ζ) - (((t₀ + j' : ℤ) : K) - ζ) := by
        push_cast
        ring
      rw [e, sub_eq_add_neg]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [norm_neg]
      exact max_lt hx hx'
    rw [← map_intCast (algebraMap ℚ_[p] K), norm_algebraMap'] at hn
    have e2 : (p : ℝ) ^ ((1 : ℝ) - r) = (p : ℝ) ^ (-(r : ℤ) + 1) := by
      rw [← Real.rpow_intCast]
      push_cast
      ring_nf
    rw [e2] at hn
    have h3 := (Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _).2 hn
    rw [show (-(r : ℤ)) = -((r : ℕ) : ℤ) from rfl, Padic.norm_int_le_pow_iff_dvd] at h3
    exact_mod_cast h3
  -- summing
  have hsumj : E * Real.log p * ∑ j ∈ Finset.range Y₀, β j ≤
      Y₀ * (-Real.log ‖lead‖) + roots.card * (Real.log p * (Y₀ / ((p : ℝ) - 1) + h + E)) := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range Y₀, E * Real.log p * β j
        ≤ ∑ j ∈ Finset.range Y₀, (-Real.log ‖lead‖ + (roots.map fun ζ => w ζ j).sum) :=
          Finset.sum_le_sum fun j hj => hpt j (Finset.mem_range.1 hj)
      _ = Y₀ * (-Real.log ‖lead‖) + (roots.map fun ζ => ∑ j ∈ Finset.range Y₀, w ζ j).sum := by
          rw [Finset.sum_add_distrib, sum_multiset_map_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
          have := multiset_sum_map_le roots fun ζ _ => hroot ζ
          linarith
  -- the arithmetic
  set S := ∑ j ∈ Finset.range Y₀, β j
  have hES : E * S ≤ Y₀ * (-Real.log ‖lead‖ / Real.log p + roots.card / ((p : ℝ) - 1)) + roots.card * (h + E) := by
    have e : (Y₀ * (-Real.log ‖lead‖ / Real.log p + roots.card / ((p : ℝ) - 1)) + roots.card * (h + E)) *
        Real.log p = Y₀ * (-Real.log ‖lead‖) + roots.card * (Real.log p * (Y₀ / ((p : ℝ) - 1) + h + E)) := by
      field_simp
      ring
    refine le_of_mul_le_mul_right ?_ hL
    rw [e]
    linarith
  have hLa' : -Real.log ‖lead‖ / Real.log p + roots.card / ((p : ℝ) - 1) ≤ n * La₀ := by
    rw [neg_div]
    exact hLa
  have hfin : E * S ≤ n * (δ * E + La₀ * Y₀ + δ * h) := by
    have h1 : (Y₀ : ℝ) * (-Real.log ‖lead‖ / Real.log p + roots.card / ((p : ℝ) - 1)) ≤ Y₀ * (n * La₀) :=
      mul_le_mul_of_nonneg_left hLa' hY0.le
    have h2 : (roots.card : ℝ) * (h + E) ≤ n * δ * (h + E) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    nlinarith
  rw [div_le_iff₀ hY0]
  have e : (n : ℝ) * ((δ : ℝ) / Y₀ + (La₀ + δ * h / Y₀) / E) * Y₀ = n * (δ * E + La₀ * Y₀ + δ * h) / E := by
    field_simp
    ring
  rw [e, le_div_iff₀ hE0]
  linarith

end

end PadicUnits
