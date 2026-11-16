/-
# The characters at which a smoothed prime sum is large

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveResMoment` bounds the `2k`-th moment of a polynomial over the characters and counts the characters at which it
is large. This file applies it to the smoothed prime sums of the Type II estimate, `SieveWeight.Sp`: a sum over the
primes up to `2Q` with the weights `f0(p/Q)(p/Q)^{−iy}`, of modulus at most `F₀`. A `k`-tuple of primes with a given
product is a tuple of its prime factors, of which there are at most `k`; so `F = k^k` bounds the tuples, and the
`2k`-th moment is at most `((2Q)^k + q)·k^k·(3F₀²Q)^k`. With `Q = q^s`, the characters at which the prime sum is at
least `Q^u` number at most `C_k q^{momExp k s u}`, `momExp k s u = max(1, ks) + ks(1 − 2u)`.

* `spSet`, `spCoeff`, `Sp_eq_dp`: `Sp χ f0 Q y` is the polynomial `dp (spSet Q) (spCoeff f0 Q y · χ) 0`.
* `card_tuples_primes_le`: the `k`-tuples of primes with a given product number at most `k^k`.
* `sum_spCoeff_sq_le`: `Σ_n |spCoeff f0 Q y n|² ≤ F₀²(2Q + 1)` for `|f0| ≤ F₀`.
* `sum_chars_Sp_pow_le`, **the `2k`-th moment of a prime sum**: `Σ_χ |Sp χ f0 Q y|^{2k} ≤
  ((2Q)^k + q)·k^k·(3F₀²Q)^k` for `Q ≥ 1`.
* `card_Sp_large`, **the count**: `#{χ : Q^u ≤ |Sp χ f0 Q y|} ≤ (2^k + 1)k^k(3F₀²)^k q^{momExp k (log_q Q) u}` for
  `q > 1`, `Q ≥ 1` and `k ≥ 1`.
* `momExp_anti`, `momExp_nonneg`, `one_le_momExp`, `momExp_mono_k`: `momExp k s u` does not increase in `u`; it is
  at least `0` for `u ≤ 1` and at least `1` for `u ≤ 0`; beyond `k₀` with `k₀s ≥ 1` it does not decrease in `k`.
* `lev N τ Q x = min(N, ⌊log_Q x / τ⌋)`, the level of a size `x` in steps of `τ`: `rpow_le_of_one_le_lev`, a size of
  level `ℓ ≥ 1` is at least `Q^{τℓ}`; `le_rpow_of_lev_lt`, one of level `ℓ < N` is at most `Q^{τ(ℓ+1)}`.

The file imports `SieveResMoment.lean` and `SieveResZone.lean`.
-/
import SieveResMoment
import SieveResZone

open Complex Finset

noncomputable section

namespace SieveTypeIIHM

open DirMean SieveTypeII DirichletCharacter

variable {q : ℕ}

/-- The primes up to `2Q`: the range of `Sp`'s sum. -/
def spSet (Q : ℝ) : Finset ℕ := (Finset.range (⌊2 * Q⌋₊ + 1)).filter Nat.Prime

/-- `Sp`'s weight at `n`: `(n/Q)^{−iy}f0(n/Q)`. -/
def spCoeff (f0 : ℝ → ℝ) (Q y : ℝ) (n : ℕ) : ℂ := (((n : ℝ) / Q : ℝ) : ℂ) ^ (-(y : ℂ) * I) * (f0 (n / Q) : ℂ)

/-- `Sp χ f0 Q y` is the polynomial of `spSet Q` with the coefficients `spCoeff f0 Q y`, at `t = 0`. -/
theorem Sp_eq_dp (χ : DirichletCharacter ℂ q) (f0 : ℝ → ℝ) (Q y : ℝ) :
    SieveWeight.Sp χ f0 Q y = dp (spSet Q) (fun n => spCoeff f0 Q y n * χ n) 0 := by
  unfold SieveWeight.Sp dp spSet spCoeff
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
  ring

/-- `spSet Q ⊆ (0, ⌊2Q⌋]`. -/
theorem spSet_subset (Q : ℝ) : spSet Q ⊆ Finset.Ioc 0 ⌊2 * Q⌋₊ := by
  intro n hn
  obtain ⟨hr, hp⟩ := Finset.mem_filter.1 hn
  exact Finset.mem_Ioc.2 ⟨hp.pos, Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)⟩

/-- **The tuples of primes with a given product**: for `S` of primes, the `k`-tuples of elements of `S` with
product `n` number at most `k^k`: their entries are among the prime factors of one of them. -/
theorem card_tuples_primes_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (k n : ℕ) :
    ((Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n).card ≤ k ^ k := by
  classical
  set T := (Fintype.piFinset fun _ : Fin k => S).filter fun x => ∏ i, x i = n with hT
  rcases T.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h, Finset.card_empty]; exact Nat.zero_le _
  obtain ⟨hx₀S, hx₀n⟩ := Finset.mem_filter.1 hx₀
  have hx₀p : ∀ i, (x₀ i).Prime := fun i => hS _ (Fintype.mem_piFinset.1 hx₀S i)
  -- every entry of a tuple with product `n` is an entry of `x₀`
  have hent : ∀ x ∈ T, ∀ i, x i ∈ Finset.univ.image x₀ := by
    intro x hx i
    obtain ⟨hxS, hxn⟩ := Finset.mem_filter.1 hx
    have hp : (x i).Prime := hS _ (Fintype.mem_piFinset.1 hxS i)
    have hdvd : x i ∣ ∏ j, x₀ j := by
      rw [hx₀n, ← hxn]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, ((Nat.prime_dvd_prime_iff_eq hp (hx₀p j)).1 hj).symm⟩
  calc T.card ≤ (Fintype.piFinset fun _ : Fin k => Finset.univ.image x₀).card :=
        Finset.card_le_card fun x hx => Fintype.mem_piFinset.2 (hent x hx)
    _ = (Finset.univ.image x₀).card ^ k := by rw [Fintype.card_piFinset, Fin.prod_const]
    _ ≤ k ^ k := by
        refine Nat.pow_le_pow_left ?_ k
        calc (Finset.univ.image x₀).card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]

/-- `Σ_n |spCoeff f0 Q y n|² ≤ F₀²(2Q + 1)` for `|f0| ≤ F₀` and `Q > 0`. -/
theorem sum_spCoeff_sq_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hF₀ : ∀ u, |f0 u| ≤ F₀) {Q : ℝ} (hQ : 0 < Q) (y : ℝ) :
    ∑ n ∈ spSet Q, ‖spCoeff f0 Q y n‖ ^ 2 ≤ F₀ ^ 2 * (2 * Q + 1) := by
  have hF0 : 0 ≤ F₀ := le_trans (abs_nonneg _) (hF₀ 0)
  have hterm : ∀ n ∈ spSet Q, ‖spCoeff f0 Q y n‖ ^ 2 ≤ F₀ ^ 2 := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) / Q := div_pos (by exact_mod_cast (Finset.mem_filter.1 hn).2.pos) hQ
    have h1 : ‖(((n : ℝ) / Q : ℝ) : ℂ) ^ (-(y : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp
    unfold spCoeff
    rw [norm_mul, h1, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hF₀ _) 2
  have hcard : ((spSet Q).card : ℝ) ≤ 2 * Q + 1 := by
    have h1 : (spSet Q).card ≤ ⌊2 * Q⌋₊ + 1 := by
      calc (spSet Q).card ≤ (Finset.range (⌊2 * Q⌋₊ + 1)).card := Finset.card_filter_le _ _
        _ = ⌊2 * Q⌋₊ + 1 := Finset.card_range _
    have h2 : ((⌊2 * Q⌋₊ : ℕ) : ℝ) ≤ 2 * Q := Nat.floor_le (by linarith)
    have h3 : ((spSet Q).card : ℝ) ≤ ((⌊2 * Q⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  calc ∑ n ∈ spSet Q, ‖spCoeff f0 Q y n‖ ^ 2 ≤ ∑ _n ∈ spSet Q, F₀ ^ 2 := Finset.sum_le_sum hterm
    _ = (spSet Q).card * F₀ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Q + 1) * F₀ ^ 2 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = F₀ ^ 2 * (2 * Q + 1) := by ring

/-- **The `2k`-th moment of a smoothed prime sum over the characters**: for `|f0| ≤ F₀`, `Q ≥ 1` and `k ≥ 1`,
`Σ_χ |Sp χ f0 Q y|^{2k} ≤ ((2Q)^k + q)·k^k·(3F₀²Q)^k`. -/
theorem sum_chars_Sp_pow_le [NeZero q] {f0 : ℝ → ℝ} {F₀ : ℝ} (hF₀ : ∀ u, |f0 u| ≤ F₀) {Q : ℝ} (hQ : 1 ≤ Q)
    (y : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ χ : DirichletCharacter ℂ q, ‖SieveWeight.Sp χ f0 Q y‖ ^ (2 * k) ≤
      ((2 * Q) ^ k + q) * (k : ℝ) ^ k * (3 * F₀ ^ 2 * Q) ^ k := by
  have hF0 : 0 ≤ F₀ := le_trans (abs_nonneg _) (hF₀ 0)
  have hQ0 : 0 < Q := by linarith
  simp_rw [Sp_eq_dp]
  have hmom := sum_chars_dp_pow_le (q := q) hk (spSet_subset Q) (spCoeff f0 Q y) 0 (F := (k : ℝ) ^ k)
    (fun n => by exact_mod_cast card_tuples_primes_le (fun p hp => (Finset.mem_filter.1 hp).2) k n)
  refine hmom.trans ?_
  have hB : (((⌊2 * Q⌋₊ ^ k - 0 ^ k : ℕ) : ℝ)) ≤ (2 * Q) ^ k := by
    rw [zero_pow (by omega), Nat.sub_zero, Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) k
  have hV := sum_spCoeff_sq_le hF₀ hQ0 y
  have hV' : F₀ ^ 2 * (2 * Q + 1) ≤ 3 * F₀ ^ 2 * Q := by nlinarith [sq_nonneg F₀]
  have hV0 : 0 ≤ ∑ n ∈ spSet Q, ‖spCoeff f0 Q y n‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  gcongr
  exact hV.trans hV'

/-- **The characters at which a smoothed prime sum is large.** For `q > 1`, `|f0| ≤ F₀`, `Q ≥ 1` and `k ≥ 1`:
`#{χ : Q^u ≤ |Sp χ f0 Q y|} ≤ (2^k + 1)k^k(3F₀²)^k q^{momExp k s u}` with `s = log_q Q`. -/
theorem card_Sp_large [NeZero q] (hq : 1 < (q : ℝ)) {f0 : ℝ → ℝ} {F₀ : ℝ} (hF₀ : ∀ u, |f0 u| ≤ F₀) {Q : ℝ}
    (hQ : 1 ≤ Q) (y : ℝ) {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖).card : ℝ) ≤
      (2 ^ k + 1) * (k : ℝ) ^ k * (3 * F₀ ^ 2) ^ k * (q : ℝ) ^ (momExp k (Real.logb q Q) u) := by
  have hF0 : 0 ≤ F₀ := le_trans (abs_nonneg _) (hF₀ 0)
  have hq0 : (0 : ℝ) < q := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.logb q Q := ⟨_, rfl⟩
  rw [← hs]
  have hQs : Q = (q : ℝ) ^ s := by rw [hs, Real.rpow_logb hq0 hq.ne' hQ0]
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.logb_nonneg hq hQ
  have hV0 : 0 < Q ^ u := Real.rpow_pos_of_pos hQ0 u
  -- Markov, then the moment
  have hcard := card_large_le (q := q) (spSet Q) (spCoeff f0 Q y) 0 k hV0.le
  simp_rw [← Sp_eq_dp] at hcard
  have hmom := sum_chars_Sp_pow_le (q := q) hF₀ hQ y hk
  set c : ℝ := ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
    Q ^ u ≤ ‖SieveWeight.Sp χ f0 Q y‖).card : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  -- the powers of `q`
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQk : Q ^ k = (q : ℝ) ^ (k * s) := by
    rw [hQs, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, mul_comm]
  have hVk : (Q ^ u) ^ (2 * k) = (q : ℝ) ^ (2 * (k * s * u)) := by
    rw [hQs, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hmax1 : (q : ℝ) ^ (k * s) ≤ (q : ℝ) ^ (max 1 ((k : ℝ) * s)) :=
    Real.rpow_le_rpow_of_exponent_le hq.le (le_max_right _ _)
  have hmax2 : (q : ℝ) ≤ (q : ℝ) ^ (max 1 ((k : ℝ) * s)) := by
    conv_lhs => rw [← Real.rpow_one (q : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (le_max_left _ _)
  have hfirst : (2 * Q) ^ k + q ≤ (2 ^ k + 1) * (q : ℝ) ^ (max 1 ((k : ℝ) * s)) := by
    rw [mul_pow, hQk]
    have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmax1 h2k]
  have hthird : (3 * F₀ ^ 2 * Q) ^ k = (3 * F₀ ^ 2) ^ k * (q : ℝ) ^ (k * s) := by rw [mul_pow, hQk]
  have hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (k * s * u)) := Real.rpow_pos_of_pos hq0 _
  have hexp : (q : ℝ) ^ (max 1 ((k : ℝ) * s)) * (q : ℝ) ^ (k * s) =
      (q : ℝ) ^ (momExp k s u) * (q : ℝ) ^ (2 * (k * s * u)) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
    unfold momExp
    congr 1; ring
  -- `c·q^{2ksu} ≤ (2^k + 1)k^k(3F₀²)^k q^{max(1,ks) + ks}`
  have hmain : c * (q : ℝ) ^ (2 * (k * s * u)) ≤
      (2 ^ k + 1) * (k : ℝ) ^ k * (3 * F₀ ^ 2) ^ k * ((q : ℝ) ^ (momExp k s u) * (q : ℝ) ^ (2 * (k * s * u))) := by
    rw [← hexp]
    calc c * (q : ℝ) ^ (2 * (k * s * u)) = (Q ^ u) ^ (2 * k) * c := by rw [hVk]; ring
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖SieveWeight.Sp χ f0 Q y‖ ^ (2 * k) := hcard
      _ ≤ ((2 * Q) ^ k + q) * (k : ℝ) ^ k * (3 * F₀ ^ 2 * Q) ^ k := hmom
      _ ≤ ((2 ^ k + 1) * (q : ℝ) ^ (max 1 ((k : ℝ) * s))) * (k : ℝ) ^ k *
            ((3 * F₀ ^ 2) ^ k * (q : ℝ) ^ (k * s)) := by
          rw [hthird]
          gcongr
      _ = (2 ^ k + 1) * (k : ℝ) ^ k * (3 * F₀ ^ 2) ^ k *
            ((q : ℝ) ^ (max 1 ((k : ℝ) * s)) * (q : ℝ) ^ (k * s)) := by ring
  have hmain' : c * (q : ℝ) ^ (2 * (k * s * u)) ≤
      (2 ^ k + 1) * (k : ℝ) ^ k * (3 * F₀ ^ 2) ^ k * (q : ℝ) ^ (momExp k s u) * (q : ℝ) ^ (2 * (k * s * u)) := by
    linarith [hmain]
  exact le_of_mul_le_mul_right hmain' hpos

/-! ### The moment exponent and the levels of a prime sum's size -/

/-- `momExp k s u` does not increase in `u`, for `s ≥ 0`. -/
theorem momExp_anti {k : ℕ} {s u u' : ℝ} (hs : 0 ≤ s) (hu : u ≤ u') : momExp k s u' ≤ momExp k s u := by
  unfold momExp
  have : (0 : ℝ) ≤ k * s := mul_nonneg (Nat.cast_nonneg k) hs
  nlinarith

/-- `momExp k s u ≥ 0` for `s ≥ 0` and `u ≤ 1`. -/
theorem momExp_nonneg {k : ℕ} {s u : ℝ} (hs : 0 ≤ s) (hu : u ≤ 1) : 0 ≤ momExp k s u := by
  unfold momExp
  have h0 : (0 : ℝ) ≤ k * s := mul_nonneg (Nat.cast_nonneg k) hs
  have h1 : (k : ℝ) * s ≤ max 1 ((k : ℝ) * s) := le_max_right _ _
  nlinarith

/-- `momExp k s u ≥ 1` for `s ≥ 0` and `u ≤ 0`. -/
theorem one_le_momExp {k : ℕ} {s u : ℝ} (hs : 0 ≤ s) (hu : u ≤ 0) : 1 ≤ momExp k s u := by
  unfold momExp
  have h0 : (0 : ℝ) ≤ k * s := mul_nonneg (Nat.cast_nonneg k) hs
  have h1 : (1 : ℝ) ≤ max 1 ((k : ℝ) * s) := le_max_left _ _
  nlinarith

/-- Beyond `k₀` with `k₀s ≥ 1`, `momExp k s u` does not decrease in `k`, for `s ≥ 0` and `u ≤ 1`. -/
theorem momExp_mono_k {k₀ k : ℕ} {s u : ℝ} (hs : 0 ≤ s) (hu : u ≤ 1) (hk₀ : 1 ≤ (k₀ : ℝ) * s) (hk : k₀ ≤ k) :
    momExp k₀ s u ≤ momExp k s u := by
  have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hks : (k₀ : ℝ) * s ≤ k * s := mul_le_mul_of_nonneg_right hkk hs
  unfold momExp
  rw [max_eq_right hk₀, max_eq_right (hk₀.trans hks)]
  nlinarith

/-- The level of a size `x ≥ 0` at the scale `Q`, in steps of `τ`, capped at `N`: `min N ⌊log_Q x / τ⌋`. -/
def lev (N : ℕ) (τ Q x : ℝ) : ℕ := min N ⌊Real.logb Q x / τ⌋₊

theorem lev_le (N : ℕ) (τ Q x : ℝ) : lev N τ Q x ≤ N := min_le_left _ _

/-- A size of level at least `1` is at least `Q^{τ·level}`. -/
theorem rpow_le_of_one_le_lev {N : ℕ} {τ Q x : ℝ} (hτ : 0 < τ) (hQ : 1 < Q) (hx : 0 ≤ x)
    (h1 : 1 ≤ lev N τ Q x) : Q ^ (τ * (lev N τ Q x : ℝ)) ≤ x := by
  have hfl : lev N τ Q x ≤ ⌊Real.logb Q x / τ⌋₊ := min_le_right _ _
  have hpos : 0 < ⌊Real.logb Q x / τ⌋₊ := lt_of_lt_of_le h1 hfl
  have hlog : 0 < Real.logb Q x / τ := by
    by_contra hle
    push Not at hle
    rw [Nat.floor_eq_zero.2 (lt_of_le_of_lt hle one_pos)] at hpos
    exact lt_irrefl 0 hpos
  have hx0 : 0 < x := by
    rcases hx.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.logb_zero, zero_div] at hlog; exact absurd hlog (lt_irrefl 0)
  have h2 : (lev N τ Q x : ℝ) ≤ Real.logb Q x / τ :=
    (Nat.cast_le.2 hfl).trans (Nat.floor_le hlog.le)
  have h3 : τ * (lev N τ Q x : ℝ) ≤ Real.logb Q x := by
    rw [le_div_iff₀ hτ] at h2; linarith
  calc Q ^ (τ * (lev N τ Q x : ℝ)) ≤ Q ^ (Real.logb Q x) := Real.rpow_le_rpow_of_exponent_le hQ.le h3
    _ = x := Real.rpow_logb (by linarith) hQ.ne' hx0

/-- A size of level below the cap is at most `Q^{τ(level + 1)}`. -/
theorem le_rpow_of_lev_lt {N : ℕ} {τ Q x : ℝ} (hτ : 0 < τ) (hQ : 1 < Q) (hx : 0 ≤ x)
    (hN : lev N τ Q x < N) : x ≤ Q ^ (τ * ((lev N τ Q x : ℝ) + 1)) := by
  rcases hx.lt_or_eq with hx0 | hx0
  · have heq : lev N τ Q x = ⌊Real.logb Q x / τ⌋₊ := by
      unfold lev at hN ⊢
      rcases le_total N ⌊Real.logb Q x / τ⌋₊ with h | h
      · rw [min_eq_left h] at hN; exact absurd hN (lt_irrefl _)
      · exact min_eq_right h
    have h1 : Real.logb Q x / τ < (lev N τ Q x : ℝ) + 1 := by rw [heq]; exact Nat.lt_floor_add_one _
    have h2 : Real.logb Q x < τ * ((lev N τ Q x : ℝ) + 1) := by
      rw [div_lt_iff₀ hτ] at h1; linarith
    calc x = Q ^ (Real.logb Q x) := (Real.rpow_logb (by linarith) hQ.ne' hx0).symm
      _ ≤ Q ^ (τ * ((lev N τ Q x : ℝ) + 1)) := Real.rpow_le_rpow_of_exponent_le hQ.le h2.le
  · rw [← hx0]; exact (Real.rpow_pos_of_pos (by linarith) _).le

end SieveTypeIIHM

end
