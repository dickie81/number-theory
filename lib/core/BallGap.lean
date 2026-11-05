import Mathlib
import BallSharp

/-! # The Landau gap is at least `√log N`, and the rate `λ_N ≫ √log N/N` under RH

Plain statement. For `N ≥ 3` and every real `c` on `[1, N]`,
`5Σ_{n ≤ N}c_n² + G(c) ≥ (√log N/2)·Σ_{n ≤ N}c_n²/n` (`gap_ge`), where
`G(c) = (log N + log 4 + 1)Σc_n² − 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn} ≥ 0` is Landau's slack
(`BallSharp.landauSlack`). With `c_n = x_n√n`: `Σx_n² n + G(c) ≥ (√log N/10)Σx_n²` (`edge_law`), so the spread
and the slack cannot both be small, and with `BallSharp.rate_slack`, under RH,
`Q_N(x) ≥ √log N/(220e⁸N)·Σx_n²` (`rate_gap`): `λ_N ≫ √log N/N`. Against `BallUpperEta.rate_upper_rh`
(`λ_N ≤ 67(1 + log N)/N`) this leaves a factor `√log N`. Numerically the minimum of `(Σx_n² n + G)/Σx_n²` is
`2.89`–`2.94` times `√log N` for `10³ ≤ N ≤ 10⁷` (`scripts/landau_gap.py --gap`), so the law is right up to the
constant there.

The proof is a ground-state argument for the quadratic form `5Σc² + G(c)`, whose off-diagonal entries are `≤ 0`.

- **Landau's form, with the defect kept.** Writing `b = c_{jn}`,
  `2(Λ(n)/√n)c_j b = (Λ(n)/n)c_j² + Λ(n)b² − (Λ(n)/n)(c_j − √n b)²`, so
  `G(c) = Σ_j κ_j c_j² + Σ_{n, jn ≤ N}(Λ(n)/n)(c_j − √n c_{jn})²` with
  `κ_j = log N + log 4 + 1 − Σ_{n ≤ N/j}Λ(n)/n − log j ≥ 0` (Mertens, `BallDensity.mertens_le_sharp`).
- **Each edge passes on a share of the child's weight.** For any `d(m) ≥ 0`, the square on the edge `(j, jn)` plus
  the share `Λ(n)d(jn)/log(jn)` of `d(jn)c_{jn}²` is at least `(Λ(n)/n)r(jn)c_j²`, `r(m) = d(m)/(log m + d(m))`
  (`edge_ineq`, a square). The shares of `d(m)` sum to `d(m)` as `Σ_{n ∣ m}Λ(n) = log m`, so
  `G(c) ≥ Σ_j c_j²(κ_j + Σ_{n ≤ N/j}(Λ(n)/n)r(jn) − d(j)[j ≥ 2])` (`slack_ge`).
- **The profile** `D(u) = √(u² + 2K) − u` solves `D(u) = D(L) + ∫_u^L D/(s + D)ds` exactly: the integrand is the
  derivative of `−D`. By Abel summation against Mertens from below (`mertens_ge`, from Stirling), the sum
  `Σ_{n ≤ N/j}(Λ(n)/n)·D/(s + D)` at `s = log(jn)` is at least `D(log j) − D(log N) − 1 − log 2` (`child_ge`).
- **The weights.** `K = 2log N`, `η = √log N/2` and `d(m) = D(log m) − 4η/m`: the correction `4η/m` pays for the
  target weight `η/m` at the small `m`, and costs its parents at most `3η/j` (`Σ_{n ≥ 2}1/n² ≤ 3/4`). At `j = 1`
  the inequality reads `5 + D(0) − D(log N) − 1 − log 2 − 3η ≥ η`, with `D(0) = 2√log N = 4η`.
-/

open Real Finset BallDensity BallSharp
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallGap

/-! ## Mertens from below -/

/-- **Mertens from below**: `Σ_{n ≤ k}Λ(n)/n ≥ log k − 1`, from `k·Σ_{n ≤ k}Λ(n)/n ≥ Σ_n Λ(n)⌊k/n⌋ = log k!` and
Stirling's `log k! ≥ k log k − k` (Mathlib's `Real.le_sum_log_nat`). -/
lemma mertens_ge (k : ℕ) : Real.log k - 1 ≤ ∑ n ∈ Icc 1 k, Λ n / n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 : (k : ℝ) * Real.log k - k ≤ ∑ m ∈ Icc 1 k, Real.log m := by
    have := Real.le_sum_log_nat k
    rwa [← Icc_one_eq_Ioc] at this
  have h3 : ∑ n ∈ Icc 1 k, Λ n * ((k / n : ℕ) : ℝ) ≤ k * ∑ n ∈ Icc 1 k, Λ n / n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.1 hn).1; omega)
    have : ((k / n : ℕ) : ℝ) ≤ (k : ℝ) / n := Nat.cast_div_le
    calc Λ n * ((k / n : ℕ) : ℝ) ≤ Λ n * ((k : ℝ) / n) :=
          mul_le_mul_of_nonneg_left this ArithmeticFunction.vonMangoldt_nonneg
      _ = k * (Λ n / n) := by ring
  rw [← sum_log_eq] at h3
  have h4 : (k : ℝ) * (Real.log k - 1) ≤ k * ∑ n ∈ Icc 1 k, Λ n / n := by nlinarith
  exact le_of_mul_le_mul_left h4 hk0

/-! ## The profile `D(u) = √(u² + 2K) − u` -/

/-- The profile `D(u) = √(u² + 2K) − u`. -/
def prof (K u : ℝ) : ℝ := Real.sqrt (u ^ 2 + 2 * K) - u

/-- `h(u) = 1 − u/√(u² + 2K)`, which is `D(u)/(u + D(u))` (`hprof_eq`) and `−D′(u)`. -/
def hprof (K u : ℝ) : ℝ := 1 - u / Real.sqrt (u ^ 2 + 2 * K)

lemma sqrt_pos_K {K : ℝ} (hK : 0 < K) (u : ℝ) : 0 < Real.sqrt (u ^ 2 + 2 * K) :=
  Real.sqrt_pos.2 (by positivity)

lemma le_sqrt_K {K : ℝ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) : u ≤ Real.sqrt (u ^ 2 + 2 * K) := by
  rw [Real.le_sqrt hu (by positivity)]; linarith

lemma hprof_eq {K : ℝ} (hK : 0 < K) (u : ℝ) : prof K u / (u + prof K u) = hprof K u := by
  have hs := sqrt_pos_K hK u
  unfold prof hprof
  rw [show u + (Real.sqrt (u ^ 2 + 2 * K) - u) = Real.sqrt (u ^ 2 + 2 * K) by ring]
  field_simp

lemma hprof_nonneg {K : ℝ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ hprof K u := by
  have hs := sqrt_pos_K hK u
  have h := le_sqrt_K hK hu
  unfold hprof
  rw [sub_nonneg, div_le_one hs]; exact h

lemma hprof_le_one {K : ℝ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) : hprof K u ≤ 1 := by
  have hs := sqrt_pos_K hK u
  unfold hprof
  have : 0 ≤ u / Real.sqrt (u ^ 2 + 2 * K) := div_nonneg hu hs.le
  linarith

/-- `h` decreases on `[0, ∞)`: `u/√(u² + 2K)` increases. -/
lemma hprof_anti {K : ℝ} (hK : 0 < K) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : hprof K v ≤ hprof K u := by
  have hv : 0 ≤ v := hu.trans huv
  have hsu := sqrt_pos_K hK u
  have hsv := sqrt_pos_K hK v
  unfold hprof
  suffices h : u / Real.sqrt (u ^ 2 + 2 * K) ≤ v / Real.sqrt (v ^ 2 + 2 * K) by linarith
  rw [div_le_div_iff₀ hsu hsv]
  have h1 : 0 ≤ u * Real.sqrt (v ^ 2 + 2 * K) := mul_nonneg hu hsv.le
  have h2 : 0 ≤ v * Real.sqrt (u ^ 2 + 2 * K) := mul_nonneg hv hsu.le
  rw [← pow_le_pow_iff_left₀ h1 h2 two_ne_zero, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  have : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
  nlinarith

/-- `D(u) = 2K/(√(u² + 2K) + u)`. -/
lemma prof_eq {K : ℝ} (hK : 0 < K) {u : ℝ} (hu : 0 ≤ u) :
    prof K u = 2 * K / (Real.sqrt (u ^ 2 + 2 * K) + u) := by
  have hs := sqrt_pos_K hK u
  have hss : Real.sqrt (u ^ 2 + 2 * K) ^ 2 = u ^ 2 + 2 * K := Real.sq_sqrt (by positivity)
  unfold prof
  rw [eq_div_iff (by linarith)]
  nlinarith

/-- `D` decreases on `[0, ∞)`. -/
lemma prof_anti {K : ℝ} (hK : 0 < K) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : prof K v ≤ prof K u := by
  have hv : 0 ≤ v := hu.trans huv
  rw [prof_eq hK hu, prof_eq hK hv]
  have hsu := sqrt_pos_K hK u
  have hle : Real.sqrt (u ^ 2 + 2 * K) ≤ Real.sqrt (v ^ 2 + 2 * K) :=
    Real.sqrt_le_sqrt (by nlinarith)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **Concavity of `−D`**: `D(u) − D(v) ≤ h(u)(v − u)` for `0 ≤ u ≤ v`, from
`√(u² + 2K)√(v² + 2K) ≥ uv + 2K`. -/
lemma prof_step {K : ℝ} (hK : 0 < K) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    prof K u - prof K v ≤ hprof K u * (v - u) := by
  have hv : 0 ≤ v := hu.trans huv
  set a := Real.sqrt (u ^ 2 + 2 * K) with ha
  set b := Real.sqrt (v ^ 2 + 2 * K) with hb
  have hapos : 0 < a := sqrt_pos_K hK u
  have hbpos : 0 < b := sqrt_pos_K hK v
  have haa : a ^ 2 = u ^ 2 + 2 * K := Real.sq_sqrt (by positivity)
  have hab : u * v + 2 * K ≤ a * b := by
    have h1 : a * b = Real.sqrt ((u ^ 2 + 2 * K) * (v ^ 2 + 2 * K)) := by
      rw [ha, hb, ← Real.sqrt_mul (by positivity)]
    have h2 : u * v + 2 * K = Real.sqrt ((u * v + 2 * K) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [h1, h2]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (u - v)])
  unfold prof hprof
  rw [← ha, ← hb]
  have key : u * (v - u) / a ≤ b - a := by
    rw [div_le_iff₀ hapos]; nlinarith
  have e : (1 - u / a) * (v - u) = (v - u) - u * (v - u) / a := by ring
  rw [e]; linarith

/-! ## Abel summation against Mertens from below -/

/-- **Abel summation against a lower bound for the partial sums**: if `Σ_{n ≤ k}a_n ≥ log k − c` for
`1 ≤ k ≤ B` and `g ≥ 0` decreases on `[1, B]`, then
`Σ_{n ≤ B}a_n g_n ≥ Σ_{2 ≤ n ≤ B}(log n − log(n − 1))g_n − c·g_1`. -/
lemma abel_ge {a g : ℕ → ℝ} {c : ℝ} {B : ℕ} (hB : 1 ≤ B)
    (ha : ∀ k, 1 ≤ k → k ≤ B → Real.log k - c ≤ ∑ n ∈ Icc 1 k, a n)
    (hg : ∀ k, 1 ≤ k → k < B → g (k + 1) ≤ g k) (hg0 : ∀ k, 1 ≤ k → k ≤ B → 0 ≤ g k) :
    ∑ n ∈ Icc 2 B, (Real.log n - Real.log (n - 1 : ℕ)) * g n - c * g 1 ≤ ∑ n ∈ Icc 1 B, a n * g n := by
  -- the stronger statement with the boundary term `(S_k − log k + c)g_k ≥ 0`, by induction on `k`
  have key : ∀ k, 1 ≤ k → k ≤ B →
      (∑ n ∈ Icc 1 k, a n - Real.log k + c) * g k +
          (∑ n ∈ Icc 2 k, (Real.log n - Real.log (n - 1 : ℕ)) * g n - c * g 1) ≤
        ∑ n ∈ Icc 1 k, a n * g n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _
      simp
      linarith
    | succ k hk ih =>
      intro hkB
      have ih' := ih (by omega)
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have hS := ha k hk (by omega)
      have hgk := hg k hk (by omega)
      have e : ((k + 1 - 1 : ℕ) : ℝ) = k := by simp
      rw [e]
      push_cast
      have hmono : 0 ≤ (∑ n ∈ Icc 1 k, a n - Real.log k + c) * (g k - g (k + 1)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  have h := key B hB le_rfl
  have hbd : 0 ≤ (∑ n ∈ Icc 1 B, a n - Real.log B + c) * g B :=
    mul_nonneg (by linarith [ha B hB le_rfl]) (hg0 B hB le_rfl)
  linarith

/-- **The telescoping comparison**: for `B ≥ 1`,
`Σ_{2 ≤ n ≤ B}(log n − log(n − 1))h(u₀ + log n) ≥ D(u₀ + log 2) − D(u₀ + log(B + 1))`, as
`log n − log(n − 1) ≥ log(n + 1) − log n` and `D(s) − D(s′) ≤ h(s)(s′ − s)` (`prof_step`). -/
lemma tele_ge {K u₀ : ℝ} (hK : 0 < K) (hu : 0 ≤ u₀) {B : ℕ} (hB : 1 ≤ B) :
    prof K (u₀ + Real.log 2) - prof K (u₀ + Real.log ((B : ℝ) + 1)) ≤
      ∑ n ∈ Icc 2 B, (Real.log n - Real.log (n - 1 : ℕ)) * hprof K (u₀ + Real.log n) := by
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have e : ((k + 1 - 1 : ℕ) : ℝ) = k := by simp
    rw [e]
    push_cast
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hlk : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hstep := prof_step hK (u := u₀ + Real.log ((k : ℝ) + 1)) (v := u₀ + Real.log ((k : ℝ) + 1 + 1))
      (by linarith) (by have := Real.log_le_log (by linarith) (show (k : ℝ) + 1 ≤ k + 1 + 1 by linarith); linarith)
    -- `log(k + 2) − log(k + 1) ≤ log(k + 1) − log k`
    have hcmp : Real.log ((k : ℝ) + 1 + 1) - Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
      have h1 : Real.log ((k : ℝ) + 1 + 1) + Real.log k ≤ Real.log ((k : ℝ) + 1) + Real.log ((k : ℝ) + 1) := by
        rw [← Real.log_mul (by linarith) hk0.ne', ← Real.log_mul (by linarith) (by linarith)]
        exact Real.log_le_log (by positivity) (by nlinarith)
      linarith
    have hh := hprof_nonneg hK (show 0 ≤ u₀ + Real.log ((k : ℝ) + 1) by linarith)
    have hm := mul_le_mul_of_nonneg_left hcmp hh
    have e2 : u₀ + Real.log ((k : ℝ) + 1 + 1) - (u₀ + Real.log ((k : ℝ) + 1)) =
        Real.log ((k : ℝ) + 1 + 1) - Real.log ((k : ℝ) + 1) := by ring
    rw [e2] at hstep
    nlinarith

/-- **The children sum, from below**: for `1 ≤ j ≤ N` and `K > 0`,
`Σ_{n ≤ N/j}(Λ(n)/n)h(log j + log n) ≥ D(log j) − D(log N) − 1 − log 2` (`abel_ge` with `mertens_ge`,
`tele_ge`, and `j(⌊N/j⌋ + 1) > N`). -/
lemma child_ge {K : ℝ} (hK : 0 < K) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    prof K (Real.log j) - prof K (Real.log N) - 1 - Real.log 2 ≤
      ∑ n ∈ Icc 1 (N / j), Λ n / n * hprof K (Real.log j + Real.log n) := by
  have hB : 1 ≤ N / j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hu : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  have hab := abel_ge (a := fun n => Λ n / n) (g := fun n => hprof K (Real.log j + Real.log n)) (c := 1) hB
    (fun k _ _ => mertens_ge k)
    (fun k hk _ => by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      refine hprof_anti hK (by have := Real.log_natCast_nonneg k; linarith) ?_
      push_cast
      have := Real.log_le_log hk0 (show (k : ℝ) ≤ k + 1 by linarith)
      linarith)
    (fun k _ _ => hprof_nonneg hK (by have := Real.log_natCast_nonneg k; linarith))
  have htel := tele_ge hK hu hB
  simp only [Nat.cast_one, Real.log_one, add_zero] at hab
  -- `D(log j + log 2) ≥ D(log j) − log 2`
  have h2 := prof_step hK (u := Real.log j) (v := Real.log j + Real.log 2) hu
    (by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith)
  have hle1 := hprof_le_one hK hu
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2' : prof K (Real.log j) - prof K (Real.log j + Real.log 2) ≤ Real.log 2 := by
    have : hprof K (Real.log j) * (Real.log j + Real.log 2 - Real.log j) ≤ Real.log 2 := by
      rw [show Real.log j + Real.log 2 - Real.log j = Real.log 2 by ring]
      nlinarith
    linarith
  -- `D(log j + log(⌊N/j⌋ + 1)) ≤ D(log N)`
  have hNj : (N : ℝ) ≤ j * (((N / j : ℕ) : ℝ) + 1) := by
    have h := Nat.lt_div_mul_add (a := N) (b := j) (by omega)
    have h' : (N : ℝ) < ((N / j : ℕ) : ℝ) * j + j := by exact_mod_cast h
    nlinarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : Real.log N ≤ Real.log j + Real.log (((N / j : ℕ) : ℝ) + 1) := by
    rw [← Real.log_mul hj0.ne' (by positivity)]
    exact Real.log_le_log hN0 hNj
  have hD := prof_anti hK (Real.log_natCast_nonneg N) hlogN
  have hg1 := hprof_nonneg hK hu
  nlinarith

/-! ## Landau's slack, with the defect kept and shared out -/

/-- **The edge inequality**: for `Λ ≥ 0`, `s > 0` with `s² = n`, `ℓ > 0` and `d ≥ 0`,
`2(Λ/s)ab ≤ a²Λ/n + b²Λ − a²(Λ/n)·d/(ℓ + d) + b²Λd/ℓ`, i.e.
`(Λ/n)(a − sb)² + (Λd/ℓ)b² ≥ (Λ/n)(d/(ℓ + d))a²`: the difference is `Λ(aℓ − sb(ℓ + d))²/(nℓ(ℓ + d))`. -/
lemma edge_ineq {Λ' n s ℓ d a b : ℝ} (hΛ : 0 ≤ Λ') (hs : 0 < s) (hn : s ^ 2 = n) (hℓ : 0 < ℓ) (hd : 0 ≤ d) :
    2 * (Λ' / s) * (a * b) ≤
      a ^ 2 * (Λ' / n) + b ^ 2 * Λ' - a ^ 2 * (Λ' / n) * (d / (ℓ + d)) + b ^ 2 * (Λ' * (d / ℓ)) := by
  subst hn
  have hld : 0 < ℓ + d := by linarith
  have key : a ^ 2 * (Λ' / s ^ 2) + b ^ 2 * Λ' - a ^ 2 * (Λ' / s ^ 2) * (d / (ℓ + d)) + b ^ 2 * (Λ' * (d / ℓ)) -
      2 * (Λ' / s) * (a * b) = Λ' * (a * ℓ - b * s * (ℓ + d)) ^ 2 / (s ^ 2 * ℓ * (ℓ + d)) := by
    field_simp
    ring
  have : 0 ≤ Λ' * (a * ℓ - b * s * (ℓ + d)) ^ 2 / (s ^ 2 * ℓ * (ℓ + d)) := by positivity
  linarith

/-- `Σ_{n ≤ N}Σ_{jn ≤ N}G(n, j) = Σ_{j ≤ N}Σ_{n ≤ N/j}G(n, j)`. -/
lemma sum_swap (N : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), G n j =
      ∑ j ∈ Icc 1 N, ∑ n ∈ Icc 1 (N / j), G n j := by
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun j => Icc 1 (N / j))]
  intro n j
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, ⟨hj1, hjN⟩, hjn⟩
    exact ⟨⟨hn1, (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hjn)⟩, hj1, hjN⟩
  · rintro ⟨⟨hn1, hnj⟩, hj1, hjN⟩
    have hjn : n * j ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hnj
    exact ⟨⟨hn1, by nlinarith⟩, ⟨hj1, hjN⟩, by rw [mul_comm]; exact hjn⟩

/-- `Σ_{n ≤ N}Σ_{jn ≤ N}F(jn)Λ(n) = Σ_{m ≤ N}F(m)log m`, as `Σ_{n ∣ m}Λ(n) = log m`. -/
lemma sum_dvd_log (N : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), F (j * n) * Λ n =
      ∑ m ∈ Icc 1 N, F m * Real.log m := by
  have h1 : ∀ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), F (j * n) * Λ n =
      ∑ m ∈ (Icc 1 N).filter (n ∣ ·), F m * Λ n := fun n hn =>
    sum_mul_eq_sum_dvd N (Finset.mem_Icc.1 hn).1 (fun m => F m * Λ n)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm' (t' := Icc 1 N) (s' := fun m => m.divisors)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  · intro n m
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, ⟨hm1, hmN⟩, hnm⟩
      exact ⟨⟨hnm, by omega⟩, hm1, hmN⟩
    · rintro ⟨⟨hnm, -⟩, hm1, hmN⟩
      have hn1 : 1 ≤ n := Nat.pos_of_dvd_of_pos hnm (by omega)
      exact ⟨⟨hn1, (Nat.le_of_dvd (by omega) hnm).trans hmN⟩, ⟨hm1, hmN⟩, hnm⟩

/-- `r(m) = d(m)/(log m + d(m))`, the share of the edge into `m` that its parent keeps. -/
def rr (d : ℕ → ℝ) (m : ℕ) : ℝ := d m / (Real.log m + d m)

/-- **Landau's slack, from below, for any weights** `d(m) ≥ 0` (`m ≥ 2`):
`G(c) ≥ Σ_j c_j²(κ_j + Σ_{n ≤ N/j}(Λ(n)/n)r(jn) − d(j)·log j/log j)`, with
`κ_j = log N + log 4 + 1 − Σ_{n ≤ N/j}Λ(n)/n − log j`. (`log j/log j` is `1` for `j ≥ 2` and `0` at `j = 1`.) -/
lemma slack_ge (N : ℕ) (c d : ℕ → ℝ) (hd : ∀ m, 2 ≤ m → 0 ≤ d m) :
    ∑ j ∈ Icc 1 N, c j ^ 2 * (Real.log N + (Real.log 4 + 1) - ∑ n ∈ Icc 1 (N / j), Λ n / n - Real.log j +
        ∑ n ∈ Icc 1 (N / j), Λ n / n * rr d (j * n) - d j / Real.log j * Real.log j) ≤ landauSlack N c := by
  have hterm : ∀ n ∈ Icc 1 N, ∀ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N),
      2 * (Λ n / Real.sqrt n) * (c j * c (j * n)) ≤
        c j ^ 2 * (Λ n / n) + c (j * n) ^ 2 * Λ n - c j ^ 2 * (Λ n / n) * rr d (j * n) +
          c (j * n) ^ 2 * d (j * n) / Real.log ((j * n : ℕ) : ℝ) * Λ n := by
    intro n hn j hj
    have hn1 := (Finset.mem_Icc.1 hn).1
    have hj1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hj).1).1
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have : n = 1 := by omega
      subst this
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hm2 : 2 ≤ j * n := by nlinarith
    have hℓ : 0 < Real.log ((j * n : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < j * n by omega))
    have h := edge_ineq (Λ' := Λ n) (n := n) (s := Real.sqrt n) (ℓ := Real.log ((j * n : ℕ) : ℝ))
      (d := d (j * n)) (a := c j) (b := c (j * n)) ArithmeticFunction.vonMangoldt_nonneg
      (Real.sqrt_pos.2 hn0) (Real.sq_sqrt hn0.le) hℓ (hd _ hm2)
    have e : c (j * n) ^ 2 * d (j * n) / Real.log ((j * n : ℕ) : ℝ) * Λ n =
        c (j * n) ^ 2 * (Λ n * (d (j * n) / Real.log ((j * n : ℕ) : ℝ))) := by ring
    rw [e]
    unfold rr
    exact h
  have hsum := Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun j hj => hterm n hn j hj
  -- the four double sums
  have hA : ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N),
      (c j ^ 2 * (Λ n / n) + c (j * n) ^ 2 * Λ n - c j ^ 2 * (Λ n / n) * rr d (j * n) +
        c (j * n) ^ 2 * d (j * n) / Real.log ((j * n : ℕ) : ℝ) * Λ n) =
      ∑ j ∈ Icc 1 N, c j ^ 2 * (∑ n ∈ Icc 1 (N / j), Λ n / n - ∑ n ∈ Icc 1 (N / j), Λ n / n * rr d (j * n)) +
        ∑ m ∈ Icc 1 N, (c m ^ 2 + c m ^ 2 * d m / Real.log m) * Real.log m := by
    have e1 : ∀ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N),
        (c j ^ 2 * (Λ n / n) + c (j * n) ^ 2 * Λ n - c j ^ 2 * (Λ n / n) * rr d (j * n) +
          c (j * n) ^ 2 * d (j * n) / Real.log ((j * n : ℕ) : ℝ) * Λ n) =
        ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), (c j ^ 2 * (Λ n / n) - c j ^ 2 * (Λ n / n) * rr d (j * n)) +
          ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N),
            (c (j * n) ^ 2 + c (j * n) ^ 2 * d (j * n) / Real.log ((j * n : ℕ) : ℝ)) * Λ n := by
      intro n _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, sum_swap N
      (fun n j => c j ^ 2 * (Λ n / n) - c j ^ 2 * (Λ n / n) * rr d (j * n)),
      sum_dvd_log N (fun m => c m ^ 2 + c m ^ 2 * d m / Real.log m)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hA] at hsum
  have hL : 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n =
      ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), 2 * (Λ n / Real.sqrt n) * (c j * c (j * n)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold ex
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold landauSlack S2
  rw [hL]
  have e3 : (Real.log N + (Real.log 4 + 1)) * ∑ j ∈ Icc 1 N, c j ^ 2 -
      (∑ j ∈ Icc 1 N, c j ^ 2 * (∑ n ∈ Icc 1 (N / j), Λ n / n - ∑ n ∈ Icc 1 (N / j), Λ n / n * rr d (j * n)) +
        ∑ m ∈ Icc 1 N, (c m ^ 2 + c m ^ 2 * d m / Real.log m) * Real.log m) =
      ∑ j ∈ Icc 1 N, c j ^ 2 * (Real.log N + (Real.log 4 + 1) - ∑ n ∈ Icc 1 (N / j), Λ n / n - Real.log j +
        ∑ n ∈ Icc 1 (N / j), Λ n / n * rr d (j * n) - d j / Real.log j * Real.log j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith

/-! ## The weights, and the gap -/

lemma sum_inv_sq_le (B : ℕ) : ∑ n ∈ Icc 2 B, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 3 / 4 := by
  rcases Nat.lt_or_ge B 2 with hB | hB
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; norm_num
  have key : ∀ k : ℕ, 2 ≤ k → ∑ n ∈ Icc 2 k, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 3 / 4 - 1 / (k : ℝ) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have h : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / k - 1 / ((k + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hk0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have h := key B hB
  have : (0 : ℝ) ≤ 1 / B := by positivity
  linarith

/-- **The profile beats the correction**: for `L ≥ 1` and `m ≥ 2`, `D(log m) ≥ 2√L/m` with `K = 2L`, as
`√L(m² − 1) ≥ m log m`. -/
lemma prof_ge {L : ℝ} (hL : 1 ≤ L) {m : ℕ} (hm : 2 ≤ m) :
    2 * Real.sqrt L / m ≤ prof (2 * L) (Real.log m) := by
  have hm0 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hu : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hum : Real.log m ≤ m - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by linarith); linarith
  have hsL : 1 ≤ Real.sqrt L := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL
  have hss : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  unfold prof
  have hx : 0 ≤ Real.log m + 2 * Real.sqrt L / m := by positivity
  have hsq : (Real.log m + 2 * Real.sqrt L / m) ^ 2 ≤ Real.log m ^ 2 + 2 * (2 * L) := by
    have h1 : Real.log m * m ≤ Real.sqrt L * (m ^ 2 - 1) := by
      have h1a : Real.log m * m ≤ (m - 1) * m := mul_le_mul_of_nonneg_right hum (by linarith)
      have h1b : ((m : ℝ) - 1) * m ≤ m ^ 2 - 1 := by nlinarith
      have h1c : (m : ℝ) ^ 2 - 1 ≤ Real.sqrt L * (m ^ 2 - 1) := by
        have := mul_le_mul_of_nonneg_right hsL (show (0 : ℝ) ≤ m ^ 2 - 1 by nlinarith)
        linarith
      linarith
    have hm0' : (0 : ℝ) < m := by linarith
    rw [add_sq, div_pow, show 2 * Real.log m * (2 * Real.sqrt L / m) = 4 * Real.sqrt L * Real.log m / m by ring]
    rw [mul_pow, hss]
    have h2 : 4 * Real.sqrt L * Real.log m / m ≤ 4 * L * (1 - 1 / m ^ 2) := by
      rw [div_le_iff₀ hm0']
      have : 4 * L * (1 - 1 / (m : ℝ) ^ 2) * m = 4 * L * (m ^ 2 - 1) / m := by field_simp
      rw [this, le_div_iff₀ hm0']
      nlinarith
    have h3 : (2 : ℝ) ^ 2 * L / (m : ℝ) ^ 2 = 4 * L * (1 / m ^ 2) := by ring
    rw [h3]
    nlinarith
  have := (Real.le_sqrt hx (by positivity)).2 hsq
  linarith

/-- `r(m) ≥ h(log m) − ψ/log m` when `d(m) = D(log m) − ψ`, `0 ≤ ψ ≤ D(log m)`, `m ≥ 2`. -/
lemma rr_ge {K : ℝ} (hK : 0 < K) {ℓ ψ : ℝ} (hℓ : 0 < ℓ) (hψ : 0 ≤ ψ) (hψD : ψ ≤ prof K ℓ) :
    hprof K ℓ - ψ / ℓ ≤ (prof K ℓ - ψ) / (ℓ + (prof K ℓ - ψ)) := by
  rw [← hprof_eq hK ℓ]
  set D := prof K ℓ
  have hX : 0 < ℓ + D := by linarith
  have hY : 0 < ℓ + (D - ψ) := by linarith
  have key : (D - ψ) / (ℓ + (D - ψ)) - (D / (ℓ + D) - ψ / ℓ) =
      ψ * ((ℓ + D) * (D - ψ) + D * ℓ) / (ℓ * (ℓ + D) * (ℓ + (D - ψ))) := by
    field_simp
    ring
  have : 0 ≤ ψ * ((ℓ + D) * (D - ψ) + D * ℓ) / (ℓ * (ℓ + D) * (ℓ + (D - ψ))) := by
    have h1 : 0 ≤ (ℓ + D) * (D - ψ) + D * ℓ := by nlinarith
    positivity
  linarith

/-- **The Landau gap is at least `√log N`**: for `N ≥ 3` and every real `c`,
`(√log N/2)·Σ_{j ≤ N}c_j²/j ≤ 5Σ_{j ≤ N}c_j² + G(c)`. -/
theorem gap_ge {N : ℕ} (hN : 3 ≤ N) (c : ℕ → ℝ) :
    Real.sqrt (Real.log N) / 2 * ∑ j ∈ Icc 1 N, c j ^ 2 / j ≤ 5 * S2 N c + landauSlack N c := by
  set L := Real.log N with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hN0]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.exp_one_lt_d9
    linarith
  have hK : 0 < 2 * L := by linarith
  set K := 2 * L with hKdef
  set s := Real.sqrt L with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL1
  have hss : s ^ 2 = L := Real.sq_sqrt (by linarith)
  -- the weights
  set d : ℕ → ℝ := fun m => prof K (Real.log m) - 2 * s / m with hd
  have hdnn : ∀ m, 2 ≤ m → 0 ≤ d m := fun m hm => by
    simp only [hd]; linarith [prof_ge hL1 hm]
  have hslack := slack_ge N c d hdnn
  have hl2 := Real.log_two_lt_d9
  -- `D(L) ≤ 2`
  have hDL : prof K L ≤ 2 := by
    rw [prof_eq hK (by linarith)]
    have h1 : L ≤ Real.sqrt (L ^ 2 + 2 * K) := le_sqrt_K hK (by linarith)
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- the vertex inequality
  have hvert : ∀ j ∈ Icc 1 N, s / 2 / j ≤ 5 + (L + (Real.log 4 + 1) - ∑ n ∈ Icc 1 (N / j), Λ n / n -
      Real.log j + ∑ n ∈ Icc 1 (N / j), Λ n / n * rr d (j * n) - d j / Real.log j * Real.log j) := by
    intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.1 hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hu : 0 ≤ Real.log j := Real.log_natCast_nonneg j
    -- `κ_j ≥ 0`
    have hκ : 0 ≤ L + (Real.log 4 + 1) - ∑ n ∈ Icc 1 (N / j), Λ n / n - Real.log j := by
      have h1 := mertens_le_sharp (N / j)
      have hB : 1 ≤ N / j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have hBpos : (0 : ℝ) < ((N / j : ℕ) : ℝ) := by exact_mod_cast (show 0 < N / j by omega)
      have h2 : Real.log ((N / j : ℕ) : ℝ) ≤ L - Real.log j := by
        rw [hLdef, ← Real.log_div hN0.ne' hj0.ne']
        exact Real.log_le_log hBpos Nat.cast_div_le
      linarith
    -- the children sum, from below
    have hch : prof K (Real.log j) - prof K L - 1 - Real.log 2 - 3 * (s / 2 / j) ≤
        ∑ n ∈ Icc 1 (N / j), Λ n / n * rr d (j * n) := by
      have hc := child_ge (N := N) hK hj1 hjN
      have hterm : ∀ n ∈ Icc 1 (N / j), Λ n / n * hprof K (Real.log j + Real.log n) -
          2 * s / j * (1 / (n : ℝ) ^ 2) * (if 2 ≤ n then 1 else 0) ≤ Λ n / n * rr d (j * n) := by
        intro n hn
        have hn1 := (Finset.mem_Icc.1 hn).1
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · have : n = 1 := by omega
          subst this
          simp [ArithmeticFunction.vonMangoldt_apply_one]
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hm2 : 2 ≤ j * n := by nlinarith
        have hmR : ((j * n : ℕ) : ℝ) = j * n := by push_cast; ring
        have hℓ : 0 < Real.log ((j * n : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < j * n by omega))
        have hlogjn : Real.log ((j * n : ℕ) : ℝ) = Real.log j + Real.log n := by
          rw [hmR, Real.log_mul hj0.ne' hn0.ne']
        have hψ : 0 ≤ 2 * s / ((j * n : ℕ) : ℝ) := by positivity
        have hψD := prof_ge hL1 hm2
        have hr := rr_ge hK hℓ hψ hψD
        have hrr : rr d (j * n) = (prof K (Real.log ((j * n : ℕ) : ℝ)) - 2 * s / ((j * n : ℕ) : ℝ)) /
            (Real.log ((j * n : ℕ) : ℝ) + (prof K (Real.log ((j * n : ℕ) : ℝ)) - 2 * s / ((j * n : ℕ) : ℝ))) := rfl
        rw [hrr, ← hlogjn]
        simp only [hn2, ↓reduceIte, mul_one]
        have hΛ : 0 ≤ Λ n / n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn0.le
        have hm := mul_le_mul_of_nonneg_left hr hΛ
        -- `(Λ(n)/n)·(2s/(jn))/log(jn) ≤ 2s/(jn²)`
        have hloss : Λ n / n * (2 * s / ((j * n : ℕ) : ℝ) / Real.log ((j * n : ℕ) : ℝ)) ≤
            2 * s / j * (1 / (n : ℝ) ^ 2) := by
          have hΛl : Λ n ≤ Real.log ((j * n : ℕ) : ℝ) := by
            rw [hlogjn]; linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)]
          have e : Λ n / n * (2 * s / ((j * n : ℕ) : ℝ) / Real.log ((j * n : ℕ) : ℝ)) =
              2 * s / j * (1 / (n : ℝ) ^ 2) * (Λ n / Real.log ((j * n : ℕ) : ℝ)) := by
            rw [hmR]; field_simp
          rw [e]
          have h1 : Λ n / Real.log ((j * n : ℕ) : ℝ) ≤ 1 := (div_le_one hℓ).2 hΛl
          have h2 : 0 ≤ 2 * s / j * (1 / (n : ℝ) ^ 2) := by positivity
          nlinarith
        have e2 : Λ n / n * (hprof K (Real.log ((j * n : ℕ) : ℝ)) -
            2 * s / ((j * n : ℕ) : ℝ) / Real.log ((j * n : ℕ) : ℝ)) =
            Λ n / n * hprof K (Real.log ((j * n : ℕ) : ℝ)) -
              Λ n / n * (2 * s / ((j * n : ℕ) : ℝ) / Real.log ((j * n : ℕ) : ℝ)) := by ring
        rw [e2] at hm
        linarith
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_sub_distrib] at hsum
      have hcorr : ∑ n ∈ Icc 1 (N / j), 2 * s / j * (1 / (n : ℝ) ^ 2) * (if 2 ≤ n then 1 else 0) ≤
          3 * (s / 2 / j) := by
        have e : ∑ n ∈ Icc 1 (N / j), 2 * s / j * (1 / (n : ℝ) ^ 2) * (if 2 ≤ n then 1 else 0) =
            2 * s / j * ∑ n ∈ Icc 2 (N / j), (1 : ℝ) / (n : ℝ) ^ 2 := by
          simp only [mul_ite, mul_one, mul_zero]
          rw [← Finset.sum_filter]
          have hf : (Icc 1 (N / j)).filter (fun n => 2 ≤ n) = Icc 2 (N / j) := by
            ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
          rw [hf, Finset.mul_sum]
        rw [e]
        have h := sum_inv_sq_le (N / j)
        have hpos : 0 ≤ 2 * s / j := by positivity
        have := mul_le_mul_of_nonneg_left h hpos
        have e' : 2 * s / j * (3 / 4) = 3 * (s / 2 / j) := by ring
        linarith
      linarith
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · -- the root
      have : j = 1 := by omega
      subst this
      simp only [Nat.cast_one, Real.log_one, div_zero, zero_mul, sub_zero, div_one] at hch hκ ⊢
      have hD0 : prof K 0 = 2 * s := by
        unfold prof
        rw [show (0 : ℝ) ^ 2 + 2 * K = (2 * s) ^ 2 by rw [hKdef, mul_pow, hss]; ring]
        rw [Real.sqrt_sq (by linarith)]; ring
      rw [hD0] at hch
      linarith
    · have hlj : 0 < Real.log j := Real.log_pos (by exact_mod_cast (show 1 < j by omega))
      have hdj : d j / Real.log j * Real.log j = prof K (Real.log j) - 2 * s / j := by
        rw [div_mul_cancel₀ _ hlj.ne']
      rw [hdj]
      have e : 2 * s / (j : ℝ) = 4 * (s / 2 / j) := by ring
      rw [e]
      have : 0 ≤ s / 2 / j := by positivity
      linarith
  -- assemble
  have hS2 : 5 * S2 N c = ∑ j ∈ Icc 1 N, c j ^ 2 * 5 := by
    unfold S2; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hlow : ∑ j ∈ Icc 1 N, c j ^ 2 * (s / 2 / j) ≤
      ∑ j ∈ Icc 1 N, c j ^ 2 * 5 + ∑ j ∈ Icc 1 N, c j ^ 2 * (L + (Real.log 4 + 1) -
        ∑ n ∈ Icc 1 (N / j), Λ n / n - Real.log j + ∑ n ∈ Icc 1 (N / j), Λ n / n * rr d (j * n) -
          d j / Real.log j * Real.log j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hvert j hj) (sq_nonneg _)
  have hlhs : s / 2 * ∑ j ∈ Icc 1 N, c j ^ 2 / j = ∑ j ∈ Icc 1 N, c j ^ 2 * (s / 2 / j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hlhs, hS2]
  linarith

/-- **The edge law**: for `N ≥ 3` and every real `x`, `Σ_{n ≤ N}x_n² n + G(c) ≥ (√log N/10)Σ_{n ≤ N}x_n²`,
`c_n = x_n√n`: `gap_ge`, and `G ≥ 0` (`BallSharp.landauSlack_nonneg`) for the factor `5`. -/
theorem edge_law {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    Real.sqrt (Real.log N) / 10 * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      ∑ n ∈ Icc 1 N, x n ^ 2 * n + landauSlack N (fun n => x n * Real.sqrt n) := by
  have h := gap_ge hN (fun n => x n * Real.sqrt n)
  have hG := landauSlack_nonneg N (fun n => x n * Real.sqrt n)
  have hS2 : S2 N (fun n => x n * Real.sqrt n) = ∑ n ∈ Icc 1 N, x n ^ 2 * n := by
    unfold S2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hmass : ∑ j ∈ Icc 1 N, (x j * Real.sqrt j) ^ 2 / j = ∑ n ∈ Icc 1 N, x n ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.1 hn).1; omega)
    rw [mul_pow, Real.sq_sqrt hn0.le]
    field_simp
  rw [hS2, hmass] at h
  have hsq : 0 ≤ Real.sqrt (Real.log N) / 10 * ∑ n ∈ Icc 1 N, x n ^ 2 := by positivity
  nlinarith

/-- **The rate `λ_N ≫ √log N/N`** (RH): for `N ≥ 3` and every real `x`,
`Q_N(x) ≥ √log N/(220e⁸N)·Σ_{n ≤ N}x_n²` (`BallSharp.rate_slack` with `edge_law`). -/
theorem rate_gap (hRH : RiemannHypothesis) {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    Real.sqrt (Real.log N) / (220 * Real.exp 8 * N) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  have h := rate_slack hRH (show 1 ≤ N by omega) x
  have he := edge_law hN x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 0 < 1 / (22 * Real.exp 8 * N) := by positivity
  have hm := mul_le_mul_of_nonneg_left he hc.le
  have e : Real.sqrt (Real.log N) / (220 * Real.exp 8 * N) * ∑ n ∈ Icc 1 N, x n ^ 2 =
      1 / (22 * Real.exp 8 * N) * (Real.sqrt (Real.log N) / 10 * ∑ n ∈ Icc 1 N, x n ^ 2) := by
    field_simp; ring
  rw [e]
  linarith

end BallGap
