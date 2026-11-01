/-
# The frontier of the orbit lattice: the primes above `N/2`, always some and asymptotically half

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. Among the integers up to `N`, a prime `p ≤ N` has no multiple other than itself exactly when
`N < 2p` (`lonely_iff`), that is when `N/2 < p ≤ N`. Call these the lonely primes of stage `N`, and let
`lonely N = π(N) − π(⌊N/2⌋)` be their number.
* Every stage `N ≥ 2` has a lonely prime (`exists_lonely`, `lonely_pos`). This is Bertrand's postulate, Mathlib's
  `Nat.exists_prime_lt_and_le_two_mul`.
* They are asymptotically half of the primes up to `N` (`tendsto_lonely_ratio`): `lonely N/π(N) → ½`, by the prime
  number theorem `π(x) ~ x/log x` (PrimeNumberTheoremAnd's `pi_alt'`).
* So the proportion is bounded below by a positive constant at every stage (`lonely_ratio_pos`): some `c > 0` has
  `lonely N ≥ c·π(N)` for every `N ≥ 2`.

In the orbit lattice of `docs/ball-conjecture.md`, a lonely prime `p` of stage `N` enters the Gram matrix of
`w_1, …, w_N` only through the entries `⟨w_1, w_m⟩` with `p < m ≤ N`. Yet the positivity of that matrix needs each of
them. So at every stage a positive proportion of the prime directions is held in place by the real place alone.

* For the limit, `π(x/2)/π(x)` is equivalent to `((x/2)/log(x/2))/(x/log x) = log x/(2 log(x/2))`, which tends to `½`.
* For the bound, the limit gives `lonely N ≥ π(N)/4` from some `N₀` on. Below `N₀`, `lonely N ≥ 1` while
  `π(N) ≤ N + 1 ≤ N₀`, so `c = min(¼, 1/N₀)` works.
-/
import Mathlib
import PrimeNumberTheoremAnd.Consequences

open Filter Topology Real Asymptotics

noncomputable section

namespace LonelyPrimes

/-- The number of **lonely primes** of stage `N`: the primes `p ≤ N` with no other multiple up to `N`. -/
def lonely (N : ℕ) : ℕ := Nat.primeCounting N - Nat.primeCounting (N / 2)

/-- A prime `p ≤ N` has no multiple `kp ≤ N` with `k ≥ 2` exactly when `N/2 < p`. -/
theorem lonely_iff {p N : ℕ} : (∀ k : ℕ, 2 ≤ k → N < k * p) ↔ N / 2 < p := by
  constructor
  · intro h
    have := h 2 le_rfl
    omega
  · intro h k hk
    have : 2 * p ≤ k * p := Nat.mul_le_mul_right p hk
    omega

/-- **Every stage has a lonely prime**: for `N ≥ 2` some prime `p` has `N/2 < p ≤ N`. -/
theorem exists_lonely {N : ℕ} (hN : 2 ≤ N) : ∃ p, p.Prime ∧ N / 2 < p ∧ p ≤ N := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  exact ⟨p, hp, h1, by omega⟩

lemma primeCounting_lt {a b p : ℕ} (hp : p.Prime) (hap : a < p) (hpb : p ≤ b) :
    Nat.primeCounting a < Nat.primeCounting b := by
  unfold Nat.primeCounting Nat.primeCounting'
  calc Nat.count Nat.Prime (a + 1) ≤ Nat.count Nat.Prime p := Nat.count_monotone _ hap
    _ < Nat.count Nat.Prime (p + 1) := Nat.count_strict_mono hp (Nat.lt_succ_self p)
    _ ≤ Nat.count Nat.Prime (b + 1) := Nat.count_monotone _ (by omega)

/-- **The lonely primes are never absent**: `lonely N ≥ 1` for `N ≥ 2`. -/
theorem lonely_pos {N : ℕ} (hN : 2 ≤ N) : 0 < lonely N := by
  obtain ⟨p, hp, h1, h2⟩ := exists_lonely hN
  have := primeCounting_lt hp h1 h2
  unfold lonely
  omega

lemma primeCounting_half_le (N : ℕ) : Nat.primeCounting (N / 2) ≤ Nat.primeCounting N :=
  Nat.monotone_primeCounting (Nat.div_le_self N 2)

lemma primeCounting_le (N : ℕ) : Nat.primeCounting N ≤ N + 1 := by
  unfold Nat.primeCounting Nat.primeCounting'
  exact Nat.count_le Nat.Prime

/-- `log x/(2 log(x/2)) → ½`. -/
lemma tendsto_log_ratio :
    Tendsto (fun x : ℝ => (x / 2 / Real.log (x / 2)) / (x / Real.log x)) atTop (𝓝 (1 / 2)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h2 : Tendsto (fun x : ℝ => 1 / 2 * (1 - Real.log 2 / Real.log x)⁻¹) atTop (𝓝 (1 / 2 * (1 - 0)⁻¹)) :=
    ((tendsto_const_nhds.sub hlog).inv₀ (by norm_num)).const_mul _
  rw [sub_zero, inv_one, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 4] with x hx
  have hx0 : x ≠ 0 := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hL2 : Real.log 2 < Real.log x := Real.log_lt_log (by norm_num) (by linarith)
  have hd : Real.log (x / 2) = Real.log x - Real.log 2 := Real.log_div hx0 (by norm_num)
  have hne : Real.log x - Real.log 2 ≠ 0 := by linarith
  rw [hd]
  field_simp

/-- **The lonely primes are asymptotically half of the primes**: `lonely N/π(N) → ½`, by the prime number theorem. -/
theorem tendsto_lonely_ratio :
    Tendsto (fun N : ℕ => (lonely N : ℝ) / Nat.primeCounting N) atTop (𝓝 (1 / 2)) := by
  set f : ℝ → ℝ := fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ) with hf
  set g : ℝ → ℝ := fun x => x / Real.log x with hg
  have E : f ~[atTop] g := pi_alt'
  have hh : Tendsto (fun x : ℝ => x / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have E2 : (f ∘ fun x => x / 2) ~[atTop] (g ∘ fun x => x / 2) := E.comp_tendsto hh
  have R : (f ∘ fun x => x / 2) / f ~[atTop] (g ∘ fun x => x / 2) / g := E2.div E
  have hR : Tendsto ((f ∘ fun x => x / 2) / f) atTop (𝓝 (1 / 2)) := by
    refine R.symm.tendsto_nhds ?_
    have e : ((g ∘ fun x => x / 2) / g) = fun x : ℝ => (x / 2 / Real.log (x / 2)) / (x / Real.log x) := by
      funext x
      simp [hg, Function.comp_def]
    rw [e]
    exact tendsto_log_ratio
  have hN := hR.comp tendsto_natCast_atTop_atTop
  have hN' : Tendsto (fun N : ℕ => 1 - (Nat.primeCounting (N / 2) : ℝ) / Nat.primeCounting N) atTop
      (𝓝 (1 - 1 / 2)) := by
    refine tendsto_const_nhds.sub (hN.congr fun N => ?_)
    simp only [Function.comp_apply, Pi.div_apply, hf, Nat.floor_natCast]
    congr 3
    have := Nat.floor_div_eq_div (K := ℝ) N 2
    simpa using this
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hN'
  refine hN'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hpos : (0 : ℝ) < Nat.primeCounting N := by
    have := lonely_pos hN2
    unfold lonely at this
    exact_mod_cast (show 0 < Nat.primeCounting N by omega)
  unfold lonely
  rw [Nat.cast_sub (primeCounting_half_le N)]
  field_simp

/-- **The lonely proportion is bounded below at every stage**: some `c > 0` has `lonely N ≥ c·π(N)` for every
`N ≥ 2`. -/
theorem lonely_ratio_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * (Nat.primeCounting N : ℝ) ≤ (lonely N : ℝ) := by
  have hev : ∀ᶠ N : ℕ in atTop, (1 / 4 : ℝ) < (lonely N : ℝ) / Nat.primeCounting N :=
    tendsto_lonely_ratio.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  set M : ℕ := max N₀ 2 with hM
  have hM0 : (0 : ℝ) < M := by positivity
  refine ⟨min (1 / 4) (1 / M), lt_min (by norm_num) (by positivity), fun N hN => ?_⟩
  have hl : (1 : ℝ) ≤ lonely N := by exact_mod_cast lonely_pos hN
  have hpos : (0 : ℝ) < Nat.primeCounting N := by
    have := lonely_pos hN
    unfold lonely at this
    exact_mod_cast (show 0 < Nat.primeCounting N by omega)
  rcases le_or_gt M N with hMN | hMN
  · have h := hN₀ N (le_trans (le_max_left _ _) hMN)
    rw [lt_div_iff₀ hpos] at h
    calc min (1 / 4) (1 / (M : ℝ)) * Nat.primeCounting N ≤ 1 / 4 * Nat.primeCounting N :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hpos.le
      _ ≤ lonely N := h.le
  · have hle : (Nat.primeCounting N : ℝ) ≤ M := by
      have := primeCounting_le N
      exact_mod_cast (show Nat.primeCounting N ≤ M by omega)
    calc min (1 / 4) (1 / (M : ℝ)) * Nat.primeCounting N ≤ 1 / M * Nat.primeCounting N :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
      _ ≤ 1 / M * M := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 := by field_simp
      _ ≤ lonely N := hl

end LonelyPrimes

#print axioms LonelyPrimes.lonely_iff
#print axioms LonelyPrimes.exists_lonely
#print axioms LonelyPrimes.lonely_pos
#print axioms LonelyPrimes.tendsto_lonely_ratio
#print axioms LonelyPrimes.lonely_ratio_pos
