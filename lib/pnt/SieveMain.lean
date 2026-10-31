/-
# The primes of `(x, 2x]` prime to `q`, for Linnik's theorem by the sieve route

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK`, `GridOKC` and `Fits`).

* `primes_dyadic_ge`: for `ε > 0`, the primes of `(⌊x⌋, ⌊2x⌋]` number at least `(1 − ε)x/log x` for large `x`.
* `TB_ev`: for `ε > 0`, `S(B, z_top) ≥ φ(q)⁻¹((1 − ε)x/log x − q)` for large `q`, at `x = q^L`.

The proof:

* `primes_dyadic_ge`: `SieveRough.theta_near` at `x` and `2x`. `TB_ev`: `z_top = ⌊√N₂⌋ + 1`, so the `z_top`-rough
  `n ∈ (N₁, N₂]` are the primes there, and at most `ω(q) ≤ q` of them divide `q`.

The route's numbers and the certificate's grids are parameters. `SieveMain8.lean` proves Linnik's theorem by the
sieve route with `TB_ev`.

The file imports `SieveDrop.lean`.
-/
import SieveDrop

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveDrop SieveRoute
open scoped Chebyshev

namespace SieveMain

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits]

/-! ### `S(B, z_top)`: the primes of `(x, 2x]` prime to `q` -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits] in
/-- For `ε > 0`, the primes of `(⌊x⌋, ⌊2x⌋]` number at least `(1 − ε)x/log x` for large `x`. -/
theorem primes_dyadic_ge {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop,
    (1 - ε) * (x / Real.log x) ≤ (((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime).card : ℝ) := by
  have hT := theta_near (ε := 1) one_pos
  have hT2 : ∀ᶠ x : ℝ in atTop, |θ (2 * x) - 2 * x| ≤ 1 * (2 * x) / Real.log (2 * x) :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually hT
  filter_upwards [hT, hT2, eventually_ge_atTop (Real.exp (4 / ε)), eventually_ge_atTop (Real.exp 1)]
    with x h1 h2 h3 h4
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) h4
  have hlx1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) h4
  have hlx : 4 / ε ≤ Real.log x := by
    rw [← Real.log_exp (4 / ε)]
    exact Real.log_le_log (Real.exp_pos _) h3
  have hl2 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2x : Real.log x ≤ Real.log (2 * x) := by linarith
  -- `Σ log p = θ(2x) − θ(x) ≥ x − 3x/log x`
  have hsum := sum_log_primes_dyadic hx0.le
  set P := (Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime with hP
  have hθ : x - 3 * x / Real.log x ≤ θ (2 * x) - θ x := by
    have e1 := (abs_le.1 h1).2
    have e2 := (abs_le.1 h2).1
    have e3 : 1 * (2 * x) / Real.log (2 * x) ≤ 2 * x / Real.log x := by
      rw [one_mul]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) hl2x
    have e4 : 1 * x / Real.log x = x / Real.log x := by ring
    have e5 : 3 * x / Real.log x = 2 * x / Real.log x + x / Real.log x := by ring
    linarith
  have hle : ∑ p ∈ P, Real.log p ≤ (P.card : ℝ) * Real.log (2 * x) := by
    have : ∀ p ∈ P, Real.log p ≤ Real.log (2 * x) := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      exact Real.log_le_log hp0 ((Nat.cast_le.2 hp.1.2).trans (Nat.floor_le (by linarith)))
    calc ∑ p ∈ P, Real.log p ≤ ∑ _p ∈ P, Real.log (2 * x) := Finset.sum_le_sum this
      _ = (P.card : ℝ) * Real.log (2 * x) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlx0 : 0 < Real.log x := by linarith
  have h2x0 : 0 < Real.log (2 * x) := by linarith
  -- `(1 − ε)(x/log x)·log 2x ≤ x − 3x/log x`
  have hkey : (1 - ε) * (x / Real.log x) * Real.log (2 * x) ≤ x - 3 * x / Real.log x := by
    rw [hl2]
    have h5 : (1 - ε) * (x / Real.log x) * (Real.log 2 + Real.log x) =
        (1 - ε) * x + (1 - ε) * x * Real.log 2 / Real.log x := by
      field_simp
      ring
    rw [h5]
    have h6 : ε * Real.log x ≥ 4 := by
      rw [div_le_iff₀ hε] at hlx
      linarith
    have h7 : (1 - ε) * x * Real.log 2 / Real.log x + 3 * x / Real.log x ≤ ε * x := by
      rw [← add_div, div_le_iff₀ hlx0]
      have hA : x * 4 ≤ x * (ε * Real.log x) := mul_le_mul_of_nonneg_left h6 hx0.le
      have hB : (1 - ε) * Real.log 2 ≤ 1 := by
        by_cases hε1 : ε ≤ 1
        · have : (1 - ε) * Real.log 2 ≤ 1 * Real.log 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hlog20.le
          linarith
        · have : (1 - ε) * Real.log 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog20.le
          linarith
      have hC : x * ((1 - ε) * Real.log 2) ≤ x * 1 := mul_le_mul_of_nonneg_left hB hx0.le
      nlinarith
    linarith
  rw [hsum] at hle
  rw [← div_le_iff₀ h2x0] at hle
  have : (1 - ε) * (x / Real.log x) ≤ (x - 3 * x / Real.log x) / Real.log (2 * x) := by
    rw [le_div_iff₀ h2x0]
    exact hkey
  linarith [this, (div_le_div_of_nonneg_right hθ h2x0.le)]

/-- For a route with `RouteOK` and a grid with `GridOK` that fit (`Fits`), and `ε > 0`:
`S(B, z_top) ≥ φ(q)⁻¹((1 − ε)x/log x − q)` for large `q`. -/
theorem TB_ev {ε : ℝ} (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop, LargeQ q →
    (q.totient : ℝ)⁻¹ * ((1 - ε) * (xq q / Real.log (xq q)) - q) ≤ (parQ q).T (gB q) := by
  filter_upwards [tendsto_xq.eventually (primes_dyadic_ge hε)] with q hq hL
  have hq3 := hL.q3
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have G := good_of_large hL
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  set P := (Ioc (N1 q) (N2 q)).filter Nat.Prime with hP
  set Pc := P.filter (fun p => Nat.Coprime p q) with hPc
  -- the primes of `(N₁, N₂]` prime to `q` are rough and prime to `q`
  have hztopN : (parQ q).ztop ≤ N1 q + 1 := by
    have h1 : ((parQ q).ztop : ℝ) ≤ Real.sqrt (2 * xq q) + 1 := (ztop_bounds q (by omega)).2
    have hx16 : (16 : ℝ) ≤ xq q := by
      have h4 : (4 : ℝ) ≤ (q : ℝ) ^ (L / 2 : ℝ) := hL.hhalf
      have : xq q = ((q : ℝ) ^ (L / 2 : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        push_cast
        ring_nf
      rw [this]
      nlinarith
    have h2 : Real.sqrt (2 * xq q) ≤ xq q - 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h3 : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    have : ((parQ q).ztop : ℝ) < (N1 q : ℝ) + 1 := by linarith
    exact_mod_cast this.le
  have hT : (q.totient : ℝ)⁻¹ * (Pc.card : ℝ) ≤ (parQ q).T (gB q) := by
    unfold Par.T
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    have hsub : Pc ⊆ Ioc (N1 q) (N2 q) := fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
      mul_nonneg (gB_nonneg q m) (by split_ifs <;> norm_num))
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hPc, hP, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨h1, -⟩, hpp⟩, hcop⟩ := hp
    have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).2 hcop
    have hr : SieveTree.rough (parQ q).ztop p := by
      intro ℓ hℓ hℓp hd
      have := (Nat.prime_dvd_prime_iff_eq hℓp hpp).1 hd
      omega
    simp only [gB, hu, ite_true, hr, Nat.cast_one, mul_one]
  -- the primes dividing `q` are at most `q`
  have hcount : (P.card : ℝ) - q ≤ Pc.card := by
    have h1 : P.filter (fun p => ¬ Nat.Coprime p q) ⊆ q.primeFactors := by
      intro p hp
      rw [Finset.mem_filter, hP, Finset.mem_filter] at hp
      rw [Nat.mem_primeFactors]
      exact ⟨hp.1.2, (Nat.Prime.dvd_iff_not_coprime hp.1.2).2 hp.2, by omega⟩
    have h2 : q.primeFactors.card ≤ q := by
      calc q.primeFactors.card ≤ (Finset.Icc 1 q).card := Finset.card_le_card fun p hp => by
            rw [Finset.mem_Icc]
            exact ⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le,
              Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)⟩
        _ = q := by simp
    have h3 := Finset.card_filter_add_card_filter_not (s := P) (fun p => Nat.Coprime p q)
    have h4 := (Finset.card_le_card h1).trans h2
    have : (P.card : ℝ) ≤ Pc.card + q := by
      rw [hPc]
      exact_mod_cast (show P.card ≤ (P.filter fun p => Nat.Coprime p q).card + q by omega)
    linarith
  have hP' : (1 - ε) * (xq q / Real.log (xq q)) ≤ (P.card : ℝ) := hq
  calc (q.totient : ℝ)⁻¹ * ((1 - ε) * (xq q / Real.log (xq q)) - q)
      ≤ (q.totient : ℝ)⁻¹ * (Pc.card : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hφ.le
    _ ≤ (parQ q).T (gB q) := hT

/-! ### The count, and the theorem -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits] in
/-- `log q ≤ c q^r` for large `q`, any `c > 0`, `r > 0`. -/
theorem ev_log_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) : ∀ᶠ q : ℕ in atTop, Real.log q ≤ c * (q : ℝ) ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with q hq hq1
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  rw [Real.norm_of_nonneg (Real.log_nonneg hq0), Real.norm_of_nonneg (by positivity)] at hq
  exact hq

end SieveMain
