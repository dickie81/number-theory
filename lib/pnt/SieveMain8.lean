/-
# Linnik's theorem by the sieve route, under the certificate of depth 8

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK`, `GridOKC` and `Fits`), with
`HC = 4H`, `H > 0` and `4H + 4HC ≤ V` (`SieveDrop8.DeepGrid`). The decomposition's rule is the bilinear Type I rule
(`SieveCert.ibRule`) with the route's exponent (`IBFits`), and its decisions are the certificate's
(`SieveDrop8.schemeD`, from `SieveDeep.scheme`); `totalD` is the certificate's total (`SieveDeepDefs.lean`).

* `linnik_large8`: given the route's Type II estimate (`hII`) and `totalD/K ≤ c` in the reals for some `c < 1`
  (`htot`), there is `q₀` such that for `q ≥ 1` with `q ≥ q₀` and `a` a unit mod `q` there is a prime `p ≡ a (mod q)`
  with `q^L < p ≤ 2q^L`.
* `linnik_route8`: given `hII` and `htot`, there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there
  is a prime `p ≡ a (mod q)` with `p ≤ K·q^L`; `linnik_route_lt8`: the same for `totalD < K`.

The proof combines `SieveBuch.Par.decomp8` (the decomposition to depth 8), `SieveQ8.leaves_ev8`,
`SieveDrop8.drop_ev8` and the decomposition's constant `Cdec8`; the small moduli are `SieveMain2.route_of_large`'s.

The file imports `SieveDrop8.lean`, `SieveQ8.lean` and `SieveMain2.lean`.
-/
import SieveDrop8
import SieveQ8
import SieveMain2

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveRoute SieveDeep
  SieveDrop8

namespace SieveMain8

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits]

attribute [local instance] SieveCert.ibRule

omit [Route] [RouteOK] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits] in
theorem Cdec8_pos : 0 < SieveBuch.Par.Cdec8 := by
  unfold SieveBuch.Par.Cdec8 SieveBuch.Par.ec0'
  have := SieveBuch.Par.ec1'_nonneg
  positivity

omit [Route] [RouteOK] [SieveCert.GridOK] [SieveCert.GridOKC] [Fits] in
theorem totalD_div_lt [SieveCert.IBPar] (htot : totalD < SieveCert.K) : (totalD : ℝ) / SieveCert.K < 1 := by
  rw [div_lt_one SieveCert.K_pos']
  exact_mod_cast htot

/-- **Linnik's theorem at `x = q^L`, for large `q`, under the certificate of depth 8.** For a route with `RouteOK` and
a grid with `GridOK`, `GridOKC` and `DeepGrid` that fit (`Fits`), under the bilinear Type I rule with the route's
exponent (`IBFits`), given the route's Type II estimate (`hII`) and `totalD/K ≤ c` in the reals for some `c < 1`
(`htot`), there is `q₀` such that for `q ≥ 1` with `q ≥ q₀` and `a` a unit mod `q` there is a prime `p ≡ a (mod q)`
with `q^L < p ≤ 2q^L`. The losses are five shares `ε = (1 − c)/10` of `X = x/log x`, leaving `(1 − c)X/2` of
`S(A, z_top)`. -/
theorem linnik_large8 [SieveCert.IBPar] [IBFits] [DeepGrid] (hII : TypeIIAt) {c : ℝ} (hc : c < 1)
    (htot : (totalD : ℝ) / SieveCert.K ≤ c) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L := by
  have : SieveCert.RuleIB := SieveCert.ibRule_ib
  have : SieveCert.RuleNB := SieveCert.RuleIB.toRuleNB
  have hC := Cdec8_pos
  have hL0 : 0 < L := L_pos
  set ε : ℝ := (1 - c) / 10 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set η : ℝ := ε / (SieveBuch.Par.Cdec8 * L) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ, hδ, q₁, hlv⟩ := SieveQ8.leaves_ev8 hII hη0
  have hev1 := SieveMain.ev_log_le (c := ε / (SieveBuch.Par.Cdec8 * L)) (by positivity) hδ
  have hev2 := SieveMain.ev_log_le (c := ε / L) (by positivity) (show (0 : ℝ) < L - 1 by linarith [two_lt_L])
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 ((SieveMain.TB_ev hε).and
    ((drop_ev8 htot hε).and (hev1.and (hev2.and (eventually_ge_atTop 3)))))
  refine ⟨q₁ + q₂, fun q _ hq a ha => ?_⟩
  obtain ⟨hTB, hD, h1, h2, hq3⟩ := hq₂ q (by omega)
  obtain ⟨hL, Lv⟩ := hlv q (by omega) a ha
  have G := good_of_large hL
  have hq3' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  have hdec := (parQ q).decomp8 G (gA_nonneg q a) (Err_nonneg hη0 δ q (by omega)) Lv
  have hTB := hTB hL
  have hD := hD hL
  -- `X = x/log x = q^L/(L log q)`
  set Q := (q : ℝ) ^ L with hQ
  have hQ0 : 0 < Q := by positivity
  have hlogx : Real.log (xq q) = L * Real.log q := Real.log_rpow hq0 _
  set X := xq q / Real.log (xq q) with hXdef
  have hX : X = Q / (L * Real.log q) := by rw [hXdef, hlogx]
  have hX0 : 0 < X := by rw [hX]; positivity
  -- the leaves' error: `Cdec8·Err ≤ φ⁻¹(εX + εX)`
  have hErr : SieveBuch.Par.Cdec8 * Err η δ q ≤ (q.totient : ℝ)⁻¹ * (ε * X + ε * X) := by
    have hsplit : (q : ℝ) ^ (L - δ) * (q : ℝ) ^ δ = Q := by
      rw [← Real.rpow_add hq0, sub_add_cancel]
    have hd0 : 0 < (q : ℝ) ^ δ := by positivity
    have hA : SieveBuch.Par.Cdec8 * (η * Q / (q.totient * Real.log q)) = (q.totient : ℝ)⁻¹ * (ε * X) := by
      rw [hX, hη]
      field_simp
    have hB : SieveBuch.Par.Cdec8 * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) ≤ (q.totient : ℝ)⁻¹ * (ε * X) := by
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ hφ.le
      rw [hX, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      have h1' : SieveBuch.Par.Cdec8 * L * Real.log q ≤ ε * (q : ℝ) ^ δ := by
        have := h1
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
        linarith
      calc SieveBuch.Par.Cdec8 * (q : ℝ) ^ (L - δ) * (L * Real.log q)
          = (q : ℝ) ^ (L - δ) * (SieveBuch.Par.Cdec8 * L * Real.log q) := by ring
        _ ≤ (q : ℝ) ^ (L - δ) * (ε * (q : ℝ) ^ δ) := mul_le_mul_of_nonneg_left h1' (by positivity)
        _ = ε * Q := by rw [← hsplit]; ring
    unfold SieveQ.Err
    rw [mul_add]
    linarith
  -- `q ≤ εX`
  have hqX : (q : ℝ) ≤ ε * X := by
    rw [hX, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have h2' : L * Real.log q ≤ ε * (q : ℝ) ^ (L - 1) := by
      have := h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      linarith
    have hsplit : (q : ℝ) * (q : ℝ) ^ (L - 1) = Q := by
      rw [← Real.rpow_one_add' hq0.le (by rw [add_sub_cancel]; exact hL0.ne'), add_sub_cancel]
    calc (q : ℝ) * (L * Real.log q) ≤ (q : ℝ) * (ε * (q : ℝ) ^ (L - 1)) := mul_le_mul_of_nonneg_left h2' hq0.le
      _ = ε * Q := by rw [← hsplit]; ring
  -- `S(A, z_top) > 0`: what is left is `(1 − c − 5ε)X = (1 − c)X/2`
  have hpos : 0 < (parQ q).T (gA q a) := by
    have : (q.totient : ℝ)⁻¹ * ((1 - c) / 2 * X) ≤ (parQ q).T (gA q a) := by
      have e1 : (q.totient : ℝ)⁻¹ * ((1 - ε) * X - q) - (q.totient : ℝ)⁻¹ * ((c + ε) * X) -
          (q.totient : ℝ)⁻¹ * (ε * X + ε * X) ≤ (parQ q).T (gA q a) := by
        linarith
      have e2 : (q.totient : ℝ)⁻¹ * ((1 - c) / 2 * X) ≤ (q.totient : ℝ)⁻¹ * ((1 - ε) * X - q) -
          (q.totient : ℝ)⁻¹ * ((c + ε) * X) - (q.totient : ℝ)⁻¹ * (ε * X + ε * X) := by
        have : (1 - c) / 2 * X ≤ ((1 - ε) * X - q) - ((c + ε) * X) - (ε * X + ε * X) := by
          rw [hεdef] at hqX ⊢
          linarith
        nlinarith
      linarith
    have : 0 < (q.totient : ℝ)⁻¹ * ((1 - c) / 2 * X) := by
      have : 0 < (1 - c) / 2 * X := mul_pos (by linarith) hX0
      positivity
    linarith
  -- a term of `S(A, z_top)` is positive: a prime `≡ a`
  unfold Par.T at hpos
  obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  have hmA : (m : ZMod q) = a := by
    by_contra h
    simp [gA, h] at hm0
  have hmr : SieveTree.rough (parQ q).ztop m := by
    by_contra h
    simp [h] at hm0
  rw [Finset.mem_Ioc] at hm
  have hN1 : 1 ≤ N1 q := Nat.le_floor (by simpa using (Real.one_le_rpow hq1.le hL0.le : (1 : ℝ) ≤ xq q))
  have hm2 : 2 ≤ m := by have := hm.1; change N1 q < m at this; omega
  refine ⟨m, ?_, hmA, Nat.lt_of_floor_lt hm.1, ?_⟩
  · by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hmin := (SieveStops2.rough_iff_le_minFac hm2).1 hmr
    have hz : N2 q < ((parQ q).ztop) ^ 2 := by
      show N2 q < (Nat.sqrt (N2 q) + 1) ^ 2
      exact Nat.lt_succ_sqrt' _
    have : (parQ q).ztop ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hmin 2
    have := hm.2
    change m ≤ N2 q at this
    omega
  · have : (m : ℝ) ≤ N2 q := by exact_mod_cast hm.2
    exact this.trans (N2_le q)

/-- **Linnik's theorem with exponent `L`, under the certificate of depth 8.** For a route with `RouteOK` and a grid
with `GridOK`, `GridOKC` and `DeepGrid` that fit (`Fits`), under the bilinear Type I rule with the route's exponent
(`IBFits`), given the route's Type II estimate (`hII`) and `totalD/K ≤ c` in the reals for some `c < 1` (`htot`),
there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
`p ≤ K·q^L`. -/
theorem linnik_route8 [SieveCert.IBPar] [IBFits] [DeepGrid] (hII : TypeIIAt) {c : ℝ} (hc : c < 1)
    (htot : (totalD : ℝ) / SieveCert.K ≤ c) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L :=
  SieveMain2.route_of_large L_pos.le (linnik_large8 hII hc htot)

/-- **Linnik's theorem with exponent `L`, under a certificate of depth 8 whose total is below `K`.** For a route with
`RouteOK` and a grid with `GridOK`, `GridOKC` and `DeepGrid` that fit (`Fits`), under the bilinear Type I rule with
the route's exponent (`IBFits`), given the route's Type II estimate (`hII`) and the certificate's total less than `K`
(`htot`), there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
`p ≤ K·q^L`. -/
theorem linnik_route_lt8 [SieveCert.IBPar] [IBFits] [DeepGrid] (hII : TypeIIAt) (htot : totalD < SieveCert.K) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L :=
  linnik_route8 hII (totalD_div_lt htot) le_rfl

end SieveMain8

#print axioms SieveMain8.linnik_route_lt8
