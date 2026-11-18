/-
# A family's `B`-count

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `L` is a route's exponent (`SieveRoute.Route`), with `RouteOK` where the Lean takes it;
`xq q = q^L`, `N1 q = ⌊q^L⌋` and `N2 q = ⌊2q^L⌋`.

* `card_le_Psi`: for `x > 0` and `W > 0`, the `n = Wc ∈ (x, 2x]` with no prime factor below `z` inject into
  `Ψ(x/W, z)` by `n ↦ n/W`.
* `gB_le`, `gB_nonneg`: `0 ≤ gB q m ≤ φ(q)⁻¹`.
* `famI_gB_le`: for `q ≥ 1`, a family of tuples of primes has `B`-count `famI(g_B)` on `(N₁, N₂]` at most
  `φ(q)⁻¹ Σ_rt Ψ(x/∏rt, rt_last)` at `x = q^L`.
* `tendsto_xq`: with `RouteOK`, `q^L → ∞` as `q → ∞`.

The file imports `SieveQ.lean`.
-/
import SieveQ

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute
open SieveCert (DEN U1 U2 K)

namespace SieveDrop

open Classical

variable [Route] [RouteOK] [SieveCert.Grid]

/-! ### A dropped family's `B`-count, by rough numbers -/

omit [Route] [RouteOK] [SieveCert.Grid] in
/-- For `x > 0` and `W > 0`, the multiples `n = Wc ∈ (x, 2x]` of `W` with no prime factor below `z` inject into
`Ψ(x/W, z)` by `n ↦ n/W`. -/
theorem card_le_Psi {x : ℝ} (hx : 0 < x) {W z : ℕ} (hW : 0 < W) :
    ((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (fun n => W ∣ n ∧ SieveTree.rough z n)).card ≤ Psi (x / W) z := by
  unfold Psi roughSet
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  refine Finset.card_le_card_of_injOn (fun n => n / W) ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    dsimp only
    rw [Nat.mul_div_cancel_left c hW]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.floor_lt (by positivity), div_lt_iff₀ hW']
      have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h4 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((W * c : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h4
      linarith
    · rw [Nat.le_floor_iff (by positivity)]
      have h3 : ((W * c : ℕ) : ℝ) ≤ 2 * x := (Nat.cast_le.2 h2).trans (Nat.floor_le (by positivity))
      push_cast at h3
      rw [mul_div_assoc', le_div_iff₀ hW']
      linarith
    · intro p hp
      by_contra hlt
      exact hr p (not_le.1 hlt) (Nat.prime_of_mem_primeFactors hp)
        (dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) W)
  · intro n₁ hn₁ n₂ hn₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hn₁ hn₂
    exact (Nat.div_left_inj hn₁.2.1 hn₂.2.1).1 h

omit [Route] [RouteOK] [SieveCert.Grid] in
theorem gB_le (q m : ℕ) : gB q m ≤ (q.totient : ℝ)⁻¹ := by
  unfold gB
  split_ifs
  · exact le_rfl
  · positivity

omit [Route] [RouteOK] [SieveCert.Grid] in
theorem gB_nonneg (q m : ℕ) : 0 ≤ gB q m := by
  unfold gB
  split_ifs <;> positivity

omit [RouteOK] [SieveCert.Grid] in
/-- **A family's `B`-count.** For `q ≥ 1` and a family of tuples of primes, it is at most
`φ(q)⁻¹ Σ_rt Ψ(x/∏rt, rt_last)`. -/
theorem famI_gB_le (q : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) (hF : ∀ rt ∈ F, ∀ i, (rt i).Prime)
    (hq : 1 ≤ q) :
    famI (gB q) (N1 q) (N2 q) F ≤
      (q.totient : ℝ)⁻¹ * ∑ rt ∈ F, (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last k')) : ℝ) := by
  have hx : 0 < xq q := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  unfold famI
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun rt hrt => ?_
  have hW : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hF rt hrt i).pos
  calc ∑ n ∈ Ioc (N1 q) (N2 q), gB q n *
        (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0)
      ≤ ∑ n ∈ Ioc (N1 q) (N2 q), (q.totient : ℝ)⁻¹ *
        (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (gB_le q n) (by split_ifs <;> norm_num)
    _ = (q.totient : ℝ)⁻¹ * (((Ioc (N1 q) (N2 q)).filter
          (fun n => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n)).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.card_filter]
        push_cast
        rfl
    _ ≤ (q.totient : ℝ)⁻¹ * (Psi (xq q / (∏ i, rt i : ℕ)) (rt (Fin.last k')) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast card_le_Psi hx hW

/-! ### `x = q^L` tends to infinity -/

omit [SieveCert.Grid] in
theorem tendsto_xq : Tendsto xq atTop atTop :=
  (tendsto_rpow_atTop (L_pos : (0 : ℝ) < L)).comp tendsto_natCast_atTop_atTop

end SieveDrop
