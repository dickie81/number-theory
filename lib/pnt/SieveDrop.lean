/-
# The dropped terms' `B`-count

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The route and the grid are as in `SieveQ`, with `RouteOK`, `GridOK` and `Fits` where the Lean
takes them. `xq q = q^L`, and `cornerP z` is the set of primes of `(⌊z/4⌋, z]`.

* `card_le_Psi`, `famI_gB_le`: a family's `B`-count is at most `φ(q)⁻¹ Σ_rt Ψ(x/∏rt, rt_last)`, since the `n = Wc ∈
  (x, 2x]` with no prime factor below `z` inject into `Ψ(x/W, z)`.
* `drop2_le`, `S2`: a dropped cell's `B`-count at depth 2 is at most `φ(q)⁻¹` times its sum over the primes of its
  cells (`SieveRough.cellP`), `Σ Ψ(x/(p₁p₂), p₂)`.
* `corner_le`, `corner_ev`: for `(parQ q).Good` and `z_top² ≤ 4N₁`, a corner cell (not a candidate, not surely
  evaluable, `p₁`'s cell not inside the window) counts only the `n = p₁p₂`, both primes in `cornerP z_top`, so it is at
  most `φ(q)⁻¹|cornerP|²`; for `ε > 0` and large `q`, `z_top² ≤ 4N₁` and `n²|cornerP|² ≤ εx/log x` (`n` the grid's
  number of cells a side), by `cornerP_card_ev`.

So the corner near `(1/2, 1/2)` is `o(x/log x)`. The library's theorem (`Linnik22000E`) bounds the dropped terms to
depth 8 (`SieveDrop8`), with the shares of the dropped cells and the certificate's total.

The file imports `SieveQ.lean`.
-/
import SieveQ

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute
open SieveCert (V DEN H U1 U2 cell K)

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

/-! ### The dropped cells -/

/-! ### The corner is small -/

omit [SieveCert.Grid] in
theorem tendsto_xq : Tendsto xq atTop atTop :=
  (tendsto_rpow_atTop (L_pos : (0 : ℝ) < L)).comp tendsto_natCast_atTop_atTop

/-! ### All the dropped terms -/

end SieveDrop
