/-
# A stop's cofactor

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement.

* `sum_cofactor`: for a `p`-rough `W ≤ N₁` with `0 < W`, the multiples `n ∈ (N₁, N₂]` of `W` that are `p`-rough are
  the `Wk` with `k ≥ 2` `p`-rough and `N₁ < Wk ≤ N₂`.

`sum_cofactor` is used by `SieveStops2` and `SieveChain`.

The file imports `SieveDiff.lean` and `SieveTypeIIR.lean`.
-/
import SieveDiff
import SieveTypeIIR

open Real Finset SieveFamily SieveTree SieveRoute

namespace SieveStops1

/-- A multiple in `(N₁, N₂]` of a `p`-rough `W` with `0 < W ≤ N₁` is `Wk` with `k ≥ 2`; `n` is `p`-rough iff `k` is. -/
theorem sum_cofactor (f : ℕ → ℂ) {W p N₁ N₂ : ℕ} (hW : 0 < W) (hWN : W ≤ N₁) (hWp : rough p W) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0) =
      ∑ k ∈ (Finset.Icc 2 N₂).filter (fun k => (∀ p' < p, p'.Prime → ¬ p' ∣ k) ∧ N₁ < W * k ∧ W * k ≤ N₂),
        f (W * k) := by
  rw [show (∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0)) =
      ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => W ∣ n ∧ rough p n), f n by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp]
  refine Finset.sum_nbij' (fun n => n / W) (fun k => W * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Nat.mul_div_cancel_left c hW, Finset.mem_Icc]
    have hc2 : 2 ≤ c := by
      by_contra h
      interval_cases c <;> omega
    refine ⟨⟨hc2, le_trans (Nat.le_mul_of_pos_left c hW) hn2⟩,
      fun p' hp' hpp hpd => hr p' hp' hpp (dvd_mul_of_dvd_right hpd W), hn1, hn2⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hk ⊢
    obtain ⟨-, hr, h1, h2⟩ := hk
    refine ⟨⟨h1, h2⟩, dvd_mul_right W k, fun p' hp' hpp hpd => ?_⟩
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact hWp p' hp' hpp h
    · exact hr p' hp' hpp h
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2.1
  · intro k _
    exact Nat.mul_div_cancel_left k hW
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2.1]

/-! ### A stop determines its tree node -/

section Recover

variable {r p z₀ : ℕ} {P : Finset ℕ}

end Recover

section Bound

open Classical

end Bound

end SieveStops1
