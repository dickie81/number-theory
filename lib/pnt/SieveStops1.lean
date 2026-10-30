/-
# A stop's cofactor, and the stops below the window

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements.

* `sum_cofactor`: for a `p`-rough `W ≤ N₁` with `0 < W`, the multiples `n ∈ (N₁, N₂]` of `W` that are `p`-rough are
  the `Wk` with `k ≥ 2` `p`-rough and `N₁ < Wk ≤ N₂`.
* `stops1_bound`: let `L`, `w₁` and `w₂` be a route's parameters with `RouteOK`, assume its Type II estimate
  (`hII : SieveRoute.TypeIIAt`), and fix `e₀ > 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod
  `q`: let `r` run over `R`, each `r > 0` with every prime factor at least `z₀` and coefficients `|c_r| ≤ 1`, let
  `w ≥ q^{e₀}`, and let `q^{w₁L} ≤ X` and `Xz₀ ≤ q^{w₂L}`. Then the stops of Buchstab's tree at the threshold `X`
  (`SieveDiff.tree_weighted`), weighted by `c_r` and summed over `r`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.
* `window_bound`: the same with `r` itself in the window, `R ⊆ (P₁, P₂]`, for `S(A_r, z₀) − S(B_r, z₀)/φ(q)`.

`stops1_bound` and `window_bound` are the first case of Proposition 6's proof (`r ≤ x^{u₁}`).
The proof of `SieveMain.linnik_route` does not use them: `SieveProp6.prop6` runs one tree, at the
threshold `X'` (`SieveStops2`). `sum_cofactor` is used by `SieveStops2` and `SieveChain`.

The proof of the bounds: a stop `W = r∏P·p` lies in `(X, Xz₀]`, inside the lower window; its least prime is `p`
(`minFac_W`), so `W` determines `(r, P, p)` (`filter_W`, `div_W`), and the stop's cofactor is a `p`-rough `k ≥ 2`
(`sum_cofactor`). `SieveTypeIIR.typeII_rough` with `m = W` and `z(m) = minFac m` bounds the sum.

`L`, `w₁` and `w₂` are a route's parameters and the Type II estimate is a hypothesis (`hII`); the case
`SieveRoute.route2333` has `SieveRoute.typeII2333` for `hII`.

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
