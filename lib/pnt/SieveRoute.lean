/-
# The parameters of the sieve route

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The sieve route runs at `x = q^L`. `Route` holds `L` and the ends `w₁`, `w₂` of a Type II window as fractions of `L`,
and `RouteOK` the facts about them: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. The route's proofs use those about `L`
(`two_lt_L`, `L_pos`, `L_le`, and the tactic `route_num`).

The file imports `SieveTypeII.lean`.
-/
import SieveTypeII

open Complex

noncomputable section

namespace SieveRoute

/-- **The sieve route's parameters**: the exponent `L` of `x = q^L`, and the Type II window `[w₁, w₂]` as fractions
of `L`. -/
class Route where
  /-- The exponent. -/
  L : ℝ
  /-- The Type II window's left end, a fraction of `L`. -/
  w₁ : ℝ
  /-- The Type II window's right end, a fraction of `L`. -/
  w₂ : ℝ

export Route (L w₁ w₂)

variable [Route]

/-- **The facts about the parameters** that the route's proofs use. -/
class RouteOK : Prop where
  two_lt_L : 2 < L
  w₁_pos : 0 < w₁
  w₁_lt_w₂ : w₁ < w₂
  w₂_lt_one : w₂ < 1
  L_le : L ≤ 5 / 2

variable [RouteOK]

theorem two_lt_L : 2 < L := RouteOK.two_lt_L
theorem L_pos : 0 < L := by linarith [two_lt_L]
theorem L_le : L ≤ 5 / 2 := RouteOK.L_le

/-- Closes the numeric side goals about `L` that the route's proofs meet: `norm_num`, or `nlinarith` with
`0 < L`, `L ≤ 5/2` and `2 < L`. -/
macro "route_num" : tactic =>
  `(tactic| first
    | (norm_num; done)
    | nlinarith [SieveRoute.L_pos, SieveRoute.L_le, SieveRoute.two_lt_L])

end SieveRoute
