/-
# Linnik's theorem with exponent `11/5` from a tree that passes the tests

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The route is `L = 11/5` on the window `[43457/100000, 46959/100000]` and the grid is
`SieveCert.grid22000E`, as in `Linnik22000E.lean`, whose route, fit and estimate are restated here so that this file
does not import the certificate to depth 8.

* `route`, `routeOK`, `typeII`, `fits`, `ibFits`: the route at `11/5`, its Type II estimate
  (`SieveTypeIIU22000D.typeII_22000d`), and the grid's fit.
* `linnik_tree_22000`: **the theorem from a tree.** If the terms at a floor of the box with no prime pass the test
  (`SieveAd.mixTests` on `grid22000E`: the window's tests, and those of the estimate in two variables), a tree
  passes `SieveAd.ok` with those tests on the box of one prime with the cell `(f₀, DEN/2 + 1)`, for a term of the
  sign `−`, and its cost is below `K`, then there is `K'` such that for every `q ≥ 1` and every `a` prime to `q`
  there is a prime `p ≡ a (mod q)` with `p ≤ K'·q^{11/5}`.

This is `SieveAd.linnik_tree` with `SieveAd.mixTests_sound`: the paper's theorem for any decomposition that a tree
describes, in place of the decomposition to depth 8, and with the estimate in two variables beside the window. No
tree is given here.

The file imports `SieveAdMix.lean`, `SieveGrid22000E.lean` and `SieveTypeIIU22000D.lean`.
-/
import SieveAdMix
import SieveGrid22000E
import SieveTypeIIU22000D

namespace SieveAd22000

open SieveCert SieveRoute SieveQ SieveAd

/-- **The route's parameters at `11/5`**: `L = 11/5` on the window `[43457/100000, 46959/100000]`. -/
@[instance_reducible] noncomputable def route : Route := ⟨11 / 5, 43457 / 100000, 46959 / 100000⟩

/-- `route` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK : @RouteOK route :=
  @RouteOK.mk route (show (2 : ℝ) < 11 / 5 by norm_num) (show (0 : ℝ) < 43457 / 100000 by norm_num)
    (show (43457 / 100000 : ℝ) < 46959 / 100000 by norm_num) (show (46959 / 100000 : ℝ) < 1 by norm_num)
    (show (11 / 5 : ℝ) ≤ 5 / 2 by norm_num)

/-- The route's Type II estimate. -/
theorem typeII : @TypeIIAt route := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU22000D.typeII_22000d hf0 hsupp K₀ he₁ hη hη1

/-- `grid22000E` fits `route`. -/
theorem fits : @Fits route grid22000E := by
  refine @Fits.mk route grid22000E ?_ ?_ ?_
  · have h : (43457 * DEN : ℕ) < 100000 * ((43457 * DEN + 99999) / 100000) := by decide
    have h' : (43457 : ℝ) * DEN < 100000 * (((43457 * DEN + 99999) / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (43457 / 100000 : ℝ) * DEN < (((43457 * DEN + 99999) / 100000 : ℕ) : ℝ)
    linarith
  · have h : 100000 * (46959 * DEN / 100000) < 46959 * DEN := by decide
    have h' : (100000 : ℝ) * ((46959 * DEN / 100000 : ℕ) : ℝ) < 46959 * DEN := by exact_mod_cast h
    show ((46959 * DEN / 100000 : ℕ) : ℝ) < 46959 / 100000 * DEN
    linarith
  · have h : 5 * DEN < 11 * (46959 * DEN / 100000) := by decide
    have h' : (5 : ℝ) * DEN < 11 * ((46959 * DEN / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 11 / 5 * ((46959 * DEN / 100000 : ℕ) : ℝ)
    linarith

/-- The bilinear rule's exponent on `grid22000E` is the route's. -/
theorem ibFits : @IBFits route ibPar22000E :=
  @IBFits.mk route ibPar22000E (show ((11 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 11 / 5 by norm_num)

/-- **Linnik's theorem with exponent `11/5`, from a tree that passes the tests.** If the terms at the floor
`x^{f₀/DEN}` of the box with no prime pass the test on `grid22000E` (the window's, or the estimate's in two
variables), the tree passes the check with these tests on the box of one prime with the cell `(f₀, DEN/2 + 1)`,
for a term of the sign `−`, and its cost is below `K`, then there is `K'` such that for every `q ≥ 1` and every `a`
prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K'·q^{11/5}`. -/
theorem linnik_tree_22000 (T : Tree) (f₀ : ℕ) (cfg₀ : Cfg) (hf₀ : f₀ ≤ DEN / 2 + 1)
    (hroot : (@mixTests grid22000E ibPar22000E).okJ [] f₀ cfg₀ = true)
    (hok : ok (@mixTests grid22000E ibPar22000E) T [(f₀, DEN / 2 + 1)] false = true)
    (hcost : cost T [(f₀, DEN / 2 + 1)] < K) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K' * (q : ℝ) ^ (11 / 5 : ℝ) :=
  @linnik_tree route routeOK (@mixTests grid22000E ibPar22000E)
    (@mixTests_sound route routeOK grid22000E gridOK22000E fits ibPar22000E ibFits typeII) T f₀ cfg₀ hf₀ hroot hok
    hcost

end SieveAd22000

#print axioms SieveAd22000.linnik_tree_22000
