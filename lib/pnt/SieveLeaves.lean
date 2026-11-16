/-
# The leaves' estimates on families of atoms

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `gA q a m = 1[m ≡ a]` and `gB q m = 1[(m, q) = 1]/φ(q)`; `L`, `w₁` and `w₂` are a route's parameters
(`SieveRoute.Route`); `N1 q = ⌊q^L⌋`, `N2 q = ⌊2q^L⌋`; `ThrOK q spec` says that the atoms' thresholds lie in
`[1, q^{L+1}]`. The cells are those of `SieveCert`'s grid (`SieveCert.Grid`).

* `exists_inside`: a box (its primes' ranges, in units of `1/DEN`) that `SieveCert.surelyEval` passes has a set `T` of
  its primes whose subset sums over the box stay inside `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)`.
* `window_lo`, `window_hi`: for `x > 1` and primes in their cells, `⌊x^{B/DEN}⌋ < ∏_T rt` when `B` is below the box's
  lower sum over `T`, and `∏_T rt ≤ ⌊x^{B/DEN}⌋` when `B` is above its upper sum; `window_lo_gen` and
  `window_hi_gen` for primes in ranges of any widths.
* `TL_spec`, `TU_spec`, `TR_spec`: `SieveChain.chainTL_bound`, `chainTU_bound` and `SieveChainR.chainTR_bound` (with
  `RouteOK` and `hII`) on a family of at most `40` atoms with `ThrOK`, as bounds on `|famI(g_A) − famI(g_B)|`: the
  product of a set of the primes in the lower window, the product of all of them in the upper one, and the product of
  a set of them in the reflected window `(N₁/W₁, N₂/(W₀ + 1)]`.
* `P6_spec`: `SieveProp6.prop6` (with `RouteOK` and `hII`) on a family of at most `40` atoms with `ThrOK` and nonzero
  coefficients (`NZ`), as a bound on `|famJ(g_A, z₀) − famJ(g_B, z₀)|`.
* `P6IB_spec`: `SieveP6ib.prop6ib`, Proposition 6 with the bilinear Type I estimate (with `RouteOK` and `hII`), on a
  family of at most `40` atoms with `ThrOK` whose tuples are strictly decreasing, with entries at least `q^{a₀}` and the
  `i`-th in `[q^{lo_i}, q^{hi_i}]` for exponents meeting its conditions, as a bound on
  `|famJ(g_A, z₀) − famJ(g_B, z₀)|`.

These connect the families (`SieveDecomp`) with the Type II bounds and Proposition 6. `dw_eq`, `sum_dw_famI` and
`sum_dw_famJ` write `SieveFamily.dw = gA − gB` on the families, and `RTg_eq_of_thrOK` and `RT_pivoted` identify a
family with the comparisons of its atoms.

The route's numbers and the certificate's grid parameters are parameters and the Type II estimate is a hypothesis
(`hII`); the case of the library's theorem, `Linnik22000E.route22000D` and `SieveCert.grid22000E`, takes
`Linnik22000E.typeII22000d` for `hII`.

The file imports `SieveBuch.lean` and `SieveP6ib.lean`.
-/
import SieveDecomp
import SieveCert
import SieveRuleDefs
import SieveP6ib

open Real Finset SieveFamily SieveChain SieveDecomp SieveRoute
open SieveCert (V DEN H U1 U2 cell)

namespace SieveLeaves

open Classical

/-! ### A box surely evaluable has one set of primes in a window -/

/-! ### The weights, and the sums of `dw` -/

/-- `1[n ≡ a]`. -/
noncomputable def gA (q : ℕ) (a : ZMod q) (m : ℕ) : ℝ := if (m : ZMod q) = a then 1 else 0

/-- `1[(n, q) = 1]/φ(q)`. -/
noncomputable def gB (q : ℕ) (m : ℕ) : ℝ := if IsUnit (m : ZMod q) then (q.totient : ℝ)⁻¹ else 0

theorem gA_nonneg (q : ℕ) (a : ZMod q) (m : ℕ) : 0 ≤ gA q a m := by
  unfold gA
  split_ifs <;> norm_num

theorem dw_eq (q : ℕ) (a : ZMod q) (m : ℕ) : SieveFamily.dw q a m = ((gA q a m - gB q m : ℝ) : ℂ) := by
  unfold SieveFamily.dw gA gB
  split_ifs <;> push_cast <;> simp [div_eq_mul_inv]

theorem sum_dw_famI (q : ℕ) (a : ZMod q) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) :
    ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, SieveFamily.dw q a n *
        (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) =
      ((famI (gA q a) N₁ N₂ F - famI (gB q) N₁ N₂ F : ℝ) : ℂ) := by
  unfold famI
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dw_eq]
  split_ifs <;> push_cast <;> ring

theorem sum_dw_famJ (q : ℕ) (a : ZMod q) (N₁ N₂ z : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) :
    ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, SieveFamily.dw q a n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0) =
      ((famJ (gA q a) N₁ N₂ z F - famJ (gB q) N₁ N₂ z F : ℝ) : ℂ) := by
  unfold famJ
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dw_eq]
  split_ifs <;> push_cast <;> ring

/-! ### The estimates on families of atoms -/

variable [Route]

/-- `N₁ = ⌊q^L⌋`. -/
noncomputable abbrev N1 (q : ℕ) : ℕ := ⌊(q : ℝ) ^ L⌋₊
/-- `N₂ = ⌊2q^L⌋`. -/
noncomputable abbrev N2 (q : ℕ) : ℕ := ⌊2 * (q : ℝ) ^ L⌋₊

/-- The thresholds of a family's atoms lie in `[1, q^{L+1}]`. -/
def ThrOK (q : ℕ) {k : ℕ} (spec : List (Atom k)) : Prop :=
  ∀ A ∈ spec, 1 ≤ A.thr ∧ A.thr ≤ (q : ℝ) ^ (L + 1 : ℝ)

theorem c_le_of_thrOK {q : ℕ} (hq : 1 ≤ q) {k : ℕ} {spec : List (Atom k)} (h : ThrOK q spec) :
    ∀ C ∈ spec.map Atom.toG, C.c 0 ≤ (L + 1) * Real.log q := by
  intro C hC
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hC
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  refine (Atom.toG_c_le A).trans ?_
  have h1 := (h A hA).1
  rw [abs_of_nonneg (Real.log_nonneg h1), ← Real.log_rpow hq0]
  exact Real.log_le_log (by linarith) (h A hA).2

theorem holds_iff_sem {q : ℕ} {k : ℕ} {spec : List (Atom k)} (h : ThrOK q spec) {rt : Fin k → ℕ}
    (hp : ∀ i, (rt i).Prime) : (∀ C ∈ spec.map Atom.toG, C.holds 0 rt) ↔ ∀ A ∈ spec, A.sem rt := by
  simp only [List.forall_mem_map]
  exact forall₂_congr fun A hA => A.toG_holds (by linarith [(h A hA).1]) 0 fun i => (hp i).one_lt.le

theorem RTg_eq_of_thrOK {q : ℕ} {k Y : ℕ} {spec : List (Atom k)} (h : ThrOK q spec) :
    RTg k Y (spec.map Atom.toG) = famSet k Y spec :=
  RTg_eq k Y spec fun A hA => by linarith [(h A hA).1]

variable (a₀ : ℝ)

variable (b₀ : ℝ)

end SieveLeaves
