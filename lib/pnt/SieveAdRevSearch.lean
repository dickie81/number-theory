/-
# The bound of a box's term by a cost, and Linnik's theorem from it

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. For a route:

* `PR bl par c`: the term of the box `bl`, with the sign `par`, is at least `−(c/K + o(1))x/(φ(q) log x)` in `𝒜`
  minus the comparison set.
* `pr_of_has`: a tree that passes on the box at a cost at most `c` gives `PR bl par c`, by `SieveAd.sound`.
* `pr_split`, `pr_buch`, `pr_drop`, `pr_mono`: the steps that join the parts of a search: a cut of a cell
  (`SieveAd.bd_split`), Buchstab's identity at a floor that passes (`SieveAd.bd_buch`), a box dropped at the cost
  that `SieveAd.dropC` gives, a larger cost.
* `revOK_length`: a box that may be reversed (`SieveAd.revOK`) has three primes.
* `linnik_pr`: **the theorem from the bound of the box of one prime.** For a route and sound tests: if the terms at
  the floor of the box with no prime pass `okJ` and the box of one prime has `PR` at a cost below `K`, then every
  class prime to `q` has a prime at most `K'q^L`.

The file imports `SieveAdRevSum.lean` and `SieveAdSearch.lean`.
-/
import SieveAdRevSum
import SieveAdSearch

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

variable [Route]

/-- The term of the box, with the sign `par`, is at least `−(c/K + o(1))x/(φ(q) log x)`. -/
def PR (bl : List Cell) (par : Bool) (c : ℕ) : Prop :=
  ∀ (k' : ℕ) (h : bl.length = k' + 1), Bd par ((c : ℝ) / K) (boxFn bl (k' + 1) h)

/-- A larger cost. -/
theorem pr_mono [RouteOK] {bl : List Cell} {par : Bool} {c c' : ℕ} (h : PR bl par c) (hc : c ≤ c') :
    PR bl par c' := by
  intro k' hl
  exact bd_mono (h k' hl) (div_le_div_of_nonneg_right (by exact_mod_cast hc) K_pos'.le)

/-- A tree that passes on the box bounds its term. -/
theorem pr_of_has [RouteOK] {τ : Tests} (hτ : τ.Sound) {bl : List Cell} {par : Bool} {c : ℕ}
    (h : Has τ bl par c) : PR bl par c := by
  obtain ⟨T, hok, hc⟩ := h
  intro k' hl
  exact bd_mono (sound hτ T bl par k' hl hok) (div_le_div_of_nonneg_right (by exact_mod_cast hc) K_pos'.le)

/-- A cut of the newest prime's cell. -/
theorem pr_split [RouteOK] {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ} (h1 : a < m) (h2 : m < top)
    (hl : PR ((a, m) :: bl) par c1) (hr : PR ((m, top) :: bl) par c2) : PR ((a, top) :: bl) par (c1 + c2) := by
  intro k' h
  have hk : bl.length = k' := by simpa using h
  subst hk
  have hL := hl bl.length rfl
  have hR := hr bl.length rfl
  have ebx : boxFn ((a, top) :: bl) (bl.length + 1) h =
      Fin.snoc (α := fun _ => Cell) (boxFn bl bl.length rfl) (a, top) := boxFn_cons _ _ _ rfl
  have el : Function.update (boxFn ((a, top) :: bl) (bl.length + 1) h) (Fin.last _)
      ((boxFn ((a, top) :: bl) (bl.length + 1) h (Fin.last _)).1, m) =
        boxFn ((a, m) :: bl) (bl.length + 1) rfl := by
    rw [ebx, boxFn_cons (a, m) bl bl.length rfl, Fin.snoc_last, Fin.update_snoc_last]
  have er : Function.update (boxFn ((a, top) :: bl) (bl.length + 1) h) (Fin.last _)
      (m, (boxFn ((a, top) :: bl) (bl.length + 1) h (Fin.last _)).2) =
        boxFn ((m, top) :: bl) (bl.length + 1) rfl := by
    rw [ebx, boxFn_cons (m, top) bl bl.length rfl, Fin.snoc_last, Fin.update_snoc_last]
  have key := bd_split (par := par) (boxFn ((a, top) :: bl) (bl.length + 1) h) (Fin.last _) (c := m)
    (by rw [ebx, Fin.snoc_last]; exact h1.le) (by rw [ebx, Fin.snoc_last]; exact h2.le)
    (by rw [el]; exact hL) (by rw [er]; exact hR)
  have e : ((c1 + c2 : ℕ) : ℝ) / K = (c1 : ℝ) / K + (c2 : ℝ) / K := by
    push_cast; ring
  rw [e]
  exact key

/-- Buchstab's identity at a floor that passes a test. -/
theorem pr_buch [RouteOK] {τ : Tests} (hτ : τ.Sound) {x : Cell} {b : List Cell} {par : Bool} {f : ℕ} {cfg : Cfg}
    {c : ℕ} (hfx : f ≤ x.1) (hJ : τ.okJ (x :: b) f cfg = true) (hc : PR ((f, x.2) :: x :: b) (!par) c) :
    PR (x :: b) par c := by
  intro k' h
  have hlast : boxFn (x :: b) (k' + 1) h (Fin.last k') = x := by simp [boxFn]
  have h2len : ((f, x.2) :: x :: b).length = k' + 1 + 1 := by simp [← h]
  have hch := hc (k' + 1) h2len
  have ech : boxFn ((f, x.2) :: x :: b) (k' + 1 + 1) h2len =
      Fin.snoc (α := fun _ => Cell) (boxFn (x :: b) (k' + 1) h) (f, x.2) := boxFn_cons (f, x.2) (x :: b) (k' + 1) h
  rw [ech] at hch
  refine bd_buch (boxFn (x :: b) (k' + 1) h) (f := f) (by rw [hlast]; exact hfx)
    (hτ.soundJ (x :: b) f cfg (k' + 1) h hJ) ?_
  rw [hlast]
  exact hch

/-- A box that is dropped, at the cost that `dropC` gives. -/
theorem pr_drop [RouteOK] {τ : Tests} (hτ : τ.Sound) {bl : List Cell} {par : Bool} {dc : ℕ}
    (h : dropC bl par = some dc) : PR bl par dc :=
  pr_of_has hτ (dropC_spec h)

omit [Route] in
/-- A box that may be reversed has three primes. -/
theorem revOK_length {bl : List Cell} (h : revOK bl = true) : bl.length = 3 := by
  match bl, h with
  | [_, _, _], _ => rfl

/-- **Linnik's theorem from the bound of the box of one prime.** For a route with `RouteOK` and sound tests: if the
terms at the floor `x^{f₀/DEN}` of the box with no prime pass `okJ`, and the term of the box of one prime with the
cell `(f₀, DEN/2 + 1)`, of the sign `−`, has a bound at a cost below `K`, then there is `K'` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K'·q^L`. -/
theorem linnik_pr [RouteOK] {τ : Tests} (hτ : τ.Sound) (f₀ : ℕ) (cfg₀ : Cfg) (hf₀ : f₀ ≤ DEN / 2 + 1)
    (hroot : τ.okJ [] f₀ cfg₀ = true) {c : ℕ} (h : PR [(f₀, DEN / 2 + 1)] false c) (hc : c < K) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K' * (q : ℝ) ^ L := by
  refine linnik_bd f₀ hf₀ (hτ.soundJ [] f₀ cfg₀ 0 rfl hroot) (C := (c : ℝ) / K) ?_ (h 0 rfl)
  rw [div_lt_one K_pos']
  exact_mod_cast hc

end SieveAd

#print axioms SieveAd.linnik_pr
