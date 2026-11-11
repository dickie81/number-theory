/-
# The search with role reversal is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdRevDefs.lean` defines a search (`SieveAd.solveG` with the nodes `SieveAd.opsR`) whose
nodes are those of `SieveAdDefs.lean`'s trees and, for a box of three primes of the sign `−`, the cost of a role
reversal as one more bound. Here:

* `PR bl par c`: the term of the box `bl`, with the sign `par`, is at least `−(c/K + o(1))x/(φ(q) log x)` in `𝒜`
  minus the comparison set.
* `pr_of_has`: a tree that passes on the box at a cost at most `c` gives `PR bl par c`.
* `rulesR`: **the nodes of the search prove `PR`**, for tests that are sound and sound under two more atoms: the
  nodes of a tree by `SieveAd.sound`, a reversal by `SieveAd.bd_rev`, a cut and Buchstab's identity by
  `SieveAd.bd_split` and `SieveAd.bd_buch`.
* `solveR_sound`: **the search is sound.** A cost that the search returns below the limit it was given bounds the
  term.
* `pr_split`, `pr_buch`, `pr_drop`, `pr_mono`: the steps that join the parts of a search: a cut of a cell,
  Buchstab's identity at a floor that passes, a box dropped at the cost that `SieveAd.dropC` gives, a larger cost.
* `pr_of_kids`: a part of a search, as the kernel checks it: if the costs of the cells of the new prime between `a`
  and `top`, searched with the limit `K`, sum to at most `c < K`, the box of the whole range has `PR` at `c`.
* `linnik_pr`: **the theorem from a search with role reversal.** For a route and sound tests: if the terms at the
  floor of the box with no prime pass `okJ` and the box of one prime has `PR` at a cost below `K`, then every class
  prime to `q` has a prime at most `K'q^L`.

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

/-- **The nodes of the search with role reversal bound the term**, for tests that are sound and sound under two
more atoms. -/
theorem rulesR [RouteOK] {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK : Cell → ℕ → Strat) (fuel : ℕ)
    (cq : ℕ → ℕ → List ℕ) : Rules (opsR τ SK fuel cq) τ PR where
  van := fun _ hv => pr_of_has hτ (has_vanish hv)
  evl := by
    intro bl par cfg _ hI
    cases bl with
    | nil =>
      intro k' h
      simp at h
    | cons x b => exact pr_of_has hτ (has_eval hI)
  drp := fun _ hd => pr_drop hτ hd
  alt := by
    intro bl par l _ h
    simp only [opsR] at h ⊢
    by_cases hc : (!par && revOK bl) = true
    · rw [hc, Bool.cond_true] at h ⊢
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨hp, hrev⟩ := hc
      subst hp
      intro k' hl
      have h3 := revOK_length hrev
      have hk : k' = 2 := by omega
      subst hk
      exact bd_rev hτX SK fuel cq hrev h hl
    · rw [Bool.not_eq_true] at hc
      rw [hc, Bool.cond_false] at h
      omega
  split := pr_split
  buch := fun _ _ hfx hJ hc => pr_buch hτ hfx hJ hc

/-- **The search with role reversal is sound**: a cost that it returns below its limit bounds the term. -/
theorem solveR_sound [RouteOK] {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK : Cell → ℕ → Strat) (fuel : ℕ)
    (cq : ℕ → ℕ → List ℕ) (S : Strat) (n : ℕ) : RecP PR (solveG (opsR τ SK fuel cq) τ S n) :=
  solveG_sound (rulesR hτ hτX SK fuel cq) S n

/-- **A part of a search with role reversal**, as the kernel checks it: if the costs of the cells of the new prime
between `a` and `top`, cut at `cs` and searched with the limit `K`, sum to at most `c < K`, then the term of the box
of the whole range is at least `−(c/K + o(1))x/(φ(q) log x)` with its sign. -/
theorem pr_of_kids [RouteOK] {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK : Cell → ℕ → Strat) (fuel : ℕ)
    (cq : ℕ → ℕ → List ℕ) (S : Strat) (n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c : ℕ}
    (h : kids (solveG (opsR τ SK fuel cq) τ S n) top bl par cs a K ≤ c) (hc : c < K) :
    PR ((a, top) :: bl) par c :=
  pr_mono (kidsP_sound pr_split (solveR_sound hτ hτX SK fuel cq S n) top bl par cs a K (lt_of_le_of_lt h hc)) h

/-- **Linnik's theorem from a search with role reversal.** For a route with `RouteOK` and sound tests: if the terms
at the floor `x^{f₀/DEN}` of the box with no prime pass `okJ`, and the term of the box of one prime with the cell
`(f₀, DEN/2 + 1)`, of the sign `−`, has a bound at a cost below `K`, then there is `K'` such that for every `q ≥ 1`
and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K'·q^L`. -/
theorem linnik_pr [RouteOK] {τ : Tests} (hτ : τ.Sound) (f₀ : ℕ) (cfg₀ : Cfg) (hf₀ : f₀ ≤ DEN / 2 + 1)
    (hroot : τ.okJ [] f₀ cfg₀ = true) {c : ℕ} (h : PR [(f₀, DEN / 2 + 1)] false c) (hc : c < K) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K' * (q : ℝ) ^ L := by
  refine linnik_bd f₀ hf₀ (hτ.soundJ [] f₀ cfg₀ 0 rfl hroot) (C := (c : ℝ) / K) ?_ (h 0 rfl)
  rw [div_lt_one K_pos']
  exact_mod_cast hc

end SieveAd

#print axioms SieveAd.solveR_sound
#print axioms SieveAd.pr_of_kids
#print axioms SieveAd.linnik_pr
