/-
# The search for a tree is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdSearchDefs.lean` defines a search (`SieveAd.solveF`) that returns a cost and no tree. Here:

* `Has τ bl par c`: some tree passes `SieveAd.ok` on the box `bl`, for a term of the sign `par`, with cost at most `c`.
  `has_vanish`, `has_eval`, `has_drop`, `has_dropB`, `has_split`, `has_buch`: the nodes of a tree, in this form.
* `kids_sound`: if every box that `rec` searches to a cost below its limit has a tree at that cost (`RecOK`), then
  so has the box of the new prime's whole range when the cells' costs sum to less than the limit.
* `step_sound`, `solveF_sound`: **the search is sound.** A cost that `solveF` returns below the limit it was given
  is the cost of a tree. The strategy that proposes the nodes is any: the search uses a node only after its check
  has passed.
* `has_of_kids`: a part of a search, as the kernel checks it: if the costs of the cells of the new prime between
  `a` and `top`, searched with the limit `K`, sum to at most `c < K`, the box of the whole range has a tree at
  cost `c`.
* `linnik_has`: **the theorem from the tree of a search.** For a route and sound tests: if the terms at the floor of
  the box with no prime pass `okJ` and the box of one prime has a tree at a cost below `K`, then every class prime
  to `q` has a prime at most `K'q^L`.

The file imports `SieveAdSearchDefs.lean` and `SieveAdTree.lean`.
-/
import SieveAdSearchDefs
import SieveAdTree

namespace SieveAd

open SieveCert (DEN K)

/-- Some tree passes on the box, for a term of the sign `par`, with cost at most `c`. -/
def Has (τ : Tests) (bl : List Cell) (par : Bool) (c : ℕ) : Prop :=
  ∃ T : Tree, ok τ T bl par = true ∧ cost T bl ≤ c

theorem Has.mono {τ : Tests} {bl : List Cell} {par : Bool} {c c' : ℕ} (h : Has τ bl par c) (hc : c ≤ c') :
    Has τ bl par c' := by
  obtain ⟨T, h1, h2⟩ := h
  exact ⟨T, h1, h2.trans hc⟩

/-- A box with no term. -/
theorem has_vanish {τ : Tests} {bl : List Cell} {par : Bool} (h : vanishOK bl = true) : Has τ bl par 0 :=
  ⟨.vanish, by simp [ok, h], by simp [cost]⟩

/-- A box that a test evaluates. -/
theorem has_eval {τ : Tests} {x : Cell} {b : List Cell} {par : Bool} {cfg : Cfg} (h : τ.okI (x :: b) cfg = true) :
    Has τ (x :: b) par 0 :=
  ⟨.evalI cfg, by simp [ok, h], by simp [cost]⟩

/-- A box that is dropped. -/
theorem has_drop {τ : Tests} {bl : List Cell} (h : dropOK bl = true) : Has τ bl true (dropCost bl) :=
  ⟨.drop, by simp [ok, h], by simp [cost]⟩

/-- A box that is dropped for its products. -/
theorem has_dropB {τ : Tests} {bl : List Cell} (h : dropBOK bl = true) : Has τ bl true (dropBCost bl) :=
  ⟨.dropB, by simp [ok, h], by simp [cost]⟩

/-- A cut of the newest prime's cell. -/
theorem has_split {τ : Tests} {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ} (h1 : a < m) (h2 : m < top)
    (hl : Has τ ((a, m) :: bl) par c1) (hr : Has τ ((m, top) :: bl) par c2) :
    Has τ ((a, top) :: bl) par (c1 + c2) := by
  obtain ⟨Tl, hl1, hl2⟩ := hl
  obtain ⟨Tr, hr1, hr2⟩ := hr
  refine ⟨.split 0 m Tl Tr, ?_, ?_⟩
  · have e1 : setHi ((a, top) :: bl) 0 m = (a, m) :: bl := rfl
    have e2 : setLo ((a, top) :: bl) 0 m = (m, top) :: bl := rfl
    have e3 : splitOK ((a, top) :: bl) 0 m = true := by
      simp [splitOK, getC, h1, h2]
    simp only [ok, e1, e2, e3, hl1, hr1, Bool.and_self]
  · have e1 : setHi ((a, top) :: bl) 0 m = (a, m) :: bl := rfl
    have e2 : setLo ((a, top) :: bl) 0 m = (m, top) :: bl := rfl
    simp only [cost, e1, e2]
    omega

/-- Buchstab's identity at a floor that passes. -/
theorem has_buch {τ : Tests} {x : Cell} {b : List Cell} {par : Bool} {f : ℕ} {cfg : Cfg} {c : ℕ} (hf : 0 < f)
    (hfx : f ≤ x.1) (hJ : τ.okJ (x :: b) f cfg = true) (h : Has τ ((f, x.2) :: x :: b) (!par) c) :
    Has τ (x :: b) par c := by
  obtain ⟨T, h1, h2⟩ := h
  refine ⟨.buch f cfg T, ?_, ?_⟩
  · simp [ok, hf, hfx, hJ, h1]
  · simpa [cost] using h2

/-- What the search of the boxes below must satisfy: a cost below the limit is the cost of a tree. -/
def RecOK (τ : Tests) (rec : List Cell → Bool → ℕ → ℕ) : Prop :=
  ∀ bl par lim, rec bl par lim < lim → Has τ bl par (rec bl par lim)

/-- The cells of the new prime: costs that sum to less than the limit give a tree on the whole range. -/
theorem kids_sound {τ : Tests} {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecOK τ rec) (top : ℕ) (bl : List Cell)
    (par : Bool) : ∀ (cs : List ℕ) (a lim : ℕ), kids rec top bl par cs a lim < lim →
      Has τ ((a, top) :: bl) par (kids rec top bl par cs a lim) := by
  intro cs
  induction cs with
  | nil =>
    intro a lim h
    exact hrec _ _ _ h
  | cons c cs ih =>
    intro a lim h
    by_cases hc : (Nat.blt a c && Nat.blt c top) = true
    · have e : kids rec top bl par (c :: cs) a lim =
          cond (Nat.ble lim (rec ((a, c) :: bl) par lim)) (rec ((a, c) :: bl) par lim)
            (rec ((a, c) :: bl) par lim + kids rec top bl par cs c (lim - rec ((a, c) :: bl) par lim)) := by
        simp only [kids, hc, Bool.cond_true]
        rfl
      rw [e] at h ⊢
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      by_cases hl : Nat.ble lim (rec ((a, c) :: bl) par lim) = true
      · rw [hl, Bool.cond_true] at h
        rw [Nat.ble_eq] at hl
        omega
      · rw [Bool.not_eq_true] at hl
        rw [hl, Bool.cond_false] at h ⊢
        have hl' : ¬ lim ≤ rec ((a, c) :: bl) par lim := by
          rw [← Nat.ble_eq, hl]
          simp
        exact has_split hc.1 hc.2 (hrec _ _ _ (by omega)) (ih c _ (by omega))
    · rw [Bool.not_eq_true] at hc
      have e : kids rec top bl par (c :: cs) a lim = kids rec top bl par cs a lim := by
        simp only [kids, hc, Bool.cond_false]
      rw [e] at h ⊢
      exact ih a lim h

theorem anyI_spec {τ : Tests} {bl : List Cell} : ∀ {cs : List Cfg}, anyI τ bl cs = true →
    ∃ cfg, τ.okI bl cfg = true := by
  intro cs
  induction cs with
  | nil => intro h; simp [anyI] at h
  | cons cfg cs ih =>
    intro h
    simp only [anyI, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨cfg, h⟩
    · exact ih h

theorem firstJ_spec {τ : Tests} {bl : List Cell} {lo0 f : ℕ} : ∀ {ps : List (ℕ × Cfg)},
    firstJ τ bl lo0 ps = some f → 0 < f ∧ f ≤ lo0 ∧ ∃ cfg, τ.okJ bl f cfg = true := by
  intro ps
  induction ps with
  | nil => intro h; simp [firstJ] at h
  | cons p ps ih =>
    intro h
    by_cases hp : (Nat.blt 0 p.1 && Nat.ble p.1 lo0 && τ.okJ bl p.1 p.2) = true
    · simp only [firstJ, hp, Bool.cond_true, Option.some.injEq] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hp
      subst h
      exact ⟨hp.1.1, hp.1.2, p.2, hp.2⟩
    · rw [Bool.not_eq_true] at hp
      simp only [firstJ, hp, Bool.cond_false] at h
      exact ih h

theorem dropC_spec {τ : Tests} {bl : List Cell} {par : Bool} {dc : ℕ} (h : dropC bl par = some dc) :
    Has τ bl par dc := by
  unfold dropC at h
  cases par with
  | false => simp at h
  | true =>
    simp only [Bool.cond_true] at h
    by_cases h1 : dropOK bl = true
    · simp only [h1, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact has_drop h1
    · rw [Bool.not_eq_true] at h1
      simp only [h1, Bool.cond_false] at h
      by_cases h2 : dropBOK bl = true
      · simp only [h2, Bool.cond_true, Option.some.injEq] at h
        subst h
        exact has_dropB h2
      · rw [Bool.not_eq_true] at h2
        simp [h2] at h

theorem buchC_sound {τ : Tests} {S : Strat} {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecOK τ rec) (x : Cell)
    (b : List Cell) (par : Bool) (lim : ℕ) (h : buchC τ S rec x b par lim < lim) :
    Has τ (x :: b) par (buchC τ S rec x b par lim) := by
  unfold buchC at h ⊢
  by_cases hd : Nat.blt (Nat.succ b.length) S.depth = true
  · simp only [hd, Bool.cond_true] at h ⊢
    cases hJ : firstJ τ (x :: b) x.1 (S.propJ (x :: b)) with
    | none =>
      simp only [hJ] at h
      have : lim ≤ Nat.add lim BIG := Nat.le_add_right _ _
      omega
    | some f =>
      simp only [hJ] at h ⊢
      obtain ⟨hf, hfx, cfg, hok⟩ := firstJ_spec hJ
      exact has_buch hf hfx hok (kids_sound hrec _ _ _ _ _ _ h)
  · rw [Bool.not_eq_true] at hd
    simp only [hd, Bool.cond_false] at h
    have : lim ≤ Nat.add lim BIG := Nat.le_add_right _ _
    omega

theorem splitC_sound {τ : Tests} {S : Strat} {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecOK τ rec) (x : Cell)
    (b : List Cell) (par : Bool) (lim : ℕ) (h : splitC S rec x b par lim < lim) :
    Has τ (x :: b) par (splitC S rec x b par lim) := by
  have e : splitC S rec x b par lim =
      cond (Nat.blt S.wmin (Nat.sub x.2 x.1) && Nat.blt x.1 (Nat.div (Nat.add x.1 x.2) 2) &&
          Nat.blt (Nat.div (Nat.add x.1 x.2) 2) x.2)
        (cond (Nat.ble lim (rec ((x.1, Nat.div (Nat.add x.1 x.2) 2) :: b) par lim))
          (rec ((x.1, Nat.div (Nat.add x.1 x.2) 2) :: b) par lim)
          (rec ((x.1, Nat.div (Nat.add x.1 x.2) 2) :: b) par lim +
            rec ((Nat.div (Nat.add x.1 x.2) 2, x.2) :: b) par
              (lim - rec ((x.1, Nat.div (Nat.add x.1 x.2) 2) :: b) par lim)))
        (Nat.add lim BIG) := rfl
  rw [e] at h ⊢
  generalize Nat.div (Nat.add x.1 x.2) 2 = mid at h ⊢
  by_cases hc : (Nat.blt S.wmin (Nat.sub x.2 x.1) && Nat.blt x.1 mid && Nat.blt mid x.2) = true
  · rw [hc, Bool.cond_true] at h ⊢
    simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    by_cases hl : Nat.ble lim (rec ((x.1, mid) :: b) par lim) = true
    · rw [hl, Bool.cond_true] at h
      rw [Nat.ble_eq] at hl
      omega
    · rw [Bool.not_eq_true] at hl
      rw [hl, Bool.cond_false] at h ⊢
      have hl' : ¬ lim ≤ rec ((x.1, mid) :: b) par lim := by
        rw [← Nat.ble_eq, hl]
        simp
      exact has_split (top := x.2) hc.1.2 hc.2 (hrec _ _ _ (by omega)) (hrec _ _ _ (by omega))
  · rw [Bool.not_eq_true] at hc
    rw [hc, Bool.cond_false] at h
    have : lim ≤ Nat.add lim BIG := Nat.le_add_right _ _
    omega

theorem node_sound {τ : Tests} {S : Strat} {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecOK τ rec) (x : Cell)
    (b : List Cell) (par : Bool) (lim : ℕ) (h : node τ S rec x b par lim < lim) :
    Has τ (x :: b) par (node τ S rec x b par lim) := by
  unfold node at h ⊢
  cases hd : dropC (x :: b) par with
  | some dc =>
    simp only [hd] at h ⊢
    generalize hlim : cond (Nat.ble dc lim) dc lim = lim1 at h ⊢
    by_cases h1 : Nat.ble dc (buchC τ S rec x b par lim1) = true
    · rw [h1, Bool.cond_true]
      exact dropC_spec hd
    · rw [Bool.not_eq_true] at h1
      rw [h1, Bool.cond_false] at h ⊢
      have h1' : ¬ dc ≤ buchC τ S rec x b par lim1 := by
        rw [← Nat.ble_eq, h1]
        simp
      refine buchC_sound hrec x b par _ ?_
      by_cases h2 : Nat.ble dc lim = true
      · rw [h2, Bool.cond_true] at hlim
        omega
      · rw [Bool.not_eq_true] at h2
        rw [h2, Bool.cond_false] at hlim
        omega
  | none =>
    simp only [hd] at h ⊢
    by_cases h1 : Nat.blt (buchC τ S rec x b par lim) BIG = true
    · rw [h1, Bool.cond_true] at h ⊢
      exact buchC_sound hrec x b par lim h
    · rw [Bool.not_eq_true] at h1
      rw [h1, Bool.cond_false] at h ⊢
      exact splitC_sound hrec x b par lim h

/-- **One step of the search is sound**, if the search of the boxes below is. -/
theorem step_sound {τ : Tests} {S : Strat} {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecOK τ rec) :
    RecOK τ (step τ S rec) := by
  intro bl par lim h
  cases bl with
  | nil => simp [step] at h
  | cons x b =>
    unfold step at h ⊢
    simp only at h ⊢
    by_cases hv : (vanishOK (x :: b) || anyI τ (x :: b) (S.propI (x :: b))) = true
    · rw [hv, Bool.cond_true]
      simp only [Bool.or_eq_true] at hv
      rcases hv with hv | hv
      · exact has_vanish hv
      · obtain ⟨cfg, hcfg⟩ := anyI_spec hv
        exact has_eval hcfg
    · rw [Bool.not_eq_true] at hv
      rw [hv, Bool.cond_false] at h ⊢
      exact node_sound hrec x b par lim h

/-- **The search is sound**: a cost that the search returns below its limit is the cost of a tree that passes on
the box. -/
theorem solveF_sound {τ : Tests} (S : Strat) : ∀ n : ℕ, RecOK τ (solveF τ S n) := by
  intro n
  induction n with
  | zero =>
    intro bl par lim h
    simp [solveF] at h
  | succ n ih => exact step_sound ih

/-- **A part of a search**, as the kernel checks it: if the costs of the cells of the new prime between `a` and
`top`, cut at `cs` and searched with the limit `K`, sum to at most `c < K`, then the box of the whole range has a
tree at cost `c`. -/
theorem has_of_kids {τ : Tests} (S : Strat) (n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c : ℕ}
    (h : kids (solveF τ S n) top bl par cs a K ≤ c) (hc : c < K) : Has τ ((a, top) :: bl) par c :=
  (kids_sound (solveF_sound S n) top bl par cs a K (lt_of_le_of_lt h hc)).mono h

open SieveRoute in
/-- **Linnik's theorem from the tree of a search.** For a route with `RouteOK` and sound tests: if the terms at the
floor `x^{f₀/DEN}` of the box with no prime pass `okJ`, and the box of one prime with the cell `(f₀, DEN/2 + 1)`
has a tree, for a term of the sign `−`, at a cost below `K`, then there is `K'` such that for every `q ≥ 1` and
every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K'·q^L`. -/
theorem linnik_has [Route] [RouteOK] {τ : Tests} (hτ : τ.Sound) (f₀ : ℕ) (cfg₀ : Cfg) (hf₀ : f₀ ≤ DEN / 2 + 1)
    (hroot : τ.okJ [] f₀ cfg₀ = true) {c : ℕ} (h : Has τ [(f₀, DEN / 2 + 1)] false c) (hc : c < K) :
    ∃ K' : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K' * (q : ℝ) ^ L := by
  obtain ⟨T, hok, hc'⟩ := h
  exact linnik_tree hτ T f₀ cfg₀ hf₀ hroot hok (lt_of_le_of_lt hc' hc)

end SieveAd

#print axioms SieveAd.solveF_sound
#print axioms SieveAd.has_of_kids
#print axioms SieveAd.linnik_has
