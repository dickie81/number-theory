/-
# The search with its nodes' tests as parameters is sound, for any statement that the nodes prove

Plain statements, without Mathlib. `SieveAdRevDefs.lean` defines a search (`SieveAd.solveG`) whose nodes' tests are
parameters (`SieveAd.Ops`). Here, for a statement `P bl par c` about a box, a sign and a cost:

* `Rules O τ P`: what the nodes prove. A larger cost keeps the statement; a box with no term and a box that a test
  evaluates have it at the cost `0`; a dropped box at its cost; a box that `alt` bounds below its limit at that
  bound; a box cut in two at the sum of the two costs; and a box decomposed at a floor that passes at the cost of
  the box with the new prime.
* `kidsP_sound`: if every box that `rec` searches to a cost below its limit has the statement at that cost
  (`RecP`), then so has the box of the new prime's whole range when the cells' costs sum to less than the limit.
* `solveG_sound`: **the search is sound.** A cost that `solveG` returns below the limit it was given has the
  statement.
* `addL_lt`: a sum of two costs below the limit, as `addL` computes it.

The file imports `SieveAdRevDefs.lean`.
-/
import SieveAdRevDefs

namespace SieveAd

/-- What the nodes of a search prove of a statement `P bl par c` about a box, a sign and a cost. -/
structure Rules (O : Ops) (τ : Tests) (P : List Cell → Bool → ℕ → Prop) : Prop where
  van : ∀ {bl : List Cell} {par : Bool}, O.grd bl = true → O.van bl = true → P bl par 0
  evl : ∀ {bl : List Cell} {par : Bool} {cfg : Cfg}, O.grd bl = true → τ.okI bl cfg = true → P bl par 0
  drp : ∀ {bl : List Cell} {par : Bool} {dc : ℕ}, O.grd bl = true → O.drp bl par = some dc → P bl par dc
  alt : ∀ {bl : List Cell} {par : Bool} {l : ℕ}, O.grd bl = true → O.alt bl par l < l → P bl par (O.alt bl par l)
  split : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
    P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2)
  buch : ∀ {x : Cell} {b : List Cell} {par : Bool} {f : ℕ} {cfg : Cfg} {c : ℕ}, O.grd (x :: b) = true → 0 < f →
    f ≤ x.1 → τ.okJ (x :: b) f cfg = true → P ((f, x.2) :: x :: b) (!par) c → P (x :: b) par c

/-- What the search of the boxes below must satisfy: a cost below the limit has the statement. -/
def RecP (P : List Cell → Bool → ℕ → Prop) (rec : List Cell → Bool → ℕ → ℕ) : Prop :=
  ∀ bl par lim, rec bl par lim < lim → P bl par (rec bl par lim)

/-- The cells of the new prime: costs that sum to less than the limit give the statement on the whole range. -/
theorem kidsP_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecP P rec) (top : ℕ) (bl : List Cell) (par : Bool) :
    ∀ (cs : List ℕ) (a lim : ℕ), kids rec top bl par cs a lim < lim →
      P ((a, top) :: bl) par (kids rec top bl par cs a lim) := by
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
        exact hsplit hc.1 hc.2 (hrec _ _ _ (by omega)) (ih c _ (by omega))
    · rw [Bool.not_eq_true] at hc
      have e : kids rec top bl par (c :: cs) a lim = kids rec top bl par cs a lim := by
        simp only [kids, hc, Bool.cond_false]
      rw [e] at h ⊢
      exact ih a lim h

theorem anyI_some {τ : Tests} {bl : List Cell} : ∀ {cs : List Cfg}, anyI τ bl cs = true →
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

theorem firstJ_some {τ : Tests} {bl : List Cell} {lo0 f : ℕ} : ∀ {ps : List (ℕ × Cfg)},
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

theorem buchP_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) {S : Strat}
    {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecP P rec) (x : Cell) (b : List Cell) (par : Bool) (lim : ℕ)
    (hg : O.grd (x :: b) = true) (h : buchC τ S rec x b par lim < lim) :
    P (x :: b) par (buchC τ S rec x b par lim) := by
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
      obtain ⟨hf, hfx, cfg, hok⟩ := firstJ_some hJ
      exact R.buch hg hf hfx hok (kidsP_sound R.split hrec _ _ _ _ _ _ h)
  · rw [Bool.not_eq_true] at hd
    simp only [hd, Bool.cond_false] at h
    have : lim ≤ Nat.add lim BIG := Nat.le_add_right _ _
    omega

theorem splitP_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) {S : Strat}
    {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecP P rec) (x : Cell) (b : List Cell) (par : Bool) (lim : ℕ)
    (h : splitC S rec x b par lim < lim) : P (x :: b) par (splitC S rec x b par lim) := by
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
      exact R.split (top := x.2) hc.1.2 hc.2 (hrec _ _ _ (by omega)) (hrec _ _ _ (by omega))
  · rw [Bool.not_eq_true] at hc
    rw [hc, Bool.cond_false] at h
    have : lim ≤ Nat.add lim BIG := Nat.le_add_right _ _
    omega

theorem nodeG_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) {S : Strat}
    {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecP P rec) (x : Cell) (b : List Cell) (par : Bool) (lim : ℕ)
    (hg : O.grd (x :: b) = true) (h : nodeG O τ S rec x b par lim < lim) :
    P (x :: b) par (nodeG O τ S rec x b par lim) := by
  unfold nodeG at h ⊢
  cases hd : O.drp (x :: b) par with
  | some dc =>
    simp only [hd] at h ⊢
    generalize hlim : cond (Nat.ble dc lim) dc lim = lim1 at h ⊢
    by_cases h1 : Nat.ble dc (buchC τ S rec x b par lim1) = true
    · rw [h1, Bool.cond_true]
      exact R.drp hg hd
    · rw [Bool.not_eq_true] at h1
      rw [h1, Bool.cond_false] at h ⊢
      have h1' : ¬ dc ≤ buchC τ S rec x b par lim1 := by
        rw [← Nat.ble_eq, h1]
        simp
      refine buchP_sound R hrec x b par _ hg ?_
      by_cases h2 : Nat.ble dc lim = true
      · rw [h2, Bool.cond_true] at hlim
        omega
      · rw [Bool.not_eq_true] at h2
        rw [h2, Bool.cond_false] at hlim
        omega
  | none =>
    simp only [hd] at h ⊢
    generalize hl2 : cond (Nat.ble (buchC τ S rec x b par lim) lim) (buchC τ S rec x b par lim) lim = l2 at h ⊢
    by_cases h0 : Nat.blt (O.alt (x :: b) par l2) l2 = true
    · rw [h0, Bool.cond_true]
      rw [Nat.blt_eq] at h0
      exact R.alt hg h0
    · rw [Bool.not_eq_true] at h0
      rw [h0, Bool.cond_false] at h ⊢
      by_cases h1 : Nat.blt (buchC τ S rec x b par lim) BIG = true
      · rw [h1, Bool.cond_true] at h ⊢
        exact buchP_sound R hrec x b par lim hg h
      · rw [Bool.not_eq_true] at h1
        rw [h1, Bool.cond_false] at h ⊢
        exact splitP_sound R hrec x b par lim h

/-- **One step of the search is sound**, if the search of the boxes below is. -/
theorem stepG_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) {S : Strat}
    {rec : List Cell → Bool → ℕ → ℕ} (hrec : RecP P rec) : RecP P (stepG O τ S rec) := by
  intro bl par lim h
  cases bl with
  | nil => simp [stepG] at h
  | cons x b =>
    unfold stepG at h ⊢
    simp only at h ⊢
    by_cases hg : O.grd (x :: b) = true
    · rw [hg, Bool.cond_true] at h ⊢
      by_cases hv : (O.van (x :: b) || anyI τ (x :: b) (S.propI (x :: b))) = true
      · rw [hv, Bool.cond_true]
        simp only [Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · exact R.van hg hv
        · obtain ⟨cfg, hcfg⟩ := anyI_some hv
          exact R.evl hg hcfg
      · rw [Bool.not_eq_true] at hv
        rw [hv, Bool.cond_false] at h ⊢
        exact nodeG_sound R hrec x b par lim hg h
    · rw [Bool.not_eq_true] at hg
      rw [hg, Bool.cond_false] at h
      omega

/-- **The search is sound**: a cost that the search returns below its limit has the statement. -/
theorem solveG_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) (S : Strat) :
    ∀ n : ℕ, RecP P (solveG O τ S n) := by
  intro n
  induction n with
  | zero =>
    intro bl par lim h
    simp [solveG] at h
  | succ n ih => exact stepG_sound R ih

/-- A sum of two costs below the limit, as `addL` computes it: the first is below the limit, the second is below
what the first leaves, and the sum is the value. -/
theorem addL_lt {c1 : ℕ} {rest : ℕ → ℕ} {lim : ℕ} (h : addL c1 rest lim < lim) :
    c1 < lim ∧ rest (lim - c1) < lim - c1 ∧ addL c1 rest lim = c1 + rest (lim - c1) := by
  unfold addL at h ⊢
  by_cases hl : Nat.ble lim c1 = true
  · rw [hl, Bool.cond_true] at h
    rw [Nat.ble_eq] at hl
    omega
  · rw [Bool.not_eq_true] at hl
    rw [hl, Bool.cond_false] at h ⊢
    have hl' : ¬ lim ≤ c1 := by
      rw [← Nat.ble_eq, hl]
      simp
    exact ⟨by omega, by omega, rfl⟩

end SieveAd

#print axioms SieveAd.solveG_sound
#print axioms SieveAd.kidsP_sound
#print axioms SieveAd.addL_lt
