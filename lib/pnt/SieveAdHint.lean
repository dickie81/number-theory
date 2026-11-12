/-
# The search led by hints is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdHintDefs.lean` has, without Mathlib, a search that does at each box what a number, the
hints, tells it: evaluate, drop, Buchstab's identity at the floor and with the configuration that a guide gives for
four bits of the hints, one more bound, or the cell cut in two. Each of these steps is one of the rules that the
search of `SieveAdRevDefs.lean` chooses among (`Rules`), checked before it is used; so a cost that the search
returns below its limit bounds the term, whatever the hints.

* `RecPH`: what a search led by hints proves: a cost below the limit has the statement, for any hints.
* `kidsH_sound`: the cells of the new prime. `stepH_sound`, `solveH_sound`: **the search led by hints is sound**,
  for nodes that prove a statement `P` (`Rules O τ P`) and a hinted bound that does.
* `bd_flipCostH`: the cost of the reversal of a box through its largest prime, its tree searched by hints, bounds
  the term: `bd_flip_core` with the tree's bound from `solveH_sound`. `altFH_sound`: the hinted bound of the main
  search proves `PR`.
* `solveFH_sound`, `pr_of_kidsH`: the main search led by hints is sound, and a part of it as the kernel checks it
  bounds its term; `pr_of_kidsH_at` with the route and its exponent as variables.

The file imports `SieveAdFlipSearch.lean` and `SieveAdHintDefs.lean`.
-/
import SieveAdFlipSearch
import SieveAdHintDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K cdiv)

/-! ### The search led by hints, for any rules -/

/-- What a search led by hints must satisfy: a cost below the limit has the statement, whatever the hints. -/
def RecPH (P : List Cell → Bool → ℕ → Prop) (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) : Prop :=
  ∀ bl par lim h, (rec bl par lim h).1 < lim → P bl par (rec bl par lim h).1

/-- The cells of the new prime, by hints: costs that sum to less than the limit give the statement on the whole
range. -/
theorem kidsH_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) (top : ℕ) (bl : List Cell) (par : Bool) :
    ∀ (cs : List ℕ) (a lim h : ℕ), (kidsH rec top bl par cs a lim h).1 < lim →
      P ((a, top) :: bl) par (kidsH rec top bl par cs a lim h).1 := by
  intro cs
  induction cs with
  | nil =>
    intro a lim h hh
    exact hrec _ _ _ _ hh
  | cons c cs ih =>
    intro a lim h hh
    by_cases hc : (Nat.blt a c && Nat.blt c top) = true
    · by_cases hb : Nat.beq (Nat.mod h 2) 1 = true
      · have e : kidsH rec top bl par (c :: cs) a lim h =
            cond (Nat.ble lim (rec ((a, c) :: bl) par lim (Nat.div h 2)).1) (rec ((a, c) :: bl) par lim (Nat.div h 2))
              ((rec ((a, c) :: bl) par lim (Nat.div h 2)).1 +
                  (kidsH rec top bl par cs c (lim - (rec ((a, c) :: bl) par lim (Nat.div h 2)).1)
                    (rec ((a, c) :: bl) par lim (Nat.div h 2)).2).1,
                (kidsH rec top bl par cs c (lim - (rec ((a, c) :: bl) par lim (Nat.div h 2)).1)
                  (rec ((a, c) :: bl) par lim (Nat.div h 2)).2).2) := by
          simp only [kidsH, hc, hb, Bool.cond_true]
          rfl
        rw [e] at hh ⊢
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc
        have hr := hrec ((a, c) :: bl) par lim (Nat.div h 2)
        generalize rec ((a, c) :: bl) par lim (Nat.div h 2) = r at hh hr ⊢
        by_cases hl : Nat.ble lim r.1 = true
        · rw [hl, Bool.cond_true] at hh
          rw [Nat.ble_eq] at hl
          omega
        · rw [Bool.not_eq_true] at hl
          rw [hl, Bool.cond_false] at hh ⊢
          have hl' : ¬ lim ≤ r.1 := by
            rw [← Nat.ble_eq, hl]
            simp
          have hh' : r.1 + (kidsH rec top bl par cs c (lim - r.1) r.2).1 < lim := hh
          exact hsplit hc.1 hc.2 (hr (by omega)) (ih c _ _ (by omega))
      · rw [Bool.not_eq_true] at hb
        have e : kidsH rec top bl par (c :: cs) a lim h = kidsH rec top bl par cs a lim (Nat.div h 2) := by
          simp only [kidsH, hc, hb, Bool.cond_true, Bool.cond_false]
        rw [e] at hh ⊢
        exact ih a lim _ hh
    · rw [Bool.not_eq_true] at hc
      have e : kidsH rec top bl par (c :: cs) a lim h = kidsH rec top bl par cs a lim h := by
        simp only [kidsH, hc, Bool.cond_false]
      rw [e] at hh ⊢
      exact ih a lim h hh

/-- **A step of the search led by hints is sound**: for nodes that prove `P`, a hinted bound that proves `P` and
a search of the boxes below that does, a cost below the limit has `P`, whatever the hints and the guide. -/
theorem stepH_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) {S : Strat}
    {gJ : List Cell → ℕ → Option (ℕ × Cfg)} {altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ}
    (haltH : ∀ bl par l h, O.grd bl = true → (altH bl par l h).1 < l → P bl par (altH bl par l h).1)
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) : RecPH P (stepH O τ S gJ altH rec) := by
  intro bl par lim h hh
  cases bl with
  | nil => exact absurd hh (lt_irrefl _)
  | cons x b =>
    by_cases hg : O.grd (x :: b) = true
    swap
    · rw [Bool.not_eq_true] at hg
      have e : stepH O τ S gJ altH rec (x :: b) par lim h = (lim, h) := by
        simp only [stepH, hg, Bool.cond_false]
      rw [e] at hh
      exact absurd hh (lt_irrefl _)
    simp only [stepH, hg, Bool.cond_true] at hh ⊢
    by_cases h0 : Nat.beq (Nat.mod h 2) 0 = true
    · -- evaluated, or no term
      rw [h0, Bool.cond_true] at hh ⊢
      by_cases hv : (O.van (x :: b) || anyI τ (x :: b) (S.propI (x :: b))) = true
      · rw [hv, Bool.cond_true]
        rw [Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · exact R.van hg hv
        · obtain ⟨cfg, hcfg⟩ := anyI_some hv
          exact R.evl hg hcfg
      · rw [Bool.not_eq_true] at hv
        rw [hv, Bool.cond_false] at hh
        exact absurd hh (lt_irrefl _)
    rw [Bool.not_eq_true] at h0
    rw [h0, Bool.cond_false] at hh ⊢
    by_cases h1 : Nat.beq (Nat.mod h 4) 1 = true
    · -- Buchstab's identity at the guide's floor
      rw [h1, Bool.cond_true] at hh ⊢
      cases hgJ : gJ (x :: b) (Nat.mod (Nat.div h 4) 16) with
      | some p =>
        simp only [hgJ] at hh ⊢
        by_cases hc : (Nat.blt 0 p.1 && Nat.ble p.1 x.1 && τ.okJ (x :: b) p.1 p.2) = true
        · rw [hc, Bool.cond_true] at hh ⊢
          simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
          exact R.buch hg hc.1.1 hc.1.2 hc.2 (kidsH_sound R.split hrec _ _ _ _ _ _ _ hh)
        · rw [Bool.not_eq_true] at hc
          rw [hc, Bool.cond_false] at hh
          exact absurd hh (lt_irrefl _)
      | none =>
        simp only [hgJ] at hh
        exact absurd hh (lt_irrefl _)
    rw [Bool.not_eq_true] at h1
    rw [h1, Bool.cond_false] at hh ⊢
    by_cases h2 : Nat.beq (Nat.mod h 8) 3 = true
    · -- dropped
      rw [h2, Bool.cond_true] at hh ⊢
      cases hd : O.drp (x :: b) par with
      | some dc =>
        simp only [hd] at hh ⊢
        exact R.drp hg hd
      | none =>
        simp only [hd] at hh
        exact absurd hh (lt_irrefl _)
    rw [Bool.not_eq_true] at h2
    rw [h2, Bool.cond_false] at hh ⊢
    by_cases h3 : Nat.beq (Nat.mod h 16) 7 = true
    · -- the bound `alt`
      rw [h3, Bool.cond_true] at hh ⊢
      exact R.alt hg hh
    rw [Bool.not_eq_true] at h3
    rw [h3, Bool.cond_false] at hh ⊢
    by_cases h4 : Nat.beq (Nat.mod h 32) 15 = true
    · -- the hinted bound
      rw [h4, Bool.cond_true] at hh ⊢
      exact haltH _ _ _ _ hg hh
    rw [Bool.not_eq_true] at h4
    rw [h4, Bool.cond_false] at hh ⊢
    by_cases h5 : Nat.beq (Nat.mod h 64) 31 = true
    · -- the cell cut in two
      rw [h5, Bool.cond_true] at hh ⊢
      generalize Nat.div (Nat.add x.1 x.2) 2 = mid at hh ⊢
      generalize Nat.div h 64 = h' at hh ⊢
      by_cases hc : (Nat.blt x.1 mid && Nat.blt mid x.2) = true
      · rw [hc, Bool.cond_true] at hh ⊢
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc
        have hr := hrec ((x.1, mid) :: b) par lim h'
        generalize rec ((x.1, mid) :: b) par lim h' = r at hh hr ⊢
        by_cases hl : Nat.ble lim r.1 = true
        · rw [hl, Bool.cond_true] at hh
          rw [Nat.ble_eq] at hl
          omega
        · rw [Bool.not_eq_true] at hl
          rw [hl, Bool.cond_false] at hh ⊢
          have hl' : ¬ lim ≤ r.1 := by
            rw [← Nat.ble_eq, hl]
            simp
          have hh' : r.1 + (rec ((mid, x.2) :: b) par (lim - r.1) r.2).1 < lim := hh
          have h2' : (rec ((mid, x.2) :: b) par (lim - r.1) r.2).1 < lim - r.1 := by omega
          exact R.split (top := x.2) hc.1 hc.2 (hr (by omega)) (hrec _ _ _ _ h2')
      · rw [Bool.not_eq_true] at hc
        rw [hc, Bool.cond_false] at hh
        exact absurd hh (lt_irrefl _)
    rw [Bool.not_eq_true] at h5
    rw [h5, Bool.cond_false] at hh
    exact absurd hh (lt_irrefl _)

/-- **The search led by hints is sound**: a cost that it returns below its limit has the statement that its nodes
and its hinted bound prove, whatever the hints and the guide. -/
theorem solveH_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) (S : Strat)
    (gJ : List Cell → ℕ → Option (ℕ × Cfg)) {altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ}
    (haltH : ∀ bl par l h, O.grd bl = true → (altH bl par l h).1 < l → P bl par (altH bl par l h).1) :
    ∀ n : ℕ, RecPH P (solveH O τ S gJ altH n)
  | 0 => fun _ _ _ _ h => absurd h (lt_irrefl _)
  | n + 1 => stepH_sound R haltH (solveH_sound R S gJ haltH n)

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

/-! ### The reversal through the largest prime, its tree searched by hints -/

/-- **The cost of a reversal through the largest prime, its tree searched by hints, bounds the term.** For a box
that passes `flipOK`: a cost that `flipCostH` returns below its limit gives `Bd false (cost/K)` for the box,
whatever the hints and the guide. -/
theorem bd_flipCostH (SK : Cell → List Cell → Strat) (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg))
    (fuel maxlen : ℕ) {bl : List Cell} (hok : flipOK maxlen bl = true) {lim h : ℕ}
    (hlt : (flipCostH SK GK fuel bl lim h).1 < lim) (k' : ℕ) (hl : bl.length = k' + 1) :
    Bd false (((flipCostH SK GK fuel bl lim h).1 : ℝ) / K) (boxFn bl (k' + 1) hl) := by
  have h2 : 2 ≤ bl.length := by
    simp only [flipOK, Bool.and_eq_true, Nat.ble_eq] at hok
    exact hok.1.1.1.1.1.1.1.1
  obtain ⟨c0, b, hβdef⟩ : ∃ c0 b, c0 :: b = initC bl := by
    cases hb : initC bl with
    | nil =>
      have hne : bl ≠ [] := by
        intro h0
        rw [h0] at h2
        simp at h2
      have := congrArg List.length (initC_append_lastC hne)
      rw [hb] at this
      simp at this
      omega
    | cons c0 b => exact ⟨c0, b, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = flipTreeH SK GK fuel (lastC bl) (c0 :: b) CAPK h := ⟨_, rfl⟩
  have hunf : (flipCostH SK GK fuel bl lim h).1 = cond (Nat.ble CAPK r.1) lim
      (cdiv (r.1 * ((lastC bl).2 * dropCost bl +
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) +
        bdK (lastC bl) (flipT (lastC bl)) *
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) (DEN * K)) := by
    unfold flipCostH
    rw [← hβdef]
    beta_reduce
    rw [← hrdef]
  cases hcap : Nat.ble CAPK r.1
  swap
  · rw [hunf, hcap] at hlt
    exact absurd hlt (lt_irrefl _)
  rw [hcap, Bool.cond_false] at hunf
  have hccap : r.1 < CAPK := by
    by_contra hge
    rw [Nat.ble_eq_true_of_le (not_lt.1 hge)] at hcap
    exact Bool.noConfusion hcap
  obtain ⟨St, hSt⟩ : ∃ St : Strat, St = SK (lastC bl) (c0 :: b) := ⟨_, rfl⟩
  have hrunf : r = match GK (lastC bl) (c0 :: b) (c0 :: b) (Nat.mod h 16) with
      | some p =>
        cond (Nat.blt 0 p.1 && Nat.ble p.1 (minN c0.1 (flipT (lastC bl))) &&
            (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b)
              p.1 p.2)
          (kidsH (solveH (opsK (lastC bl) (c0 :: b).length)
              (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b)) St
              (GK (lastC bl) (c0 :: b)) noAltH fuel)
            (flipT (lastC bl)) (c0 :: b) true (St.cuts (c0 :: b) p.1) p.1 CAPK (Nat.div h 16))
          (CAPK, Nat.div h 16)
      | none => (CAPK, Nat.div h 16) := by
    rw [hrdef, hSt]
    rfl
  cases hg : GK (lastC bl) (c0 :: b) (c0 :: b) (Nat.mod h 16) with
  | none =>
    rw [hg] at hrunf
    rw [hrunf] at hccap
    exact absurd hccap (lt_irrefl _)
  | some p =>
    rw [hg] at hrunf
    by_cases hc : (Nat.blt 0 p.1 && Nat.ble p.1 (minN c0.1 (flipT (lastC bl))) &&
        (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b) p.1
          p.2) = true
    · simp only [hc, Bool.cond_true] at hrunf
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
      rw [hunf]
      refine bd_flip_core hok k' hl hβdef hc.1.2 hc.2 fun s hβl hR => ?_
      have hk := kidsH_sound hR.split
        (solveH_sound hR St (GK (lastC bl) (c0 :: b)) (altH := noAltH)
          (fun _ _ _ _ _ hh => absurd hh (lt_irrefl _)) fuel)
        (flipT (lastC bl)) (c0 :: b) true (St.cuts (c0 :: b) p.1) p.1 CAPK (Nat.div h 16)
        (by rw [← hrunf]; exact hccap)
      rw [← hrunf] at hk
      exact hk
    · rw [Bool.not_eq_true] at hc
      simp only [hc, Bool.cond_false] at hrunf
      rw [hrunf] at hccap
      exact absurd hccap (lt_irrefl _)

/-- **The hinted bound of the main search proves `PR`**: a cost that `altFH` returns below its limit bounds the
term of the box. -/
theorem altFH_sound (SK : Cell → List Cell → Strat) (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg))
    (fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ)
    (hlt : (altFH SK GK fuel maxlen bl par l h).1 < l) : PR bl par (altFH SK GK fuel maxlen bl par l h).1 := by
  unfold altFH at hlt ⊢
  by_cases hf : (!par && flipOK maxlen bl) = true
  · rw [hf, Bool.cond_true] at hlt ⊢
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
    obtain ⟨hp, hfok⟩ := hf
    subst hp
    intro k' hl
    exact bd_flipCostH SK GK fuel maxlen hfok hlt k' hl
  · rw [Bool.not_eq_true] at hf
    rw [hf, Bool.cond_false] at hlt
    exact absurd hlt (lt_irrefl _)

/-! ### The main search led by hints -/

/-- **The main search led by hints is sound**: the nodes of the search with role reversal, the reversal through
the largest prime as the hinted bound; a cost that it returns below its limit bounds the term, whatever the hints
and the guides. -/
theorem solveFH_sound {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ)
    (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat)
    (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg)) (fuel maxlen : ℕ) (S : Strat)
    (gJ : List Cell → ℕ → Option (ℕ × Cfg)) (n : ℕ) :
    RecPH PR (solveH (opsR τ SK₀ fuel₀ cq) τ S gJ (altFH SK GK fuel maxlen) n) :=
  solveH_sound (rulesR hτ hτX SK₀ fuel₀ cq) S gJ
    (fun bl par l h _ hlt => altFH_sound SK GK fuel maxlen bl par l h hlt) n

/-- **A part of the main search led by hints**, as the kernel checks it: if the costs of the cells of the new
prime between `a` and `top`, cut at `cs` and searched by the hints `h` with the limit `K`, sum to at most `c < K`,
then the term of the box of the whole range is at least `−(c/K + o(1))x/(φ(q) log x)` with its sign. -/
theorem pr_of_kidsH {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ)
    (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat)
    (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg)) (fuel maxlen : ℕ) (S : Strat)
    (gJ : List Cell → ℕ → Option (ℕ × Cfg)) (n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ}
    {a c h : ℕ}
    (hk : (kidsH (solveH (opsR τ SK₀ fuel₀ cq) τ S gJ (altFH SK GK fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : PR ((a, top) :: bl) par c :=
  pr_mono (kidsH_sound pr_split (solveFH_sound hτ hτX SK₀ fuel₀ cq SK GK fuel maxlen S gJ n) top bl par cs a K h
    (lt_of_le_of_lt hk hc)) hk

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of the main search led by hints, for any route**: `pr_of_kidsH` with the route and its exponent as
variables. -/
theorem pr_of_kidsH_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {τ : Tests}
    (hτ : @Tests.Sound Rt τ) (hτX : @Tests.SoundX Rt τ) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ)
    (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat)
    (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg)) (fuel maxlen : ℕ) (S : Strat)
    (gJ : List Cell → ℕ → Option (ℕ × Cfg)) (n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ}
    {a c h : ℕ}
    (hk : (kidsH (solveH (opsR τ SK₀ fuel₀ cq) τ S gJ (@altFH Pr SK GK fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : @PR Rt ((a, top) :: bl) par c :=
  @pr_of_kidsH Rt hRt Pr hPr τ hτ hτX SK₀ fuel₀ cq SK GK fuel maxlen S gJ n top bl par cs a c h hk hc

end SieveAd

#print axioms SieveAd.pr_of_kidsH_at
