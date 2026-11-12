/-
# The search led by hints is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdDirDefs.lean` has a search that is told what to do at each box by a number, the hints:
what is done with the box, with which configuration, and where the range of a new prime is cut; and what the
kernel computes at a box is written for it. Here:

* `omKwP_eq`, `drpMP_eq`, `opsKP_eq`: Buchstab's function with the arithmetic written out is `SieveCert.omKw`;
  the cost of a dropped box in one pass is `dropC`'s; the nodes of a tree over a frozen part with that cost are
  `opsK`'s.
* `kidsC_sound`, `stepD_sound`, `solveD_sound`: **the search is sound**: for nodes that prove a statement and a
  hinted bound that does, a cost that it returns below its limit has the statement, whatever the hints are. Each
  step is one of the rules among which a search chooses (`SieveAd.Rules`), and is checked before it is used.
* `rules_frozC`: the nodes of a tree over a frozen part prove its statements with the tests `frozTestsC`, which
  read the frozen primes once for the tree: a statement of the tree concerns the boxes that end with the frozen
  primes, and on those `frozTestsC` implies `frozTests`.
* `bd_flipCostD`, `altFD_sound`: the reversal of a box through its largest prime, its tree searched by hints,
  bounds the term (`bd_flip_core` with the tree's bound from `solveD_sound` and `rules_frozC`).
* `pr_of_partD`, `pr_of_partD_at`: a part of the main search, as the kernel checks it, bounds the term of its
  range.

The file imports `SieveAdFlipSearch.lean`, `SieveAdFast.lean` and `SieveAdDirDefs.lean`.
-/
import SieveAdFlipSearch
import SieveAdFast
import SieveAdDirDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K cdiv omKw topK w1K LD)

/-! ### The arithmetic written out is the arithmetic of the type classes -/

theorem cond_blt (a b : ℕ) {α : Type} (x y : α) : cond (Nat.blt a b) x y = if a < b then x else y := by
  unfold Nat.blt
  rw [cond_ble]
  rfl

theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  rw [cond_ble, Nat.max_def]

theorem lnTP_eq (k : ℕ) : lnTP k = SieveCert.lnT k := by
  unfold lnTP SieveCert.lnT
  simp only [cond_blt]

theorem omFP_eq (P Q : ℕ) : omFP P Q = SieveCert.omF P Q := by
  unfold omFP SieveCert.omF omFkP SieveCert.omFk
  simp only [lnTP_eq]
  rfl

theorem invKwP_eq (s t W w : ℕ) : invKwP s t W w = SieveCert.invKw s t W w := by
  unfold invKwP SieveCert.invKw
  rw [cond_ble]
  rfl

/-- **Buchstab's function with the arithmetic written out is `SieveCert.omKw`.** -/
theorem omKwP_eq (s t W w : ℕ) : omKwP s t W w = omKw s t W w := by
  unfold omKwP omKw
  simp only [cond_blt, cond_ble, maxN_eq, omFP_eq, invKwP_eq]
  rfl

/-- `cellI` is `1` for a cell with `0 < lo < hi`. -/
theorem cellI_one {x : Cell} (h1 : 0 < x.1) (h2 : x.1 < x.2) : cellI x = 1 := by
  have e1 : Nat.sub 1 (Nat.sub 1 x.1) = 1 := by
    show 1 - (1 - x.1) = 1
    omega
  have e2 : Nat.sub 1 (Nat.sub 1 (Nat.sub x.2 x.1)) = 1 := by
    show 1 - (1 - (x.2 - x.1)) = 1
    omega
  unfold cellI
  rw [e1, e2]

/-- `cellI` is `0` for a cell without `0 < lo < hi`. -/
theorem cellI_zero {x : Cell} (h : ¬ (0 < x.1 ∧ x.1 < x.2)) : cellI x = 0 := by
  unfold cellI
  by_cases h1 : 0 < x.1
  · have e2 : Nat.sub 1 (Nat.sub 1 (Nat.sub x.2 x.1)) = 0 := by
      show 1 - (1 - (x.2 - x.1)) = 0
      have : ¬ x.1 < x.2 := fun h2 => h ⟨h1, h2⟩
      omega
    rw [e2]
    rfl
  · have e1 : Nat.sub 1 (Nat.sub 1 x.1) = 0 := by
      show 1 - (1 - x.1) = 0
      omega
    rw [e1]
    exact Nat.zero_mul _

/-- The product of `cellI` over the cells. -/
def okProd : List Cell → ℕ
  | [] => 1
  | c :: b => cellI c * okProd b

/-- The upper end of the last cell, or `d` for no cell. -/
def lastHiP (d : ℕ) : List Cell → ℕ
  | [] => d
  | c :: b => lastHiP c.2 b

/-- The product of `cellI` is `1` exactly for cells with `0 < lo < hi`. -/
theorem okProd_beq : ∀ l : List Cell, Nat.beq (okProd l) 1 = cellsOK l
  | [] => rfl
  | c :: b => by
    have ih := okProd_beq b
    show Nat.beq (cellI c * okProd b) 1 = (Nat.blt 0 c.1 && Nat.blt c.1 c.2 && cellsOK b)
    rw [← ih]
    by_cases h : 0 < c.1 ∧ c.1 < c.2
    · rw [cellI_one h.1 h.2, Nat.one_mul]
      have e1 : Nat.blt 0 c.1 = true := by
        rw [Nat.blt_eq]
        exact h.1
      have e2 : Nat.blt c.1 c.2 = true := by
        rw [Nat.blt_eq]
        exact h.2
      rw [e1, e2]
      rfl
    · rw [cellI_zero h, Nat.zero_mul]
      have e : (Nat.blt 0 c.1 && Nat.blt c.1 c.2) = false := by
        rw [Bool.and_eq_false_iff]
        by_cases h1 : 0 < c.1
        · right
          rw [← Bool.not_eq_true, Nat.blt_eq]
          exact fun h2 => h ⟨h1, h2⟩
        · left
          rw [← Bool.not_eq_true, Nat.blt_eq]
          exact h1
      rw [e]
      rfl

/-- **The pass over the cells of a box after the first**: what `tailP` gives to its continuation. -/
theorem tailP_eq {α : Type} : ∀ (l : List Cell) (ls hs tp ok n lh : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → α),
    tailP l ls hs tp ok n lh k =
      k (ls + loSum l) (hs + hiSum l) (tp * trProd l) (ok * okProd l) (n + l.length) (lastHiP lh l)
  | [], ls, hs, tp, ok, n, lh, k => by
    show k ls hs tp ok n lh = _
    simp [loSum, hiSum, trProd, okProd, lastHiP]
  | x :: b, ls, hs, tp, ok, n, lh, k => by
    show tailP b (Nat.add ls x.1) (Nat.add hs x.2) (Nat.mul tp (trFP x.1 (Nat.sub x.2 x.1)))
      (Nat.mul ok (cellI x)) (Nat.succ n) x.2 k = _
    rw [tailP_eq b]
    have e1 : Nat.add ls x.1 + loSum b = ls + loSum (x :: b) := by
      show ls + x.1 + loSum b = ls + (x.1 + loSum b)
      omega
    have e2 : Nat.add hs x.2 + hiSum b = hs + hiSum (x :: b) := by
      show hs + x.2 + hiSum b = hs + (x.2 + hiSum b)
      omega
    have e3 : Nat.mul tp (trFP x.1 (Nat.sub x.2 x.1)) * trProd b = tp * trProd (x :: b) := by
      show tp * trF x.1 (x.2 - x.1) * trProd b = tp * (trF x.1 (x.2 - x.1) * trProd b)
      exact Nat.mul_assoc _ _ _
    have e4 : Nat.mul ok (cellI x) * okProd b = ok * okProd (x :: b) := by
      show ok * cellI x * okProd b = ok * (cellI x * okProd b)
      exact Nat.mul_assoc _ _ _
    have e5 : Nat.succ n + b.length = n + (x :: b).length := by
      show n + 1 + b.length = n + (b.length + 1)
      omega
    rw [e1, e2, e3, e4, e5]
    rfl

/-- `dropF` on the sums of a box's cells after the first is `dropCost`. -/
theorem dropF_eq (c : Cell) (b : List Cell) :
    dropF c (loSum b) (hiSum b) (trProd b) b.length = dropCost (c :: b) := by
  unfold dropF
  rw [omKwP_eq]
  rfl

/-- **The cost of a dropped box of the main tree in one pass is `dropC`'s.** -/
theorem drpMP_eq (bl : List Cell) (par : Bool) : drpMP bl par = dropC bl par := by
  cases bl with
  | nil => cases par <;> rfl
  | cons c b =>
    cases par with
    | false => rfl
    | true =>
      show tailP b 0 0 1 (cellI c) 0 0 _ = _
      rw [tailP_eq]
      simp only [Nat.zero_add, Nat.one_mul]
      have hok : Nat.beq (cellI c * okProd b) 1 = cellsOK (c :: b) := okProd_beq (c :: b)
      rw [hok, dropF_eq]
      rfl

/-- **The pass over the first `j` cells of the cells of a box after the first.** -/
theorem chainP_eq {α : Type} : ∀ (l : List Cell) (j ls hs tp ok n : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → α),
    chainP l j ls hs tp ok n k =
      k (ls + loSum (l.take j)) (hs + hiSum (l.take j)) (tp * trProd (l.take j)) (ok * okProd (l.take j))
        (n + (l.take j).length)
  | [], j, ls, hs, tp, ok, n, k => by
    show k ls hs tp ok n = _
    simp [loSum, hiSum, trProd, okProd]
  | x :: b, 0, ls, hs, tp, ok, n, k => by
    show k ls hs tp ok n = _
    simp [loSum, hiSum, trProd, okProd]
  | x :: b, j + 1, ls, hs, tp, ok, n, k => by
    show chainP b (Nat.sub (j + 1) 1) (Nat.add ls x.1) (Nat.add hs x.2) (Nat.mul tp (trFP x.1 (Nat.sub x.2 x.1)))
      (Nat.mul ok (cellI x)) (Nat.succ n) k = _
    rw [chainP_eq b]
    have ej : Nat.sub (j + 1) 1 = j := rfl
    rw [ej]
    have et : (x :: b).take (j + 1) = x :: b.take j := rfl
    rw [et]
    have e1 : Nat.add ls x.1 + loSum (b.take j) = ls + loSum (x :: b.take j) := by
      show ls + x.1 + loSum (b.take j) = ls + (x.1 + loSum (b.take j))
      omega
    have e2 : Nat.add hs x.2 + hiSum (b.take j) = hs + hiSum (x :: b.take j) := by
      show hs + x.2 + hiSum (b.take j) = hs + (x.2 + hiSum (b.take j))
      omega
    have e3 : Nat.mul tp (trFP x.1 (Nat.sub x.2 x.1)) * trProd (b.take j) = tp * trProd (x :: b.take j) := by
      show tp * trF x.1 (x.2 - x.1) * trProd (b.take j) = tp * (trF x.1 (x.2 - x.1) * trProd (b.take j))
      exact Nat.mul_assoc _ _ _
    have e4 : Nat.mul ok (cellI x) * okProd (b.take j) = ok * okProd (x :: b.take j) := by
      show ok * cellI x * okProd (b.take j) = ok * (cellI x * okProd (b.take j))
      exact Nat.mul_assoc _ _ _
    have e5 : Nat.succ n + (b.take j).length = n + (x :: b.take j).length := by
      show n + 1 + (b.take j).length = n + ((b.take j).length + 1)
      omega
    rw [e1, e2, e3, e4, e5]

/-- **The cost of the dropped chain of a box in one pass is `dropK`'s.** -/
theorem drpKP_eq (ctx : Cell) (j : ℕ) (bl : List Cell) (par : Bool) :
    drpKP ctx j bl par = dropK ctx (bl.take j) par := by
  cases bl with
  | nil => cases j <;> rfl
  | cons c b =>
    cases j with
    | zero => rfl
    | succ j =>
      show chainP b (Nat.sub (j + 1) 1) 0 0 1 (cellI c) 0 _ = dropK ctx (c :: b.take j) par
      rw [chainP_eq]
      have ej : Nat.sub (j + 1) 1 = j := rfl
      rw [ej]
      simp only [Nat.zero_add, Nat.one_mul]
      have hok : Nat.beq (cellI c * okProd (b.take j)) 1 = cellsOK (c :: b.take j) := okProd_beq (c :: b.take j)
      rw [hok, omKwP_eq]
      rfl

/-- **The nodes of a tree over a frozen part, a dropped box's cost in one pass, are `opsK`'s.** -/
theorem opsKP_eq (ctx : Cell) (na : ℕ) : opsKP ctx na = opsK ctx na := by
  unfold opsKP opsK
  congr 1
  · funext bl
    rw [lenR_eq]
  · funext bl par
    rw [drpKP_eq, lenR_eq]
    rfl

/-! ### The search -/

/-- What a search led by hints must satisfy: a cost below the limit has the statement, whatever the hints. -/
def RecPH (P : List Cell → Bool → ℕ → Prop) (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) : Prop :=
  ∀ bl par lim h, (rec bl par lim h).1 < lim → P bl par (rec bl par lim h).1

theorem brec_eq {α : Type} (a b : α) (c : Bool) : Bool.rec (motive := fun _ => α) a b c = cond c b a := by
  cases c <;> rfl

/-- What follows a cut is sound: a cost that it returns below its limit has the statement, for the range from
where it starts to `top`. -/
def KontP (P : List Cell → Bool → ℕ → Prop) (top : ℕ) (bl : List Cell) (par : Bool) (kont : ℕ → ℕ → ℕ → ℕ × ℕ) :
    Prop :=
  ∀ a lim h, (kont a lim h).1 < lim → P ((a, top) :: bl) par (kont a lim h).1

/-- The last cell of a range is sound. -/
theorem kontP_last {P : List Cell → Bool → ℕ → Prop} {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec)
    (top : ℕ) (bl : List Cell) (par : Bool) : KontP P top bl par (fun a lim h => rec ((a, top) :: bl) par lim h) :=
  fun _ _ _ hh => hrec _ _ _ _ hh

/-- **A cut is sound**, if what follows it is. -/
theorem cutK_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) {top : ℕ} {bl : List Cell} {par : Bool} (p : ℕ)
    {kont : ℕ → ℕ → ℕ → ℕ × ℕ} (hk : KontP P top bl par kont) : KontP P top bl par (cutK rec top bl par p kont) := by
  intro a lim h hh
  unfold cutK at hh ⊢
  simp only [brec_eq] at hh ⊢
  by_cases h1 : Nat.ble (Nat.succ a) p = true
  swap
  · rw [Bool.not_eq_true] at h1
    rw [h1, Bool.cond_false] at hh
    exact absurd hh (lt_irrefl _)
  rw [h1, Bool.cond_true] at hh ⊢
  by_cases h2 : Nat.ble (Nat.succ p) top = true
  swap
  · rw [Bool.not_eq_true] at h2
    rw [h2, Bool.cond_false] at hh
    exact absurd hh (lt_irrefl _)
  rw [h2, Bool.cond_true] at hh ⊢
  rw [Nat.ble_eq] at h1 h2
  have hr := hrec ((a, p) :: bl) par lim h
  generalize rec ((a, p) :: bl) par lim h = r at hh hr ⊢
  by_cases hl : Nat.ble lim r.1 = true
  · rw [hl, Bool.cond_true] at hh
    rw [Nat.ble_eq] at hl
    omega
  · rw [Bool.not_eq_true] at hl
    rw [hl, Bool.cond_false] at hh ⊢
    have hl' : ¬ lim ≤ r.1 := by
      rw [← Nat.ble_eq, hl]
      simp
    have hh' : r.1 + (kont p (lim - r.1) r.2).1 < lim := hh
    have h2' : (kont p (lim - r.1) r.2).1 < lim - r.1 := by omega
    exact hsplit h1 h2 (hr (by omega)) (hk p _ _ h2')

/-- **The next cell of the new prime is sound**, if what follows it is. -/
theorem kidsCS_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) (top : ℕ) (bl : List Cell) (par : Bool)
    (κ st reg e last : ℕ) {ih : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ} (hih : ∀ c, KontP P top bl par (ih c)) (c : ℕ) :
    KontP P top bl par (kidsCS rec top bl par κ st reg e last ih c) := by
  intro a lim h hh
  unfold kidsCS at hh ⊢
  simp only [brec_eq] at hh ⊢
  by_cases h0 : Nat.beq (Nat.land h 1) 1 = true
  swap
  · rw [Bool.not_eq_true] at h0
    rw [h0, Bool.cond_false] at hh ⊢
    exact hrec _ _ _ _ hh
  rw [h0, Bool.cond_true] at hh ⊢
  by_cases hj : Nat.beq (Nat.land (Nat.div h 2) 3) 3 = true
  swap
  · rw [Bool.not_eq_true] at hj
    rw [hj, Bool.cond_false] at hh ⊢
    exact cutK_sound hsplit hrec _ (hih _) a lim _ hh
  rw [hj, Bool.cond_true] at hh ⊢
  by_cases ht : Nat.ble (Nat.land (Nat.div h 8) 7) 3 = true
  · rw [ht, Bool.cond_true] at hh ⊢
    exact cutK_sound hsplit hrec _ (hih _) a lim _ hh
  rw [Bool.not_eq_true] at ht
  rw [ht, Bool.cond_false] at hh ⊢
  by_cases h4 : Nat.beq (Nat.land (Nat.div h 8) 7) 4 = true
  · rw [h4, Bool.cond_true] at hh ⊢
    exact hih _ a lim _ hh
  rw [Bool.not_eq_true] at h4
  rw [h4, Bool.cond_false] at hh ⊢
  exact cutK_sound hsplit hrec _ (hih _) a lim _ hh

/-- **The cells of the new prime, their cuts read from the hints, are sound**: costs that sum to less than the
limit give the statement on the whole range, whatever the hints, the grid and the cuts off the grid. -/
theorem kidsC_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) (top : ℕ) (bl : List Cell) (par : Bool)
    (κ st reg e last : ℕ) : ∀ n c : ℕ, KontP P top bl par (kidsC rec top bl par κ st reg e last n c)
  | 0, _ => fun _ _ _ hh => absurd hh (lt_irrefl _)
  | n + 1, c =>
    kidsCS_sound hsplit hrec top bl par κ st reg e last
      (fun c' => kidsC_sound hsplit hrec top bl par κ st reg e last n c') c

/-- The pass `sumsP` gives its continuation four numbers. -/
theorem sumsP_eq {α : Type} : ∀ (l : List Cell) (ls hs n ll : ℕ) (k : ℕ → ℕ → ℕ → ℕ → α),
    ∃ ls' hs' n' ll', sumsP l ls hs n ll k = k ls' hs' n' ll'
  | [], ls, hs, n, ll, _ => ⟨ls, hs, n, ll, rfl⟩
  | x :: b, ls, hs, n, _, k => sumsP_eq b (Nat.add ls x.1) (Nat.add hs x.2) (Nat.succ n) x.1 k

/-- What the search of the cells of a new prime must satisfy: for a search of the boxes below that is sound,
costs below the limit give the statement on the range from the floor to `top`. -/
def KidsP (P : List Cell → Bool → ℕ → Prop)
    (kd : (List Cell → Bool → ℕ → ℕ → ℕ × ℕ) → ℕ → List Cell → Bool → ℕ → ℕ → ℕ → ℕ × ℕ) : Prop :=
  ∀ rec, RecPH P rec → ∀ top bl par f lim h, (kd rec top bl par f lim h).1 < lim →
    P ((f, top) :: bl) par (kd rec top bl par f lim h).1

/-- The cells of the new prime in the main tree are sound. -/
theorem kidsM_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    (κ hI : ℕ) : KidsP P (kidsM κ hI) := by
  intro rec hrec top bl par f lim h hh
  unfold kidsM at hh ⊢
  obtain ⟨ls, hs, n, ll, e⟩ := sumsP_eq bl 0 0 0 0 fun ls hs n ll =>
    kidsC rec top bl par κ (stepOf hI (Nat.succ n)) (minN top (Nat.add (Nat.div (Nat.sub DEN ls) 2) 2))
      (Nat.sub ll 1) (Nat.sub (Nat.sub DEN 1) hs) 4096 f f lim h
  rw [e] at hh ⊢
  exact kidsC_sound hsplit hrec top bl par _ _ _ _ _ 4096 f f lim h hh

/-- The pass `headP` gives its continuation two numbers. -/
theorem headP_eq {α : Type} : ∀ (l : List Cell) (j ls hs : ℕ) (k : ℕ → ℕ → α),
    ∃ ls' hs', headP l j ls hs k = k ls' hs'
  | [], _, ls, hs, _ => ⟨ls, hs, rfl⟩
  | x :: b, j, ls, hs, k => by
    show ∃ ls' hs', Bool.rec (motive := fun _ => α) (headP b (Nat.sub j 1) (Nat.add ls x.1) (Nat.add hs x.2) k)
      (k ls hs) (Nat.beq j 0) = k ls' hs'
    cases Nat.beq j 0 with
    | true => exact ⟨ls, hs, rfl⟩
    | false => exact headP_eq b (Nat.sub j 1) (Nat.add ls x.1) (Nat.add hs x.2) k

/-- The cells of the new prime in a tree over a frozen part are sound. -/
theorem kidsF_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    (κ hR : ℕ) (ctx : Cell) (nb : ℕ) : KidsP P (kidsF κ hR ctx nb) := by
  intro rec hrec top bl par f lim h hh
  unfold kidsF at hh ⊢
  simp only [] at hh ⊢
  obtain ⟨ls, hs, e⟩ := headP_eq bl (Nat.sub (lenR bl) nb) 0 0 fun lsc hsc =>
    kidsC rec top bl par κ (cond (Nat.blt (Nat.sub (lenR bl) nb) 2) hR (Nat.mul 2 hR))
      (minN top (Nat.add (Nat.div (Nat.sub (Nat.succ ctx.2) lsc) 2) 2)) 0 (Nat.sub (Nat.sub ctx.1 1) hsc) 4096 f f
      lim h
  rw [e] at hh ⊢
  exact kidsC_sound hsplit hrec top bl par _ _ _ _ _ 4096 f f lim h hh

/-- **The cells of the new prime cut at given cuts are sound.** -/
theorem partD_sound {P : List Cell → Bool → ℕ → Prop}
    (hsplit : ∀ {a m top : ℕ} {bl : List Cell} {par : Bool} {c1 c2 : ℕ}, a < m → m < top →
      P ((a, m) :: bl) par c1 → P ((m, top) :: bl) par c2 → P ((a, top) :: bl) par (c1 + c2))
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) (top : ℕ) (bl : List Cell) (par : Bool) :
    ∀ cs : List ℕ, KontP P top bl par (partD rec top bl par cs)
  | [] => kontP_last hrec top bl par
  | c :: cs => by
    have ih := partD_sound hsplit hrec top bl par cs
    intro a lim h hh
    have e : partD rec top bl par (c :: cs) a lim h = partDS rec top bl par c (partD rec top bl par cs) a lim h :=
      rfl
    rw [e] at hh ⊢
    unfold partDS at hh ⊢
    simp only [brec_eq] at hh ⊢
    by_cases hc : (Nat.blt a c && Nat.blt c top) = true
    swap
    · rw [Bool.not_eq_true] at hc
      rw [hc, Bool.cond_false] at hh
      exact absurd hh (lt_irrefl _)
    rw [hc, Bool.cond_true] at hh ⊢
    simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    have hr := hrec ((a, c) :: bl) par lim h
    generalize rec ((a, c) :: bl) par lim h = r at hh hr ⊢
    by_cases hl : Nat.ble lim r.1 = true
    · rw [hl, Bool.cond_true] at hh
      rw [Nat.ble_eq] at hl
      omega
    · rw [Bool.not_eq_true] at hl
      rw [hl, Bool.cond_false] at hh ⊢
      have hl' : ¬ lim ≤ r.1 := by
        rw [← Nat.ble_eq, hl]
        simp
      have hh' : r.1 + (partD rec top bl par cs c (lim - r.1) r.2).1 < lim := hh
      have h2' : (partD rec top bl par cs c (lim - r.1) r.2).1 < lim - r.1 := by omega
      exact hsplit hc.1 hc.2 (hr (by omega)) (ih c _ _ h2')

/-- **A step of the search led by hints is sound**: for nodes that prove `P`, cells of
the new prime, a hinted bound and a search of the boxes below that are sound, a cost below the limit has `P`,
whatever the hints and what is read from them. -/
theorem stepD_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P)
    {dI : List Cell → ℕ → Cfg × ℕ} {dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ}
    {kd : (List Cell → Bool → ℕ → ℕ → ℕ × ℕ) → ℕ → List Cell → Bool → ℕ → ℕ → ℕ → ℕ × ℕ} (hkd : KidsP P kd)
    {altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ}
    (haltH : ∀ bl par l h, O.grd bl = true → (altH bl par l h).1 < l → P bl par (altH bl par l h).1)
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) : RecPH P (stepD O τ dI dJ kd altH rec) := by
  intro bl par lim h hh
  cases bl with
  | nil => exact absurd hh (lt_irrefl _)
  | cons x b =>
    simp only [stepD, brec_eq] at hh ⊢
    by_cases hg : O.grd (x :: b) = true
    swap
    · rw [Bool.not_eq_true] at hg
      rw [hg, Bool.cond_false] at hh
      exact absurd hh (lt_irrefl _)
    rw [hg, Bool.cond_true] at hh ⊢
    by_cases h0 : Nat.beq (Nat.land h 1) 0 = true
    · -- evaluated by the configuration of the hints
      rw [h0, Bool.cond_true] at hh ⊢
      by_cases hI : τ.okI (x :: b) (dI (x :: b) (Nat.div h 2)).1 = true
      · rw [hI, Bool.cond_true]
        exact R.evl hg hI
      · rw [Bool.not_eq_true] at hI
        rw [hI, Bool.cond_false] at hh
        exact absurd hh (lt_irrefl _)
    rw [Bool.not_eq_true] at h0
    rw [h0, Bool.cond_false] at hh ⊢
    by_cases h1 : Nat.beq (Nat.land h 3) 1 = true
    · -- Buchstab's identity at the floor and with the configuration of the hints
      rw [h1, Bool.cond_true] at hh ⊢
      generalize dJ (x :: b) (Nat.div h 4) = p at hh ⊢
      by_cases hf1 : Nat.ble 1 p.1.1 = true
      swap
      · rw [Bool.not_eq_true] at hf1
        rw [hf1, Bool.cond_false] at hh
        exact absurd hh (lt_irrefl _)
      rw [hf1, Bool.cond_true] at hh ⊢
      by_cases hf2 : Nat.ble p.1.1 x.1 = true
      swap
      · rw [Bool.not_eq_true] at hf2
        rw [hf2, Bool.cond_false] at hh
        exact absurd hh (lt_irrefl _)
      rw [hf2, Bool.cond_true] at hh ⊢
      by_cases hJ : τ.okJ (x :: b) p.1.1 p.1.2 = true
      swap
      · rw [Bool.not_eq_true] at hJ
        rw [hJ, Bool.cond_false] at hh
        exact absurd hh (lt_irrefl _)
      rw [hJ, Bool.cond_true] at hh ⊢
      rw [Nat.ble_eq] at hf1 hf2
      exact R.buch hg hf1 hf2 hJ (hkd rec hrec _ _ _ _ _ _ hh)
    rw [Bool.not_eq_true] at h1
    rw [h1, Bool.cond_false] at hh ⊢
    by_cases h2 : Nat.beq (Nat.land h 7) 3 = true
    · -- dropped
      rw [h2, Bool.cond_true] at hh ⊢
      cases hd : O.drp (x :: b) par with
      | some dc => exact R.drp hg hd
      | none =>
        rw [hd] at hh
        exact absurd hh (lt_irrefl _)
    rw [Bool.not_eq_true] at h2
    rw [h2, Bool.cond_false] at hh ⊢
    by_cases h3 : Nat.beq (Nat.land h 15) 7 = true
    · -- the hinted bound
      rw [h3, Bool.cond_true] at hh ⊢
      exact haltH _ _ _ _ hg hh
    rw [Bool.not_eq_true] at h3
    rw [h3, Bool.cond_false] at hh ⊢
    by_cases h4 : Nat.beq (Nat.land h 31) 15 = true
    · -- the cell cut in two
      rw [h4, Bool.cond_true] at hh ⊢
      generalize Nat.div (Nat.add x.1 x.2) 2 = mid at hh ⊢
      generalize Nat.div h 32 = h' at hh ⊢
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
    rw [Bool.not_eq_true] at h4
    rw [h4, Bool.cond_false] at hh ⊢
    by_cases h5 : Nat.beq (Nat.land h 63) 31 = true
    · -- no term
      rw [h5, Bool.cond_true] at hh ⊢
      by_cases hv : O.van (x :: b) = true
      · rw [hv, Bool.cond_true]
        exact R.van hg hv
      · rw [Bool.not_eq_true] at hv
        rw [hv, Bool.cond_false] at hh
        exact absurd hh (lt_irrefl _)
    rw [Bool.not_eq_true] at h5
    rw [h5, Bool.cond_false] at hh ⊢
    exact R.alt hg hh

/-- **The search led by hints is sound**: a cost that it returns below its limit has the statement that its nodes
and its hinted bound prove, whatever the hints and what is read from them. -/
theorem solveD_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P)
    (dI : List Cell → ℕ → Cfg × ℕ) (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    {kd : (List Cell → Bool → ℕ → ℕ → ℕ × ℕ) → ℕ → List Cell → Bool → ℕ → ℕ → ℕ → ℕ × ℕ} (hkd : KidsP P kd)
    {altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ}
    (haltH : ∀ bl par l h, O.grd bl = true → (altH bl par l h).1 < l → P bl par (altH bl par l h).1) :
    ∀ n : ℕ, RecPH P (solveD O τ dI dJ kd altH n)
  | 0 => fun _ _ _ _ h => absurd h (lt_irrefl _)
  | n + 1 => stepD_sound R hkd haltH (solveD_sound R dI dJ hkd haltH n)

/-! ### The reversal through the largest prime -/

theorem lastP_cons : ∀ (b : List Cell) (x d : Cell), lastP (x :: b) d = lastC (x :: b)
  | [], _, _ => rfl
  | y :: b, x, _ => by
    show lastP (y :: b) x = lastC (y :: b)
    exact lastP_cons b y x

theorem lastP_eq (l : List Cell) : lastP l (0, 0) = lastC l := by
  cases l with
  | nil => rfl
  | cons x b => exact lastP_cons b x _

theorem initP_eq : ∀ l : List Cell, initP l = initC l
  | [] => rfl
  | [_] => rfl
  | x :: y :: b => by
    show x :: initP (y :: b) = x :: initC (y :: b)
    rw [initP_eq (y :: b)]

theorem loSum_snoc (b : List Cell) (d : Cell) : loSum (b ++ [d]) = loSum b + d.1 := by
  induction b with
  | nil => simp [loSum]
  | cons x b ih =>
    show x.1 + loSum (b ++ [d]) = x.1 + loSum b + d.1
    rw [ih]
    omega

theorem hiSum_snoc (b : List Cell) (d : Cell) : hiSum (b ++ [d]) = hiSum b + d.2 := by
  induction b with
  | nil => simp [hiSum]
  | cons x b ih =>
    show x.2 + hiSum (b ++ [d]) = x.2 + hiSum b + d.2
    rw [ih]
    omega

theorem trProd_snoc (b : List Cell) (d : Cell) : trProd (b ++ [d]) = trProd b * trF d.1 (d.2 - d.1) := by
  induction b with
  | nil => simp [trProd]
  | cons x b ih =>
    show trF x.1 (x.2 - x.1) * trProd (b ++ [d]) = trF x.1 (x.2 - x.1) * trProd b * trF d.1 (d.2 - d.1)
    rw [ih, Nat.mul_assoc]

theorem okProd_snoc (b : List Cell) (d : Cell) : okProd (b ++ [d]) = okProd b * cellI d := by
  induction b with
  | nil => simp [okProd]
  | cons x b ih =>
    show cellI x * okProd (b ++ [d]) = cellI x * okProd b * cellI d
    rw [ih, Nat.mul_assoc]

theorem lastHiP_eq : ∀ (b : List Cell) (c : Cell), (lastC (c :: b)).2 = lastHiP c.2 b
  | [], _ => rfl
  | y :: b, _ => by
    show (lastC (y :: b)).2 = lastHiP y.2 b
    exact lastHiP_eq b y

/-- `dropL` on the sums of the cells between the first and the last is `dropCost`. -/
theorem dropL_eq (c d : Cell) (b : List Cell) :
    dropL c d (loSum b) (hiSum b) (trProd b) b.length = dropCost ((c :: b) ++ [d]) := by
  have e : (c :: b) ++ [d] = c :: (b ++ [d]) := rfl
  rw [e, ← dropF_eq, loSum_snoc, hiSum_snoc, trProd_snoc, List.length_append]
  rfl

theorem bdKP_eq (ctx : Cell) (y : ℕ) : bdKP ctx y = bdK ctx y := by
  unfold bdKP bdK
  rw [omKwP_eq]
  rfl

/-- **The test `flipOKP` on the sums of a box is `flipOK`'s.** -/
theorem flipOK_of_P {maxlen : ℕ} {bl : List Cell} {c0 : Cell} {b : List Cell} (hβ : initC bl = c0 :: b)
    (h : flipOKP maxlen (lastC bl) c0 (hiSum b) (cellI c0 * okProd b) b.length (lastHiP c0.2 b) = true) :
    flipOK maxlen bl = true := by
  have hne : bl ≠ [] := by
    intro h0
    rw [h0] at hβ
    simp [initC] at hβ
  have hbl : (c0 :: b) ++ [lastC bl] = bl := by
    rw [← hβ]
    exact initC_append_lastC hne
  simp only [flipOKP, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hlen : bl.length = b.length + 2 := by
    rw [← hbl]
    simp
  have hcells : cellsOK bl = true := by
    rw [← okProd_beq, ← hbl, okProd_snoc]
    exact h3
  have hhs : hiSum bl = c0.2 + hiSum b + (lastC bl).2 := by
    conv_lhs => rw [← hbl]
    rw [hiSum_snoc]
    rfl
  have hlast : (lastC (initC bl)).2 = lastHiP c0.2 b := by
    rw [hβ]
    exact lastHiP_eq b c0
  simp only [flipOK, Bool.and_eq_true, Nat.ble_eq]
  have h1' : b.length + 2 ≤ maxlen := h1
  have h4' : c0.2 + hiSum b + (lastC bl).2 + 2 ≤ DEN := h4
  have h5' : lastHiP c0.2 b + 1 ≤ (lastC bl).1 := h5
  have h8' : (lastC bl).2 + flipT (lastC bl) + 1 ≤ DEN := h8
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, h2⟩, hcells⟩, ?_⟩, ?_⟩, h6⟩, h7⟩, h8'⟩
  · omega
  · omega
  · rw [hhs]
    exact h4'
  · rw [hlast]
    exact h5'

/-- Cells with `0 < lo < hi` whose upper ends sum to at most `DEN` pass the check of the tests from `1`: for the
cells of a box but the last. -/
theorem cellsFrom_one_init {d : Cell} : ∀ l : List Cell, cellsOK (l ++ [d]) = true → hiSum (l ++ [d]) ≤ DEN →
    cellsFrom 1 l = true
  | [], _, _ => rfl
  | x :: l, h, hs => by
    have h' : (Nat.blt 0 x.1 && Nat.blt x.1 x.2 && cellsOK (l ++ [d])) = true := h
    have hs' : x.2 + hiSum (l ++ [d]) ≤ DEN := hs
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    show (Nat.ble 1 x.1 && Nat.ble x.1 x.2 && Nat.ble x.2 DEN && cellsFrom 1 l) = true
    simp only [Bool.and_eq_true, Nat.ble_eq]
    exact ⟨⟨⟨h'.1.1, h'.1.2.le⟩, by omega⟩, cellsFrom_one_init l h'.2 (by omega)⟩

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

omit [RouteOK] [IBFits] in
/-- **The nodes of a tree over a frozen part, with the tests that read the frozen primes once for the tree**:
they are the nodes of the tree with the tests `frozTests`, since a statement of the tree only concerns the boxes
that end with the frozen primes, and on those the tests `frozTestsC` imply `frozTests`. -/
theorem rules_frozC {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {O : Ops} {e₁ e₂ Kb : ℕ} {β : List Cell}
    (hβ : cellsFrom 1 β = true) (h : Rules O (frozTests e₁ e₂ Kb β) (PF S R β)) :
    Rules O (frozTestsC e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN)) (PF S R β) where
  van := h.van
  evl := by
    intro bl par cfg hg hI ch hch
    subst hch
    exact h.evl hg (frozTestsC_okI e₁ e₂ Kb β ch cfg hβ hI) ch rfl
  drp := h.drp
  alt := h.alt
  split := h.split
  buch := by
    intro x b par f cfg c hg hf hfx hJ hc ch hch
    have hJ' : (frozTests e₁ e₂ Kb β).okJ (x :: b) f cfg = true := by
      rw [hch] at hJ ⊢
      exact frozTestsC_okJ e₁ e₂ Kb β ch f cfg hβ hJ
    exact h.buch hg hf hfx hJ' hc ch hch

/-- **The cost of a reversal through the largest prime, its tree searched by hints, bounds the term.** A cost
that `flipCostD` returns below its limit gives `Bd false (cost/K)` for the box, whatever the hints. -/
theorem bd_flipCostD (κ hR fuel maxlen : ℕ) {bl : List Cell} {lim h : ℕ}
    (hlt : (flipCostD κ hR fuel maxlen bl lim h).1 < lim) (k' : ℕ) (hl : bl.length = k' + 1) :
    Bd false (((flipCostD κ hR fuel maxlen bl lim h).1 : ℝ) / K) (boxFn bl (k' + 1) hl) := by
  unfold flipCostD at hlt ⊢
  rw [lastP_eq, initP_eq] at hlt ⊢
  revert hlt
  cases hβ : initC bl with
  | nil => exact fun hlt => absurd hlt (lt_irrefl _)
  | cons c0 b =>
    intro hlt
    simp only [] at hlt ⊢
    rw [tailP_eq] at hlt ⊢
    simp only [Nat.zero_add, Nat.one_mul] at hlt ⊢
    unfold flipCostB at hlt ⊢
    by_cases hok' : flipOKP maxlen (lastC bl) c0 (hiSum b) (cellI c0 * okProd b) b.length (lastHiP c0.2 b) = true
    swap
    · rw [Bool.not_eq_true] at hok'
      rw [hok', Bool.cond_false] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [hok', Bool.cond_true] at hlt ⊢
    have hok := flipOK_of_P hβ hok'
    have hne : bl ≠ [] := by
      intro h0
      rw [h0] at hβ
      simp [initC] at hβ
    have hbl : (c0 :: b) ++ [lastC bl] = bl := by
      rw [← hβ]
      exact initC_append_lastC hne
    simp only [dropL_eq, bdKP_eq] at hlt ⊢
    rw [hbl] at hlt ⊢
    obtain ⟨r, hrdef⟩ : ∃ r, r = flipTreeD κ hR fuel (lastC bl) c0 b (Nat.add c0.1 (loSum b))
        (Nat.add c0.2 (hiSum b)) (Nat.succ b.length) CAPK h := ⟨_, rfl⟩
    rw [← hrdef] at hlt ⊢
    by_cases hcap : Nat.ble CAPK r.1 = true
    · rw [hcap, Bool.cond_true] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [Bool.not_eq_true] at hcap
    rw [hcap, Bool.cond_false] at hlt ⊢
    have hccap : r.1 < CAPK := by
      by_contra hge
      rw [Nat.ble_eq_true_of_le (not_lt.1 hge)] at hcap
      exact Bool.noConfusion hcap
    -- the cells of the frozen primes
    have hcf : cellsFrom 1 (c0 :: b) = true := by
      have hok2 := hok
      simp only [flipOK, Bool.and_eq_true, Nat.ble_eq] at hok2
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hcells⟩, hfit⟩, _⟩, _⟩, _⟩, _⟩ := hok2
      have h1 : cellsOK ((c0 :: b) ++ [lastC bl]) = true := by
        rw [hbl]
        exact hcells
      have h2 : hiSum ((c0 :: b) ++ [lastC bl]) ≤ DEN := by
        rw [hbl]
        omega
      exact cellsFrom_one_init (c0 :: b) h1 h2
    -- the tree over the frozen part
    unfold flipTreeD at hrdef
    simp only [] at hrdef
    generalize hpdef : cfgJF (Nat.add 12 (Nat.div DEN c0.1))
      (maxN 1 (Nat.sub (Nat.sub DEN (lastC bl).2) (Nat.add c0.2 (hiSum b))))
      (Nat.sub (Nat.succ (Nat.sub DEN (lastC bl).1)) (Nat.add c0.1 (loSum b))) (c0 :: b) (Nat.succ b.length)
      (lomP (c0 :: b) DEN) (c0 :: b) h = p at hrdef
    by_cases hc : (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c0.1 (flipT (lastC bl))) &&
        (frozTestsC (Nat.sub DEN (lastC bl).2) (Nat.add (Nat.sub DEN (lastC bl).1) 1)
          (Nat.add 12 (Nat.div DEN c0.1)) (c0 :: b) (Nat.add c0.1 (loSum b)) (Nat.add c0.2 (hiSum b))
          (Nat.succ b.length) (lomP (c0 :: b) DEN)).okJ (c0 :: b) p.1.1 p.1.2) = true
    swap
    · rw [Bool.not_eq_true] at hc
      rw [hc, Bool.cond_false] at hrdef
      rw [hrdef] at hccap
      exact absurd hccap (lt_irrefl _)
    rw [hc, Bool.cond_true] at hrdef
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
    have hokJ : (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b)
        p.1.1 p.1.2 = true :=
      frozTestsC_okJ (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b) [] p.1.1 p.1.2 hcf
        hc.2
    refine bd_flip_core hok k' hl hβ.symm hc.1.2 hokJ fun s hβl hR' => ?_
    have hR'' : Rules (opsKP (lastC bl) (Nat.succ b.length))
        (frozTestsC (Nat.sub DEN (lastC bl).2) (Nat.add (Nat.sub DEN (lastC bl).1) 1)
          (Nat.add 12 (Nat.div DEN c0.1)) (c0 :: b) (Nat.add c0.1 (loSum b)) (Nat.add c0.2 (hiSum b))
          (Nat.succ b.length) (lomP (c0 :: b) DEN))
        (PF (fun q => frozS q (e1 (lastC bl)) (e2 (lastC bl)) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)) := by
      rw [opsKP_eq]
      exact rules_frozC hcf hR'
    have hk := kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length) _
      (solveD_sound hR'' cfgIF _ (kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length)) (altH := noAltH)
        (fun _ _ _ _ _ hh => absurd hh (lt_irrefl _)) fuel)
      (flipT (lastC bl)) (c0 :: b) true p.1.1 CAPK p.2 (by rw [← hrdef]; exact hccap)
    rw [← hrdef] at hk
    exact hk

/-- **The hinted bound of the main search proves `PR`**: a cost that `altFD` returns below its limit bounds the
term of the box. -/
theorem altFD_sound (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ)
    (hlt : (altFD κ hR fuel maxlen bl par l h).1 < l) : PR bl par (altFD κ hR fuel maxlen bl par l h).1 := by
  unfold altFD at hlt ⊢
  cases par with
  | true => exact absurd hlt (lt_irrefl _)
  | false =>
    intro k' hl
    exact bd_flipCostD κ hR fuel maxlen hlt k' hl

/-! ### The main search -/

omit [SieveCert.IBPar] [IBFits] in
/-- **The nodes of the main tree, a dropped box's cost in one pass, bound the term**, for tests that are
sound. -/
theorem rulesMP {τ : Tests} (hτ : τ.Sound) : Rules opsMP τ PR where
  van := fun _ hv => pr_of_has hτ (has_vanish hv)
  evl := by
    intro bl par cfg _ hI
    cases bl with
    | nil =>
      intro k' h
      simp at h
    | cons x b => exact pr_of_has hτ (has_eval hI)
  drp := by
    intro bl par dc _ hd
    have hd' : drpMP bl par = some dc := hd
    rw [drpMP_eq] at hd'
    exact pr_drop hτ hd'
  alt := fun _ h => absurd h (lt_irrefl _)
  split := pr_split
  buch := fun _ _ hfx hJ hc => pr_buch hτ hfx hJ hc

/-- **The main search led by hints is sound**: the nodes of a tree with the reversal through the largest prime as
the hinted bound; a cost that it returns below its limit bounds the term, whatever the hints and what is read
from them. -/
theorem solveMD_sound {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) :
    RecPH PR (solveD opsMP τ dI dJ (kidsM κ hI) (altFD κ hR fuel maxlen) n) :=
  solveD_sound (rulesMP hτ) dI dJ (kidsM_sound pr_split κ hI)
    (fun bl par l h _ hlt => altFD_sound κ hR fuel maxlen bl par l h hlt) n

/-- **A part of the main search**, as the kernel checks it: if the costs of the cells of the new prime between
`a` and `top`, cut at `cs` and searched by the hints `h` with the limit `K`, sum to at most `c < K`, then the term
of the box of the whole range is at least `−(c/K + o(1))x/(φ(q) log x)` with its sign. -/
theorem pr_of_partD {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool}
    {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP τ dI dJ (kidsM κ hI) (altFD κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : PR ((a, top) :: bl) par c :=
  pr_mono (partD_sound pr_split (solveMD_sound hτ dI dJ κ hI hR fuel maxlen n) top bl par cs a K h
    (lt_of_le_of_lt hk hc)) hk

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of the main search, for any route**: `pr_of_partD` with the route and its exponent as variables. -/
theorem pr_of_partD_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {τ : Tests}
    (hτ : @Tests.Sound Rt τ) (dI : List Cell → ℕ → Cfg × ℕ) (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP τ dI dJ (kidsM κ hI) (@altFD Pr κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : @PR Rt ((a, top) :: bl) par c :=
  @pr_of_partD Rt hRt Pr hPr τ hτ dI dJ κ hI hR fuel maxlen n top bl par cs a c h hk hc

end SieveAd

#print axioms SieveAd.pr_of_partD_at
