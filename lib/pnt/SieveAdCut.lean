/-
# The search led by hints with a cut of any cell of a box at any point is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdCutDefs.lean` has the search led by hints in which a box may be cut at any of its cells,
at any point (`altC`, `solveDS`), and the reversal whose trees are searched that way (`flipTreeDYS` … `altFDYS`).
Here it is sound:

* `pr_splitAt`: **a cut of any cell of a box of the main tree**: the costs of the two boxes add (`bd_split` at the
  cell's index). `pf_splitAt`: the same for a cell of the chain of a box `ch ++ β` over a frozen part
  (`bdF_split`).
* `altC_sound`: a cost that `altC nb altH rec` returns below its limit has the statement, when a cut of one of the
  first `bl.length − nb` cells adds costs, the bound `altH` proves the statement, and `rec` is sound.
  `solveDS_sound`: **the search with cuts of any cell is sound**, by `stepD_sound` at each depth.
* `bd_flipCostDYS`, `altFDYS_sound`: a cost that `flipCostDYS` (`altFDYS`) returns below its limit bounds the term.
* `solveMDYS_sound`, `pr_of_partDYS`: **the main search with cuts of any cell and the hinted bound `altFDYS` is
  sound**; `pr_of_partDYS_at` with the route and its exponent as variables.

The file imports `SieveAdFrozResYTree.lean` and `SieveAdCutDefs.lean`.
-/
import SieveAdFrozResYTree
import SieveAdCutDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K cdiv omKw topK w1K LD)

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

omit [SieveCert.IBPar] [IBFits] in
/-- **A cut of any cell of a box of the main tree**: if the cell at the position `t` is cut at `c` strictly inside
it, the costs of the box with that cell's upper end at `c` and of the box with its lower end at `c` add. -/
theorem pr_splitAt {bl : List Cell} {t c : ℕ} {par : Bool} {c1 c2 : ℕ} (hs : splitOK bl t c = true)
    (hl : PR (setHi bl t c) par c1) (hr : PR (setLo bl t c) par c2) : PR bl par (c1 + c2) := by
  intro k' h
  simp only [splitOK, Bool.and_eq_true, Nat.blt_eq] at hs
  obtain ⟨⟨ht, hlo⟩, hhi⟩ := hs
  have ht' : t < k' + 1 := by omega
  have hget : getC bl t = boxFn bl (k' + 1) h ⟨k' + 1 - 1 - t, by omega⟩ := getC_eq bl (k' + 1) h t ht'
  have hl1 : (setHi bl t c).length = k' + 1 := by simp [setHi, h]
  have hr1 : (setLo bl t c).length = k' + 1 := by simp [setLo, h]
  have el : boxFn (setHi bl t c) (k' + 1) hl1 =
      Function.update (boxFn bl (k' + 1) h) ⟨k' + 1 - 1 - t, by omega⟩
        ((boxFn bl (k' + 1) h ⟨k' + 1 - 1 - t, by omega⟩).1, c) :=
    (boxFn_set bl (k' + 1) h t ht' ((getC bl t).1, c)).trans (by rw [hget])
  have er : boxFn (setLo bl t c) (k' + 1) hr1 =
      Function.update (boxFn bl (k' + 1) h) ⟨k' + 1 - 1 - t, by omega⟩
        (c, (boxFn bl (k' + 1) h ⟨k' + 1 - 1 - t, by omega⟩).2) :=
    (boxFn_set bl (k' + 1) h t ht' (c, (getC bl t).2)).trans (by rw [hget])
  have hL := hl k' hl1
  have hR := hr k' hr1
  rw [el] at hL
  rw [er] at hR
  rw [hget] at hlo hhi
  have key := bd_split (par := par) (boxFn bl (k' + 1) h) ⟨k' + 1 - 1 - t, by omega⟩ (c := c) hlo.le hhi.le hL hR
  have e : ((c1 + c2 : ℕ) : ℝ) / K = (c1 : ℝ) / K + (c2 : ℝ) / K := by
    push_cast; ring
  rw [e]
  exact key

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- A cell of the chain of `ch ++ β`, read at its position in the whole box. -/
theorem getC_append_left (ch β : List Cell) {t : ℕ} (ht : t < ch.length) : getC (ch ++ β) t = getC ch t := by
  unfold getC
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega), List.getD_eq_getElem _ _ ht,
    List.getElem_append_left ht]

omit [SieveCert.IBPar] [IBFits] in
/-- **A cut of a cell of the chain of a box over a frozen part**: for a box `bl = ch ++ β` and a position `t` among
the chain's, the costs of the two boxes that a cut at `c` strictly inside that cell leaves add. -/
theorem pf_splitAt {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {β bl : List Cell} {t c : ℕ} {par : Bool} {c1 c2 : ℕ}
    (ht : t < bl.length - β.length) (hs : splitOK bl t c = true) (hl : PF S R β (setHi bl t c) par c1)
    (hr : PF S R β (setLo bl t c) par c2) : PF S R β bl par (c1 + c2) := by
  intro ch hbl k' h ε hε
  subst hbl
  have htc : t < ch.length := by
    rw [List.length_append] at ht
    omega
  have ht' : t < k' + 1 := by omega
  simp only [splitOK, Bool.and_eq_true, Nat.blt_eq] at hs
  obtain ⟨⟨-, hlo⟩, hhi⟩ := hs
  rw [getC_append_left ch β htc] at hlo hhi
  have e1 : setHi (ch ++ β) t c = setHi ch t c ++ β := by
    unfold setHi
    rw [getC_append_left ch β htc, List.set_append_left _ _ htc]
  have e2 : setLo (ch ++ β) t c = setLo ch t c ++ β := by
    unfold setLo
    rw [getC_append_left ch β htc, List.set_append_left _ _ htc]
  have hl1 : (setHi ch t c).length = k' + 1 := by simp [setHi, h]
  have hr1 : (setLo ch t c).length = k' + 1 := by simp [setLo, h]
  have hL := hl (setHi ch t c) e1 k' hl1 (ε / 2) (by positivity)
  have hR := hr (setLo ch t c) e2 k' hr1 (ε / 2) (by positivity)
  have hget : getC ch t = boxFn ch (k' + 1) h ⟨k' + 1 - 1 - t, by omega⟩ := getC_eq ch (k' + 1) h t ht'
  have el : boxFn (setHi ch t c) (k' + 1) hl1 =
      Function.update (boxFn ch (k' + 1) h) ⟨k' + 1 - 1 - t, by omega⟩
        ((boxFn ch (k' + 1) h ⟨k' + 1 - 1 - t, by omega⟩).1, c) :=
    (boxFn_set ch (k' + 1) h t ht' ((getC ch t).1, c)).trans (by rw [hget])
  have er : boxFn (setLo ch t c) (k' + 1) hr1 =
      Function.update (boxFn ch (k' + 1) h) ⟨k' + 1 - 1 - t, by omega⟩
        (c, (boxFn ch (k' + 1) h ⟨k' + 1 - 1 - t, by omega⟩).2) :=
    (boxFn_set ch (k' + 1) h t ht' (c, (getC ch t).2)).trans (by rw [hget])
  rw [el] at hL
  rw [er] at hR
  rw [hget] at hlo hhi
  have key := bdF_split (S := S) (R := R) (par := par) (boxFn ch (k' + 1) h) ⟨k' + 1 - 1 - t, by omega⟩ (c := c)
    hlo.le hhi.le hL hR
  have e : ((c1 + c2 : ℕ) : ℝ) / K + ε = ((c1 : ℝ) / K + ε / 2) + ((c2 : ℝ) / K + ε / 2) := by
    push_cast; ring
  rw [e]
  exact key

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The cut, or the hinted bound, is sound**: a cost that `altC nb altH rec` returns below its limit has the
statement, when a cut of one of the first `bl.length − nb` cells adds the costs of its two boxes, a cost that
`altH` returns below its limit has the statement, and `rec` is sound. -/
theorem altC_sound {O : Ops} {P : List Cell → Bool → ℕ → Prop} {nb : ℕ}
    (hsp : ∀ {bl : List Cell} {t c : ℕ} {par : Bool} {c1 c2 : ℕ}, t < bl.length - nb → splitOK bl t c = true →
      P (setHi bl t c) par c1 → P (setLo bl t c) par c2 → P bl par (c1 + c2))
    {altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ}
    (haltH : ∀ bl par l h, O.grd bl = true → (altH bl par l h).1 < l → P bl par (altH bl par l h).1)
    {rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ} (hrec : RecPH P rec) (bl : List Cell) (par : Bool) (l h : ℕ)
    (hg : O.grd bl = true) (hh : (altC nb altH rec bl par l h).1 < l) :
    P bl par (altC nb altH rec bl par l h).1 := by
  unfold altC at hh ⊢
  by_cases h0 : Nat.beq (Nat.land h 1) 0 = true
  · rw [h0, Bool.cond_true] at hh ⊢
    exact haltH _ _ _ _ hg hh
  rw [Bool.not_eq_true] at h0
  rw [h0, Bool.cond_false] at hh ⊢
  simp only [] at hh ⊢
  generalize Nat.land (Nat.div h 2) 15 = t at hh ⊢
  generalize Nat.land (Nat.div h 32) 1099511627775 = c at hh ⊢
  generalize Nat.div h 35184372088832 = h' at hh ⊢
  by_cases hc : (Nat.blt t (Nat.sub (lenR bl) nb) && splitOK bl t c) = true
  swap
  · rw [Bool.not_eq_true] at hc
    rw [hc, Bool.cond_false] at hh
    exact absurd hh (lt_irrefl _)
  rw [hc, Bool.cond_true] at hh ⊢
  simp only [Bool.and_eq_true, Nat.blt_eq] at hc
  have ht : t < bl.length - nb := by
    have h1 := hc.1
    rw [lenR_eq] at h1
    exact h1
  have hr := hrec (setHi bl t c) par l h'
  generalize rec (setHi bl t c) par l h' = r at hh hr ⊢
  by_cases hl : Nat.ble l r.1 = true
  · rw [hl, Bool.cond_true] at hh
    exact absurd hh (lt_irrefl _)
  rw [Bool.not_eq_true] at hl
  rw [hl, Bool.cond_false] at hh ⊢
  have hl' : ¬ l ≤ r.1 := by
    rw [← Nat.ble_eq, hl]
    simp
  have hh' : r.1 + (rec (setLo bl t c) par (l - r.1) r.2).1 < l := hh
  have h2' : (rec (setLo bl t c) par (l - r.1) r.2).1 < l - r.1 := by omega
  exact hsp ht hc.2 (hr (by omega)) (hrec _ _ _ _ h2')

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The search led by hints with cuts of any cell is sound**: a cost that it returns below its limit has the
statement that its nodes, its cuts and its hinted bound prove, whatever the hints and what is read from them. -/
theorem solveDS_sound {O : Ops} {τ : Tests} {P : List Cell → Bool → ℕ → Prop} (R : Rules O τ P) {nb : ℕ}
    (hsp : ∀ {bl : List Cell} {t c : ℕ} {par : Bool} {c1 c2 : ℕ}, t < bl.length - nb → splitOK bl t c = true →
      P (setHi bl t c) par c1 → P (setLo bl t c) par c2 → P bl par (c1 + c2))
    (dI : List Cell → ℕ → Cfg × ℕ) (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    {kd : (List Cell → Bool → ℕ → ℕ → ℕ × ℕ) → ℕ → List Cell → Bool → ℕ → ℕ → ℕ → ℕ × ℕ} (hkd : KidsP P kd)
    {altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ}
    (haltH : ∀ bl par l h, O.grd bl = true → (altH bl par l h).1 < l → P bl par (altH bl par l h).1) :
    ∀ n : ℕ, RecPH P (solveDS O τ dI dJ kd nb altH n)
  | 0 => fun _ _ _ _ h => absurd h (lt_irrefl _)
  | n + 1 =>
    stepD_sound R hkd (altC_sound hsp haltH (solveDS_sound R hsp dI dJ hkd haltH n))
      (solveDS_sound R hsp dI dJ hkd haltH n)

/-- **The cost of a reversal through the largest prime, its tree searched with cuts of any cell of the chain,
bounds the term**, for a box of the sign `−` (`pos = false`) or `+`: `bd_flipCostDY` for `flipCostDYS`. -/
theorem bd_flipCostDYS (κ hR fuel maxlen : ℕ) (pos : Bool) {bl : List Cell} {lim h : ℕ}
    (hlt : (flipCostDYS κ hR fuel maxlen pos bl lim h).1 < lim) (k' : ℕ) (hl : bl.length = k' + 1) :
    Bd pos (((flipCostDYS κ hR fuel maxlen pos bl lim h).1 : ℝ) / K) (boxFn bl (k' + 1) hl) := by
  unfold flipCostDYS at hlt ⊢
  rw [lastP_eq, initP_eq] at hlt ⊢
  revert hlt
  cases hβ : initC bl with
  | nil => exact fun hlt => absurd hlt (lt_irrefl _)
  | cons c0 b =>
    intro hlt
    simp only [] at hlt ⊢
    rw [tailP_eq] at hlt ⊢
    simp only [Nat.zero_add, Nat.one_mul] at hlt ⊢
    unfold flipCostBYS at hlt ⊢
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
    obtain ⟨r, hrdef⟩ : ∃ r, r = flipTreeDYS κ hR fuel pos (lastC bl) c0 b (Nat.add c0.1 (loSum b))
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
    -- the ends of the slab are at most `DEN`
    have hctx : 3 ≤ (lastC bl).1 ∧ (lastC bl).1 < (lastC bl).2 := by
      have hok2 := hok
      simp only [flipOK, Bool.and_eq_true, Nat.ble_eq] at hok2
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hcells⟩, _⟩, _⟩, h3⟩, _⟩, _⟩ := hok2
      have hmem : lastC bl ∈ bl := by
        have h := List.mem_append_right (c0 :: b) (List.mem_singleton_self (lastC bl))
        rwa [hbl] at h
      exact ⟨h3, ((cellsOK_iff bl).1 hcells _ hmem).2⟩
    have hDEN : 1 ≤ DEN := SieveCert.DEN_pos
    have he₁' : cond pos (e1 (lastC bl) + 1) (e1 (lastC bl)) ≤ DEN := by
      have h1 : e1 (lastC bl) + 1 ≤ DEN := by
        unfold e1
        omega
      cases pos
      · exact (Nat.le_succ _).trans h1
      · exact h1
    have he₂' : cond pos (e2 (lastC bl) - 1) (e2 (lastC bl)) ≤ DEN := by
      have h1 : e2 (lastC bl) ≤ DEN := by
        unfold e2
        omega
      cases pos
      · exact h1
      · exact (Nat.sub_le _ _).trans h1
    -- the tree over the frozen part
    unfold flipTreeDYS at hrdef
    simp only [] at hrdef
    generalize hpdef : cfgJF (Nat.add 12 (Nat.div DEN c0.1))
      (maxN 1 (Nat.sub (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
        (Nat.add c0.2 (hiSum b))))
      (Nat.sub (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
        (Nat.add c0.1 (loSum b))) (c0 :: b) (Nat.succ b.length)
      (lomP (c0 :: b) DEN) (c0 :: b) h = p at hrdef
    by_cases hc : (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c0.1 (flipT (lastC bl))) &&
        (frozResTestsY (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
          (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
          (Nat.add 12 (Nat.div DEN c0.1)) (c0 :: b) (Nat.add c0.1 (loSum b)) (Nat.add c0.2 (hiSum b))
          (Nat.succ b.length) (lomP (c0 :: b) DEN)).okJ (c0 :: b) p.1.1 p.1.2) = true
    swap
    · rw [Bool.not_eq_true] at hc
      rw [hc, Bool.cond_false] at hrdef
      rw [hrdef] at hccap
      exact absurd hccap (lt_irrefl _)
    rw [hc, Bool.cond_true] at hrdef
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
    have hokJ : (frozTests (cond pos (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).2))
        (cond pos (DEN - (lastC bl).1) (DEN - (lastC bl).1 + 1)) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b)
        p.1.1 p.1.2 = true :=
      frozTestsC_okJ (cond pos (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).2))
        (cond pos (DEN - (lastC bl).1) (DEN - (lastC bl).1 + 1)) (12 + DEN / c0.1) (c0 :: b) [] p.1.1 p.1.2 hcf
        hc.2
    refine bd_flip_coreB pos hok k' hl hβ.symm hc.1.2 hokJ fun s hβl hR' => ?_
    have hR'' : Rules (opsKP (lastC bl) (Nat.succ b.length))
        (frozResTestsY (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
          (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
          (Nat.add 12 (Nat.div DEN c0.1)) (c0 :: b) (Nat.add c0.1 (loSum b)) (Nat.add c0.2 (hiSum b))
          (Nat.succ b.length) (lomP (c0 :: b) DEN))
        (PF (fun q => frozS q (cond pos (e1 (lastC bl) + 1) (e1 (lastC bl)))
          (cond pos (e2 (lastC bl) - 1) (e2 (lastC bl))) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)) := by
      rw [opsKP_eq]
      refine rules_frozResY hβl he₁' he₂' ?_ ?_ hcf hR'
      · cases pos <;> rfl
      · cases pos
        · rfl
        · show DEN - (lastC bl).1 = DEN - (lastC bl).1 + 1 - 1
          omega
    have hk := kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length) _
      (solveDS_sound hR'' (nb := Nat.succ b.length) (fun ht hs hl hr => pf_splitAt ht hs hl hr) cfgIFY _
        (kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length)) (altH := noAltH)
        (fun _ _ _ _ _ hh => absurd hh (lt_irrefl _)) fuel)
      (flipT (lastC bl)) (c0 :: b) (!pos) p.1.1 CAPK p.2 (by rw [← hrdef]; exact hccap)
    rw [← hrdef] at hk
    exact hk

/-- **The reversal whose trees are searched with cuts of any cell proves `PR`**: a cost that `altFDYS` returns
below its limit bounds the term of the box, of either sign. -/
theorem altFDYS_sound (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ)
    (hlt : (altFDYS κ hR fuel maxlen bl par l h).1 < l) : PR bl par (altFDYS κ hR fuel maxlen bl par l h).1 := by
  unfold altFDYS at hlt ⊢
  intro k' hl
  exact bd_flipCostDYS κ hR fuel maxlen par hlt k' hl

/-- **The main search led by hints with cuts of any cell is sound**: `solveDS` on the main tree's boxes, where
every cell may be cut (`nb = 0`), with the hinted bound `altFDYS`. -/
theorem solveMDYS_sound {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) :
    RecPH PR (solveDS opsMP τ dI dJ (kidsM κ hI) 0 (altFDYS κ hR fuel maxlen) n) :=
  solveDS_sound (rulesMP hτ) (fun _ hs hl hr => pr_splitAt hs hl hr) dI dJ (kidsM_sound pr_split κ hI)
    (fun bl par l h _ hlt => altFDYS_sound κ hR fuel maxlen bl par l h hlt) n

/-- **A part of the main search with cuts of any cell**, as the kernel checks it: `pr_of_partDY` for `solveDS`
and `altFDYS`. -/
theorem pr_of_partDYS {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool}
    {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveDS opsMP τ dI dJ (kidsM κ hI) 0 (altFDYS κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : PR ((a, top) :: bl) par c :=
  pr_mono (partD_sound pr_split (solveMDYS_sound hτ dI dJ κ hI hR fuel maxlen n) top bl par cs a K h
    (lt_of_le_of_lt hk hc)) hk

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of the main search with cuts of any cell, for any route**: `pr_of_partDYS` with the route and its
exponent as variables. -/
theorem pr_of_partDYS_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {τ : Tests}
    (hτ : @Tests.Sound Rt τ) (dI : List Cell → ℕ → Cfg × ℕ) (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveDS opsMP τ dI dJ (kidsM κ hI) 0 (@altFDYS Pr κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : @PR Rt ((a, top) :: bl) par c :=
  @pr_of_partDYS Rt hRt Pr hPr τ hτ dI dJ κ hI hR fuel maxlen n top bl par cs a c h hk hc

end SieveAd

#print axioms SieveAd.pr_of_partDYS_at
