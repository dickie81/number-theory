/-
# The search with the window's test at the two corners and the lines named by the hint is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveAdResYHDefs.lean` has the search with the window's test at the two corners of a box and the resonant window's
test with the lines named by the hint (`SieveResTest.resXH`). Its proofs are those of `SieveAdResY.lean` and
`SieveAdFrozResYTree.lean`, with `SieveAdResH.lean`'s soundness of the tests with the named lines in place of that of
the tests with `resX`; the names end in `YH`:

* `resTestsFYH_sound`: **the main tree's tests are sound**: an evaluation of kind `4` by `evI_resY`, the others by
  `resTestsFCH_sound`.
* `rules_frozResYH`: the nodes of a tree over a frozen part: `rules_frozResCH`'s, and an evaluation of kind `4` by
  `evIF_froz_resTY`.
* `bd_flipCostDYH`, `altFDYH_sound`, `solveMDYH_sound`, `pr_of_partDYH`, `pr_of_partDYH_at`: **the main search with
  the hinted bound `altFDYH` is sound**; `pr_of_partDYCH_at`, with the tests `resTestsFYH` and the configurations
  `cfgIMYH`, `cfgJM`: what a certificate's parts use.

The file imports `SieveAdResY.lean`, `SieveAdFrozResYTree.lean`, `SieveAdResH.lean` and `SieveAdResYHDefs.lean`.
-/
import SieveAdResY
import SieveAdFrozResYTree
import SieveAdResH
import SieveAdResYHDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K cdiv omKw topK w1K LD)

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

/-- **The tests with the window's test at the two corners and the lines named by the hint are sound.** -/
theorem resTestsFYH_sound : (resTestsFYH).Sound := by
  refine ⟨fun bl cfg k' h hok => ?_, fun bl f cfg k h hok => resTestsFCH_sound.soundJ bl f cfg k h hok⟩
  change cond (Nat.beq cfg.kind 4) (chkIRY bl cfg.sr cfg.s1) (resTestsFCH.okI bl cfg) = true at hok
  by_cases h4 : cfg.kind = 4
  · rw [show Nat.beq cfg.kind 4 = true from Nat.beq_eq_true_eq _ _ ▸ h4, Bool.cond_true] at hok
    exact evI_resY bl k' h _ _ hok
  · rw [show Nat.beq cfg.kind 4 = false from Bool.eq_false_iff.mpr fun h' => h4 (Nat.eq_of_beq_eq_true h'),
      Bool.cond_false] at hok
    exact resTestsFCH_sound.soundI bl cfg k' h hok


/-- **The nodes of a tree over a frozen part, with the window's test at the two corners and the lines named by the
hint**: those of `rules_frozResCH`, and an evaluation of kind `4` (`chkIRFY` on the box `ch ++ β`) evaluates the term of
the chain `ch` over the frozen part (`evIF_froz_resTY`), for a slab whose ends are at most `DEN` and are the tests'
`e₁, e₂`. -/
theorem rules_frozResYH {O : Ops} {e₁ e₂ Kb : ℕ} {β : List Cell} {s : ℕ} (hβl : β.length = s + 1)
    {e₁' e₂' : ℕ} (he₁ : e₁' ≤ DEN) (he₂ : e₂' ≤ DEN) (hee₁ : e₁ = e₁') (hee₂ : e₂ = e₂')
    (hβ : cellsFrom 1 β = true)
    (h : Rules O (frozTests e₁ e₂ Kb β) (PF (fun q => frozS q e₁' e₂' (boxFn β (s + 1) hβl)) frozR β)) :
    Rules O (frozResTestsYH e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN))
      (PF (fun q => frozS q e₁' e₂' (boxFn β (s + 1) hβl)) frozR β) where
  van := h.van
  evl := by
    intro bl par cfg hg hI
    change cond (Nat.beq cfg.kind 4) (chkIRFY e₁ e₂ β bl cfg.sr cfg.s1)
      ((frozResTestsCH e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN)).okI bl cfg) = true at hI
    by_cases h4 : cfg.kind = 4
    · rw [show Nat.beq cfg.kind 4 = true from Nat.beq_eq_true_eq _ _ ▸ h4, Bool.cond_true] at hI
      intro ch hbl k' hch ε hε
      subst hbl hee₁ hee₂
      have hev := evIF_froz_resTY β hβl he₁ he₂ ch k' hch cfg.sr _ hI
      refine bdF_mono (bdF_eval hev) ?_
      simp only [Nat.cast_zero, zero_div, zero_add]
      exact hε.le
    · rw [show Nat.beq cfg.kind 4 = false from Bool.eq_false_iff.mpr fun h' => h4 (Nat.eq_of_beq_eq_true h'),
        Bool.cond_false] at hI
      exact (rules_frozResCH hβl he₁ he₂ hee₁ hee₂ hβ h).evl hg hI
  drp := h.drp
  alt := h.alt
  split := h.split
  buch := (rules_frozC hβ h).buch

/-- **The cost of a reversal through the largest prime, its tree searched by hints with the window's test at
the two corners too, bounds the term**, for a box of the sign `−` (`pos = false`) or `+`: `bd_flipCostD` for
`flipCostDYH`. -/
theorem bd_flipCostDYH (κ hR fuel maxlen : ℕ) (pos : Bool) {bl : List Cell} {lim h : ℕ}
    (hlt : (flipCostDYH κ hR fuel maxlen pos bl lim h).1 < lim) (k' : ℕ) (hl : bl.length = k' + 1) :
    Bd pos (((flipCostDYH κ hR fuel maxlen pos bl lim h).1 : ℝ) / K) (boxFn bl (k' + 1) hl) := by
  unfold flipCostDYH at hlt ⊢
  rw [lastP_eq, initP_eq] at hlt ⊢
  revert hlt
  cases hβ : initC bl with
  | nil => exact fun hlt => absurd hlt (lt_irrefl _)
  | cons c0 b =>
    intro hlt
    simp only [] at hlt ⊢
    rw [tailP_eq] at hlt ⊢
    simp only [Nat.zero_add, Nat.one_mul] at hlt ⊢
    unfold flipCostBYH at hlt ⊢
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
    obtain ⟨r, hrdef⟩ : ∃ r, r = flipTreeDYH κ hR fuel pos (lastC bl) c0 b (Nat.add c0.1 (loSum b))
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
    unfold flipTreeDYH at hrdef
    simp only [] at hrdef
    generalize hpdef : cfgJF (Nat.add 12 (Nat.div DEN c0.1))
      (maxN 1 (Nat.sub (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
        (Nat.add c0.2 (hiSum b))))
      (Nat.sub (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
        (Nat.add c0.1 (loSum b))) (c0 :: b) (Nat.succ b.length)
      (lomP (c0 :: b) DEN) (c0 :: b) h = p at hrdef
    by_cases hc : (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c0.1 (flipT (lastC bl))) &&
        (frozResTestsYH (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
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
        (frozResTestsYH (cond pos (Nat.add (Nat.sub DEN (lastC bl).2) 1) (Nat.sub DEN (lastC bl).2))
          (cond pos (Nat.sub DEN (lastC bl).1) (Nat.add (Nat.sub DEN (lastC bl).1) 1))
          (Nat.add 12 (Nat.div DEN c0.1)) (c0 :: b) (Nat.add c0.1 (loSum b)) (Nat.add c0.2 (hiSum b))
          (Nat.succ b.length) (lomP (c0 :: b) DEN))
        (PF (fun q => frozS q (cond pos (e1 (lastC bl) + 1) (e1 (lastC bl)))
          (cond pos (e2 (lastC bl) - 1) (e2 (lastC bl))) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)) := by
      rw [opsKP_eq]
      refine rules_frozResYH hβl he₁' he₂' ?_ ?_ hcf hR'
      · cases pos <;> rfl
      · cases pos
        · rfl
        · show DEN - (lastC bl).1 = DEN - (lastC bl).1 + 1 - 1
          omega
    have hk := kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length) _
      (solveD_sound hR'' cfgIFYH _ (kidsF_sound hR''.split κ hR (lastC bl) (Nat.succ b.length)) (altH := noAltH)
        (fun _ _ _ _ _ hh => absurd hh (lt_irrefl _)) fuel)
      (flipT (lastC bl)) (c0 :: b) (!pos) p.1.1 CAPK p.2 (by rw [← hrdef]; exact hccap)
    rw [← hrdef] at hk
    exact hk

/-- **The hinted bound with the window's test at the two corners and the lines named by the hint over the frozen parts
proves `PR`**: a cost that `altFDYH` returns below its limit bounds the term of the box, of either sign. -/
theorem altFDYH_sound (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ)
    (hlt : (altFDYH κ hR fuel maxlen bl par l h).1 < l) : PR bl par (altFDYH κ hR fuel maxlen bl par l h).1 := by
  unfold altFDYH at hlt ⊢
  intro k' hl
  exact bd_flipCostDYH κ hR fuel maxlen par hlt k' hl

/-- **The main search led by hints, with the window's test at the two corners and the lines named by the hint over the
frozen parts, is sound**: `solveMD_sound` with the hinted bound `altFDYH`. -/
theorem solveMDYH_sound {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) :
    RecPH PR (solveD opsMP τ dI dJ (kidsM κ hI) (altFDYH κ hR fuel maxlen) n) :=
  solveD_sound (rulesMP hτ) dI dJ (kidsM_sound pr_split κ hI)
    (fun bl par l h _ hlt => altFDYH_sound κ hR fuel maxlen bl par l h hlt) n

/-- **A part of the main search, with the window's test at the two corners and the lines named by the hint over the
frozen parts**, as the kernel checks it: `pr_of_partD` with the hinted bound `altFDYH`. -/
theorem pr_of_partDYH {τ : Tests} (hτ : τ.Sound) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ) (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool}
    {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP τ dI dJ (kidsM κ hI) (altFDYH κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : PR ((a, top) :: bl) par c :=
  pr_mono (partD_sound pr_split (solveMDYH_sound hτ dI dJ κ hI hR fuel maxlen n) top bl par cs a K h
    (lt_of_le_of_lt hk hc)) hk

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of the main search with the window's test at the two corners and the lines named by the hint over the
frozen parts, for any route**: `pr_of_partDYH` with the route and its exponent as variables. -/
theorem pr_of_partDYH_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {τ : Tests}
    (hτ : @Tests.Sound Rt τ) (dI : List Cell → ℕ → Cfg × ℕ) (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP τ dI dJ (kidsM κ hI) (@altFDYH Pr κ hR fuel maxlen) n) top bl par cs a K h).1 ≤ c)
    (hc : c < K) : @PR Rt ((a, top) :: bl) par c :=
  @pr_of_partDYH Rt hRt Pr hPr τ hτ dI dJ κ hI hR fuel maxlen n top bl par cs a c h hk hc


omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of the search with the window's test at the two corners and the lines named by the hint bounds its
term**, for any route: `pr_of_partDYH_at` with the tests `resTestsFYH` (`resTestsFYH_sound`) and the configurations
read by `cfgIMYH` and `cfgJM`, the search of a certificate written with them (`tools/linnik/hint_cert.py --ycorner
--hl`). -/
theorem pr_of_partDYCH_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr)
    (κ hI hR fuel maxlen n : ℕ) {top : ℕ} {bl : List Cell} {par : Bool} {cs : List ℕ} {a c h : ℕ}
    (hk : (partD (solveD opsMP (@resTestsFYH Pr) cfgIMYH (@cfgJM Pr) (kidsM κ hI) (@altFDYH Pr κ hR fuel maxlen) n)
      top bl par cs a K h).1 ≤ c)
    (hc : c < K) : @PR Rt ((a, top) :: bl) par c :=
  pr_of_partDYH_at Rt hRt Pr hPr (@resTestsFYH_sound Rt hRt Pr hPr) cfgIMYH (@cfgJM Pr) κ hI hR fuel maxlen n hk hc

end SieveAd

#print axioms SieveAd.resTestsFYH_sound
#print axioms SieveAd.pr_of_partDYH_at
#print axioms SieveAd.pr_of_partDYCH_at
