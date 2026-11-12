/-
# The search with the reversal of a box through its largest prime is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFlipDefs.lean` has, without Mathlib, the cost `flipCost` of the reversal of a box of the
sign `−` through its largest prime and the nodes `opsF` of the search that takes it as one more bound. Here that
cost bounds the term, so the search is sound.

* `initC_append_lastC`, `boxFn_append_singleton`, `boxFn_zero_lastC`: a box is its largest prime's cell after the
  rest, and as a function of the prime's index it is that cell before the rest's.
* `shareLe_list`: the share of a box of cells with `0 < lo < hi` and upper ends of sum at most `DEN` is at most
  `dropCost/K`. `bd_of_eps`: a bound at `C + εW` for every `ε > 0` is a bound at `C`.
* `bd_flip_core`: **the reversal from the bound of a tree**: for a box that passes `flipOK`, a floor at which
  `frozTests` evaluates the terms of the frozen part and a cost `c` of the cells of the chain's first prime, for
  any search whose nodes prove `PF`, give `Bd false` at `⌈(c·(h₁·D₀ + E) + bdK·E)/(DEN·K)⌉/K`. It is
  `bd_flip_neg` with `frozTests_sound` and the weights of the frozen part and of its two ends from the shares of
  three boxes (`froz_weight_le`).
* `bd_flipCost`: **the cost of a reversal bounds the term**: a cost that `flipCost` returns below its limit gives
  `Bd false (cost/K)`: `bd_flip_core` with the tree's bound from `solveG_sound`.
* `rulesF`, `solveF2_sound`, `pr_of_kidsF`: the nodes `opsF` bound the term, the search with them is sound, and a
  part of it as the kernel checks it; `pr_of_kidsF_at` with the route and its exponent as variables.

The file imports `SieveAdFrozTests.lean`, `SieveAdFlipSum.lean`, `SieveAdFlipDefs.lean` and
`SieveAdRevSearch.lean`.
-/
import SieveAdFrozTests
import SieveAdFlipSum
import SieveAdFlipDefs
import SieveAdRevSearch

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos' cdiv)

/-! ### The largest prime's cell and the rest -/

/-- A box is the rest of its primes and then its largest prime's cell. -/
theorem initC_append_lastC : ∀ {bl : List Cell}, bl ≠ [] → initC bl ++ [lastC bl] = bl
  | [], h => absurd rfl h
  | [_], _ => rfl
  | x :: c :: b, _ => by
    show x :: (initC (c :: b) ++ [lastC (c :: b)]) = x :: c :: b
    rw [initC_append_lastC (List.cons_ne_nil c b)]

/-- The cell of the first index is the last of the list. -/
theorem boxFn_zero_lastC : ∀ (bl : List Cell) (m : ℕ) (h : bl.length = m + 1), boxFn bl (m + 1) h 0 = lastC bl
  | [], m, h => by simp at h
  | [c], m, h => by
    have hm : m = 0 := by simpa using h.symm
    subst hm
    rfl
  | x :: c :: b, m, h => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at h; omega⟩
    have hcb : (c :: b).length = m' + 1 := by simpa using h
    have e := boxFn_cons x (c :: b) (m' + 1) hcb
    have e0 : boxFn (x :: c :: b) (m' + 1 + 1) h 0 = boxFn (c :: b) (m' + 1) hcb 0 := by
      rw [e]
      exact Fin.snoc_castSucc (α := fun _ => Cell) x (boxFn (c :: b) (m' + 1) hcb) 0
    rw [e0]
    exact boxFn_zero_lastC (c :: b) m' hcb

/-- The cell of the last index is the first of the list. -/
theorem boxFn_last_head (c : Cell) (b : List Cell) (s : ℕ) (h : (c :: b).length = s + 1) :
    boxFn (c :: b) (s + 1) h (Fin.last s) = c := by
  simp [boxFn]

/-- A box with one more prime, the largest: as a function of the prime's index, its cell before the rest's. -/
theorem boxFn_append_singleton (β : List Cell) (ctx : Cell) (s : ℕ) (hβ : β.length = s + 1)
    (h : (β ++ [ctx]).length = s + 1 + 1) :
    boxFn (β ++ [ctx]) (s + 1 + 1) h = Fin.cons (α := fun _ => Cell) ctx (boxFn β (s + 1) hβ) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [boxFn, Fin.cons_zero, Fin.val_zero]
    rw [List.getElem_append_right (by omega)]
    simp [hβ]
  | succ j =>
    simp only [boxFn, Fin.cons_succ, Fin.val_succ]
    have hj := j.2
    rw [List.getElem_append_left (by omega)]
    congr 1
    omega

theorem minN_le (a b : ℕ) : minN a b ≤ a ∧ minN a b ≤ b := by
  unfold minN
  cases h : Nat.ble a b
  · simp only [Bool.cond_false]
    have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; exact Bool.noConfusion h
    omega
  · simp only [Bool.cond_true]
    exact ⟨le_refl a, Nat.le_of_ble_eq_true h⟩

variable [Route]

/-- **The share of a box of cells.** For cells with `0 < lo < hi` whose upper ends sum to at most `DEN`, the share
of the box is at most `dropCost/K`. -/
theorem shareLe_list [RouteOK] (bl : List Cell) (m : ℕ) (h : bl.length = m + 1) (hok : cellsOK bl = true)
    (hfit : hiSum bl ≤ DEN) : ShareLe (boxFn bl (m + 1) h) ((dropCost bl : ℝ) / K) := by
  have hc := (cellsOK_iff bl).1 hok
  refine shareLe_of_box _ (fun i => (hc _ (boxFn_mem bl _ h i)).1) (fun i => (hc _ (boxFn_mem bl _ h i)).2.le) ?_
    (dropCost_ge bl m h hok)
  rw [sum_boxFn (fun c => c.2) bl (m + 1) h, ← hiSum_eq]
  exact hfit

/-- A bound at `C + εW`, `W ≥ 0`, for every `ε > 0` is a bound at `C`. -/
theorem bd_of_eps [RouteOK] {par : Bool} {C W : ℝ} (hW : 0 ≤ W) {k' : ℕ} {bx : Fin (k' + 1) → Cell}
    (h : ∀ ε : ℝ, 0 < ε → Bd par (C + ε * W) bx) : Bd par C bx := by
  intro η hη
  have hε : 0 < η / (2 * (W + 1)) := by positivity
  filter_upwards [h _ hε (η / 2) (by positivity), big_ev] with q hq hbig a ha
  refine le_trans ?_ (hq a ha)
  have hX := Xq_pos hbig
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have h1 : η / (2 * (W + 1)) * W ≤ η / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hX.le) hφ

variable [RouteOK] [SieveCert.IBPar] [IBFits]

/-! ### The cost of a reversal bounds the term -/

/-- **The reversal through the largest prime, from the bound of a tree.** For a box `bl` that passes `flipOK`,
with `c₀ :: b` its cells but the largest prime's: if the tests `frozTests` evaluate the terms of the frozen part at
a floor `f ≤ min(lo_s, t)`, and the cells of the chain's first prime from `f` to the level `t` cost `c` over the
frozen part (for any search whose nodes prove `PF`), then the term of the box is at most
`(⌈(c·(h₁·D₀ + E) + bdK·E)/(DEN·K)⌉/K + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set. -/
theorem bd_flip_core {maxlen : ℕ} {bl : List Cell} (hok : flipOK maxlen bl = true) (k' : ℕ)
    (hl : bl.length = k' + 1) {c0 : Cell} {b : List Cell} (hβdef : c0 :: b = initC bl) {f c : ℕ} {cfg : Cfg}
    (hfle : f ≤ minN c0.1 (flipT (lastC bl)))
    (hokJ : (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b) f
      cfg = true)
    (htree : ∀ (s : ℕ) (hβl : (c0 :: b).length = s + 1),
      Rules (opsK (lastC bl) (c0 :: b).length)
          (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b))
          (PF (fun q => frozS q (e1 (lastC bl)) (e2 (lastC bl)) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)) →
        PF (fun q => frozS q (e1 (lastC bl)) (e2 (lastC bl)) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)
          ((f, flipT (lastC bl)) :: c0 :: b) true c) :
    Bd false
      (((cdiv (c * ((lastC bl).2 * dropCost bl +
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) +
        bdK (lastC bl) (flipT (lastC bl)) *
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) (DEN * K) : ℕ) :
          ℝ) / K)
      (boxFn bl (k' + 1) hl) := by
  simp only [flipOK, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h2, hmax⟩, hmax11⟩, hcells⟩, hfit⟩, hsep⟩, hl3⟩, htl⟩, htD⟩ := hok
  have hD := DEN_pos'
  have hK := K_pos'
  have hne : bl ≠ [] := by
    intro h0
    rw [h0] at h2
    simp at h2
  have hbl : (c0 :: b) ++ [lastC bl] = bl := by
    rw [hβdef]
    exact initC_append_lastC hne
  rw [← hβdef] at hsep
  generalize hctxdef : lastC bl = ctx at hl3 htl htD hsep hfle hokJ htree hbl ⊢
  obtain ⟨s, rfl⟩ : ∃ s, k' = s + 1 := ⟨k' - 1, by omega⟩
  have hβl : (c0 :: b).length = s + 1 := by
    have := congrArg List.length hbl
    simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
    omega
  generalize htdef : flipT ctx = t at htl htD hfle htree ⊢
  have htdef' : t = flipT ctx := htdef.symm
  -- the cells
  have hc := (cellsOK_iff bl).1 hcells
  have hctxm : ctx ∈ bl := by rw [← hbl]; simp
  obtain ⟨hl0, hlh⟩ := hc ctx hctxm
  have hfit' : hiSum (c0 :: b) + ctx.2 + 2 ≤ DEN := by
    rw [← hbl, hiSum_eq, List.map_append, List.sum_append, ← hiSum_eq] at hfit
    simpa using hfit
  have hhD : ctx.2 ≤ DEN := by omega
  have ht2 : ctx.2 ≤ 2 * t := by rw [htdef']; unfold flipT; omega
  have ht0 : 0 < t := by omega
  obtain ⟨βx, hβx⟩ : ∃ βx : Fin (s + 1) → Cell, βx = boxFn (c0 :: b) (s + 1) hβl := ⟨_, rfl⟩
  have hβ0 : (βx 0).2 + 1 ≤ ctx.1 := by
    rw [hβx, boxFn_zero_lastC]
    exact hsep
  have hc0 : 0 < c0.1 ∧ c0.1 < c0.2 := hc c0 (by rw [← hbl]; simp)
  generalize hEdef : (ctx.2 + 1) * dropCost ((c0 :: b) ++ [(ctx.2 - 1, ctx.2 + 1)]) +
      (ctx.1 + 1) * dropCost ((c0 :: b) ++ [(ctx.1 - 1, ctx.1 + 1)]) = E
  have hEdef' : E = (ctx.2 + 1) * dropCost ((c0 :: b) ++ [(ctx.2 - 1, ctx.2 + 1)]) +
      (ctx.1 + 1) * dropCost ((c0 :: b) ++ [(ctx.1 - 1, ctx.1 + 1)]) := hEdef.symm
  generalize hτdef : frozTests (DEN - ctx.2) (DEN - ctx.1 + 1) (12 + DEN / c0.1) (c0 :: b) = τ at hokJ htree
  have hτdef' : τ = frozTests (DEN - ctx.2) (DEN - ctx.1 + 1) (12 + DEN / c0.1) (c0 :: b) := hτdef.symm
  have hft : f ≤ t := hfle.trans (minN_le c0.1 t).2
  have hctx' : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN := ⟨hl0, hlh.le, hhD⟩
  have he : DEN - ctx.2 ≤ DEN - ctx.1 + 1 := by omega
  have he₂ : DEN - ctx.1 + 1 ≤ DEN := by omega
  have hT : DEN + 1 ≤ (DEN / c0.1 + 1) * (boxFn (c0 :: b) (s + 1) hβl (Fin.last s)).1 := by
    rw [boxFn_last_head]
    have := Nat.lt_mul_div_succ DEN hc0.1
    rw [Nat.mul_comm] at this
    omega
  have hτs : SoundF τ (fun q => frozS q (e1 ctx) (e2 ctx) βx) frozR (c0 :: b) := by
    rw [hτdef', hβx]
    exact frozTests_sound (c0 :: b) hβl he he₂ hT (le_refl _)
  have hS := inSlab_frozS ctx βx
  have hk := htree s hβl (by rw [hβx] at hS hτs; exact frozRules hctx' hS hτs)
  rw [← hβx] at hk
  have hJ : EvJF (fun q => frozS q (e1 ctx) (e2 ctx) βx) frozR f (boxFn [] 0 rfl) :=
    hτs.soundJ [] f cfg 0 rfl (by simp only [List.length_nil, hβl]; omega) hokJ
  -- the weights
  have hbl1 : ((c0 :: b) ++ [(ctx.2 - 1, ctx.2 + 1)]).length = s + 1 + 1 := by
    simp only [List.length_append, hβl, List.length_cons, List.length_nil]
  have hbl2 : ((c0 :: b) ++ [(ctx.1 - 1, ctx.1 + 1)]).length = s + 1 + 1 := by
    simp only [List.length_append, hβl, List.length_cons, List.length_nil]
  have hcβ : ∀ c' ∈ c0 :: b, 0 < c'.1 ∧ c'.1 < c'.2 := fun c' hc' => hc c' (by rw [← hbl]; exact List.mem_append_left _ hc')
  have hcells1 : cellsOK ((c0 :: b) ++ [(ctx.2 - 1, ctx.2 + 1)]) = true := by
    rw [cellsOK_iff]
    intro c' hc'
    rcases List.mem_append.1 hc' with h' | h'
    · exact hcβ c' h'
    · simp only [List.mem_singleton] at h'
      subst h'
      exact ⟨by show 0 < ctx.2 - 1; omega, by show ctx.2 - 1 < ctx.2 + 1; omega⟩
  have hcells2 : cellsOK ((c0 :: b) ++ [(ctx.1 - 1, ctx.1 + 1)]) = true := by
    rw [cellsOK_iff]
    intro c' hc'
    rcases List.mem_append.1 hc' with h' | h'
    · exact hcβ c' h'
    · simp only [List.mem_singleton] at h'
      subst h'
      exact ⟨by show 0 < ctx.1 - 1; omega, by show ctx.1 - 1 < ctx.1 + 1; omega⟩
  have hfit1 : hiSum ((c0 :: b) ++ [(ctx.2 - 1, ctx.2 + 1)]) ≤ DEN := by
    rw [hiSum_eq, List.map_append, List.sum_append, ← hiSum_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hfit2 : hiSum ((c0 :: b) ++ [(ctx.1 - 1, ctx.1 + 1)]) ≤ DEN := by
    rw [hiSum_eq, List.map_append, List.sum_append, ← hiSum_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hbx0 : boxFn bl (s + 1 + 1) hl = Fin.cons (α := fun _ => Cell) ctx βx := by
    subst hbl
    rw [hβx]
    exact boxFn_append_singleton (c0 :: b) ctx s hβl hl
  have hS0 : ShareLe (Fin.cons (α := fun _ => Cell) ctx βx) ((dropCost bl : ℝ) / K) := by
    rw [← hbx0]
    exact shareLe_list bl (s + 1) hl hcells (by omega)
  have hS1 : ShareLe (Fin.cons (α := fun _ => Cell) (ctx.2 - 1, ctx.2 + 1) βx)
      ((dropCost ((c0 :: b) ++ [(ctx.2 - 1, ctx.2 + 1)]) : ℝ) / K) := by
    rw [hβx, ← boxFn_append_singleton (c0 :: b) (ctx.2 - 1, ctx.2 + 1) s hβl hbl1]
    exact shareLe_list _ (s + 1) hbl1 hcells1 hfit1
  have hS2 : ShareLe (Fin.cons (α := fun _ => Cell) (ctx.1 - 1, ctx.1 + 1) βx)
      ((dropCost ((c0 :: b) ++ [(ctx.1 - 1, ctx.1 + 1)]) : ℝ) / K) := by
    rw [hβx, ← boxFn_append_singleton (c0 :: b) (ctx.1 - 1, ctx.1 + 1) s hβl hbl2]
    exact shareLe_list _ (s + 1) hbl2 hcells2 hfit2
  obtain ⟨D0, hD0⟩ : ∃ D0 : ℝ, D0 = (dropCost bl : ℝ) / K := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D1 : ℝ, D1 = (dropCost ((c0 :: b) ++ [(ctx.2 - 1, ctx.2 + 1)]) : ℝ) / K := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ D2 : ℝ, D2 = (dropCost ((c0 :: b) ++ [(ctx.1 - 1, ctx.1 + 1)]) : ℝ) / K := ⟨_, rfl⟩
  rw [← hD0] at hS0
  rw [← hD1] at hS1
  rw [← hD2] at hS2
  have hD00 : 0 ≤ D0 := by rw [hD0]; positivity
  have hD10 : 0 ≤ D1 := by rw [hD1]; positivity
  have hD20 : 0 ≤ D2 := by rw [hD2]; positivity
  have hw₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop,
      WF (frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR ≤ (ctx.2 : ℝ) / DEN * D0 + δ := fun δ hδ =>
    froz_weight_le hctx' (by omega) βx (by omega) hD00 hS0 hδ
  have hw₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop,
      WF (frozS q (e1 ctx) (e1 ctx + 1) βx) frozR ≤ ((ctx.2 + 1 : ℕ) : ℝ) / DEN * D1 + δ := by
    intro δ hδ
    have h1 := froz_weight_le (ctx := (ctx.2 - 1, ctx.2 + 1))
      ⟨by show 0 < ctx.2 - 1; omega, by show ctx.2 - 1 ≤ ctx.2 + 1; omega, by show ctx.2 + 1 ≤ DEN; omega⟩
      (by show ctx.2 + 1 ≤ 2 * (ctx.2 - 1); omega) βx (by show (βx 0).2 ≤ ctx.2 - 1; omega) hD10 hS1 hδ
    have ea : e1 (ctx.2 - 1, ctx.2 + 1) + 1 = e1 ctx := by
      show DEN - (ctx.2 + 1) + 1 = DEN - ctx.2
      omega
    have eb : e2 (ctx.2 - 1, ctx.2 + 1) - 1 = e1 ctx + 1 := by
      show DEN - (ctx.2 - 1) + 1 - 1 = DEN - ctx.2 + 1
      omega
    rw [ea, eb] at h1
    exact h1
  have hw₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ q : ℕ in atTop,
      WF (frozS q (e2 ctx - 1) (e2 ctx) βx) frozR ≤ ((ctx.1 + 1 : ℕ) : ℝ) / DEN * D2 + δ := by
    intro δ hδ
    have h1 := froz_weight_le (ctx := (ctx.1 - 1, ctx.1 + 1))
      ⟨by show 0 < ctx.1 - 1; omega, by show ctx.1 - 1 ≤ ctx.1 + 1; omega, by show ctx.1 + 1 ≤ DEN; omega⟩
      (by show ctx.1 + 1 ≤ 2 * (ctx.1 - 1); omega) βx (by show (βx 0).2 ≤ ctx.1 - 1; omega) hD20 hS2 hδ
    have ea : e1 (ctx.1 - 1, ctx.1 + 1) + 1 = e2 ctx - 1 := by
      show DEN - (ctx.1 + 1) + 1 = DEN - ctx.1 + 1 - 1
      omega
    have eb : e2 (ctx.1 - 1, ctx.1 + 1) - 1 = e2 ctx := by
      show DEN - (ctx.1 - 1) + 1 - 1 = DEN - ctx.1 + 1
      omega
    rw [ea, eb] at h1
    exact h1
  obtain ⟨w₀, hw₀def⟩ : ∃ w : ℝ, w = (ctx.2 : ℝ) / DEN * D0 := ⟨_, rfl⟩
  obtain ⟨w₁, hw₁def⟩ : ∃ w : ℝ, w = ((ctx.2 + 1 : ℕ) : ℝ) / DEN * D1 := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂def⟩ : ∃ w : ℝ, w = ((ctx.1 + 1 : ℕ) : ℝ) / DEN * D2 := ⟨_, rfl⟩
  rw [← hw₀def] at hw₀
  rw [← hw₁def] at hw₁
  rw [← hw₂def] at hw₂
  have hw₀0 : 0 ≤ w₀ := by rw [hw₀def]; positivity
  have hw₁0 : 0 ≤ w₁ := by rw [hw₁def]; positivity
  have hw₂0 : 0 ≤ w₂ := by rw [hw₂def]; positivity
  obtain ⟨bd, hbddef⟩ : ∃ bd : ℝ, bd = (bdK ctx t : ℝ) / K := ⟨_, rfl⟩
  have hbd : (SieveCert.omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) ≤ bd := by
    rw [hbddef]
    have h1 := SieveCert.div_le_cdiv (SieveCert.omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 * DEN) t ht0
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht0
    have e : (SieveCert.omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 : ℝ) / K * ((DEN : ℝ) / t) =
        ((SieveCert.omKw (DEN - ctx.2 - t - 1) t (ctx.2 - ctx.1 + 2) 1 * DEN : ℕ) : ℝ) / t / K := by
      push_cast
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h1 hK.le
  -- the bound for every ε
  have hflip : ∀ ε : ℝ, 0 < ε → Bd false (((c : ℝ) / K + ε) * (w₀ + w₁ + w₂) + bd * (w₁ + w₂))
      (Fin.cons (α := fun _ => Cell) ctx βx) := by
    intro ε hε
    exact bd_flip_neg ⟨hl0, hlh, hhD⟩ hft ht0 htl ht2 htD βx (by omega) (by positivity) hJ
      (hk [(f, t)] rfl 0 rfl ε hε) hbd hw₁0 hw₂0 hw₀ hw₁ hw₂
  rw [hbx0]
  refine bd_of_eps (W := w₀ + w₁ + w₂) (by positivity) fun ε hε => bd_mono (hflip ε hε) ?_
  -- the arithmetic
  have harith : (c : ℝ) / K * (w₀ + w₁ + w₂) + bd * (w₁ + w₂) ≤
      ((cdiv (c * (ctx.2 * dropCost bl + E) + bdK ctx t * E) (DEN * K) : ℕ) : ℝ) / K := by
    have h1 := SieveCert.div_le_cdiv (c * (ctx.2 * dropCost bl + E) + bdK ctx t * E) (DEN * K)
      (Nat.mul_pos SieveCert.DEN_pos (by exact_mod_cast hK))
    have e : (c : ℝ) / K * (w₀ + w₁ + w₂) + bd * (w₁ + w₂) =
        ((c * (ctx.2 * dropCost bl + E) + bdK ctx t * E : ℕ) : ℝ) / ((DEN * K : ℕ) : ℝ) / K := by
      rw [hw₀def, hw₁def, hw₂def, hD0, hD1, hD2, hbddef, hEdef']
      push_cast
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right h1 hK.le
  linarith

/-- **The cost of a reversal through the largest prime bounds the term.** For a box that passes `flipOK`: a cost
that `flipCost` returns below its limit gives `Bd false (cost/K)` for the box, that is, its term in `𝒜` minus the
comparison set is at most `(cost/K + o(1))x/(φ(q) log x)`. -/
theorem bd_flipCost (SK : Cell → List Cell → Strat) (fuel maxlen : ℕ) {bl : List Cell}
    (hok : flipOK maxlen bl = true) {lim : ℕ} (h : flipCost SK fuel bl lim < lim) (k' : ℕ)
    (hl : bl.length = k' + 1) : Bd false ((flipCost SK fuel bl lim : ℝ) / K) (boxFn bl (k' + 1) hl) := by
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
  obtain ⟨cl, hcldef⟩ : ∃ cl : ℕ, cl = minN CAPK (Nat.succ (Nat.div
      (Nat.sub (Nat.mul (Nat.sub lim 1) (DEN * K)) (bdK (lastC bl) (flipT (lastC bl)) *
        (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
          ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))))
      ((lastC bl).2 * dropCost bl +
        (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
          ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))))) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = flipTree SK fuel (lastC bl) (c0 :: b) cl := ⟨_, rfl⟩
  have hunf : flipCost SK fuel bl lim = cond (Nat.ble cl c) lim
      (cdiv (c * ((lastC bl).2 * dropCost bl +
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) +
        bdK (lastC bl) (flipT (lastC bl)) *
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) (DEN * K)) := by
    unfold flipCost
    rw [← hβdef]
    beta_reduce
    rw [← hcldef, ← hcdef]
  cases hcap : Nat.ble cl c
  swap
  · rw [hunf, hcap] at h
    exact absurd h (lt_irrefl _)
  rw [hcap, Bool.cond_false] at hunf
  have hccap : c < cl := by
    by_contra hge
    rw [Nat.ble_eq_true_of_le (not_lt.1 hge)] at hcap
    exact Bool.noConfusion hcap
  obtain ⟨St, hSt⟩ : ∃ St : Strat, St = SK (lastC bl) (c0 :: b) := ⟨_, rfl⟩
  have hcunf : c = match firstJ (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b))
      (c0 :: b) (minN c0.1 (flipT (lastC bl))) (St.propJ (c0 :: b)) with
      | some f => kids (solveG (opsK (lastC bl) (Nat.succ b.length))
          (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b)) St fuel)
          (flipT (lastC bl)) (c0 :: b) true (St.cuts (c0 :: b) f) f cl
      | none => cl := by
    rw [hcdef, hSt]
    rfl
  cases hfj : firstJ (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b))
      (c0 :: b) (minN c0.1 (flipT (lastC bl))) (St.propJ (c0 :: b)) with
  | none =>
    rw [hfj] at hcunf
    have : c = cl := hcunf
    omega
  | some f =>
    rw [hfj] at hcunf
    have hck : c = kids (solveG (opsK (lastC bl) (c0 :: b).length)
        (frozTests (DEN - (lastC bl).2) (DEN - (lastC bl).1 + 1) (12 + DEN / c0.1) (c0 :: b)) St fuel)
        (flipT (lastC bl)) (c0 :: b) true (St.cuts (c0 :: b) f) f cl := hcunf
    obtain ⟨-, hfle, cfg, hokJ⟩ := firstJ_some hfj
    rw [hunf]
    refine bd_flip_core hok k' hl hβdef hfle hokJ fun s hβl hR => ?_
    have hk := kidsP_sound hR.split (solveG_sound hR St fuel) (flipT (lastC bl)) (c0 :: b) true
      (St.cuts (c0 :: b) f) f cl (by rw [← hck]; exact hccap)
    rw [← hck] at hk
    exact hk

/-! ### The search -/

/-- **The nodes of the search with the reversal through the largest prime bound the term**, for tests that are
sound and sound under two more atoms. -/
theorem rulesF {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ)
    (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat) (fuel maxlen : ℕ) :
    Rules (opsF τ SK₀ fuel₀ cq SK fuel maxlen) τ PR where
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
    -- the bound of `opsR`, as a statement about any limit
    have hold : ∀ r : ℕ, r = cond (!par && revOK bl) (revCost τ SK₀ fuel₀ cq bl l) l → r < l → PR bl par r := by
      intro r hr hrl
      by_cases hc : (!par && revOK bl) = true
      · rw [hc, Bool.cond_true] at hr
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨hp, hrev⟩ := hc
        subst hp
        intro k' hl
        have h3 := revOK_length hrev
        have hk : k' = 2 := by omega
        subst hk
        rw [hr]
        exact bd_rev hτX SK₀ fuel₀ cq hrev (by rw [← hr]; exact hrl) hl
      · rw [Bool.not_eq_true] at hc
        rw [hc, Bool.cond_false] at hr
        omega
    obtain ⟨r, hr⟩ : ∃ r, r = cond (!par && revOK bl) (revCost τ SK₀ fuel₀ cq bl l) l := ⟨_, rfl⟩
    have hval : (opsF τ SK₀ fuel₀ cq SK fuel maxlen).alt bl par l =
        cond (!par && flipOK maxlen bl) (cond (Nat.blt (flipCost SK fuel bl r) r) (flipCost SK fuel bl r) r) r := by
      rw [hr]
      rfl
    rw [hval] at h ⊢
    by_cases hf : (!par && flipOK maxlen bl) = true
    · rw [hf, Bool.cond_true] at h ⊢
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      obtain ⟨hp, hfok⟩ := hf
      subst hp
      by_cases hlt : flipCost SK fuel bl r < r
      · have hb : Nat.blt (flipCost SK fuel bl r) r = true := by rw [Nat.blt_eq]; exact hlt
        rw [hb, Bool.cond_true] at h ⊢
        intro k' hl
        exact bd_flipCost SK fuel maxlen hfok hlt k' hl
      · have hb : Nat.blt (flipCost SK fuel bl r) r = false := by
          rw [← Bool.not_eq_true, Nat.blt_eq]
          exact hlt
        rw [hb, Bool.cond_false] at h ⊢
        exact hold r hr h
    · rw [Bool.not_eq_true] at hf
      rw [hf, Bool.cond_false] at h ⊢
      exact hold r hr h
  split := pr_split
  buch := fun _ _ hfx hJ hc => pr_buch hτ hfx hJ hc

/-- **The search with the reversal through the largest prime is sound**: a cost that it returns below its limit
bounds the term. -/
theorem solveF2_sound {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ)
    (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat) (fuel maxlen : ℕ) (S : Strat) (n : ℕ) :
    RecP PR (solveG (opsF τ SK₀ fuel₀ cq SK fuel maxlen) τ S n) :=
  solveG_sound (rulesF hτ hτX SK₀ fuel₀ cq SK fuel maxlen) S n

/-- **A part of a search with the reversal through the largest prime**, as the kernel checks it: if the costs of
the cells of the new prime between `a` and `top`, cut at `cs` and searched with the limit `K`, sum to at most
`c < K`, then the term of the box of the whole range is at least `−(c/K + o(1))x/(φ(q) log x)` with its sign. -/
theorem pr_of_kidsF {τ : Tests} (hτ : τ.Sound) (hτX : τ.SoundX) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ)
    (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat) (fuel maxlen : ℕ) (S : Strat) (n : ℕ) {top : ℕ}
    {bl : List Cell} {par : Bool} {cs : List ℕ} {a c : ℕ}
    (h : kids (solveG (opsF τ SK₀ fuel₀ cq SK fuel maxlen) τ S n) top bl par cs a K ≤ c) (hc : c < K) :
    PR ((a, top) :: bl) par c :=
  pr_mono (kidsP_sound pr_split (solveF2_sound hτ hτX SK₀ fuel₀ cq SK fuel maxlen S n) top bl par cs a K
    (lt_of_le_of_lt h hc)) h

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **A part of a search with the reversal through the largest prime, for any route**: `pr_of_kidsF` with the
route and its exponent as variables. -/
theorem pr_of_kidsF_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr) {τ : Tests}
    (hτ : @Tests.Sound Rt τ) (hτX : @Tests.SoundX Rt τ) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ)
    (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat) (fuel maxlen : ℕ) (S : Strat) (n : ℕ) {top : ℕ}
    {bl : List Cell} {par : Bool} {cs : List ℕ} {a c : ℕ}
    (h : kids (solveG (@opsF Pr τ SK₀ fuel₀ cq SK fuel maxlen) τ S n) top bl par cs a K ≤ c) (hc : c < K) :
    @PR Rt ((a, top) :: bl) par c :=
  @pr_of_kidsF Rt hRt Pr hPr τ hτ hτX SK₀ fuel₀ cq SK fuel maxlen S n top bl par cs a c h hc

end SieveAd

#print axioms SieveAd.pr_of_kidsF_at
