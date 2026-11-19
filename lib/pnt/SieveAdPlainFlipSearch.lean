/-
# The search with the reversal of a box through its largest prime is sound: the paper's conditions on the leaves alone

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveAdFlipSearch.lean` as it stood at commit `40411d7`, before the leaves of a comparison could be cut in three, with its
declarations in the namespace `SieveAd.Plain`. Their statements are about the tests of `SieveAdPlainDefs.lean`,
whose conditions on the leaves are the paper's alone, and their proofs are that file's proofs, so nothing here rests
on the estimate in two variables on the leaves' region, nor on the density curve `g7d` behind it. The theorem at
`2150/1000` (`Linnik21500.linnik_21500`) takes its tests, its reversal and its search from the `SieveAdPlain`
modules; `SieveAdFlipSearch.lean` serves the later theorems, and its header describes the statements.

Its declarations: `initC_append_lastC`, `boxFn_zero_lastC`, `boxFn_last_head`, `boxFn_append_singleton`, `minN_le`,
`shareLe_list`, `bd_of_eps`, `bd_flip_core`.

Left out, as no result of that theorem uses them: `bd_flipCost`, `rulesF`, `solveF2_sound`, `pr_of_kidsF`, `pr_of_kidsF_at`.

The file imports `SieveAdPlainFrozTests.lean`, `SieveAdFlipSum.lean`, `SieveAdFlipDefs.lean` and `SieveAdRevSearch.lean`.
-/
import SieveAdPlainFrozTests
import SieveAdFlipSum
import SieveAdFlipDefs
import SieveAdRevSearch

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd.Plain

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

/-! ### The search -/

end SieveAd.Plain

