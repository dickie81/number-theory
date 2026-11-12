/-
# The reversal of a box of the sign `+` through its largest prime, from the bound of a tree

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFlipSearch.lean` bounds the term of a box of the sign `−` by its reversal through its
largest prime (`bd_flip_core`): the term is at most the sum, over the frozen numbers, of the terms of the chain of
one prime below the level, which a tree bounds from below. For a box of the sign `+` the same identity gives a
bound of the term from below (`SieveAdFlipSum.lean`, `bd_flip_pos`): the frozen numbers are then those of the
narrower slab, between `x^{(DEN − h₁ + 1)/DEN}` and `x^{(DEN − l₁)/DEN}`, and the chain's terms need upper bounds,
so the cells of the chain's first prime are searched with the sign `−`.

* `bd_flip_core_pos`: **the reversal of a box of the sign `+` from the bound of a tree**: for a box that passes
  `flipOK`, a floor at which `frozTests` evaluates the terms of the narrower frozen part and a cost `c` of the
  cells of the chain's first prime with the sign `−`, for any search whose nodes prove `PF`, give `Bd true` at
  `⌈(c·h₁·D₀ + bdK·E)/(DEN·K)⌉/K`: the tree's cost weighs on the share `D₀` of the box alone, and the frozen
  numbers within `x^{1/DEN}` of the slab's two ends, of shares `E`, are bounded by Buchstab's function.
* `bd_flip_coreB`: the two signs in one statement, as the search led by hints uses it.

The file imports `SieveAdFlipSearch.lean`.
-/
import SieveAdFlipSearch

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos' cdiv)

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

/-- **The reversal of a box of the sign `+` through its largest prime, from the bound of a tree.** For a box `bl`
that passes `flipOK`, with `c₀ :: b` its cells but the largest prime's: if the tests `frozTests` of the narrower
slab evaluate the terms of the frozen part at a floor `f ≤ min(lo_s, t)`, and the cells of the chain's first prime
from `f` to the level `t` cost `c` with the sign `−` over the frozen part (for any search whose nodes prove `PF`),
then the term of the box is at least `−(⌈(c·h₁·D₀ + bdK·E)/(DEN·K)⌉/K + o(1))x/(φ(q) log x)` in `𝒜` minus the
comparison set. -/
theorem bd_flip_core_pos {maxlen : ℕ} {bl : List Cell} (hok : flipOK maxlen bl = true) (k' : ℕ)
    (hl : bl.length = k' + 1) {c0 : Cell} {b : List Cell} (hβdef : c0 :: b = initC bl) {f c : ℕ} {cfg : Cfg}
    (hfle : f ≤ minN c0.1 (flipT (lastC bl)))
    (hokJ : (frozTests (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).1) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b) f
      cfg = true)
    (htree : ∀ (s : ℕ) (hβl : (c0 :: b).length = s + 1),
      Rules (opsK (lastC bl) (c0 :: b).length)
          (frozTests (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).1) (12 + DEN / c0.1) (c0 :: b))
          (PF (fun q => frozS q (e1 (lastC bl) + 1) (e2 (lastC bl) - 1) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)) →
        PF (fun q => frozS q (e1 (lastC bl) + 1) (e2 (lastC bl) - 1) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)
          ((f, flipT (lastC bl)) :: c0 :: b) false c) :
    Bd true
      (((cdiv (c * ((lastC bl).2 * dropCost bl) +
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
  generalize hτdef : frozTests (DEN - ctx.2 + 1) (DEN - ctx.1) (12 + DEN / c0.1) (c0 :: b) = τ at hokJ htree
  have hτdef' : τ = frozTests (DEN - ctx.2 + 1) (DEN - ctx.1) (12 + DEN / c0.1) (c0 :: b) := hτdef.symm
  have hft : f ≤ t := hfle.trans (minN_le c0.1 t).2
  have hctx' : 0 < ctx.1 ∧ ctx.1 ≤ ctx.2 ∧ ctx.2 ≤ DEN := ⟨hl0, hlh.le, hhD⟩
  have he : DEN - ctx.2 + 1 ≤ DEN - ctx.1 := by omega
  have he₂ : DEN - ctx.1 ≤ DEN := by omega
  have hee : e2 ctx - 1 = DEN - ctx.1 := by unfold e2; omega
  have hT : DEN + 1 ≤ (DEN / c0.1 + 1) * (boxFn (c0 :: b) (s + 1) hβl (Fin.last s)).1 := by
    rw [boxFn_last_head]
    have := Nat.lt_mul_div_succ DEN hc0.1
    rw [Nat.mul_comm] at this
    omega
  have hτs : SoundF τ (fun q => frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR (c0 :: b) := by
    rw [hτdef', hβx, hee]
    exact frozTests_sound (c0 :: b) hβl he he₂ hT (le_refl _)
  have hS := inSlab_frozS_inner ctx βx
  have hk := htree s hβl (by rw [hβx] at hS hτs; exact frozRules hctx' hS hτs)
  rw [← hβx] at hk
  have hJ : EvJF (fun q => frozS q (e1 ctx + 1) (e2 ctx - 1) βx) frozR f (boxFn [] 0 rfl) :=
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
  have hflip : ∀ ε : ℝ, 0 < ε → Bd true (((c : ℝ) / K + ε) * w₀ + bd * (w₁ + w₂))
      (Fin.cons (α := fun _ => Cell) ctx βx) := by
    intro ε hε
    exact bd_flip_pos ⟨hl0, hlh, hhD⟩ hft ht0 htl ht2 htD βx (by omega) (by positivity) hJ
      (hk [(f, t)] rfl 0 rfl ε hε) hbd hw₁0 hw₂0 hw₀ hw₁ hw₂
  rw [hbx0]
  refine bd_of_eps (W := w₀) hw₀0 fun ε hε => bd_mono (hflip ε hε) ?_
  -- the arithmetic
  have harith : (c : ℝ) / K * w₀ + bd * (w₁ + w₂) ≤
      ((cdiv (c * (ctx.2 * dropCost bl) + bdK ctx t * E) (DEN * K) : ℕ) : ℝ) / K := by
    have h1 := SieveCert.div_le_cdiv (c * (ctx.2 * dropCost bl) + bdK ctx t * E) (DEN * K)
      (Nat.mul_pos SieveCert.DEN_pos (by exact_mod_cast hK))
    have e : (c : ℝ) / K * w₀ + bd * (w₁ + w₂) =
        ((c * (ctx.2 * dropCost bl) + bdK ctx t * E : ℕ) : ℝ) / ((DEN * K : ℕ) : ℝ) / K := by
      rw [hw₀def, hw₁def, hw₂def, hD0, hD1, hD2, hbddef, hEdef']
      push_cast
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h1 hK.le
  linarith

/-- **The reversal through the largest prime, from the bound of a tree, for a box of either sign**: `bd_flip_core`
for the sign `−` (`pos = false`), `bd_flip_core_pos` for the sign `+`. -/
theorem bd_flip_coreB (pos : Bool) {maxlen : ℕ} {bl : List Cell} (hok : flipOK maxlen bl = true) (k' : ℕ)
    (hl : bl.length = k' + 1) {c0 : Cell} {b : List Cell} (hβdef : c0 :: b = initC bl) {f c : ℕ} {cfg : Cfg}
    (hfle : f ≤ minN c0.1 (flipT (lastC bl)))
    (hokJ : (frozTests (cond pos (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).2))
      (cond pos (DEN - (lastC bl).1) (DEN - (lastC bl).1 + 1)) (12 + DEN / c0.1) (c0 :: b)).okJ (c0 :: b) f
      cfg = true)
    (htree : ∀ (s : ℕ) (hβl : (c0 :: b).length = s + 1),
      Rules (opsK (lastC bl) (c0 :: b).length)
          (frozTests (cond pos (DEN - (lastC bl).2 + 1) (DEN - (lastC bl).2))
            (cond pos (DEN - (lastC bl).1) (DEN - (lastC bl).1 + 1)) (12 + DEN / c0.1) (c0 :: b))
          (PF (fun q => frozS q (cond pos (e1 (lastC bl) + 1) (e1 (lastC bl)))
            (cond pos (e2 (lastC bl) - 1) (e2 (lastC bl))) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)) →
        PF (fun q => frozS q (cond pos (e1 (lastC bl) + 1) (e1 (lastC bl)))
            (cond pos (e2 (lastC bl) - 1) (e2 (lastC bl))) (boxFn (c0 :: b) (s + 1) hβl)) frozR (c0 :: b)
          ((f, flipT (lastC bl)) :: c0 :: b) (!pos) c) :
    Bd pos
      (((cdiv (c * cond pos ((lastC bl).2 * dropCost bl) ((lastC bl).2 * dropCost bl +
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) +
        bdK (lastC bl) (flipT (lastC bl)) *
          (((lastC bl).2 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).2 - 1, (lastC bl).2 + 1)]) +
            ((lastC bl).1 + 1) * dropCost ((c0 :: b) ++ [((lastC bl).1 - 1, (lastC bl).1 + 1)]))) (DEN * K) : ℕ) :
          ℝ) / K)
      (boxFn bl (k' + 1) hl) := by
  cases pos with
  | false =>
    simp only [Bool.cond_false, Bool.not_false] at hokJ htree
    rw [Bool.cond_false]
    exact bd_flip_core hok k' hl hβdef hfle hokJ htree
  | true =>
    simp only [Bool.cond_true, Bool.not_true] at hokJ htree
    rw [Bool.cond_true]
    exact bd_flip_core_pos hok k' hl hβdef hfle hokJ htree

end SieveAd

#print axioms SieveAd.bd_flip_coreB
