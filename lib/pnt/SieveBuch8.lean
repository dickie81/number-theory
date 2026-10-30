/-
# The decomposition to depth 8

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveBuch.lean`'s decomposition decomposes the cells of depth 4 to depth 6 and drops the counted
cells of depth 6. This file decomposes a counted cell of depth 6 two levels further, as the cells of depth 4 are, and
takes the decisions to decompose as parameters (`Scheme8`).

* `sp6`, `sp7`: the modes of the boxes of depths 6 and 7 (split at `X'` when `limOK` passes them, whole otherwise).
* `S6cle`, `S6cgt`, `S7`, `S7c`, `S7le`, `S7gt`, `S8`, `S8c`: the families below a cell of depth 6, as `S4cle` …
  `S6c` below a cell of depth 4: the cell split at its threshold, the coarse cells of `p₇`, split at theirs, and the
  coarse cells of `p₈`.
* `I_S6c`, `I_S6cle`, `I_S7`, `I_S7c`, `I_S7le`, `I_S8`: the identities, as `I_S4c` … `I_S6`.
* `I_S7c_vanish_lt`, `I_S7c_vanish_reg`, `I_S8c_vanish_lt`, `I_S8c_vanish_reg`: the cells of depths 7 and 8 whose
  prime would exceed the one before, and those outside the region (`inKK7`, `reg8`), contribute `0`.
* `Scheme8`: which cells are decomposed: `dec2` (depth 2), `dec4` (depth 4) and `dec6` (depth 6), each implying that
  the rule passes the boxes its decomposition needs (`SieveCert.allowedR`, `SieveCert.allowed4R`, `allowed6R`: the
  box of depth 6 and every box of depth 7 of its region).
* `E1` … `E8`: the dropped terms. As `SieveBuch.Par.D1`, with `dec2` and `dec4`; below a counted cell of depth 6
  that `dec6` decomposes, every cell of depth 8 of its region.
* `Leaves8`: the estimates the leaves need: `SieveBuch.Par.Leaves`'s, and at depths 6 and 7 the parts of the
  decomposed boxes above their thresholds (`e6gt`, `e7gt`) and Proposition 6's families (`p6`, `p7`).
* `decomp8`: for a grid with `GridOK` and `GridOKC`, a rule with `RuleNB`, a scheme, `P.Good`, weights `g_A ≥ 0` and
  `g_B`, and leaves within `Err ≥ 0`, `S_{g_A}(z_top) ≥ S_{g_B}(z_top) − E1(g_B) − Cdec8·Err`.

The proof: `lvl8b` (the cells of depth 8 below a cell of depth 7: dropped), `lvl7` (a cell of depth 7: sign `−`),
`lvl6c` (a decomposed cell of depth 6), and then `lvl6'` … `lvl1'` as `SieveBuch.Par.lvl6` … `lvl1`, with the scheme's
decisions.

The file imports `SieveBuch.lean`.
-/
import SieveBuch

open Real Finset SieveFamily SieveChain SieveDecomp
open SieveCert (V DEN H U1 U2 cand inKK ne3 counted4 surelyEval cell nC eC HC cellC inKK5 ne5 counted6 lim Gc
  limOK nbOK)

namespace SieveBuch

open Classical

section Modes

variable [SieveCert.Grid]

/-- The mode of the box `(i, j, k, l, b, c)`, `b` and `c` coarse cells. -/
def sp6 (i j k l b c : ℕ) : Bool := limOK [cell i, cell j, cell k, cell l, cellC b, cellC c]
/-- The mode of the box `(i, j, k, l, b, c, d)`, `b`, `c` and `d` coarse cells. -/
def sp7 (i j k l b c d : ℕ) : Bool := limOK [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d]

theorem limOK_cells6 (i j k l b c : ℕ) :
    limOK [cell i, cell j, cell k, cell l, cellC b, cellC c] =
      decide (SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) + (eC b + HC) +
        (eC c + HC) < lim) := by
  simp only [limOK, SieveCert.hiSum, cell, cellC, Nat.add_zero, Nat.add_assoc]

theorem limOK_cells7 (i j k l b c d : ℕ) :
    limOK [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] =
      decide (SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) + (eC b + HC) +
        (eC c + HC) + (eC d + HC) < lim) := by
  simp only [limOK, SieveCert.hiSum, cell, cellC, Nat.add_zero, Nat.add_assoc]

theorem nbOK_cells6 (i j k l b c : ℕ) :
    nbOK [cell i, cell j, cell k, cell l, cellC b, cellC c] =
      decide (SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) + (eC b + HC) +
        (eC c + HC) + (eC c + HC) < DEN) := by
  simp only [nbOK, SieveCert.hiSum, SieveCert.lastHi, cell, cellC, Nat.add_zero, Nat.add_assoc]

theorem nbOK_cells7 (i j k l b c d : ℕ) :
    nbOK [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] =
      decide (SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) + (eC b + HC) +
        (eC c + HC) + (eC d + HC) + (eC d + HC) < DEN) := by
  simp only [nbOK, SieveCert.hiSum, SieveCert.lastHi, cell, cellC, Nat.add_zero, Nat.add_assoc]

/-- The coarse cell `d` of `p₇` may meet the region of depth 7 below the cell `(i, j, k, l, b, c)`. -/
def inKK7 (i j k l b c d : ℕ) : Bool :=
  decide (eC d < eC c + HC) &&
    decide (SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + eC b + eC c + 2 * eC d ≤ DEN)

/-- The coarse cell `f` of `p₈` may meet the region of depth 8 below the cell `(i, j, k, l, b, c, d)`. -/
def reg8 (i j k l b c d f : ℕ) : Bool :=
  decide (SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + eC b + eC c + eC d + 2 * eC f ≤ DEN)

end Modes

namespace Par

variable (P : Par) [SieveCert.Grid]

/-! ### The families below a cell of depth 6 -/

/-- Depth 6, `p₆` in the coarse cell `c`, with `p₁⋯p₆` at most the split's threshold. -/
noncomputable def S6cle (i j k l b c : ℕ) : List (Atom 6) :=
  P.S6c i j k l b c ++ [Atom.prodLe Finset.univ (P.Xs (sp6 i j k l b c))]
/-- Depth 6, `p₆` in the coarse cell `c`, with `p₁⋯p₆` above the split's threshold. -/
noncomputable def S6cgt (i j k l b c : ℕ) : List (Atom 6) :=
  P.S6c i j k l b c ++ [Atom.prodGt Finset.univ (P.Xs (sp6 i j k l b c))]
/-- Depth 7 below `(i, j, k, l, b, c)`, `p₁⋯p₆` at most the split's threshold. -/
noncomputable def S7 (i j k l b c : ℕ) : List (Atom 7) := extS (P.z₀ : ℝ) (P.S6cle i j k l b c)
/-- Depth 7, `p₇` in the coarse cell `d`. -/
noncomputable def S7c (i j k l b c d : ℕ) : List (Atom 7) := P.S7 i j k l b c ++ cellAC 6 P.x d
/-- Depth 7, `p₇` in the coarse cell `d`, with `p₁⋯p₇` at most the split's threshold. -/
noncomputable def S7le (i j k l b c d : ℕ) : List (Atom 7) :=
  P.S7c i j k l b c d ++ [Atom.prodLe Finset.univ (P.Xs (sp7 i j k l b c d))]
/-- Depth 7, `p₇` in the coarse cell `d`, with `p₁⋯p₇` above the split's threshold. -/
noncomputable def S7gt (i j k l b c d : ℕ) : List (Atom 7) :=
  P.S7c i j k l b c d ++ [Atom.prodGt Finset.univ (P.Xs (sp7 i j k l b c d))]
/-- Depth 8 below `(i, j, k, l, b, c, d)`, `p₁⋯p₇` at most the split's threshold. -/
noncomputable def S8 (i j k l b c d : ℕ) : List (Atom 8) := extS (P.z₀ : ℝ) (P.S7le i j k l b c d)
/-- Depth 8, `p₈` in the coarse cell `f`. -/
noncomputable def S8c (i j k l b c d f : ℕ) : List (Atom 8) := P.S8 i j k l b c d ++ cellAC 7 P.x f

/-! ### Chains -/

theorem chain_S6cle {Y : ℕ} (i j k l b c : ℕ) : ∀ rt ∈ famSet 6 Y (P.S6cle i j k l b c), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S6c i j k l b c)
theorem chain_S7 {Y : ℕ} (i j k l b c : ℕ) : ∀ rt ∈ famSet 7 Y (P.S7 i j k l b c), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S6cle i j k l b c)
theorem chain_S7c {Y : ℕ} (i j k l b c d : ℕ) : ∀ rt ∈ famSet 7 Y (P.S7c i j k l b c d), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S7 i j k l b c)
theorem chain_S7le {Y : ℕ} (i j k l b c d : ℕ) :
    ∀ rt ∈ famSet 7 Y (P.S7le i j k l b c d), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S7c i j k l b c d)
theorem chain_S8 {Y : ℕ} (i j k l b c d : ℕ) : ∀ rt ∈ famSet 8 Y (P.S8 i j k l b c d), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S7le i j k l b c d)
theorem chain_S8c {Y : ℕ} (i j k l b c d f : ℕ) :
    ∀ rt ∈ famSet 8 Y (P.S8c i j k l b c d f), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S8 i j k l b c d)

variable {P}

/-! ### The identities below a cell of depth 6 -/

/-- Depth 6: a cell split at `p₁⋯p₆ = X'`. -/
theorem I_S6c (g : ℕ → ℝ) (i j k l b c : ℕ) :
    P.I g (P.S6c i j k l b c) = P.I g (P.S6cle i j k l b c) + P.I g (P.S6cgt i j k l b c) :=
  famI_split g P.N₁ P.N₂ (P.S6c i j k l b c) _ _ fun rt => by
    simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 6: the part `p₁⋯p₆ ≤ X'` decomposed. -/
theorem I_S6cle (g : ℕ → ℝ) (i j k l b c : ℕ) :
    P.I g (P.S6cle i j k l b c) = P.J g (P.S6cle i j k l b c) - P.I g (P.S7 i j k l b c) :=
  buchstab_fam g P.N₁ P.N₂ (P.S6cle i j k l b c) fun rt hrt =>
    last_le_of_chain (P.chain_S6cle i j k l b c rt hrt)

/-- **Depth 7**, for a grid with `GridOKC` and `P.Good`: the coarse cells of `p₇`. -/
theorem I_S7 [SieveCert.GridOK] [SieveCert.GridOKC] (G : P.Good) (g : ℕ → ℝ) (i j k l b c : ℕ) :
    P.I g (P.S7 i j k l b c) = ∑ d ∈ range nC, P.I g (P.S7c i j k l b c d) :=
  @famI_cells (Gc) SieveCert.GridOKC.ok g P.N₁ P.N₂ P.x G.hx 6 P.N₂ (P.S7 i j k l b c) 6
    fun rt hrt => range_of_chain_C G (P.chain_S7 i j k l b c rt hrt) 6

/-- Depth 7: a cell split at `p₁⋯p₇ = X'`. -/
theorem I_S7c (g : ℕ → ℝ) (i j k l b c d : ℕ) :
    P.I g (P.S7c i j k l b c d) = P.I g (P.S7le i j k l b c d) + P.I g (P.S7gt i j k l b c d) :=
  famI_split g P.N₁ P.N₂ (P.S7c i j k l b c d) _ _ fun rt => by
    simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 7: the part `p₁⋯p₇ ≤ X'` decomposed. -/
theorem I_S7le (g : ℕ → ℝ) (i j k l b c d : ℕ) :
    P.I g (P.S7le i j k l b c d) = P.J g (P.S7le i j k l b c d) - P.I g (P.S8 i j k l b c d) :=
  buchstab_fam g P.N₁ P.N₂ (P.S7le i j k l b c d) fun rt hrt =>
    last_le_of_chain (P.chain_S7le i j k l b c d rt hrt)

/-- **Depth 8**, for a grid with `GridOKC` and `P.Good`: the coarse cells of `p₈`. -/
theorem I_S8 [SieveCert.GridOK] [SieveCert.GridOKC] (G : P.Good) (g : ℕ → ℝ) (i j k l b c d : ℕ) :
    P.I g (P.S8 i j k l b c d) = ∑ f ∈ range nC, P.I g (P.S8c i j k l b c d f) :=
  @famI_cells (Gc) SieveCert.GridOKC.ok g P.N₁ P.N₂ P.x G.hx 7 P.N₂ (P.S8 i j k l b c d) 7
    fun rt hrt => range_of_chain_C G (P.chain_S8 i j k l b c d rt hrt) 7

/-! ### What the families say of their primes -/

theorem facts_S6cle {Y : ℕ} {i j k l b c : ℕ} {rt : Fin 6 → ℕ} (hrt : rt ∈ famSet 6 Y (P.S6cle i j k l b c)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      InCC P.x b (rt 4) ∧ InCC P.x c (rt 5) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) ∧ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xs (sp4 i j k l) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 ≤ P.Xs (sp5 i j k l b) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 ≤ P.Xs (sp6 i j k l b c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    facts_S6c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h12 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xs (sp6 i j k l b c) :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ (P.Xs (sp6 i j k l b c)))
      (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_six] at h12
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem facts_S7c {Y : ℕ} {i j k l b c d : ℕ} {rt : Fin 7 → ℕ} (hrt : rt ∈ famSet 7 Y (P.S7c i j k l b c d)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      InCC P.x b (rt 4) ∧ InCC P.x c (rt 5) ∧ InCC P.x d (rt 6) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) ∧ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xs (sp4 i j k l) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 ≤ P.Xs (sp5 i j k l b) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 ≤ P.Xs (sp6 i j k l b c) := by
  have h6 : Fin.init rt ∈ famSet 6 Y (P.S6cle i j k l b c) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := facts_S6cle h6
  exact ⟨P.chain_S7c i j k l b c d rt hrt, a1, a2, a3, a4, a5, a6,
    @inC_of_mem (Gc) 7 Y _ rt hrt 6 P.x d fun A hA => List.mem_append_right _ hA, a7, a8, a9, a10, a11⟩

theorem facts_S7le {Y : ℕ} {i j k l b c d : ℕ} {rt : Fin 7 → ℕ} (hrt : rt ∈ famSet 7 Y (P.S7le i j k l b c d)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      InCC P.x b (rt 4) ∧ InCC P.x c (rt 5) ∧ InCC P.x d (rt 6) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) ∧ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xs (sp4 i j k l) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 ≤ P.Xs (sp5 i j k l b) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 ≤ P.Xs (sp6 i j k l b c) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 ≤ P.Xs (sp7 i j k l b c d) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    facts_S7c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h14 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xs (sp7 i j k l b c d) :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ (P.Xs (sp7 i j k l b c d)))
      (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_seven] at h14
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem facts_S8c {Y : ℕ} {i j k l b c d f : ℕ} {rt : Fin 8 → ℕ}
    (hrt : rt ∈ famSet 8 Y (P.S8c i j k l b c d f)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      InCC P.x b (rt 4) ∧ InCC P.x c (rt 5) ∧ InCC P.x d (rt 6) ∧ InCC P.x f (rt 7) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 ≤ P.Xs (sp7 i j k l b c d) := by
  have h7 : Fin.init rt ∈ famSet 7 Y (P.S7le i j k l b c d) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, -, -, -, -, -, a8⟩ := facts_S7le h7
  exact ⟨P.chain_S8c i j k l b c d f rt hrt, a1, a2, a3, a4, a5, a6, a7,
    @inC_of_mem (Gc) 8 Y _ rt hrt 7 P.x f fun A hA => List.mem_append_right _ hA, a8⟩

/-! ### Cells of depths 7 and 8 that contribute nothing -/

/-- **Depth 7, `d > c`**, for `P.Good`: `p₇` would exceed `p₆`. -/
theorem I_S7c_vanish_lt (G : P.Good) (g : ℕ → ℝ) {i j k l b c d : ℕ} (h : c < d) :
    P.I g (P.S7c i j k l b c d) = 0 := by
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
  obtain ⟨hc, -, -, -, -, -, hcc, hdd, -⟩ := P.facts_S7c hrt
  have h65 : rt 6 < rt 5 := hc.1 (show (5 : Fin 7) < 6 by decide)
  have hle : SieveCert.eC c + HC ≤ SieveCert.eC d := @e_add_H_le_of_lt (Gc) c d h
  have := rpow_mono_nat hx1 hle
  have h' : (rt 5 : ℝ) < rt 6 := by
    refine lt_of_lt_of_le hcc.2 (le_trans (by push_cast at this ⊢; exact this) hdd.1)
  exact absurd h65 (not_lt.2 (by exact_mod_cast h'.le))

/-- **Depth 8, `f > d`**, for `P.Good`: `p₈` would exceed `p₇`. -/
theorem I_S8c_vanish_lt (G : P.Good) (g : ℕ → ℝ) {i j k l b c d f : ℕ} (h : d < f) :
    P.I g (P.S8c i j k l b c d f) = 0 := by
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
  obtain ⟨hc, -, -, -, -, -, -, hdd, hff, -⟩ := P.facts_S8c hrt
  have h76 : rt 7 < rt 6 := hc.1 (show (6 : Fin 8) < 7 by decide)
  have hle : SieveCert.eC d + HC ≤ SieveCert.eC f := @e_add_H_le_of_lt (Gc) d f h
  have := rpow_mono_nat hx1 hle
  have h' : (rt 6 : ℝ) < rt 7 := by
    refine lt_of_lt_of_le hdd.2 (le_trans (by push_cast at this ⊢; exact this) hff.1)
  exact absurd h76 (not_lt.2 (by exact_mod_cast h'.le))

/-- **Depth 7, outside the region**, for `P.Good`: `p₁⋯p₇² > N₂` while `p₁⋯p₇ ≤ N₁` (`p₁⋯p₆` at most the box's
threshold, and `p₇ < p₆ < p₅`). -/
theorem I_S7c_vanish_reg (G : P.Good) (g : ℕ → ℝ) {i j k l b c d : ℕ}
    (hm : sp6 i j k l b c = true ∨ nbOK [cell i, cell j, cell k, cell l, cellC b, cellC c] = true)
    (h : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + SieveCert.eC b + SieveCert.eC c +
      2 * SieveCert.eC d) :
    P.I g (P.S7c i j k l b c d) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_vanish g _ _ _ fun rt hrt => ?_
  obtain ⟨hc, hi, hj, hk, hl, hb, hcc, hdd, -, -, -, -, hX6⟩ := P.facts_S7c hrt
  have h54 : rt 5 < rt 4 := hc.1 (show (4 : Fin 7) < 5 by decide)
  have h65 : rt 6 < rt 5 := hc.1 (show (5 : Fin 7) < 6 by decide)
  rw [Fin.prod_univ_seven]
  constructor
  · have : ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 : ℕ) : ℝ) ≤ P.N₁ := by
      push_cast
      have h0 : (1 : ℝ) ≤ rt 0 := by exact_mod_cast ((mem_famSet.1 hrt).1 0).2.one_lt.le
      have h1 : (1 : ℝ) ≤ rt 1 := by exact_mod_cast ((mem_famSet.1 hrt).1 1).2.one_lt.le
      have h2 : (1 : ℝ) ≤ rt 2 := by exact_mod_cast ((mem_famSet.1 hrt).1 2).2.one_lt.le
      have h3 : (1 : ℝ) ≤ rt 3 := by exact_mod_cast ((mem_famSet.1 hrt).1 3).2.one_lt.le
      refine P.mul_le_N₁ G hX6 h54 h65 ?_ fun hs => ?_
      · have e1 : (rt 4 : ℝ) * rt 5 ≤ rt 3 * (rt 4 * rt 5) := le_mul_of_one_le_left (by positivity) h3
        have e2 : (rt 3 : ℝ) * (rt 4 * rt 5) ≤ rt 2 * (rt 3 * (rt 4 * rt 5)) :=
          le_mul_of_one_le_left (by positivity) h2
        have e3 : (rt 2 : ℝ) * (rt 3 * (rt 4 * rt 5)) ≤ rt 1 * (rt 2 * (rt 3 * (rt 4 * rt 5))) :=
          le_mul_of_one_le_left (by positivity) h1
        have e4 : (rt 1 : ℝ) * (rt 2 * (rt 3 * (rt 4 * rt 5))) ≤ rt 0 * (rt 1 * (rt 2 * (rt 3 * (rt 4 * rt 5)))) :=
          le_mul_of_one_le_left (by positivity) h0
        linarith
      have hnb := hm.resolve_left (by rw [hs]; simp)
      rw [nbOK_cells6, decide_eq_true_eq] at hnb
      have h65' : (rt 6 : ℝ) ≤ rt 5 := by exact_mod_cast h65.le
      have hb2 : (rt 4 : ℝ) ≤ P.x ^ (((SieveCert.eC b : ℝ) + HC) / DEN) := hb.2.le
      have hc2 : (rt 5 : ℝ) ≤ P.x ^ (((SieveCert.eC c : ℝ) + HC) / DEN) := hcc.2.le
      calc (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 ≤
            (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 5 := by gcongr
        _ ≤ P.x ^ (((((((((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H)) + ((SieveCert.e k : ℝ) + H)) +
              ((SieveCert.e l : ℝ) + H)) + ((SieveCert.eC b : ℝ) + HC)) + ((SieveCert.eC c : ℝ) + HC)) +
              ((SieveCert.eC c : ℝ) + HC)) / DEN) :=
            mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
              (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
              hi.2.le hj.2.le) hk.2.le) hl.2.le) hb2) hc2) hc2
        _ ≤ P.x ^ (((DEN : ℝ) - 1) / DEN) := rpow_le_top hx1 (by push_cast; linarith) hnb
    exact_mod_cast this
  · have hp4 := prod4_ge hx0 hi.1 hj.1 hk.1 hl.1
    have hb1 : P.x ^ (((SieveCert.eC b : ℕ) : ℝ) / DEN) ≤ rt 4 := hb.1
    have hc1 : P.x ^ (((SieveCert.eC c : ℕ) : ℝ) / DEN) ≤ rt 5 := hcc.1
    have hd1 : P.x ^ (((SieveCert.eC d : ℕ) : ℝ) / DEN) ≤ rt 6 := hdd.1
    have hp : P.x ^ ((((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + SieveCert.e l) +
        (SieveCert.eC b : ℕ) + (SieveCert.eC c : ℕ) + (SieveCert.eC d : ℕ) + (SieveCert.eC d : ℕ)) / DEN) ≤
        (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 * rt 6 :=
      mul_rpow_ge hx0 (mul_rpow_ge hx0 (mul_rpow_ge hx0 (mul_rpow_ge hx0 hp4 hb1) hc1) hd1) hd1
    have hreg := rpow_region hx1 (s := SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l +
      SieveCert.eC b + SieveCert.eC c + 2 * SieveCert.eC d) h
    have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 * rt (Fin.last 6) : ℕ) : ℝ) := by
      push_cast
      refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
      congr 1
      push_cast
      ring
    exact_mod_cast this

/-- **Depth 8, outside the region**, for `P.Good`: `p₁⋯p₈² > N₂` while `p₁⋯p₈ ≤ N₁`. -/
theorem I_S8c_vanish_reg (G : P.Good) (g : ℕ → ℝ) {i j k l b c d f : ℕ}
    (hm : sp7 i j k l b c d = true ∨ nbOK [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] = true)
    (h : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + SieveCert.eC b + SieveCert.eC c +
      SieveCert.eC d + 2 * SieveCert.eC f) :
    P.I g (P.S8c i j k l b c d f) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_vanish g _ _ _ fun rt hrt => ?_
  obtain ⟨hc, hi, hj, hk, hl, hb, hcc, hdd, hff, hX7⟩ := P.facts_S8c hrt
  have h65 : rt 6 < rt 5 := hc.1 (show (5 : Fin 8) < 6 by decide)
  have h76 : rt 7 < rt 6 := hc.1 (show (6 : Fin 8) < 7 by decide)
  rw [Fin.prod_univ_eight]
  constructor
  · have : ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 * rt 7 : ℕ) : ℝ) ≤ P.N₁ := by
      push_cast
      have h0 : (1 : ℝ) ≤ rt 0 := by exact_mod_cast ((mem_famSet.1 hrt).1 0).2.one_lt.le
      have h1 : (1 : ℝ) ≤ rt 1 := by exact_mod_cast ((mem_famSet.1 hrt).1 1).2.one_lt.le
      have h2 : (1 : ℝ) ≤ rt 2 := by exact_mod_cast ((mem_famSet.1 hrt).1 2).2.one_lt.le
      have h3 : (1 : ℝ) ≤ rt 3 := by exact_mod_cast ((mem_famSet.1 hrt).1 3).2.one_lt.le
      have h4 : (1 : ℝ) ≤ rt 4 := by exact_mod_cast ((mem_famSet.1 hrt).1 4).2.one_lt.le
      refine P.mul_le_N₁ G hX7 h65 h76 ?_ fun hs => ?_
      · have e1 : (rt 5 : ℝ) * rt 6 ≤ rt 4 * (rt 5 * rt 6) := le_mul_of_one_le_left (by positivity) h4
        have e2 : (rt 4 : ℝ) * (rt 5 * rt 6) ≤ rt 3 * (rt 4 * (rt 5 * rt 6)) :=
          le_mul_of_one_le_left (by positivity) h3
        have e3 : (rt 3 : ℝ) * (rt 4 * (rt 5 * rt 6)) ≤ rt 2 * (rt 3 * (rt 4 * (rt 5 * rt 6))) :=
          le_mul_of_one_le_left (by positivity) h2
        have e4 : (rt 2 : ℝ) * (rt 3 * (rt 4 * (rt 5 * rt 6))) ≤ rt 1 * (rt 2 * (rt 3 * (rt 4 * (rt 5 * rt 6)))) :=
          le_mul_of_one_le_left (by positivity) h1
        have e5 : (rt 1 : ℝ) * (rt 2 * (rt 3 * (rt 4 * (rt 5 * rt 6)))) ≤
            rt 0 * (rt 1 * (rt 2 * (rt 3 * (rt 4 * (rt 5 * rt 6))))) :=
          le_mul_of_one_le_left (by positivity) h0
        linarith
      have hnb := hm.resolve_left (by rw [hs]; simp)
      rw [nbOK_cells7, decide_eq_true_eq] at hnb
      have h76' : (rt 7 : ℝ) ≤ rt 6 := by exact_mod_cast h76.le
      have hb2 : (rt 4 : ℝ) ≤ P.x ^ (((SieveCert.eC b : ℝ) + HC) / DEN) := hb.2.le
      have hc2 : (rt 5 : ℝ) ≤ P.x ^ (((SieveCert.eC c : ℝ) + HC) / DEN) := hcc.2.le
      have hd2 : (rt 6 : ℝ) ≤ P.x ^ (((SieveCert.eC d : ℝ) + HC) / DEN) := hdd.2.le
      calc (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 * rt 7 ≤
            (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 * rt 6 := by gcongr
        _ ≤ P.x ^ ((((((((((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H)) + ((SieveCert.e k : ℝ) + H)) +
              ((SieveCert.e l : ℝ) + H)) + ((SieveCert.eC b : ℝ) + HC)) + ((SieveCert.eC c : ℝ) + HC)) +
              ((SieveCert.eC d : ℝ) + HC)) + ((SieveCert.eC d : ℝ) + HC)) / DEN) :=
            mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
              (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
              (mul_rpow_le hx0 (by positivity) hi.2.le hj.2.le) hk.2.le) hl.2.le) hb2) hc2) hd2) hd2
        _ ≤ P.x ^ (((DEN : ℝ) - 1) / DEN) := rpow_le_top hx1 (by push_cast; linarith) hnb
    exact_mod_cast this
  · have hp4 := prod4_ge hx0 hi.1 hj.1 hk.1 hl.1
    have hb1 : P.x ^ (((SieveCert.eC b : ℕ) : ℝ) / DEN) ≤ rt 4 := hb.1
    have hc1 : P.x ^ (((SieveCert.eC c : ℕ) : ℝ) / DEN) ≤ rt 5 := hcc.1
    have hd1 : P.x ^ (((SieveCert.eC d : ℕ) : ℝ) / DEN) ≤ rt 6 := hdd.1
    have hf1 : P.x ^ (((SieveCert.eC f : ℕ) : ℝ) / DEN) ≤ rt 7 := hff.1
    have hp : P.x ^ ((((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + SieveCert.e l) +
        (SieveCert.eC b : ℕ) + (SieveCert.eC c : ℕ) + (SieveCert.eC d : ℕ) + (SieveCert.eC f : ℕ) +
        (SieveCert.eC f : ℕ)) / DEN) ≤ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 * rt 7 * rt 7 :=
      mul_rpow_ge hx0 (mul_rpow_ge hx0 (mul_rpow_ge hx0 (mul_rpow_ge hx0 (mul_rpow_ge hx0 hp4 hb1) hc1) hd1)
        hf1) hf1
    have hreg := rpow_region hx1 (s := SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l +
      SieveCert.eC b + SieveCert.eC c + SieveCert.eC d + 2 * SieveCert.eC f) h
    have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 6 * rt 7 * rt (Fin.last 7) : ℕ) : ℝ) := by
      push_cast
      refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
      congr 1
      push_cast
      ring
    exact_mod_cast this

end Par

/-! ### The decisions -/

section Scheme

variable [SieveCert.Grid] [SieveCert.Rule]

/-- The rule passes the box `(i, j, k, l, b, c)` of depth 6 and every box of depth 7 of its region. -/
def allowed6R (i j k l b c : ℕ) : Bool :=
  SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c] &&
    (List.range nC).all (fun d => !inKK7 i j k l b c d ||
      SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d])

theorem ok6_of_allowed6R {i j k l b c : ℕ} (h : allowed6R i j k l b c = true) :
    SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c] = true := by
  simp only [allowed6R, Bool.and_eq_true] at h
  exact h.1

theorem ok7_of_allowed6R {i j k l b c d : ℕ} (h : allowed6R i j k l b c = true) (hd : d < nC)
    (hK : inKK7 i j k l b c d = true) :
    SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] = true := by
  simp only [allowed6R, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have h' := h.2 d hd
  simpa [hK] using h'

/-- **The decisions of a certificate of depth 8**: which cells of depths 2, 4 and 6 are decomposed. Each implies that
the rule passes the boxes its decomposition needs. -/
class Scheme8 where
  /-- The candidate cell `(i, j)` is decomposed. -/
  dec2 : ℕ → ℕ → Bool
  /-- The counted cell `(i, j, k, l)` of depth 4 is decomposed. -/
  dec4 : ℕ → ℕ → ℕ → ℕ → Bool
  /-- The counted cell `(i, j, k, l, b, c)` of depth 6 is decomposed. -/
  dec6 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  allowed2 : ∀ {i j : ℕ}, dec2 i j = true → SieveCert.allowedR i j = true
  allowed4 : ∀ {i j k l : ℕ}, dec4 i j k l = true → SieveCert.allowed4R i j k l = true
  allowed6 : ∀ {i j k l b c : ℕ}, dec6 i j k l b c = true → allowed6R i j k l b c = true

variable [Scheme8]

theorem ok2_of_dec2 {i j : ℕ} (h : Scheme8.dec2 i j = true) : SieveCert.Rule.ok [cell i, cell j] = true := by
  have := Scheme8.allowed2 h
  simp only [SieveCert.allowedR, Bool.and_eq_true] at this
  exact this.1

theorem ok3_of_dec2 {i j k : ℕ} (h : Scheme8.dec2 i j = true) (hk : k < SieveCert.n) (hkk : inKK i j k = true)
    (hn : ne3 i j k = true) : SieveCert.Rule.ok [cell i, cell j, cell k] = true := by
  have := Scheme8.allowed2 h
  simp only [SieveCert.allowedR, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  have h' := this.2 k hk
  simpa [hkk, hn] using h'

theorem ok4_of_dec4 {i j k l : ℕ} (h : Scheme8.dec4 i j k l = true) :
    SieveCert.Rule.ok [cell i, cell j, cell k, cell l] = true := by
  have := Scheme8.allowed4 h
  simp only [SieveCert.allowed4R, Bool.and_eq_true] at this
  exact this.1

theorem ok5_of_dec4 {i j k l b : ℕ} (h : Scheme8.dec4 i j k l = true) (hb : b < nC) (hK : inKK5 i j k l b = true)
    (hn : ne5 i j k l b = true) : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b] = true := by
  have := Scheme8.allowed4 h
  simp only [SieveCert.allowed4R, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  have h' := this.2 b hb
  simpa [hK, hn] using h'

/-- The prefix of the tree down to the row `(i, j, k)`, with the scheme's decision at depth 2. -/
def Row3' (i j k : ℕ) : Prop :=
  (i < SieveCert.n ∧ j < SieveCert.n ∧ cand i j = true ∧ Scheme8.dec2 i j = true) ∧
    (k < SieveCert.n ∧ inKK i j k = true ∧ ne3 i j k = true)

/-- The prefix down to the cell `(i, j, k, l)` of depth 4 that is counted and decomposed. -/
def Deep' (i j k l : ℕ) : Prop := Row3' i j k ∧ l < k + 1 ∧ counted4 i j k l = true ∧ Scheme8.dec4 i j k l = true

/-- The prefix down to the cell `(i, j, k, l, b, c)` of depth 6 that is counted and decomposed. -/
def Deep6 (i j k l b c : ℕ) : Prop :=
  Deep' i j k l ∧ b < nC ∧ inKK5 i j k l b = true ∧ ne5 i j k l b = true ∧ c < b + 1 ∧ counted6 i j k l b c = true ∧
    Scheme8.dec6 i j k l b c = true

end Scheme

namespace Par

variable (P : Par) [SieveCert.Grid] [SieveCert.Rule] [Scheme8]

/-! ### The dropped terms -/

/-- The dropped terms of depth 8 below the cell `(i, j, k, l, b, c, d)`: its cells of the region. -/
noncomputable def E8 (g : ℕ → ℝ) (i j k l b c d : ℕ) : ℝ :=
  ∑ f ∈ range (d + 1), if reg8 i j k l b c d f = true then P.I g (P.S8c i j k l b c d f) else 0

/-- The dropped terms below a decomposed cell `(i, j, k, l, b, c)` of depth 6: those below its cells of depth 7. -/
noncomputable def E7 (g : ℕ → ℝ) (i j k l b c : ℕ) : ℝ :=
  ∑ d ∈ range (c + 1), if inKK7 i j k l b c d = true then P.E8 g i j k l b c d else 0

/-- The dropped terms of depth 6 below `(i, j, k, l, b)`: the counted cells, as they are or, when decomposed, those
below them. -/
noncomputable def E6 (g : ℕ → ℝ) (i j k l b : ℕ) : ℝ :=
  ∑ c ∈ range (b + 1), if counted6 i j k l b c = true then
    (if Scheme8.dec6 i j k l b c = true then P.E7 g i j k l b c else P.I g (P.S6c i j k l b c)) else 0

/-- The dropped terms below the counted cell `(i, j, k, l)` of depth 4 when it is decomposed. -/
noncomputable def E5 (g : ℕ → ℝ) (i j k l : ℕ) : ℝ :=
  ∑ b ∈ range nC, if inKK5 i j k l b = true ∧ ne5 i j k l b = true then P.E6 g i j k l b else 0

/-- The dropped terms of depth 4 below `(i, j, k)`. -/
noncomputable def E4 (g : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  ∑ l ∈ range (k + 1), if counted4 i j k l = true then
    (if Scheme8.dec4 i j k l = true then P.E5 g i j k l else P.I g (P.S4c i j k l)) else 0

/-- The dropped terms below the cell `(i, j)`. -/
noncomputable def E3 (g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ range SieveCert.n, if inKK i j k = true ∧ ne3 i j k = true then P.E4 g i j k else 0

/-- The dropped terms below the cell `i`. -/
noncomputable def E2 (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range SieveCert.n,
    ((if (cand i j = true ∧ Scheme8.dec2 i j = false) ∨ (cand i j = false ∧ sE2 i j = false) then
      P.I g (P.S2c i j) else 0) +
      (if cand i j = true ∧ Scheme8.dec2 i j = true then P.E3 g i j else 0))

/-- All the dropped terms. -/
noncomputable def E1 (g : ℕ → ℝ) : ℝ := ∑ i ∈ range SieveCert.n, if inW i then 0 else P.E2 g i

/-- The leaves' estimates: `Leaves`'s, with the scheme's decisions, and at depths 6 and 7 the parts of the decomposed
boxes above their thresholds and Proposition 6's families. -/
structure Leaves8 (gA gB : ℕ → ℝ) (Err : ℝ) : Prop where
  j0 : |P.J0 gA - P.J0 gB| ≤ Err
  e1 : ∀ i < SieveCert.n, inW i → |P.I gA (P.S1c i) - P.I gB (P.S1c i)| ≤ Err
  p1 : ∀ i < SieveCert.n, ¬ inW i → |P.J gA (P.S1c i) - P.J gB (P.S1c i)| ≤ Err
  e2 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → Scheme8.dec2 i j = true →
    |P.I gA (P.S2gt i j) - P.I gB (P.S2gt i j)| ≤ Err
  p2 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → Scheme8.dec2 i j = true →
    |P.J gA (P.S2le i j) - P.J gB (P.S2le i j)| ≤ Err
  e2' : ∀ i < SieveCert.n, ¬ inW i → ∀ j < SieveCert.n, cand i j = false → sE2 i j = true →
    |P.I gA (P.S2c i j) - P.I gB (P.S2c i j)| ≤ Err
  e3 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → Scheme8.dec2 i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → |P.I gA (P.S3gt i j k) - P.I gB (P.S3gt i j k)| ≤ Err
  p3 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → Scheme8.dec2 i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → |P.J gA (P.S3le i j k) - P.J gB (P.S3le i j k)| ≤ Err
  e3' : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → Scheme8.dec2 i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = false → |P.I gA (P.S3c i j k) - P.I gB (P.S3c i j k)| ≤ Err
  e4 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → Scheme8.dec2 i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → ∀ l < k + 1, counted4 i j k l = false → sE4 i j k l = true →
      |P.I gA (P.S4c i j k l) - P.I gB (P.S4c i j k l)| ≤ Err
  e4gt : ∀ i j k l, Deep' i j k l → |P.I gA (P.S4cgt i j k l) - P.I gB (P.S4cgt i j k l)| ≤ Err
  p4 : ∀ i j k l, Deep' i j k l → |P.J gA (P.S4cle i j k l) - P.J gB (P.S4cle i j k l)| ≤ Err
  e5gt : ∀ i j k l, Deep' i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = true →
    |P.I gA (P.S5gt i j k l b) - P.I gB (P.S5gt i j k l b)| ≤ Err
  p5 : ∀ i j k l, Deep' i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = true →
    |P.J gA (P.S5le i j k l b) - P.J gB (P.S5le i j k l b)| ≤ Err
  e5' : ∀ i j k l, Deep' i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = false →
    |P.I gA (P.S5c i j k l b) - P.I gB (P.S5c i j k l b)| ≤ Err
  e6 : ∀ i j k l, Deep' i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = true →
    ∀ c < b + 1, counted6 i j k l b c = false → sE6 i j k l b c = true →
      |P.I gA (P.S6c i j k l b c) - P.I gB (P.S6c i j k l b c)| ≤ Err
  e6gt : ∀ i j k l b c, Deep6 i j k l b c → |P.I gA (P.S6cgt i j k l b c) - P.I gB (P.S6cgt i j k l b c)| ≤ Err
  p6 : ∀ i j k l b c, Deep6 i j k l b c → |P.J gA (P.S6cle i j k l b c) - P.J gB (P.S6cle i j k l b c)| ≤ Err
  e7gt : ∀ i j k l b c, Deep6 i j k l b c → ∀ d < c + 1, inKK7 i j k l b c d = true →
    |P.I gA (P.S7gt i j k l b c d) - P.I gB (P.S7gt i j k l b c d)| ≤ Err
  p7 : ∀ i j k l b c, Deep6 i j k l b c → ∀ d < c + 1, inKK7 i j k l b c d = true →
    |P.J gA (P.S7le i j k l b c d) - P.J gB (P.S7le i j k l b c d)| ≤ Err

variable {P}

/-! ### The levels below a cell of depth 6 -/

/-- The error constants of the decomposition to depth 8: one cell of depth 6 decomposed (`ec6'`), one cell of
depth 5 (`ec5'`), one of depth 4 (`ec4'`), and the levels above, as `ec3` … `ec0`. -/
noncomputable def ec6' : ℝ := 2 + 2 * (nC : ℝ)
/-- See `ec6'`. -/
noncomputable def ec5' : ℝ := (nC : ℝ) * ec6' + 2
/-- See `ec6'`. -/
noncomputable def ec4' : ℝ := (nC : ℝ) * ec5' + 2
/-- See `ec6'`. -/
noncomputable def ec3' : ℝ := (SieveCert.n : ℝ) * ec4'
/-- See `ec6'`. -/
noncomputable def ec2' : ℝ := (SieveCert.n : ℝ) * (ec3' + 2)
/-- See `ec6'`. -/
noncomputable def ec1' : ℝ := (SieveCert.n : ℝ) * (ec2' + 2)
/-- See `ec6'`. -/
noncomputable def ec0' : ℝ := (SieveCert.n : ℝ) * (1 + ec1')
/-- The constant of `decomp8`: the total error is at most `Cdec8·Err`. -/
noncomputable def Cdec8 : ℝ := 1 + ec0'

omit [SieveCert.Rule] [Scheme8] in
theorem ec6'_nonneg : 0 ≤ ec6' := by unfold ec6'; positivity
omit [SieveCert.Rule] [Scheme8] in
theorem ec5'_nonneg : 0 ≤ ec5' := by unfold ec5'; have := ec6'_nonneg; positivity
omit [SieveCert.Rule] [Scheme8] in
theorem ec4'_nonneg : 0 ≤ ec4' := by unfold ec4'; have := ec5'_nonneg; positivity
omit [SieveCert.Rule] [Scheme8] in
theorem ec3'_nonneg : 0 ≤ ec3' := by unfold ec3'; have := ec4'_nonneg; positivity
omit [SieveCert.Rule] [Scheme8] in
theorem ec2'_nonneg : 0 ≤ ec2' := by unfold ec2'; have := ec3'_nonneg; positivity
omit [SieveCert.Rule] [Scheme8] in
theorem ec1'_nonneg : 0 ≤ ec1' := by unfold ec1'; have := ec2'_nonneg; positivity

omit [Scheme8] in
/-- **The cells of depth 8 below a cell of depth 7**, for a grid with `GridOKC`, a rule with no boundary term, and
`P.Good`, below a box of depth 7 that the rule passes: `S(B)` below it is exactly its dropped terms. -/
theorem I_S8_eq [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) (g : ℕ → ℝ)
    {i j k l b c d : ℕ} (hd : d < nC)
    (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] = true) :
    P.I g (P.S8 i j k l b c d) = P.E8 g i j k l b c d := by
  have hm := SieveCert.RuleNB.nb _ hok
  rw [P.I_S8 G g]
  unfold E8
  have hsub : ∑ f ∈ range nC, P.I g (P.S8c i j k l b c d f) =
      ∑ f ∈ range (d + 1), P.I g (P.S8c i j k l b c d f) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun f hf hf' => ?_
    rw [Finset.mem_range] at hf hf'
    exact P.I_S8c_vanish_lt G g (by omega)
  rw [hsub]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hr : reg8 i j k l b c d f = true
  · rw [ite_eq_left hr]
  · rw [ite_eq_right hr]
    have h : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + SieveCert.eC b +
        SieveCert.eC c + SieveCert.eC d + 2 * SieveCert.eC f := by
      simpa [reg8] using hr
    exact P.I_S8c_vanish_reg G g hm h

/-- **Level 7** (a cell of depth 7, sign `−`), for a decomposed cell of depth 6 and a cell `d ≤ c` of its region:
`A ≤ B + (dropped below) + 2Err`. -/
theorem lvl7 [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (Lv : P.Leaves8 gA gB Err) {i j k l b c d : ℕ}
    (hD : Deep6 i j k l b c) (hd : d < c + 1) (hK : inKK7 i j k l b c d = true) :
    P.I gA (P.S7c i j k l b c d) ≤ P.I gB (P.S7c i j k l b c d) + P.E8 gB i j k l b c d + 2 * Err := by
  have hdn : d < nC := by have := hD.2.1; have := hD.2.2.2.2.1; omega
  have hok := ok7_of_allowed6R (Scheme8.allowed6 hD.2.2.2.2.2.2) hdn hK
  rw [P.I_S7c gA, P.I_S7c gB, P.I_S7le gA, P.I_S7le gB, P.I_S8_eq G gB hdn hok]
  have hA8 : 0 ≤ P.I gA (P.S8 i j k l b c d) := famI_nonneg hgA P.N₁ P.N₂ _
  have hJ := abs_le.1 (Lv.p7 i j k l b c hD d hd hK)
  have hE := abs_le.1 (Lv.e7gt i j k l b c hD d hd hK)
  linarith [hJ.2, hE.2]

/-- **The cells of depth 7 below a decomposed cell of depth 6** (sign `−`): `A ≤ B + (dropped) + 2nC·Err`. -/
theorem lvl7row [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) {i j k l b c : ℕ}
    (hD : Deep6 i j k l b c) :
    P.I gA (P.S7 i j k l b c) ≤ P.I gB (P.S7 i j k l b c) + P.E7 gB i j k l b c + 2 * nC * Err := by
  have hc : c < nC := by have := hD.2.1; have := hD.2.2.2.2.1; omega
  have hm := SieveCert.RuleNB.nb _ (ok6_of_allowed6R (Scheme8.allowed6 hD.2.2.2.2.2.2))
  have hsub : ∀ g, ∑ d ∈ range nC, P.I g (P.S7c i j k l b c d) = ∑ d ∈ range (c + 1), P.I g (P.S7c i j k l b c d) := by
    intro g
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun d hd hd' => ?_
    rw [Finset.mem_range] at hd hd'
    exact P.I_S7c_vanish_lt G g (by omega)
  rw [P.I_S7 G gA, P.I_S7 G gB, hsub gA, hsub gB]
  unfold E7
  have hErrs : ∑ _d ∈ range (c + 1), 2 * Err ≤ 2 * nC * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((c + 1 : ℕ) : ℝ) ≤ nC := by exact_mod_cast hc
    nlinarith
  refine le_trans ?_ (add_le_add le_rfl hErrs)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd' := Finset.mem_range.1 hd
  by_cases hK : inKK7 i j k l b c d = true
  · rw [ite_eq_left hK]
    exact lvl7 G hgA Lv hD hd' hK
  · rw [ite_eq_right hK]
    have hreg : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + SieveCert.eC b +
        SieveCert.eC c + 2 * SieveCert.eC d := by
      have hlt : SieveCert.eC d < SieveCert.eC c + HC := by
        have h1 : SieveCert.eC d ≤ SieveCert.eC c := by
          unfold SieveCert.eC SieveCert.e
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
        have h2 : 0 < HC := @SieveCert.H_pos Gc SieveCert.GridOKC.ok
        omega
      simpa [inKK7, hlt] using hK
    rw [P.I_S7c_vanish_reg G gA hm hreg, P.I_S7c_vanish_reg G gB hm hreg]
    linarith

/-- **A decomposed cell of depth 6** (sign `+`): `A ≥ B − (dropped below) − ec6'·Err`. -/
theorem lvl6c [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) {i j k l b c : ℕ}
    (hD : Deep6 i j k l b c) :
    P.I gB (P.S6c i j k l b c) - P.E7 gB i j k l b c - ec6' * Err ≤ P.I gA (P.S6c i j k l b c) := by
  rw [P.I_S6c gA, P.I_S6c gB, P.I_S6cle gA, P.I_S6cle gB]
  have h7 := lvl7row G hgA hErr Lv hD
  have hJ := abs_le.1 (Lv.p6 i j k l b c hD)
  have hE := abs_le.1 (Lv.e6gt i j k l b c hD)
  have : ec6' * Err = 2 * Err + 2 * nC * Err := by unfold ec6'; ring
  linarith [hJ.1, hE.1]

/-- **Level 6** (terms with sign `+`), for a cell `(i, j, k, l)` of depth 4 decomposed and a counted coarse cell `b`
of its row: `A ≥ B − (dropped) − (b + 1)·ec6'·Err`. -/
theorem lvl6' [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) {i j k l b : ℕ}
    (hD : Deep' i j k l) (hb : b < nC) (hK : inKK5 i j k l b = true) (hn : ne5 i j k l b = true) :
    P.I gB (P.S6 i j k l b) - P.E6 gB i j k l b - (b + 1) * ec6' * Err ≤ P.I gA (P.S6 i j k l b) := by
  have hm := SieveCert.RuleNB.nb _ (ok5_of_dec4 hD.2.2.2 hb hK hn)
  have hsub : ∀ g, ∑ c ∈ range nC, P.I g (P.S6c i j k l b c) = ∑ c ∈ range (b + 1), P.I g (P.S6c i j k l b c) := by
    intro g
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun c hc hc' => ?_
    rw [Finset.mem_range] at hc hc'
    exact P.I_S6c_vanish_lt G g (by omega)
  rw [P.I_S6 G gA, P.I_S6 G gB, hsub gA, hsub gB]
  unfold E6
  have hErrs : ((b : ℝ) + 1) * ec6' * Err = ∑ _c ∈ range (b + 1), ec6' * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hec : 1 ≤ ec6' := by unfold ec6'; have : (0 : ℝ) ≤ nC := Nat.cast_nonneg _; linarith
  have hE0 : Err ≤ ec6' * Err := le_mul_of_one_le_left hErr hec
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun c hc => ?_
  have hc' := Finset.mem_range.1 hc
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 6 P.N₂ (P.S6c i j k l b c))
  by_cases hc6 : counted6 i j k l b c = true
  · rw [ite_eq_left hc6]
    by_cases hd6 : Scheme8.dec6 i j k l b c = true
    · rw [ite_eq_left hd6]
      exact lvl6c G hgA hErr Lv ⟨hD, hb, hK, hn, hc', hc6, hd6⟩
    · rw [ite_eq_right hd6]
      have : 0 ≤ ec6' * Err := mul_nonneg ec6'_nonneg hErr
      unfold I at hA0 ⊢
      linarith
  · rw [ite_eq_right hc6]
    by_cases hs : sE6 i j k l b c = true
    · have := abs_le.1 (Lv.e6 i j k l hD b hb hK hn c hc' (by simpa using hc6) hs)
      linarith [this.1]
    · have hreg : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + eC b + 2 * eC c := by
        simp only [sE6, Bool.not_eq_true] at hs
        simp only [counted6, hs, Bool.not_false, Bool.and_true, decide_eq_true_eq, not_le] at hc6
        exact hc6
      rw [P.I_S6c_vanish_reg G gA hm hreg, P.I_S6c_vanish_reg G gB hm hreg]
      have : 0 ≤ ec6' * Err := mul_nonneg ec6'_nonneg hErr
      linarith

/-- **Level 5** (terms with sign `−`), for a counted cell `(i, j, k, l)` of depth 4 that is decomposed:
`A ≤ B + (dropped below) + nC·ec5'·Err`. -/
theorem lvl5' [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) {i j k l : ℕ} (hD : Deep' i j k l) :
    P.I gA (P.S5 i j k l) ≤ P.I gB (P.S5 i j k l) + P.E5 gB i j k l + nC * ec5' * Err := by
  rw [P.I_S5 G gA, P.I_S5 G gB]
  unfold E5
  have hErrs : (nC : ℝ) * ec5' * Err = ∑ _b ∈ range nC, ec5' * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b hb => ?_
  have hb' := Finset.mem_range.1 hb
  have h60 := ec6'_nonneg
  have hbn : ((b : ℝ) + 1) * ec6' * Err ≤ nC * ec6' * Err := by
    have : ((b : ℝ) + 1) ≤ nC := by exact_mod_cast hb'
    have := mul_nonneg h60 hErr
    nlinarith
  have hE5 : ec5' * Err = nC * ec6' * Err + 2 * Err := by unfold ec5'; ring
  by_cases hK : inKK5 i j k l b = true
  · by_cases hn : ne5 i j k l b = true
    · rw [ite_eq_left ⟨hK, hn⟩, P.I_S5c gA, P.I_S5c gB, P.I_S5le gA, P.I_S5le gB]
      have h6 := lvl6' G hgA hErr Lv hD hb' hK hn
      have hJ := abs_le.1 (Lv.p5 i j k l hD b hb' hK hn)
      have hE := abs_le.1 (Lv.e5gt i j k l hD b hb' hK hn)
      linarith [hJ.2, hE.2]
    · have hn' : ne5 i j k l b = false := by simpa using hn
      rw [ite_eq_right (show ¬(inKK5 i j k l b = true ∧ ne5 i j k l b = true) from fun h => hn h.2)]
      have hE := abs_le.1 (Lv.e5' i j k l hD b hb' hK hn')
      have : 0 ≤ nC * ec6' * Err := by positivity
      linarith [hE.2]
  · have hK' : inKK5 i j k l b = false := by simpa using hK
    rw [ite_eq_right (show ¬(inKK5 i j k l b = true ∧ ne5 i j k l b = true) from fun h => hK h.1)]
    have hz : ∀ g, P.I g (P.S5c i j k l b) = 0 := by
      intro g
      simp only [SieveCert.inKK5, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, not_le] at hK'
      rcases hK' with h | h
      · exact P.I_S5c_vanish_lt G g (by omega)
      · exact P.I_S5c_vanish_reg G g (SieveCert.RuleNB.nb _ (ok4_of_dec4 hD.2.2.2)) h
    rw [hz gA, hz gB]
    have : 0 ≤ nC * ec6' * Err := by positivity
    linarith

/-- **Level 4** (terms with sign `+`), for a row `(i, j, k)` that is reached: `A ≥ B − (dropped) − (k + 1)·ec4'·Err`. -/
theorem lvl4' [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) {i j k : ℕ} (hR : Row3' i j k) :
    P.I gB (P.S4 i j k) - P.E4 gB i j k - (k + 1) * ec4' * Err ≤ P.I gA (P.S4 i j k) := by
  have hk : k < SieveCert.n := hR.2.1
  have hsub : ∀ g, ∑ l ∈ range SieveCert.n, P.I g (P.S4c i j k l) = ∑ l ∈ range (k + 1), P.I g (P.S4c i j k l) := by
    intro g
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l hl hl' => ?_
    rw [Finset.mem_range] at hl hl'
    exact P.I_S4c_vanish_lt G g (by omega)
  rw [P.I_S4 G gA, P.I_S4 G gB, hsub gA, hsub gB]
  unfold E4
  have hErrs : ((k : ℝ) + 1) * ec4' * Err = ∑ _l ∈ range (k + 1), ec4' * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hec : 1 ≤ ec4' := by
    unfold ec4'
    have := ec5'_nonneg
    have : (0 : ℝ) ≤ nC := Nat.cast_nonneg _
    nlinarith
  have hE0 : Err ≤ ec4' * Err := le_mul_of_one_le_left hErr hec
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 4 P.N₂ (P.S4c i j k l))
  by_cases hc4 : counted4 i j k l = true
  · rw [ite_eq_left hc4]
    by_cases hd4 : Scheme8.dec4 i j k l = true
    · rw [ite_eq_left hd4, P.I_S4c gA, P.I_S4c gB, P.I_S4cle gA, P.I_S4cle gB]
      have hD : Deep' i j k l := ⟨hR, hl', hc4, hd4⟩
      have h5 := lvl5' G hgA hErr Lv hD
      have hJ := abs_le.1 (Lv.p4 i j k l hD)
      have hE := abs_le.1 (Lv.e4gt i j k l hD)
      have : ec4' * Err = nC * ec5' * Err + 2 * Err := by unfold ec4'; ring
      linarith [hJ.1, hE.1]
    · rw [ite_eq_right hd4]
      unfold I at hA0 ⊢
      linarith
  · rw [ite_eq_right hc4]
    by_cases hs : sE4 i j k l = true
    · have := abs_le.1 (Lv.e4 i hR.1.1 j hR.1.2.1 hR.1.2.2.1 hR.1.2.2.2 k hk hR.2.2.1 hR.2.2.2 l hl'
        (by simpa using hc4) hs)
      linarith [this.1]
    · have hreg : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + 2 * SieveCert.e l := by
        simp only [sE4, Bool.not_eq_true] at hs
        simp only [counted4, hs, Bool.not_false, Bool.and_true, decide_eq_true_eq, not_le] at hc4
        exact hc4
      have hm := SieveCert.RuleNB.nb _ (ok3_of_dec2 hR.1.2.2.2 hR.2.1 hR.2.2.1 hR.2.2.2)
      rw [P.I_S4c_vanish_reg G gA hm hreg, P.I_S4c_vanish_reg G gB hm hreg]
      linarith

/-- **Level 3** (terms with sign `−`), for a candidate cell `(i, j)` that is decomposed:
`A ≤ B + (dropped below) + ec2'·Err`. -/
theorem lvl3' [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) {i j : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hcd : cand i j = true ∧ Scheme8.dec2 i j = true) :
    P.I gA (P.S3 i j) ≤ P.I gB (P.S3 i j) + P.E3 gB i j + ec2' * Err := by
  rw [P.I_S3 G gA, P.I_S3 G gB]
  unfold E3
  have hErrs : ec2' * Err = ∑ _k ∈ range SieveCert.n, (ec3' + 2) * Err := by
    unfold ec2'
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hkn : ((k : ℝ) + 1) * ec4' * Err ≤ ec3' * Err := by
    unfold ec3'
    have h1 : ((k : ℝ) + 1) ≤ SieveCert.n := by exact_mod_cast hk'
    have h2 := @ec4'_nonneg
    nlinarith [mul_nonneg h2 hErr]
  have h30 : 0 ≤ ec3' := ec3'_nonneg
  by_cases hkk : inKK i j k = true
  · by_cases hn3 : ne3 i j k = true
    · rw [ite_eq_left ⟨hkk, hn3⟩, P.I_S3c gA, P.I_S3c gB, P.I_S3le gA, P.I_S3le gB]
      have h4 := lvl4' G hgA hErr Lv (i := i) (j := j) (k := k) ⟨⟨hi, hj, hcd.1, hcd.2⟩, hk', hkk, hn3⟩
      have hJ := abs_le.1 (Lv.p3 i hi j hj hcd.1 hcd.2 k hk' hkk hn3)
      have hE := abs_le.1 (Lv.e3 i hi j hj hcd.1 hcd.2 k hk' hkk hn3)
      have : (ec3' + 2) * Err = ec3' * Err + 2 * Err := by ring
      linarith [hJ.2, hE.2]
    · have hn3' : ne3 i j k = false := by simpa using hn3
      rw [ite_eq_right (show ¬(inKK i j k = true ∧ ne3 i j k = true) from fun h => hn3 h.2)]
      have hE := abs_le.1 (Lv.e3' i hi j hj hcd.1 hcd.2 k hk' hkk hn3')
      have : Err ≤ (ec3' + 2) * Err := le_mul_of_one_le_left hErr (by linarith)
      linarith [hE.2]
  · have hkk' : inKK i j k = false := by simpa using hkk
    rw [ite_eq_right (show ¬(inKK i j k = true ∧ ne3 i j k = true) from fun h => hkk h.1),
      P.I_S3c_vanish G gA (SieveCert.RuleNB.nb _ (ok2_of_dec2 hcd.2)) hkk',
      P.I_S3c_vanish G gB (SieveCert.RuleNB.nb _ (ok2_of_dec2 hcd.2)) hkk']
    have : 0 ≤ (ec3' + 2) * Err := by positivity
    linarith

/-- **Level 2** (terms with sign `+`), for a cell `i < n` of `p₁` not inside the window:
`A ≥ B − (dropped) − ec1'·Err`. -/
theorem lvl2' [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) {i : ℕ} (hi : i < SieveCert.n)
    (hW : ¬ inW i) :
    P.I gB (P.S2 i) - P.E2 gB i - ec1' * Err ≤ P.I gA (P.S2 i) := by
  rw [P.I_S2 G gA, P.I_S2 G gB]
  unfold E2
  set c3 : ℝ := ec2' with hc3
  have hc30 : 0 ≤ c3 := ec2'_nonneg
  have hErrs : ec1' * Err = ∑ _j ∈ range SieveCert.n, (c3 + 2) * Err := by
    unfold ec1'
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 2 P.N₂ (P.S2c i j))
  have hE0 : 0 ≤ (c3 + 2) * Err := by positivity
  by_cases hc : cand i j = true
  · by_cases hd : Scheme8.dec2 i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ Scheme8.dec2 i j = false) ∨
          (cand i j = false ∧ sE2 i j = false)) by simp [hc, hd]),
        ite_eq_left (show cand i j = true ∧ Scheme8.dec2 i j = true from ⟨hc, hd⟩), P.I_S2c gA, P.I_S2c gB,
        P.I_S2le gA, P.I_S2le gB]
      have h3 := lvl3' G hgA hErr Lv hi hj' ⟨hc, hd⟩
      have hJ := abs_le.1 (Lv.p2 i hi j hj' hc hd)
      have hE := abs_le.1 (Lv.e2 i hi j hj' hc hd)
      have : (c3 + 2) * Err = c3 * Err + 2 * Err := by ring
      linarith [hJ.1, hE.1]
    · rw [ite_eq_left (show (cand i j = true ∧ Scheme8.dec2 i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inl ⟨hc, by simpa using hd⟩),
        ite_eq_right (show ¬(cand i j = true ∧ Scheme8.dec2 i j = true) from fun h => hd h.2)]
      unfold I at hA0 ⊢
      linarith
  · rw [ite_eq_right (show ¬(cand i j = true ∧ Scheme8.dec2 i j = true) from fun h => hc h.1)]
    by_cases hs : sE2 i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ Scheme8.dec2 i j = false) ∨
          (cand i j = false ∧ sE2 i j = false)) by simp [hc, hs])]
      have hE := abs_le.1 (Lv.e2' i hi hW j hj' (by simpa using hc) hs)
      have : Err ≤ (c3 + 2) * Err := le_mul_of_one_le_left hErr (by linarith)
      linarith [hE.1]
    · rw [ite_eq_left (show (cand i j = true ∧ Scheme8.dec2 i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inr ⟨by simpa using hc, by simpa using hs⟩)]
      unfold I at hA0 ⊢
      linarith

/-- **Level 1** (terms with sign `−`): `A ≤ B + (dropped) + ec0'·Err`. -/
theorem lvl1' [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) :
    P.I gA P.S1 ≤ P.I gB P.S1 + P.E1 gB + ec0' * Err := by
  rw [P.I_S1 G gA, P.I_S1 G gB]
  unfold E1
  set c2 : ℝ := ec1' with hc2
  have hc20 : 0 ≤ c2 := ec1'_nonneg
  have hErrs : ec0' * Err = ∑ _i ∈ range SieveCert.n, (1 + c2) * Err := by
    unfold ec0'
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  by_cases hW : inW i
  · rw [ite_eq_left hW]
    have hE := abs_le.1 (Lv.e1 i hi' hW)
    have : Err ≤ (1 + c2) * Err := le_mul_of_one_le_left hErr (by linarith)
    linarith [hE.2]
  · rw [ite_eq_right hW, P.I_S1c gA, P.I_S1c gB]
    have h2 := lvl2' G hgA hErr Lv hi' hW
    have hJ := abs_le.1 (Lv.p1 i hi' hW)
    have : (1 + c2) * Err = Err + c2 * Err := by ring
    linarith [hJ.2]

/-- **The decomposition's inequality to depth 8.** For a grid with `GridOK` and `GridOKC`, a rule with no boundary
term, a scheme, `P.Good`, weights `g_A ≥ 0` and `g_B`, and leaves within `Err ≥ 0`:
`S(A, z_top) ≥ S(B, z_top) − (the dropped B-terms) − Cdec8·Err`. -/
theorem decomp8 [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves8 gA gB Err) :
    P.T gB - P.E1 gB - Cdec8 * Err ≤ P.T gA := by
  rw [P.T_eq G gA, P.T_eq G gB]
  have h1 := lvl1' G hgA hErr Lv
  have hJ := abs_le.1 Lv.j0
  have : Cdec8 * Err = Err + ec0' * Err := by unfold Cdec8; ring
  linarith [hJ.1]

end Par

end SieveBuch
