/-
# The decomposition to depth 6, with the certificate's classification

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `Par` holds `x`, the sieve's floor `z₀`, its top `z_top`, Proposition 6's `X'` and the range
`(N₁, N₂]`; `Good` is what the decomposition needs of them (`SieveQ.good_of_large` proves it at `x = q^L` for large
`q`), `x^{(DEN−1)/DEN} ≤ N₁` among it. For weights `g`, `T g = S_g(z_top)` and `J0 g = S_g(z₀)` count the
`n ∈ (N₁, N₂]` with no prime factor below `z_top` and `z₀`, weighted by `g`. The families of the tree are lists of
`SieveDecomp` atoms: `S1` (`p₁ ∈ [z₀, z_top)`), its cells `S1c i`, the extensions `S2 i`, `S3 i j`, … `S6 i j k l b`
(one more prime in `[z₀, rt_last)`), their cells `S2c` … `S6c` (the cells of the coarse grid `Gc` at depths 5 and 6),
and the splits `S2le`/`S2gt` … `S5le`/`S5gt` at the box's threshold `Xs`: `X'` for a box that `limOK` passes, `N₁`
for the others (`sp2` … `sp5`).

* `T_eq`, `I_S1` … `I_S6`: for `P.Good`, the exact identities of the decomposition,
  `S(A, z_top) = S(A, z₀) − Σ_{p₁} S(A_{p₁}, p₁)` and so on to depth 6: the cells of each new prime, Buchstab's identity
  on the cells that are decomposed, and the splits at the thresholds.
* `I_S3c_vanish`, `I_S4c_vanish_lt`, `I_S4c_vanish_reg`, … `I_S6c_vanish_reg`: for `P.Good`, the cells outside
  `SieveCert.inKK` at depth 3, and at depths 4 to 6 the cells whose prime would exceed the one before and those outside
  the region, contribute `0`. Outside the region the product of the primes is at most `N₁`, while it times the last
  prime exceeds `N₂`: below a box split at `X'` the product is at most `X'·√X'`, and below a box that the rule takes
  whole it is below `x^{(DEN−1)/DEN}`, by the box's test of no boundary term (`nbOK`).
* `D1`: the dropped terms, as the certificate drops them. At depth 2 the candidate cells that are not decomposed
  (`cand ∧ ¬decR`) and the corner cells (`¬cand ∧ ¬surelyEval`), below a cell `i` of `p₁` outside the window
  (`inW`); at depth 4 the counted cells (`counted4`, `l ≤ k`) below the cells of depth 3 that are split, except those
  that `dec4R` decomposes, and below these the counted cells of depth 6 (`counted6`, `c ≤ b`).
* `Leaves`: the estimates the leaves need, each `|A − B| ≤ Err`: the evaluated families (`e1`, `e2`, `e2'`, `e3`,
  `e3'`, `e4`, `e4gt`, `e5gt`, `e5'`, `e6`) and the families of Proposition 6 (`j0` for `S(z₀)`, `p1` … `p5`).
* `decomp`: for a grid with `GridOK` and `GridOKC`, a rule with `RuleNB`, `P.Good`, weights `g_A ≥ 0` and `g_B`, and
  leaves within `Err ≥ 0`, `S_{g_A}(z_top) ≥ S_{g_B}(z_top) − D1(g_B) − Cdec·Err`, with `Cdec` a polynomial in `n` and
  `nC`.

This is the decomposition with the classification by cells (the grid of `SieveCert.Grid`: `n` cells a side, of side
`H/DEN`, starting at `V/DEN = u₂ − u₁`, and its coarse grid of `nC` cells of side `HC/DEN`). The rule
(`SieveCert.Rule`) says which boxes may be decomposed (`decR`, `dec4R`); with `RuleNB`, a box it passes passes `limOK`
or `nbOK`. A decomposed box is split at `X'` when `limOK` passes it, and is otherwise taken whole, at the threshold
`N₁`, above which it has no term. At depth 1 a cell inside the window is evaluated, the others decomposed. At depth 2
a candidate cell that `decR` allows is split at its threshold (above evaluated, below decomposed), a candidate cell not
allowed is dropped, and a non-candidate cell is evaluated when surely evaluable and dropped otherwise (the corner). At
depth 3 a cell of `inKK` is split at its threshold when not surely evaluable and evaluated otherwise. At depth 4 a
counted cell is dropped, unless `dec4R` allows it, when it is split at its threshold and the part below decomposed
with the coarse cells of `p₅`; the cells that are not counted are evaluated or vanish. At depth 5 a cell of `inKK5` is
split at its threshold when not surely evaluable and evaluated otherwise, and at depth 6 a counted cell is dropped and
the rest are evaluated or vanish.

The proof of `decomp`: `lvl6`, `lvl5`, …, `lvl1`, one level at a time. A dropped term has `A ≥ 0` and costs its
`B`-version; a term with sign `−` is bounded above, so it is evaluated or decomposed, never dropped.

The certificate's grid and rule are parameters (`SieveCert.Grid` and `SieveCert.Rule`, with `GridOK`, `GridOKC` and
`RuleNB` where the Lean takes them); `SieveGrid22240R.grid22240R` with `SieveCert.limRule` is the one the library's
theorem uses.

The file imports `SieveDecomp.lean` and `SieveRule.lean`.
-/
import SieveDecomp
import SieveRule

open Real Finset SieveFamily SieveChain SieveDecomp
open SieveCert (V DEN H U1 U2 cand decR inKK ne3 counted4 surelyEval cell nC eC HC cellC inKK5 ne5 counted6 dec4R lim Gc
  limOK nbOK)

namespace SieveBuch

open Classical

/-- The parameters of the decomposition: `x`, the sieve's floor `z₀`, its top `z_top`, Proposition 6's `X'`, and the
range `(N₁, N₂]`. -/
structure Par where
  x : ℝ
  z₀ : ℕ
  ztop : ℕ
  Xp : ℕ
  N₁ : ℕ
  N₂ : ℕ

section Coarse

variable [SieveCert.Grid]

/-- The atoms of the coarse cell `c` for the prime `t`: `x^{eC_c/DEN} ≤ rt_t < x^{(eC_c + HC)/DEN}`. -/
noncomputable abbrev cellAC {k : ℕ} (t : Fin k) (x : ℝ) (c : ℕ) : List (Atom k) := @cellA (Gc) k t x c

/-- A prime in the coarse cell `c`. -/
abbrev InCC (x : ℝ) (c p : ℕ) : Prop := @InC (Gc) x c p

end Coarse

section Modes

variable [SieveCert.Grid]

/-- The mode of the box `(i, j)`: split at `X'` when it passes `limOK`, whole otherwise. -/
def sp2 (i j : ℕ) : Bool := limOK [cell i, cell j]
/-- The mode of the box `(i, j, k)`. -/
def sp3 (i j k : ℕ) : Bool := limOK [cell i, cell j, cell k]
/-- The mode of the box `(i, j, k, l)`. -/
def sp4 (i j k l : ℕ) : Bool := limOK [cell i, cell j, cell k, cell l]
/-- The mode of the box `(i, j, k, l, b)`, `b` a coarse cell. -/
def sp5 (i j k l b : ℕ) : Bool := limOK [cell i, cell j, cell k, cell l, cellC b]

end Modes

namespace Par

variable (P : Par) [SieveCert.Grid]

/-- A split's threshold: `X'` in the split mode (`s`), `N₁` in the whole one. -/
noncomputable def Xs (s : Bool) : ℝ := if s then (P.Xp : ℝ) else (P.N₁ : ℝ)

omit [SieveCert.Grid] in
theorem Xs_true : P.Xs true = P.Xp := by simp [Xs]

omit [SieveCert.Grid] in
theorem Xs_false : P.Xs false = P.N₁ := by simp [Xs]

/-! ### The families of the tree -/

/-- Depth 1: `p₁ ∈ [z₀, z_top)`. -/
noncomputable def S1 : List (Atom 1) := [Atom.ge 0 P.z₀, Atom.lt 0 P.ztop]
/-- Depth 1, `p₁` in the cell `i`. -/
noncomputable def S1c (i : ℕ) : List (Atom 1) := P.S1 ++ cellA 0 P.x i
/-- Depth 2 below the cell `i`. -/
noncomputable def S2 (i : ℕ) : List (Atom 2) := extS (P.z₀ : ℝ) (P.S1c i)
/-- Depth 2, in the cell `(i, j)`. -/
noncomputable def S2c (i j : ℕ) : List (Atom 2) := P.S2 i ++ cellA 1 P.x j
/-- Depth 2, in the cell `(i, j)`, with `p₁p₂` at most the split's threshold. -/
noncomputable def S2le (i j : ℕ) : List (Atom 2) := P.S2c i j ++ [Atom.prodLe Finset.univ (P.Xs (sp2 i j))]
/-- Depth 2, in the cell `(i, j)`, with `p₁p₂` above the split's threshold. -/
noncomputable def S2gt (i j : ℕ) : List (Atom 2) := P.S2c i j ++ [Atom.prodGt Finset.univ (P.Xs (sp2 i j))]
/-- Depth 3 below `(i, j)`, `p₁p₂` at most the split's threshold. -/
noncomputable def S3 (i j : ℕ) : List (Atom 3) := extS (P.z₀ : ℝ) (P.S2le i j)
/-- Depth 3, in the cell `(i, j, k)`. -/
noncomputable def S3c (i j k : ℕ) : List (Atom 3) := P.S3 i j ++ cellA 2 P.x k
/-- Depth 3, in the cell `(i, j, k)`, with `p₁p₂p₃` at most the split's threshold. -/
noncomputable def S3le (i j k : ℕ) : List (Atom 3) := P.S3c i j k ++ [Atom.prodLe Finset.univ (P.Xs (sp3 i j k))]
/-- Depth 3, in the cell `(i, j, k)`, with `p₁p₂p₃` above the split's threshold. -/
noncomputable def S3gt (i j k : ℕ) : List (Atom 3) := P.S3c i j k ++ [Atom.prodGt Finset.univ (P.Xs (sp3 i j k))]
/-- Depth 4 below `(i, j, k)`, `p₁p₂p₃` at most the split's threshold. -/
noncomputable def S4 (i j k : ℕ) : List (Atom 4) := extS (P.z₀ : ℝ) (P.S3le i j k)
/-- Depth 4, in the cell `(i, j, k, l)`. -/
noncomputable def S4c (i j k l : ℕ) : List (Atom 4) := P.S4 i j k ++ cellA 3 P.x l
/-- Depth 4, in the cell `(i, j, k, l)`, with `p₁p₂p₃p₄` at most the split's threshold. -/
noncomputable def S4cle (i j k l : ℕ) : List (Atom 4) :=
  P.S4c i j k l ++ [Atom.prodLe Finset.univ (P.Xs (sp4 i j k l))]
/-- Depth 4, in the cell `(i, j, k, l)`, with `p₁p₂p₃p₄` above the split's threshold. -/
noncomputable def S4cgt (i j k l : ℕ) : List (Atom 4) :=
  P.S4c i j k l ++ [Atom.prodGt Finset.univ (P.Xs (sp4 i j k l))]
/-- Depth 5 below `(i, j, k, l)`, `p₁p₂p₃p₄` at most the split's threshold. -/
noncomputable def S5 (i j k l : ℕ) : List (Atom 5) := extS (P.z₀ : ℝ) (P.S4cle i j k l)
/-- Depth 5, `p₅` in the coarse cell `b`. -/
noncomputable def S5c (i j k l b : ℕ) : List (Atom 5) := P.S5 i j k l ++ cellAC 4 P.x b
/-- Depth 5, `p₅` in the coarse cell `b`, with `p₁⋯p₅` at most the split's threshold. -/
noncomputable def S5le (i j k l b : ℕ) : List (Atom 5) :=
  P.S5c i j k l b ++ [Atom.prodLe Finset.univ (P.Xs (sp5 i j k l b))]
/-- Depth 5, `p₅` in the coarse cell `b`, with `p₁⋯p₅` above the split's threshold. -/
noncomputable def S5gt (i j k l b : ℕ) : List (Atom 5) :=
  P.S5c i j k l b ++ [Atom.prodGt Finset.univ (P.Xs (sp5 i j k l b))]
/-- Depth 6 below `(i, j, k, l, b)`, `p₁⋯p₅` at most the split's threshold. -/
noncomputable def S6 (i j k l b : ℕ) : List (Atom 6) := extS (P.z₀ : ℝ) (P.S5le i j k l b)
/-- Depth 6, `p₆` in the coarse cell `c`. -/
noncomputable def S6c (i j k l b c : ℕ) : List (Atom 6) := P.S6 i j k l b ++ cellAC 5 P.x c

/-- The terms `S(A_{∏rt}, rt_last)` of a family. -/
noncomputable def I {k' : ℕ} (g : ℕ → ℝ) (spec : List (Atom (k' + 1))) : ℝ :=
  famI g P.N₁ P.N₂ (famSet (k' + 1) P.N₂ spec)

/-- The terms `S(A_{∏rt}, z₀)` of a family. -/
noncomputable def J {k : ℕ} (g : ℕ → ℝ) (spec : List (Atom k)) : ℝ :=
  famJ g P.N₁ P.N₂ P.z₀ (famSet k P.N₂ spec)

/-- `S(A, z_top)`. -/
noncomputable def T (g : ℕ → ℝ) : ℝ := ∑ m ∈ Ioc P.N₁ P.N₂, g m * (if SieveTree.rough P.ztop m then 1 else 0)

/-- `S(A, z₀)`. -/
noncomputable def J0 (g : ℕ → ℝ) : ℝ := ∑ m ∈ Ioc P.N₁ P.N₂, g m * (if SieveTree.rough P.z₀ m then 1 else 0)

/-- What the decomposition needs of the parameters (they hold at `SieveQ.parQ q` for large `q`,
`SieveQ.good_of_large`). -/
structure Good : Prop where
  hx : 1 < P.x
  hz₀ : P.x ^ ((V : ℝ) / DEN) ≤ P.z₀
  hztop : (P.ztop : ℝ) ≤ P.x ^ (((V : ℝ) + SieveCert.n * H) / DEN)
  hz₀top : P.z₀ ≤ P.ztop
  htopN : P.ztop ≤ P.N₂ + 1
  hXN : (P.Xp : ℝ) * Real.sqrt P.Xp ≤ P.N₁
  hN₂ : (P.N₂ : ℝ) < P.x ^ (((DEN : ℝ) + 1) / DEN)
  hN₁ : P.x ^ (((DEN : ℝ) - 1) / DEN) ≤ P.N₁

/-! ### Chains -/

omit [SieveCert.Grid] in
theorem chain_S1 {Y : ℕ} : ∀ rt ∈ famSet 1 Y P.S1, Chain P.z₀ P.ztop rt := by
  intro rt hrt
  have h0 : ((P.z₀ : ℕ) : ℝ) ≤ rt 0 := sem_of_mem hrt (A := Atom.ge 0 P.z₀) (by simp [S1])
  have h1 : (rt 0 : ℝ) < P.ztop := sem_of_mem hrt (A := Atom.lt 0 P.ztop) (by simp [S1])
  refine ⟨fun a b hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _), fun i => ?_, fun i => ?_⟩
  · rw [Fin.fin_one_eq_zero i]; exact_mod_cast h0
  · rw [Fin.fin_one_eq_zero i]; exact_mod_cast h1

theorem chain_S1c {Y : ℕ} (i : ℕ) : ∀ rt ∈ famSet 1 Y (P.S1c i), Chain P.z₀ P.ztop rt :=
  chain_append _ P.chain_S1
theorem chain_S2 {Y : ℕ} (i : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2 i), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S1c i)
theorem chain_S2c {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2c i j), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S2 i)
theorem chain_S2le {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2le i j), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S2c i j)
theorem chain_S2gt {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2gt i j), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S2c i j)
theorem chain_S3 {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3 i j), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S2le i j)
theorem chain_S3c {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3c i j k), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S3 i j)
theorem chain_S3le {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3le i j k), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S3c i j k)
theorem chain_S3gt {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3gt i j k), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S3c i j k)
theorem chain_S4 {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 4 Y (P.S4 i j k), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S3le i j k)
theorem chain_S4c {Y : ℕ} (i j k l : ℕ) : ∀ rt ∈ famSet 4 Y (P.S4c i j k l), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S4 i j k)
theorem chain_S4cle {Y : ℕ} (i j k l : ℕ) : ∀ rt ∈ famSet 4 Y (P.S4cle i j k l), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S4c i j k l)
theorem chain_S4cgt {Y : ℕ} (i j k l : ℕ) : ∀ rt ∈ famSet 4 Y (P.S4cgt i j k l), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S4c i j k l)
theorem chain_S5 {Y : ℕ} (i j k l : ℕ) : ∀ rt ∈ famSet 5 Y (P.S5 i j k l), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S4cle i j k l)
theorem chain_S5c {Y : ℕ} (i j k l b : ℕ) : ∀ rt ∈ famSet 5 Y (P.S5c i j k l b), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S5 i j k l)
theorem chain_S5le {Y : ℕ} (i j k l b : ℕ) : ∀ rt ∈ famSet 5 Y (P.S5le i j k l b), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S5c i j k l b)
theorem chain_S5gt {Y : ℕ} (i j k l b : ℕ) : ∀ rt ∈ famSet 5 Y (P.S5gt i j k l b), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S5c i j k l b)
theorem chain_S6 {Y : ℕ} (i j k l b : ℕ) : ∀ rt ∈ famSet 6 Y (P.S6 i j k l b), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S5le i j k l b)
theorem chain_S6c {Y : ℕ} (i j k l b c : ℕ) : ∀ rt ∈ famSet 6 Y (P.S6c i j k l b c), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S6 i j k l b)

variable {P}

/-- For `P.Good`, a chain's primes lie in the grid. -/
theorem range_of_chain (G : P.Good) {k : ℕ} {rt : Fin k → ℕ} (h : Chain P.z₀ P.ztop rt) (t : Fin k) :
    P.x ^ ((V : ℝ) / DEN) ≤ rt t ∧ (rt t : ℝ) < P.x ^ (((V : ℝ) + SieveCert.n * H) / DEN) := by
  refine ⟨G.hz₀.trans (by exact_mod_cast h.2.1 t), lt_of_lt_of_le (by exact_mod_cast h.2.2 t) G.hztop⟩

omit [SieveCert.Grid] in
theorem last_le_of_chain {k' : ℕ} {rt : Fin (k' + 1) → ℕ} (h : Chain P.z₀ P.ztop rt) :
    (∀ i, rt (Fin.last k') ≤ rt i) ∧ P.z₀ ≤ rt (Fin.last k') :=
  ⟨fun i => h.1.antitone (Fin.le_last i), h.2.1 _⟩

/-! ### The identities of the tree, depth by depth -/

/-- **Depth 0.** For `P.Good`, `S(A, z_top) = S(A, z₀) − Σ_{z₀ ≤ p₁ < z_top} S(A_{p₁}, p₁)`. -/
theorem T_eq (G : P.Good) (g : ℕ → ℝ) : P.T g = P.J0 g - P.I g P.S1 := by
  have hpt : ∀ m ∈ Ioc P.N₁ P.N₂, g m * (if SieveTree.rough P.ztop m then 1 else 0) =
      g m * (if SieveTree.rough P.z₀ m then 1 else 0) -
        ∑ p ∈ SieveTree.primesIco P.z₀ P.ztop, g m * (if p ∣ m ∧ SieveTree.rough p m then 1 else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Ioc.1 hm).1; omega
    have h := buchstab_pt (W := 1) hm0 G.hz₀top (fun p hp hd => absurd (Nat.dvd_one.1 hd) hp.one_lt.ne')
    simp only [one_dvd, true_and, one_mul] at h
    rw [h, mul_sub, Finset.mul_sum]
  unfold T J0 I famI
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_nbij' (fun p => fun _ => p) (fun rt => rt 0) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [SieveTree.mem_primesIco] at hp
    rw [mem_famSet]
    refine ⟨fun _ => ⟨by have := G.htopN; omega, hp.2.2⟩, ?_⟩
    simp only [S1, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, Atom.sem_ge,
      Atom.sem_lt, Nat.cast_le, Nat.cast_lt]
    exact ⟨hp.1, hp.2.1⟩
  · intro rt hrt
    have hc := P.chain_S1 rt hrt
    rw [SieveTree.mem_primesIco]
    exact ⟨hc.2.1 0, hc.2.2 0, ((mem_famSet.1 hrt).1 0).2⟩
  · intro p _
    rfl
  · intro rt _
    funext i
    rw [Fin.fin_one_eq_zero i]
  · intro p _
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_add, pow_one]

/-- **Depth 1**, for a grid with `GridOK` and `P.Good`: the cells of `p₁`. -/
theorem I_S1 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) : P.I g P.S1 = ∑ i ∈ range SieveCert.n, P.I g (P.S1c i) :=
  famI_cells g P.N₁ P.N₂ G.hx P.S1 0 fun rt hrt => range_of_chain G (P.chain_S1 rt hrt) 0

/-- Depth 1: a cell decomposed. -/
theorem I_S1c (g : ℕ → ℝ) (i : ℕ) : P.I g (P.S1c i) = P.J g (P.S1c i) - P.I g (P.S2 i) :=
  buchstab_fam g P.N₁ P.N₂ (P.S1c i) fun rt hrt => last_le_of_chain (P.chain_S1c i rt hrt)

/-- **Depth 2**, for a grid with `GridOK` and `P.Good`: the cells of `p₂`. -/
theorem I_S2 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) (i : ℕ) :
    P.I g (P.S2 i) = ∑ j ∈ range SieveCert.n, P.I g (P.S2c i j) :=
  famI_cells g P.N₁ P.N₂ G.hx (P.S2 i) 1 fun rt hrt => range_of_chain G (P.chain_S2 i rt hrt) 1

/-- Depth 2: a cell split at `p₁p₂ = X'`. -/
theorem I_S2c (g : ℕ → ℝ) (i j : ℕ) : P.I g (P.S2c i j) = P.I g (P.S2le i j) + P.I g (P.S2gt i j) :=
  famI_split g P.N₁ P.N₂ (P.S2c i j) _ _ fun rt => by simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 2: the part `p₁p₂ ≤ X'` decomposed. -/
theorem I_S2le (g : ℕ → ℝ) (i j : ℕ) : P.I g (P.S2le i j) = P.J g (P.S2le i j) - P.I g (P.S3 i j) :=
  buchstab_fam g P.N₁ P.N₂ (P.S2le i j) fun rt hrt => last_le_of_chain (P.chain_S2le i j rt hrt)

/-- **Depth 3**, for a grid with `GridOK` and `P.Good`: the cells of `p₃`. -/
theorem I_S3 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) (i j : ℕ) :
    P.I g (P.S3 i j) = ∑ k ∈ range SieveCert.n, P.I g (P.S3c i j k) :=
  famI_cells g P.N₁ P.N₂ G.hx (P.S3 i j) 2 fun rt hrt => range_of_chain G (P.chain_S3 i j rt hrt) 2

/-- Depth 3: a cell split at `p₁p₂p₃ = X'`. -/
theorem I_S3c (g : ℕ → ℝ) (i j k : ℕ) :
    P.I g (P.S3c i j k) = P.I g (P.S3le i j k) + P.I g (P.S3gt i j k) :=
  famI_split g P.N₁ P.N₂ (P.S3c i j k) _ _ fun rt => by simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 3: the part `p₁p₂p₃ ≤ X'` decomposed. -/
theorem I_S3le (g : ℕ → ℝ) (i j k : ℕ) :
    P.I g (P.S3le i j k) = P.J g (P.S3le i j k) - P.I g (P.S4 i j k) :=
  buchstab_fam g P.N₁ P.N₂ (P.S3le i j k) fun rt hrt => last_le_of_chain (P.chain_S3le i j k rt hrt)

/-- **Depth 4**, for a grid with `GridOK` and `P.Good`: the cells of `p₄`. -/
theorem I_S4 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) (i j k : ℕ) :
    P.I g (P.S4 i j k) = ∑ l ∈ range SieveCert.n, P.I g (P.S4c i j k l) :=
  famI_cells g P.N₁ P.N₂ G.hx (P.S4 i j k) 3 fun rt hrt => range_of_chain G (P.chain_S4 i j k rt hrt) 3

/-- Depth 4: a cell split at `p₁p₂p₃p₄ = X'`. -/
theorem I_S4c (g : ℕ → ℝ) (i j k l : ℕ) :
    P.I g (P.S4c i j k l) = P.I g (P.S4cle i j k l) + P.I g (P.S4cgt i j k l) :=
  famI_split g P.N₁ P.N₂ (P.S4c i j k l) _ _ fun rt => by simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 4: the part `p₁⋯p₄ ≤ X'` decomposed. -/
theorem I_S4cle (g : ℕ → ℝ) (i j k l : ℕ) :
    P.I g (P.S4cle i j k l) = P.J g (P.S4cle i j k l) - P.I g (P.S5 i j k l) :=
  buchstab_fam g P.N₁ P.N₂ (P.S4cle i j k l) fun rt hrt => last_le_of_chain (P.chain_S4cle i j k l rt hrt)

/-- For `P.Good` and a grid with `GridOKC`, a chain's primes lie in the coarse grid. -/
theorem range_of_chain_C [SieveCert.GridOK] [SieveCert.GridOKC] (G : P.Good) {k : ℕ} {rt : Fin k → ℕ}
    (h : Chain P.z₀ P.ztop rt) (t : Fin k) :
    P.x ^ ((V : ℝ) / DEN) ≤ rt t ∧ (rt t : ℝ) < P.x ^ (((V : ℝ) + nC * HC) / DEN) := by
  obtain ⟨h1, h2⟩ := range_of_chain G h t
  refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
  have hD := SieveCert.DEN_pos'
  refine Real.rpow_le_rpow_of_exponent_le G.hx.le (div_le_div_of_nonneg_right ?_ hD.le)
  have : ((SieveCert.n * H : ℕ) : ℝ) ≤ ((nC * HC : ℕ) : ℝ) := by exact_mod_cast SieveCert.GridOKC.cover
  push_cast at this
  linarith

/-- **Depth 5**, for a grid with `GridOKC` and `P.Good`: the coarse cells of `p₅`. -/
theorem I_S5 [SieveCert.GridOK] [SieveCert.GridOKC] (G : P.Good) (g : ℕ → ℝ) (i j k l : ℕ) :
    P.I g (P.S5 i j k l) = ∑ b ∈ range nC, P.I g (P.S5c i j k l b) :=
  @famI_cells (Gc) SieveCert.GridOKC.ok g P.N₁ P.N₂ P.x G.hx 4 P.N₂ (P.S5 i j k l) 4
    fun rt hrt => range_of_chain_C G (P.chain_S5 i j k l rt hrt) 4

/-- Depth 5: a cell split at `p₁⋯p₅ = X'`. -/
theorem I_S5c (g : ℕ → ℝ) (i j k l b : ℕ) :
    P.I g (P.S5c i j k l b) = P.I g (P.S5le i j k l b) + P.I g (P.S5gt i j k l b) :=
  famI_split g P.N₁ P.N₂ (P.S5c i j k l b) _ _ fun rt => by simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 5: the part `p₁⋯p₅ ≤ X'` decomposed. -/
theorem I_S5le (g : ℕ → ℝ) (i j k l b : ℕ) :
    P.I g (P.S5le i j k l b) = P.J g (P.S5le i j k l b) - P.I g (P.S6 i j k l b) :=
  buchstab_fam g P.N₁ P.N₂ (P.S5le i j k l b) fun rt hrt => last_le_of_chain (P.chain_S5le i j k l b rt hrt)

/-- **Depth 6**, for a grid with `GridOKC` and `P.Good`: the coarse cells of `p₆`. -/
theorem I_S6 [SieveCert.GridOK] [SieveCert.GridOKC] (G : P.Good) (g : ℕ → ℝ) (i j k l b : ℕ) :
    P.I g (P.S6 i j k l b) = ∑ c ∈ range nC, P.I g (P.S6c i j k l b c) :=
  @famI_cells (Gc) SieveCert.GridOKC.ok g P.N₁ P.N₂ P.x G.hx 5 P.N₂ (P.S6 i j k l b) 5
    fun rt hrt => range_of_chain_C G (P.chain_S6 i j k l b rt hrt) 5

/-! ### What the families say of their primes -/

theorem facts_S2c {Y : ℕ} {i j : ℕ} {rt : Fin 2 → ℕ} (hrt : rt ∈ famSet 2 Y (P.S2c i j)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) := by
  have h1 : Fin.init rt ∈ famSet 1 Y (P.S1c i) := init_mem hrt fun A hA => List.mem_append_left _ hA
  exact ⟨P.chain_S2c i j rt hrt, inC_of_mem h1 (t := 0) fun A hA => List.mem_append_right _ hA,
    inC_of_mem hrt (t := 1) fun A hA => List.mem_append_right _ hA⟩

theorem facts_S2le {Y : ℕ} {i j : ℕ} {rt : Fin 2 → ℕ} (hrt : rt ∈ famSet 2 Y (P.S2le i j)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) := by
  obtain ⟨h1, h2, h3⟩ := facts_S2c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h4 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xs (sp2 i j) :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ (P.Xs (sp2 i j)))
      (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_two] at h4
  exact ⟨h1, h2, h3, h4⟩

theorem facts_S3c {Y : ℕ} {i j k : ℕ} {rt : Fin 3 → ℕ} (hrt : rt ∈ famSet 3 Y (P.S3c i j k)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧
      (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) := by
  have h2 : Fin.init rt ∈ famSet 2 Y (P.S2le i j) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, h3, h4, h5⟩ := facts_S2le h2
  exact ⟨P.chain_S3c i j k rt hrt, h3, h4, inC_of_mem hrt (t := 2) fun A hA => List.mem_append_right _ hA, h5⟩

theorem facts_S3le {Y : ℕ} {i j k : ℕ} {rt : Fin 3 → ℕ} (hrt : rt ∈ famSet 3 Y (P.S3le i j k)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧
      (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧ (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := facts_S3c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h6 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xs (sp3 i j k) :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ (P.Xs (sp3 i j k)))
      (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_three] at h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem facts_S4c {Y : ℕ} {i j k l : ℕ} {rt : Fin 4 → ℕ} (hrt : rt ∈ famSet 4 Y (P.S4c i j k l)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧ (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) := by
  have h3 : Fin.init rt ∈ famSet 3 Y (P.S3le i j k) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, h4, h5, h6, h7, h8⟩ := facts_S3le h3
  exact ⟨P.chain_S4c i j k l rt hrt, h4, h5, h6, inC_of_mem hrt (t := 3) fun A hA => List.mem_append_right _ hA,
    h7, h8⟩

theorem facts_S4cle {Y : ℕ} {i j k l : ℕ} {rt : Fin 4 → ℕ} (hrt : rt ∈ famSet 4 Y (P.S4cle i j k l)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧ (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xs (sp4 i j k l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := facts_S4c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h8 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xs (sp4 i j k l) :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ (P.Xs (sp4 i j k l)))
      (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_four] at h8
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem facts_S5c {Y : ℕ} {i j k l b : ℕ} {rt : Fin 5 → ℕ} (hrt : rt ∈ famSet 5 Y (P.S5c i j k l b)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      InCC P.x b (rt 4) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧ (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xs (sp4 i j k l) := by
  have h4 : Fin.init rt ∈ famSet 4 Y (P.S4cle i j k l) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7⟩ := facts_S4cle h4
  exact ⟨P.chain_S5c i j k l b rt hrt, a1, a2, a3, a4,
    @inC_of_mem (Gc) 5 Y _ rt hrt 4 P.x b fun A hA => List.mem_append_right _ hA, a5, a6, a7⟩

theorem facts_S5le {Y : ℕ} {i j k l b : ℕ} {rt : Fin 5 → ℕ} (hrt : rt ∈ famSet 5 Y (P.S5le i j k l b)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      InCC P.x b (rt 4) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧ (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xs (sp4 i j k l) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 ≤ P.Xs (sp5 i j k l b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := facts_S5c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h10 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xs (sp5 i j k l b) :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ (P.Xs (sp5 i j k l b)))
      (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_five] at h10
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem facts_S6c {Y : ℕ} {i j k l b c : ℕ} {rt : Fin 6 → ℕ} (hrt : rt ∈ famSet 6 Y (P.S6c i j k l b c)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      InCC P.x b (rt 4) ∧ InCC P.x c (rt 5) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xs (sp2 i j) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xs (sp3 i j k) ∧ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xs (sp4 i j k l) ∧
      (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 ≤ P.Xs (sp5 i j k l b) := by
  have h5 : Fin.init rt ∈ famSet 5 Y (P.S5le i j k l b) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := facts_S5le h5
  exact ⟨P.chain_S6c i j k l b c rt hrt, a1, a2, a3, a4, a5,
    @inC_of_mem (Gc) 6 Y _ rt hrt 5 P.x c fun A hA => List.mem_append_right _ hA, a6, a7, a8, a9⟩

/-! ### Cells that contribute nothing -/

omit [SieveCert.Grid] in
theorem rpow_div_add {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    x ^ (a / DEN) * x ^ (b / DEN) = x ^ ((a + b) / DEN) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

omit [SieveCert.Grid] in
/-- For `x > 0`, four reals at least `x^{a/DEN}`, …, `x^{d/DEN}` have product at least `x^{(a + b + c + d)/DEN}`. -/
theorem prod4_ge {x : ℝ} (hx : 0 < x) {a b c d : ℝ} {p₁ p₂ p₃ p₄ : ℝ} (h1 : x ^ (a / DEN) ≤ p₁)
    (h2 : x ^ (b / DEN) ≤ p₂) (h3 : x ^ (c / DEN) ≤ p₃) (h4 : x ^ (d / DEN) ≤ p₄) :
    x ^ ((a + b + c + d) / DEN) ≤ p₁ * p₂ * p₃ * p₄ := by
  rw [← rpow_div_add hx, ← rpow_div_add hx, ← rpow_div_add hx]
  have h0 : ∀ y : ℝ, 0 ≤ x ^ y := fun y => Real.rpow_nonneg hx.le y
  have hp1 : 0 ≤ p₁ := (h0 _).trans h1
  have hp2 : 0 ≤ p₂ := (h0 _).trans h2
  have hp3 : 0 ≤ p₃ := (h0 _).trans h3
  exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (h0 _) hp1) h3 (h0 _) (mul_nonneg hp1 hp2)) h4 (h0 _)
    (mul_nonneg (mul_nonneg hp1 hp2) hp3)

omit [SieveCert.Grid] in
/-- For `x ≥ 1` and `s > DEN`, `x^{(DEN + 1)/DEN} ≤ x^{s/DEN}`. -/
theorem rpow_region {x : ℝ} (hx : 1 ≤ x) {s : ℕ} (hs : DEN < s) :
    x ^ (((DEN : ℝ) + 1) / DEN) ≤ x ^ ((s : ℝ) / DEN) := by
  have hD := SieveCert.DEN_pos'
  refine Real.rpow_le_rpow_of_exponent_le hx (div_le_div_of_nonneg_right ?_ hD.le)
  have : DEN + 1 ≤ s := hs
  exact_mod_cast this

/-- For `x ≥ 1` and `e_j + H ≤ e_k`, `x^{(e_j + H)/DEN} ≤ x^{e_k/DEN}`. -/
theorem rpow_cell_le {x : ℝ} (hx : 1 ≤ x) {j k : ℕ} (h : SieveCert.e j + H ≤ SieveCert.e k) :
    x ^ (((SieveCert.e j : ℝ) + H) / DEN) ≤ x ^ ((SieveCert.e k : ℝ) / DEN) := by
  have hD := SieveCert.DEN_pos'
  refine Real.rpow_le_rpow_of_exponent_le hx (div_le_div_of_nonneg_right ?_ hD.le)
  exact_mod_cast h

theorem e_add_H_le_of_lt {k l : ℕ} (h : k < l) : SieveCert.e k + H ≤ SieveCert.e l := by
  unfold SieveCert.e
  have : H * k + H ≤ H * l := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left H h
  omega

omit [SieveCert.Grid] in
/-- Lower bounds multiply: `x^{a/DEN} ≤ P` and `x^{b/DEN} ≤ Q` give `x^{(a+b)/DEN} ≤ PQ`. -/
theorem mul_rpow_ge {x : ℝ} (hx : 0 < x) {a b P Q : ℝ} (h1 : x ^ (a / DEN) ≤ P) (h2 : x ^ (b / DEN) ≤ Q) :
    x ^ ((a + b) / DEN) ≤ P * Q := by
  rw [← rpow_div_add hx]
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hx.le _) ((Real.rpow_nonneg hx.le _).trans h1)

omit [SieveCert.Grid] in
/-- Upper bounds multiply: `0 ≤ P ≤ x^{a/DEN}` and `0 ≤ Q ≤ x^{b/DEN}` give `PQ ≤ x^{(a+b)/DEN}`. -/
theorem mul_rpow_le {x : ℝ} (hx : 0 < x) {a b P Q : ℝ} (hQ : 0 ≤ Q) (h1 : P ≤ x ^ (a / DEN))
    (h2 : Q ≤ x ^ (b / DEN)) : P * Q ≤ x ^ ((a + b) / DEN) := by
  rw [← rpow_div_add hx]
  exact mul_le_mul h1 h2 hQ (Real.rpow_nonneg hx.le _)

omit [SieveCert.Grid] in
/-- For `x ≥ 1` and naturals `a ≤ b`, `x^{a/DEN} ≤ x^{b/DEN}`. -/
theorem rpow_mono_nat {x : ℝ} (hx : 1 ≤ x) {a b : ℕ} (h : a ≤ b) :
    x ^ ((a : ℝ) / DEN) ≤ x ^ ((b : ℝ) / DEN) := by
  have hD := SieveCert.DEN_pos'
  exact Real.rpow_le_rpow_of_exponent_le hx (div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le)

omit [SieveCert.Grid] in
/-- The smallest prime of three below `√X'` when the two largest have product at most `X'`. -/
theorem third_lt_sqrt {p₁ p₂ p₃ : ℕ} {X : ℝ} (h21 : p₂ < p₁) (h32 : p₃ < p₂) (h : (p₁ : ℝ) * p₂ ≤ X) :
    (p₃ : ℝ) < Real.sqrt X := by
  rw [Real.lt_sqrt (by positivity)]
  have : p₃ * p₃ < p₁ * p₂ := Nat.mul_lt_mul'' (by omega) h32
  have : (p₃ : ℝ) * p₃ < p₁ * p₂ := by exact_mod_cast this
  nlinarith

omit [SieveCert.Grid] in
/-- For `x ≥ 1` and a real exponent `t` at most the natural `s` with `s < DEN`, `x^{t/DEN} ≤ x^{(DEN − 1)/DEN}`. -/
theorem rpow_le_top {x : ℝ} (hx : 1 ≤ x) {t : ℝ} {s : ℕ} (ht : t ≤ s) (hs : s < DEN) :
    x ^ (t / DEN) ≤ x ^ (((DEN : ℝ) - 1) / DEN) := by
  have hD := SieveCert.DEN_pos'
  refine Real.rpow_le_rpow_of_exponent_le hx (div_le_div_of_nonneg_right ?_ hD.le)
  have : ((s + 1 : ℕ) : ℝ) ≤ DEN := by exact_mod_cast hs
  push_cast at this
  linarith

/-- **A parent's product times a smaller prime is at most `N₁`**, for `P.Good`. In the split mode (`s`), `Q ≤ X'` and
`p < p₂ < p₁` with `p₁p₂ ≤ Q` give `Q·p ≤ X'·√X' ≤ N₁`; in the whole mode, `Q·p ≤ x^{(DEN−1)/DEN} ≤ N₁` when that
bound is given (`hw`). -/
theorem mul_le_N₁ (G : P.Good) {s : Bool} {Q : ℝ} {p₁ p₂ p : ℕ} (hQ : Q ≤ P.Xs s) (h21 : p₂ < p₁) (hp : p < p₂)
    (h12 : (p₁ : ℝ) * p₂ ≤ Q) (hw : s = false → Q * p ≤ P.x ^ (((DEN : ℝ) - 1) / DEN)) : Q * p ≤ P.N₁ := by
  cases s with
  | true =>
    have hQ' : Q ≤ P.Xp := by simpa [Xs] using hQ
    have hsq := third_lt_sqrt h21 hp (h12.trans hQ')
    have hQ0 : 0 ≤ Q := le_trans (by positivity) h12
    calc Q * p ≤ P.Xp * Real.sqrt P.Xp := mul_le_mul hQ' hsq.le (by positivity) (hQ0.trans hQ')
      _ ≤ P.N₁ := G.hXN
  | false => exact (hw rfl).trans G.hN₁

/-- **Depth 3, outside `inKK`**, for `P.Good`: either `p₃` would exceed `p₂`, or `p₁p₂p₃² > N₂` while `p₁p₂p₃ ≤ N₁`. -/
theorem I_S3c_vanish (G : P.Good) (g : ℕ → ℝ) {i j k : ℕ} (hm : sp2 i j = true ∨ nbOK [cell i, cell j] = true)
    (h : inKK i j k = false) : P.I g (P.S3c i j k) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  simp only [inKK, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, not_le] at h
  rcases h with h | h
  · refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
    obtain ⟨hc, -, hj, hk, -⟩ := P.facts_S3c hrt
    have h21 : rt 2 < rt 1 := hc.1 (show (1 : Fin 3) < 2 by decide)
    have : (rt 1 : ℝ) < rt 2 := lt_of_lt_of_le hj.2 ((rpow_cell_le hx1 h).trans hk.1)
    exact absurd h21 (not_lt.2 (by exact_mod_cast this.le))
  · refine famI_vanish g _ _ _ fun rt hrt => ?_
    obtain ⟨hc, hi, hj, hk, hX⟩ := P.facts_S3c hrt
    have h10 : rt 1 < rt 0 := hc.1 (show (0 : Fin 3) < 1 by decide)
    have h21 : rt 2 < rt 1 := hc.1 (show (1 : Fin 3) < 2 by decide)
    rw [Fin.prod_univ_three]
    constructor
    · have : ((rt 0 * rt 1 * rt 2 : ℕ) : ℝ) ≤ P.N₁ := by
        push_cast
        refine P.mul_le_N₁ G hX h10 h21 le_rfl fun hs => ?_
        have hnb := hm.resolve_left (by rw [hs]; simp)
        rw [SieveCert.nbOK_cells2, decide_eq_true_eq] at hnb
        have h21' : (rt 2 : ℝ) ≤ rt 1 := by exact_mod_cast h21.le
        calc (rt 0 : ℝ) * rt 1 * rt 2 ≤ (rt 0 : ℝ) * rt 1 * rt 1 := by gcongr
          _ ≤ P.x ^ (((((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H)) + ((SieveCert.e j : ℝ) + H)) / DEN) :=
              mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) hi.2.le hj.2.le) hj.2.le
          _ ≤ P.x ^ (((DEN : ℝ) - 1) / DEN) := rpow_le_top hx1 (by push_cast; linarith) hnb
      exact_mod_cast this
    · have hp := prod4_ge hx0 hi.1 hj.1 hk.1 hk.1
      have hreg := rpow_region hx1 (s := SieveCert.e i + SieveCert.e j + 2 * SieveCert.e k) (by omega)
      have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt (Fin.last 2) : ℕ) : ℝ) := by
        push_cast
        refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
        congr 1
        push_cast
        ring
      exact_mod_cast this

/-- **Depth 4, `l > k`**, for `P.Good`: `p₄` would exceed `p₃`. -/
theorem I_S4c_vanish_lt (G : P.Good) (g : ℕ → ℝ) {i j k l : ℕ} (h : k < l) : P.I g (P.S4c i j k l) = 0 := by
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
  obtain ⟨hc, -, -, hk, hl, -⟩ := P.facts_S4c hrt
  have h32 : rt 3 < rt 2 := hc.1 (show (2 : Fin 4) < 3 by decide)
  have : (rt 2 : ℝ) < rt 3 := lt_of_lt_of_le hk.2 ((rpow_cell_le hx1 (e_add_H_le_of_lt h)).trans hl.1)
  exact absurd h32 (not_lt.2 (by exact_mod_cast this.le))

/-- **Depth 4, outside the region**, for `P.Good`: `p₁p₂p₃p₄² > N₂` while `p₁p₂p₃p₄ ≤ N₁`. -/
theorem I_S4c_vanish_reg (G : P.Good) (g : ℕ → ℝ) {i j k l : ℕ}
    (hm : sp3 i j k = true ∨ nbOK [cell i, cell j, cell k] = true)
    (h : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + 2 * SieveCert.e l) :
    P.I g (P.S4c i j k l) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_vanish g _ _ _ fun rt hrt => ?_
  obtain ⟨hc, hi, hj, hk, hl, -, hX3⟩ := P.facts_S4c hrt
  have h21 : rt 2 < rt 1 := hc.1 (show (1 : Fin 4) < 2 by decide)
  have h32 : rt 3 < rt 2 := hc.1 (show (2 : Fin 4) < 3 by decide)
  rw [Fin.prod_univ_four]
  constructor
  · have : ((rt 0 * rt 1 * rt 2 * rt 3 : ℕ) : ℝ) ≤ P.N₁ := by
      push_cast
      have h0 : (1 : ℝ) ≤ rt 0 := by exact_mod_cast ((mem_famSet.1 hrt).1 0).2.one_lt.le
      refine P.mul_le_N₁ G hX3 h21 h32 ?_ fun hs => ?_
      · have : (rt 1 : ℝ) * rt 2 ≤ rt 0 * (rt 1 * rt 2) := le_mul_of_one_le_left (by positivity) h0
        linarith
      have hnb := hm.resolve_left (by rw [hs]; simp)
      rw [SieveCert.nbOK_cells3, decide_eq_true_eq] at hnb
      have h32' : (rt 3 : ℝ) ≤ rt 2 := by exact_mod_cast h32.le
      calc (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ (rt 0 : ℝ) * rt 1 * rt 2 * rt 2 := by gcongr
        _ ≤ P.x ^ ((((((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H)) + ((SieveCert.e k : ℝ) + H)) +
              ((SieveCert.e k : ℝ) + H)) / DEN) :=
            mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
              (mul_rpow_le hx0 (by positivity) hi.2.le hj.2.le) hk.2.le) hk.2.le
        _ ≤ P.x ^ (((DEN : ℝ) - 1) / DEN) := rpow_le_top hx1 (by push_cast; linarith) hnb
    exact_mod_cast this
  · have hp4 := prod4_ge hx0 hi.1 hj.1 hk.1 hl.1
    have hp : P.x ^ ((((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + SieveCert.e l) + SieveCert.e l) / DEN) ≤
        (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 3 := by
      rw [← rpow_div_add hx0]
      exact mul_le_mul hp4 hl.1 (by positivity) (by positivity)
    have hreg := rpow_region hx1 (s := SieveCert.e i + SieveCert.e j + SieveCert.e k + 2 * SieveCert.e l) h
    have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt 3 * rt (Fin.last 3) : ℕ) : ℝ) := by
      push_cast
      refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
      congr 1
      push_cast
      ring
    exact_mod_cast this

/-- **The first `m` primes of a tuple are below the limit.** For `x ≥ 1`, four primes in the cells `i, j, k, l`, with
`e_i + H + ⋯ + (e_l + H) ≤ s`, have product at most `x^{s/DEN}`. -/
theorem prod4_le_of_InC {x : ℝ} (hx : 1 ≤ x) {i j k l : ℕ} {p₁ p₂ p₃ p₄ : ℕ} (h1 : InC x i p₁) (h2 : InC x j p₂)
    (h3 : InC x k p₃) (h4 : InC x l p₄) {s : ℕ}
    (hs : SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) ≤ s) :
    (p₁ : ℝ) * p₂ * p₃ * p₄ ≤ x ^ ((s : ℝ) / DEN) := by
  have hx0 : 0 < x := by linarith
  have e1 := h1.2.le
  have e2 := h2.2.le
  have e3 := h3.2.le
  have e4 := h4.2.le
  have := mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
    (mul_rpow_le hx0 (by positivity) e1 e2) e3) e4
  refine this.trans ?_
  have := rpow_mono_nat hx (a := SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H))
    hs
  convert this using 2
  push_cast; ring

/-- **Depth 5, `eC b ≥ e_l + H`**, for `P.Good`: `p₅` would exceed `p₄`. -/
theorem I_S5c_vanish_lt (G : P.Good) (g : ℕ → ℝ) {i j k l b : ℕ} (h : ¬ SieveCert.eC b < SieveCert.e l + H) :
    P.I g (P.S5c i j k l b) = 0 := by
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
  obtain ⟨hc, -, -, -, hl, hb, -⟩ := P.facts_S5c hrt
  have h43 : rt 4 < rt 3 := hc.1 (show (3 : Fin 5) < 4 by decide)
  have hle : SieveCert.e l + H ≤ SieveCert.eC b := by omega
  have := rpow_mono_nat hx1 hle
  have h' : (rt 3 : ℝ) < rt 4 := by
    refine lt_of_lt_of_le hl.2 (le_trans (by push_cast at this ⊢; exact this) hb.1)
  exact absurd h43 (not_lt.2 (by exact_mod_cast h'.le))

/-- **Depth 5, outside the region**, for `P.Good`: `p₁⋯p₅² > N₂` while `p₁⋯p₅ ≤ X'·√X' ≤ N₁` (`p₁⋯p₄ ≤ X'` and
`p₅ < p₃ < √X'`). -/
theorem I_S5c_vanish_reg (G : P.Good) (g : ℕ → ℝ) {i j k l b : ℕ}
    (hm : sp4 i j k l = true ∨ nbOK [cell i, cell j, cell k, cell l] = true)
    (h : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + 2 * SieveCert.eC b) :
    P.I g (P.S5c i j k l b) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_vanish g _ _ _ fun rt hrt => ?_
  obtain ⟨hc, hi, hj, hk, hl, hb, -, -, hX4⟩ := P.facts_S5c hrt
  have h32 : rt 3 < rt 2 := hc.1 (show (2 : Fin 5) < 3 by decide)
  have h43 : rt 4 < rt 3 := hc.1 (show (3 : Fin 5) < 4 by decide)
  rw [Fin.prod_univ_five]
  constructor
  · have : ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 : ℕ) : ℝ) ≤ P.N₁ := by
      push_cast
      have h0 : (1 : ℝ) ≤ rt 0 := by exact_mod_cast ((mem_famSet.1 hrt).1 0).2.one_lt.le
      have h1 : (1 : ℝ) ≤ rt 1 := by exact_mod_cast ((mem_famSet.1 hrt).1 1).2.one_lt.le
      refine P.mul_le_N₁ G hX4 h32 h43 ?_ fun hs => ?_
      · have e1 : (rt 2 : ℝ) * rt 3 ≤ rt 1 * (rt 2 * rt 3) := le_mul_of_one_le_left (by positivity) h1
        have e2 : (rt 1 : ℝ) * (rt 2 * rt 3) ≤ rt 0 * (rt 1 * (rt 2 * rt 3)) :=
          le_mul_of_one_le_left (by positivity) h0
        linarith
      have hnb := hm.resolve_left (by rw [hs]; simp)
      rw [SieveCert.nbOK_cells4, decide_eq_true_eq] at hnb
      have h43' : (rt 4 : ℝ) ≤ rt 3 := by exact_mod_cast h43.le
      calc (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 ≤ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 3 := by gcongr
        _ ≤ P.x ^ (((((((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H)) + ((SieveCert.e k : ℝ) + H)) +
              ((SieveCert.e l : ℝ) + H)) + ((SieveCert.e l : ℝ) + H)) / DEN) :=
            mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
              (mul_rpow_le hx0 (by positivity) hi.2.le hj.2.le) hk.2.le) hl.2.le) hl.2.le
        _ ≤ P.x ^ (((DEN : ℝ) - 1) / DEN) := rpow_le_top hx1 (by push_cast; linarith) hnb
    exact_mod_cast this
  · have hp4 := prod4_ge hx0 hi.1 hj.1 hk.1 hl.1
    have hb1 : P.x ^ (((SieveCert.eC b : ℕ) : ℝ) / DEN) ≤ rt 4 := hb.1
    have hp : P.x ^ ((((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + SieveCert.e l) +
        (SieveCert.eC b : ℕ) + (SieveCert.eC b : ℕ)) / DEN) ≤ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 4 :=
      mul_rpow_ge hx0 (mul_rpow_ge hx0 hp4 hb1) hb1
    have hreg := rpow_region hx1
      (s := SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + 2 * SieveCert.eC b) h
    have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 * rt (Fin.last 4) : ℕ) : ℝ) := by
      push_cast
      refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
      congr 1
      push_cast
      ring
    exact_mod_cast this

/-- **Depth 6, `c > b`**, for `P.Good`: `p₆` would exceed `p₅`. -/
theorem I_S6c_vanish_lt (G : P.Good) (g : ℕ → ℝ) {i j k l b c : ℕ} (h : b < c) :
    P.I g (P.S6c i j k l b c) = 0 := by
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
  obtain ⟨hc, -, -, -, -, hb, hcc, -⟩ := P.facts_S6c hrt
  have h54 : rt 5 < rt 4 := hc.1 (show (4 : Fin 6) < 5 by decide)
  have hle : SieveCert.eC b + HC ≤ SieveCert.eC c := @e_add_H_le_of_lt (Gc) b c h
  have := rpow_mono_nat hx1 hle
  have h' : (rt 4 : ℝ) < rt 5 := by
    refine lt_of_lt_of_le hb.2 (le_trans (by push_cast at this ⊢; exact this) hcc.1)
  exact absurd h54 (not_lt.2 (by exact_mod_cast h'.le))

/-- **Depth 6, outside the region**, for `P.Good`: `p₁⋯p₆² > N₂` while `p₁⋯p₆ ≤ X'·√X' ≤ N₁` (`p₁⋯p₅ ≤ X'` and
`p₆ < p₃ < √X'`). -/
theorem I_S6c_vanish_reg (G : P.Good) (g : ℕ → ℝ) {i j k l b c : ℕ}
    (hm : sp5 i j k l b = true ∨ nbOK [cell i, cell j, cell k, cell l, cellC b] = true)
    (h : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + SieveCert.eC b + 2 * SieveCert.eC c) :
    P.I g (P.S6c i j k l b c) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_vanish g _ _ _ fun rt hrt => ?_
  obtain ⟨hc, hi, hj, hk, hl, hb, hcc, -, -, -, hX5⟩ := P.facts_S6c hrt
  have h43 : rt 4 < rt 3 := hc.1 (show (3 : Fin 6) < 4 by decide)
  have h54 : rt 5 < rt 4 := hc.1 (show (4 : Fin 6) < 5 by decide)
  rw [Fin.prod_univ_six]
  constructor
  · have : ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 : ℕ) : ℝ) ≤ P.N₁ := by
      push_cast
      have h0 : (1 : ℝ) ≤ rt 0 := by exact_mod_cast ((mem_famSet.1 hrt).1 0).2.one_lt.le
      have h1 : (1 : ℝ) ≤ rt 1 := by exact_mod_cast ((mem_famSet.1 hrt).1 1).2.one_lt.le
      have h2 : (1 : ℝ) ≤ rt 2 := by exact_mod_cast ((mem_famSet.1 hrt).1 2).2.one_lt.le
      refine P.mul_le_N₁ G hX5 h43 h54 ?_ fun hs => ?_
      · have e1 : (rt 3 : ℝ) * rt 4 ≤ rt 2 * (rt 3 * rt 4) := le_mul_of_one_le_left (by positivity) h2
        have e2 : (rt 2 : ℝ) * (rt 3 * rt 4) ≤ rt 1 * (rt 2 * (rt 3 * rt 4)) :=
          le_mul_of_one_le_left (by positivity) h1
        have e3 : (rt 1 : ℝ) * (rt 2 * (rt 3 * rt 4)) ≤ rt 0 * (rt 1 * (rt 2 * (rt 3 * rt 4))) :=
          le_mul_of_one_le_left (by positivity) h0
        linarith
      have hnb := hm.resolve_left (by rw [hs]; simp)
      rw [SieveCert.nbOK_cells5, decide_eq_true_eq] at hnb
      have h54' : (rt 5 : ℝ) ≤ rt 4 := by exact_mod_cast h54.le
      have hb2 : (rt 4 : ℝ) ≤ P.x ^ (((SieveCert.eC b : ℝ) + HC) / DEN) := hb.2.le
      calc (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 ≤ (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 4 := by
            gcongr
        _ ≤ P.x ^ ((((((((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H)) + ((SieveCert.e k : ℝ) + H)) +
              ((SieveCert.e l : ℝ) + H)) + ((SieveCert.eC b : ℝ) + HC)) + ((SieveCert.eC b : ℝ) + HC)) / DEN) :=
            mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity)
              (mul_rpow_le hx0 (by positivity) (mul_rpow_le hx0 (by positivity) hi.2.le hj.2.le) hk.2.le) hl.2.le)
              hb2) hb2
        _ ≤ P.x ^ (((DEN : ℝ) - 1) / DEN) := rpow_le_top hx1 (by push_cast; linarith) hnb
    exact_mod_cast this
  · have hp4 := prod4_ge hx0 hi.1 hj.1 hk.1 hl.1
    have hb1 : P.x ^ (((SieveCert.eC b : ℕ) : ℝ) / DEN) ≤ rt 4 := hb.1
    have hc1 : P.x ^ (((SieveCert.eC c : ℕ) : ℝ) / DEN) ≤ rt 5 := hcc.1
    have hp : P.x ^ ((((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + SieveCert.e l) +
        (SieveCert.eC b : ℕ) + (SieveCert.eC c : ℕ) + (SieveCert.eC c : ℕ)) / DEN) ≤
        (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt 5 :=
      mul_rpow_ge hx0 (mul_rpow_ge hx0 (mul_rpow_ge hx0 hp4 hb1) hc1) hc1
    have hreg := rpow_region hx1
      (s := SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + SieveCert.eC b + 2 * SieveCert.eC c) h
    have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt 3 * rt 4 * rt 5 * rt (Fin.last 5) : ℕ) : ℝ) := by
      push_cast
      refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
      congr 1
      push_cast
      ring
    exact_mod_cast this

/-! ### The inequality, level by level -/

/-- The cell `i` of `p₁` lies inside the window: its terms are evaluated at depth 1. -/
def inW (i : ℕ) : Prop := U1 < SieveCert.e i ∧ SieveCert.e i + H < U2

/-- The box `(i, j)` is surely evaluable. -/
def sE2 (i j : ℕ) : Bool := surelyEval [cell i, cell j]

/-- The box `(i, j, k, l)` is surely evaluable. -/
def sE4 (i j k l : ℕ) : Bool := surelyEval [cell i, cell j, cell k, cell l]

/-- The box `(i, j, k, l, b, c)` is surely evaluable. -/
def sE6 (i j k l b c : ℕ) : Bool := surelyEval [cell i, cell j, cell k, cell l, cellC b, cellC c]

/-- The error constants of the levels (`ec4`: one cell of depth 4; `ec3`: its row; `ec2`, `ec1`, `ec0`: the levels
above), and `Cdec` the decomposition's. -/
noncomputable def ec4 : ℝ := (nC : ℝ) * ((nC : ℝ) + 2) + 2
/-- See `ec4`. -/
noncomputable def ec3 : ℝ := (SieveCert.n : ℝ) * ec4
/-- See `ec4`. -/
noncomputable def ec2 : ℝ := (SieveCert.n : ℝ) * (ec3 + 2)
/-- See `ec4`. -/
noncomputable def ec1 : ℝ := (SieveCert.n : ℝ) * (ec2 + 2)
/-- See `ec4`. -/
noncomputable def ec0 : ℝ := (SieveCert.n : ℝ) * (1 + ec1)
/-- The constant of `decomp`: the total error is at most `Cdec·Err`. -/
noncomputable def Cdec : ℝ := 1 + ec0

theorem ec4_nonneg : 0 ≤ ec4 := by unfold ec4; positivity
theorem ec3_nonneg : 0 ≤ ec3 := by unfold ec3; have := ec4_nonneg; positivity
theorem ec2_nonneg : 0 ≤ ec2 := by unfold ec2; have := ec3_nonneg; positivity
theorem ec1_nonneg : 0 ≤ ec1 := by unfold ec1; have := ec2_nonneg; positivity

variable [SieveCert.Rule]

/-- The prefix of the tree down to the row `(i, j, k)`: the cell `(i, j)` is a decomposed candidate and `(i, j, k)` is
in `inKK` and not evaluable. -/
def Row3 (i j k : ℕ) : Prop :=
  (i < SieveCert.n ∧ j < SieveCert.n ∧ cand i j = true ∧ decR i j = true) ∧
    (k < SieveCert.n ∧ inKK i j k = true ∧ ne3 i j k = true)

/-- The prefix down to the cell `(i, j, k, l)` of depth 4 that is counted and decomposed one level further. -/
def Deep (i j k l : ℕ) : Prop := Row3 i j k ∧ l < k + 1 ∧ counted4 i j k l = true ∧ dec4R i j k l = true

variable (P)

/-- The dropped terms of depth 6 below `(i, j, k, l, b)`: the counted cells. -/
noncomputable def D6 (g : ℕ → ℝ) (i j k l b : ℕ) : ℝ :=
  ∑ c ∈ range (b + 1), if counted6 i j k l b c = true then P.I g (P.S6c i j k l b c) else 0

/-- The dropped terms of depth 6 below the counted cell `(i, j, k, l)` of depth 4. -/
noncomputable def D5 (g : ℕ → ℝ) (i j k l : ℕ) : ℝ :=
  ∑ b ∈ range nC, if inKK5 i j k l b = true ∧ ne5 i j k l b = true then P.D6 g i j k l b else 0

/-- The dropped terms of depth 4 below `(i, j, k)`: the counted cells, which are dropped as they are, or, when
decomposed one level further, their counted cells of depth 6. -/
noncomputable def D4 (g : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  ∑ l ∈ range (k + 1), if counted4 i j k l = true then
    (if dec4R i j k l = true then P.D5 g i j k l else P.I g (P.S4c i j k l)) else 0

/-- The dropped terms below the cell `(i, j)`. -/
noncomputable def D3 (g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ range SieveCert.n, if inKK i j k = true ∧ ne3 i j k = true then P.D4 g i j k else 0

/-- The dropped terms below the cell `i`: the cells `(i, j)` dropped (candidates not decomposed, and the corner),
and those below the decomposed cells. -/
noncomputable def D2 (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range SieveCert.n,
    ((if (cand i j = true ∧ decR i j = false) ∨ (cand i j = false ∧ sE2 i j = false) then P.I g (P.S2c i j) else 0) +
      (if cand i j = true ∧ decR i j = true then P.D3 g i j else 0))

/-- All the dropped terms. -/
noncomputable def D1 (g : ℕ → ℝ) : ℝ := ∑ i ∈ range SieveCert.n, if inW i then 0 else P.D2 g i

/-- The leaves' estimates: each evaluated family and each family of Proposition 6 has its `A`- and `B`-sums within
`Err`. -/
structure Leaves (gA gB : ℕ → ℝ) (Err : ℝ) : Prop where
  j0 : |P.J0 gA - P.J0 gB| ≤ Err
  e1 : ∀ i < SieveCert.n, inW i → |P.I gA (P.S1c i) - P.I gB (P.S1c i)| ≤ Err
  p1 : ∀ i < SieveCert.n, ¬ inW i → |P.J gA (P.S1c i) - P.J gB (P.S1c i)| ≤ Err
  e2 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → decR i j = true →
    |P.I gA (P.S2gt i j) - P.I gB (P.S2gt i j)| ≤ Err
  p2 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → decR i j = true →
    |P.J gA (P.S2le i j) - P.J gB (P.S2le i j)| ≤ Err
  e2' : ∀ i < SieveCert.n, ¬ inW i → ∀ j < SieveCert.n, cand i j = false → sE2 i j = true →
    |P.I gA (P.S2c i j) - P.I gB (P.S2c i j)| ≤ Err
  e3 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → decR i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → |P.I gA (P.S3gt i j k) - P.I gB (P.S3gt i j k)| ≤ Err
  p3 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → decR i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → |P.J gA (P.S3le i j k) - P.J gB (P.S3le i j k)| ≤ Err
  e3' : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → decR i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = false → |P.I gA (P.S3c i j k) - P.I gB (P.S3c i j k)| ≤ Err
  e4 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → decR i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → ∀ l < k + 1, counted4 i j k l = false → sE4 i j k l = true →
      |P.I gA (P.S4c i j k l) - P.I gB (P.S4c i j k l)| ≤ Err
  e4gt : ∀ i j k l, Deep i j k l → |P.I gA (P.S4cgt i j k l) - P.I gB (P.S4cgt i j k l)| ≤ Err
  p4 : ∀ i j k l, Deep i j k l → |P.J gA (P.S4cle i j k l) - P.J gB (P.S4cle i j k l)| ≤ Err
  e5gt : ∀ i j k l, Deep i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = true →
    |P.I gA (P.S5gt i j k l b) - P.I gB (P.S5gt i j k l b)| ≤ Err
  p5 : ∀ i j k l, Deep i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = true →
    |P.J gA (P.S5le i j k l b) - P.J gB (P.S5le i j k l b)| ≤ Err
  e5' : ∀ i j k l, Deep i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = false →
    |P.I gA (P.S5c i j k l b) - P.I gB (P.S5c i j k l b)| ≤ Err
  e6 : ∀ i j k l, Deep i j k l → ∀ b < nC, inKK5 i j k l b = true → ne5 i j k l b = true →
    ∀ c < b + 1, counted6 i j k l b c = false → sE6 i j k l b c = true →
      |P.I gA (P.S6c i j k l b c) - P.I gB (P.S6c i j k l b c)| ≤ Err

variable {P}

omit [SieveCert.Rule] in
/-- **Level 6** (terms with sign `+`), for grids with `GridOK` and `GridOKC`, `P.Good`, weights `g_A ≥ 0` and `g_B`,
`b < nC`, the parent box's mode (`hm`), and the row's surely evaluable cells of depth 6 that are not counted within
`Err ≥ 0`:
`A ≥ B − (dropped) − (b + 1)Err`. -/
theorem lvl6 [SieveCert.GridOK] [SieveCert.GridOKC] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ}
    (hErr : 0 ≤ Err) {i j k l b : ℕ} (hb : b < nC)
    (hm : sp5 i j k l b = true ∨ nbOK [cell i, cell j, cell k, cell l, cellC b] = true)
    (hE : ∀ c < b + 1, counted6 i j k l b c = false → sE6 i j k l b c = true →
      |P.I gA (P.S6c i j k l b c) - P.I gB (P.S6c i j k l b c)| ≤ Err) :
    P.I gB (P.S6 i j k l b) - P.D6 gB i j k l b - (b + 1) * Err ≤ P.I gA (P.S6 i j k l b) := by
  have hsub : ∀ g, ∑ c ∈ range nC, P.I g (P.S6c i j k l b c) = ∑ c ∈ range (b + 1), P.I g (P.S6c i j k l b c) := by
    intro g
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun c hc hc' => ?_
    rw [Finset.mem_range] at hc hc'
    exact P.I_S6c_vanish_lt G g (by omega)
  rw [P.I_S6 G gA, P.I_S6 G gB, hsub gA, hsub gB]
  unfold D6
  have hErrs : ((b : ℝ) + 1) * Err = ∑ _c ∈ range (b + 1), Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun c hc => ?_
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 6 P.N₂ (P.S6c i j k l b c))
  by_cases hc6 : counted6 i j k l b c = true
  · rw [ite_eq_left hc6]
    unfold I
    linarith
  · rw [ite_eq_right hc6]
    by_cases hs : sE6 i j k l b c = true
    · have := abs_le.1 (hE c (Finset.mem_range.1 hc) (by simpa using hc6) hs)
      linarith [this.1]
    · have hreg : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + eC b + 2 * eC c := by
        simp only [sE6, Bool.not_eq_true] at hs
        simp only [counted6, hs, Bool.not_false, Bool.and_true, decide_eq_true_eq, not_le] at hc6
        exact hc6
      rw [P.I_S6c_vanish_reg G gA hm hreg, P.I_S6c_vanish_reg G gB hm hreg]
      linarith

/-- **Level 5** (terms with sign `−`), for grids with `GridOK` and `GridOKC`, a rule with no boundary term, `P.Good`,
weights `g_A ≥ 0` and `g_B`, leaves within `Err ≥ 0`, and a counted cell `(i, j, k, l)` of depth 4 that is decomposed:
`A ≤ B + (dropped below) + nC(nC + 2)Err`. -/
theorem lvl5 [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves gA gB Err) {i j k l : ℕ} (hD : Deep i j k l) :
    P.I gA (P.S5 i j k l) ≤ P.I gB (P.S5 i j k l) + P.D5 gB i j k l + nC * (nC + 2) * Err := by
  rw [P.I_S5 G gA, P.I_S5 G gB]
  unfold D5
  have hErrs : (nC : ℝ) * ((nC : ℝ) + 2) * Err = ∑ _b ∈ range nC, ((nC : ℝ) + 2) * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b hb => ?_
  have hb' := Finset.mem_range.1 hb
  have hbn : ((b : ℝ) + 1) * Err ≤ nC * Err := mul_le_mul_of_nonneg_right (by exact_mod_cast hb') hErr
  by_cases hK : inKK5 i j k l b = true
  · by_cases hn : ne5 i j k l b = true
    · rw [ite_eq_left ⟨hK, hn⟩, P.I_S5c gA, P.I_S5c gB, P.I_S5le gA, P.I_S5le gB]
      have h6 := lvl6 G hgA hErr hb' (SieveCert.RuleNB.nb _ (SieveCert.ok5_of_dec4R hD.2.2.2 hb' hK hn))
        (Lv.e6 i j k l hD b hb' hK hn)
      have hJ := abs_le.1 (Lv.p5 i j k l hD b hb' hK hn)
      have hE := abs_le.1 (Lv.e5gt i j k l hD b hb' hK hn)
      have : ((nC : ℝ) + 2) * Err = nC * Err + 2 * Err := by ring
      linarith [hJ.2, hE.2]
    · have hn' : ne5 i j k l b = false := by simpa using hn
      rw [ite_eq_right (show ¬(inKK5 i j k l b = true ∧ ne5 i j k l b = true) from fun h => hn h.2)]
      have hE := abs_le.1 (Lv.e5' i j k l hD b hb' hK hn')
      have : Err ≤ ((nC : ℝ) + 2) * Err :=
        le_mul_of_one_le_left hErr (by have : (0 : ℝ) ≤ nC := Nat.cast_nonneg _; linarith)
      linarith [hE.2]
  · have hK' : inKK5 i j k l b = false := by simpa using hK
    rw [ite_eq_right (show ¬(inKK5 i j k l b = true ∧ ne5 i j k l b = true) from fun h => hK h.1)]
    have hz : ∀ g, P.I g (P.S5c i j k l b) = 0 := by
      intro g
      simp only [SieveCert.inKK5, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, not_le] at hK'
      rcases hK' with h | h
      · exact P.I_S5c_vanish_lt G g (by omega)
      · exact P.I_S5c_vanish_reg G g (SieveCert.RuleNB.nb _ (SieveCert.ok4_of_dec4R hD.2.2.2)) h
    rw [hz gA, hz gB]
    have : 0 ≤ ((nC : ℝ) + 2) * Err := by positivity
    linarith

/-- **Level 4** (terms with sign `+`), for grids with `GridOK` and `GridOKC`, a rule with no boundary term, `P.Good`,
weights `g_A ≥ 0` and `g_B`, leaves within `Err ≥ 0` and a row `(i, j, k)` that is reached:
`A ≥ B − (dropped) − (k + 1)·ec4·Err`. -/
theorem lvl4 [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves gA gB Err) {i j k : ℕ} (hR : Row3 i j k) :
    P.I gB (P.S4 i j k) - P.D4 gB i j k - (k + 1) * ec4 * Err ≤ P.I gA (P.S4 i j k) := by
  have hk : k < SieveCert.n := hR.2.1
  have hsub : ∀ g, ∑ l ∈ range SieveCert.n, P.I g (P.S4c i j k l) = ∑ l ∈ range (k + 1), P.I g (P.S4c i j k l) := by
    intro g
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l hl hl' => ?_
    rw [Finset.mem_range] at hl hl'
    exact P.I_S4c_vanish_lt G g (by omega)
  rw [P.I_S4 G gA, P.I_S4 G gB, hsub gA, hsub gB]
  unfold D4
  have hErrs : ((k : ℝ) + 1) * ec4 * Err = ∑ _l ∈ range (k + 1), ec4 * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hec : 1 ≤ ec4 := by
    unfold ec4
    have : (0 : ℝ) ≤ nC := Nat.cast_nonneg _
    nlinarith
  have hE0 : Err ≤ ec4 * Err := le_mul_of_one_le_left hErr hec
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 4 P.N₂ (P.S4c i j k l))
  by_cases hc4 : counted4 i j k l = true
  · rw [ite_eq_left hc4]
    by_cases hd4 : dec4R i j k l = true
    · rw [ite_eq_left hd4, P.I_S4c gA, P.I_S4c gB, P.I_S4cle gA, P.I_S4cle gB]
      have hD : Deep i j k l := ⟨hR, hl', hc4, hd4⟩
      have h5 := P.lvl5 G hgA hErr Lv hD
      have hJ := abs_le.1 (Lv.p4 i j k l hD)
      have hE := abs_le.1 (Lv.e4gt i j k l hD)
      have : ec4 * Err = nC * (nC + 2) * Err + 2 * Err := by unfold ec4; ring
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
      have hm := SieveCert.RuleNB.nb _ (SieveCert.ok3_of_decR hR.1.2.2.2 hR.2.1 hR.2.2.1 hR.2.2.2)
      rw [P.I_S4c_vanish_reg G gA hm hreg, P.I_S4c_vanish_reg G gB hm hreg]
      linarith

/-- **Level 3** (terms with sign `−`), for grids with `GridOK` and `GridOKC`, a rule with no boundary term, `P.Good`,
weights `g_A ≥ 0` and `g_B`, leaves within `Err ≥ 0`, and a candidate cell `(i, j)` that is decomposed:
`A ≤ B + (dropped below) + ec2·Err`. -/
theorem lvl3 [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves gA gB Err) {i j : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n)
    (hcd : cand i j = true ∧ decR i j = true) :
    P.I gA (P.S3 i j) ≤ P.I gB (P.S3 i j) + P.D3 gB i j + ec2 * Err := by
  rw [P.I_S3 G gA, P.I_S3 G gB]
  unfold D3
  have hErrs : ec2 * Err = ∑ _k ∈ range SieveCert.n, (ec3 + 2) * Err := by
    unfold ec2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hkn : ((k : ℝ) + 1) * ec4 * Err ≤ ec3 * Err := by
    unfold ec3
    have h1 : ((k : ℝ) + 1) ≤ SieveCert.n := by exact_mod_cast hk'
    have h2 := @ec4_nonneg
    nlinarith [mul_nonneg h2 hErr]
  have h30 : 0 ≤ ec3 := ec3_nonneg
  by_cases hkk : inKK i j k = true
  · by_cases hn3 : ne3 i j k = true
    · rw [ite_eq_left ⟨hkk, hn3⟩, P.I_S3c gA, P.I_S3c gB, P.I_S3le gA, P.I_S3le gB]
      have h4 := lvl4 G hgA hErr Lv (i := i) (j := j) (k := k) ⟨⟨hi, hj, hcd.1, hcd.2⟩, hk', hkk, hn3⟩
      have hJ := abs_le.1 (Lv.p3 i hi j hj hcd.1 hcd.2 k hk' hkk hn3)
      have hE := abs_le.1 (Lv.e3 i hi j hj hcd.1 hcd.2 k hk' hkk hn3)
      have : (ec3 + 2) * Err = ec3 * Err + 2 * Err := by ring
      linarith [hJ.2, hE.2]
    · have hn3' : ne3 i j k = false := by simpa using hn3
      rw [ite_eq_right (show ¬(inKK i j k = true ∧ ne3 i j k = true) from fun h => hn3 h.2)]
      have hE := abs_le.1 (Lv.e3' i hi j hj hcd.1 hcd.2 k hk' hkk hn3')
      have : Err ≤ (ec3 + 2) * Err := le_mul_of_one_le_left hErr (by linarith)
      linarith [hE.2]
  · have hkk' : inKK i j k = false := by simpa using hkk
    rw [ite_eq_right (show ¬(inKK i j k = true ∧ ne3 i j k = true) from fun h => hkk h.1),
      P.I_S3c_vanish G gA (SieveCert.RuleNB.nb _ (SieveCert.ok2_of_decR hcd.2)) hkk',
      P.I_S3c_vanish G gB (SieveCert.RuleNB.nb _ (SieveCert.ok2_of_decR hcd.2)) hkk']
    have : 0 ≤ (ec3 + 2) * Err := by positivity
    linarith

/-- **Level 2** (terms with sign `+`), for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, leaves within
`Err ≥ 0`, and a cell `i < n` of `p₁` not inside the window: `A ≥ B − (dropped) − ec1·Err`. -/
theorem lvl2 [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves gA gB Err) {i : ℕ} (hi : i < SieveCert.n)
    (hW : ¬ inW i) :
    P.I gB (P.S2 i) - P.D2 gB i - ec1 * Err ≤
      P.I gA (P.S2 i) := by
  rw [P.I_S2 G gA, P.I_S2 G gB]
  unfold D2
  set c3 : ℝ := ec2 with hc3
  have hc30 : 0 ≤ c3 := ec2_nonneg
  have hErrs : ec1 * Err = ∑ _j ∈ range SieveCert.n, (c3 + 2) * Err := by
    unfold ec1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 2 P.N₂ (P.S2c i j))
  have hE0 : 0 ≤ (c3 + 2) * Err := by positivity
  by_cases hc : cand i j = true
  · by_cases hd : decR i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ decR i j = false) ∨ (cand i j = false ∧ sE2 i j = false)) by
          simp [hc, hd]),
        ite_eq_left (show cand i j = true ∧ decR i j = true from ⟨hc, hd⟩), P.I_S2c gA, P.I_S2c gB, P.I_S2le gA,
        P.I_S2le gB]
      have h3 := lvl3 G hgA hErr Lv hi hj' ⟨hc, hd⟩
      have hJ := abs_le.1 (Lv.p2 i hi j hj' hc hd)
      have hE := abs_le.1 (Lv.e2 i hi j hj' hc hd)
      have : (c3 + 2) * Err = c3 * Err + 2 * Err := by ring
      linarith [hJ.1, hE.1]
    · rw [ite_eq_left (show (cand i j = true ∧ decR i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inl ⟨hc, by simpa using hd⟩),
        ite_eq_right (show ¬(cand i j = true ∧ decR i j = true) from fun h => hd h.2)]
      unfold I at hA0 ⊢
      linarith
  · rw [ite_eq_right (show ¬(cand i j = true ∧ decR i j = true) from fun h => hc h.1)]
    by_cases hs : sE2 i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ decR i j = false) ∨ (cand i j = false ∧ sE2 i j = false)) by
          simp [hc, hs])]
      have hE := abs_le.1 (Lv.e2' i hi hW j hj' (by simpa using hc) hs)
      have : Err ≤ (c3 + 2) * Err := le_mul_of_one_le_left hErr (by linarith)
      linarith [hE.1]
    · rw [ite_eq_left (show (cand i j = true ∧ decR i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inr ⟨by simpa using hc, by simpa using hs⟩)]
      unfold I at hA0 ⊢
      linarith

/-- **Level 1** (terms with sign `−`), for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, and leaves
within `Err ≥ 0`: `A ≤ B + (dropped) + ec0·Err`. -/
theorem lvl1 [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves gA gB Err) :
    P.I gA P.S1 ≤ P.I gB P.S1 + P.D1 gB + ec0 * Err := by
  rw [P.I_S1 G gA, P.I_S1 G gB]
  unfold D1
  set c2 : ℝ := ec1 with hc2
  have hc20 : 0 ≤ c2 := ec1_nonneg
  have hErrs : ec0 * Err = ∑ _i ∈ range SieveCert.n, (1 + c2) * Err := by
    unfold ec0
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
    have h2 := lvl2 G hgA hErr Lv hi' hW
    have hJ := abs_le.1 (Lv.p1 i hi' hW)
    have : (1 + c2) * Err = Err + c2 * Err := by ring
    linarith [hJ.2]

/-- **The decomposition's inequality.** For a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, and leaves
within `Err ≥ 0`: `S(A, z_top) ≥ S(B, z_top) − (the dropped B-terms) − C·Err`, `C = Cdec`. -/
theorem decomp [SieveCert.GridOK] [SieveCert.GridOKC] [SieveCert.RuleNB] (G : P.Good) {gA gB : ℕ → ℝ}
    (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err) (Lv : P.Leaves gA gB Err) :
    P.T gB - P.D1 gB - Cdec * Err ≤ P.T gA := by
  rw [P.T_eq G gA, P.T_eq G gB]
  have h1 := lvl1 G hgA hErr Lv
  have hJ := abs_le.1 Lv.j0
  have : Cdec * Err = Err + ec0 * Err := by unfold Cdec; ring
  linarith [hJ.1]

end Par

end SieveBuch
