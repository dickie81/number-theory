import Mathlib

/-!
# Orbits, V-tops, the tile condition and the frames of the local theorems

The orbit vocabulary of the two local theorems of the gain (L5 and L6), written once for both and for the design:
one orbit of length `n′` at an inert prime, its tops, the V-tops, the distance back to the previous V-top, L5's
segment condition, the tile condition (a *good set*), and L6's frame systems (N3's output) with their segments,
loose letters, pushes, rows and anchors.

**Conventions** (shared by `SymbolData`, `ChainData` and the pieces N3, N7, N8, N13–N15 of L6, and L5's
`first_local`).
* *Positions.* An orbit has `n′` positions `Fin n′`; `TT : Finset (Fin n′)` is the set of tops. A *V-top* is a top at
  an even position (`vTops`): at even positions the flat model has vector letters, at odd ones covector letters
  (`LetterFock.vecF`), and `n′` is even in both theorems, so parity is well defined cyclically.
* *Lifted positions.* Frames live on the integers: `x ∈ ℤ` reads the position `posOf n′ x = x mod n′`, and `x` is a
  top when `posOf n′ x ∈ TT` (`IsTop`). For even `n′`, `x` and `posOf n′ x` have the same parity
  (`even_posOf_iff`). The segment letters of `SymbolData` are lifted positions; `pos` of a letter of the flat model
  (`LetterFock`, letters `Fin n′`) or of `TwistedDegree` (letters `ℕ`, positions `pos : ℕ → ℕ`) is read through
  `posOf` or, for an increasing enumeration, through `lateAt`.
* *Windows and distances.* All windows are cyclic and read forward: `winCount TT s L` counts the `i < L` with
  `(s + i) mod n′` a top. `AfterV TT y d` says that `y` lies `d` positions after a V-top; `prevVDist TT y` is the
  least such `d ≥ 1`, the distance back to the previous V-top (it is in `[1, n′]` once there is a V-top,
  `prevVDist_spec`).

**L5's segments** (`SegOK TT G′ N₁`): at least two V-tops; after every V-top the next one comes within `G′`
positions, with at most `N₁` tops (necessarily odd) strictly between.

**The tile condition** (`IsGoodSet TT L₂ K r u M₀ G′ N₁`, the design's good set of M-G3, here for an abstract orbit):
(A) every cyclic window of `L₂` positions holds at most `K` tops; (T) cutting `[0, n′)` into `⌊n′/((6r + 1)u)⌋` blocks
of `6r + 1` cells of `u` positions, a block is *marked* when its odd cells hold no top and each even cell exactly one,
at an even position, and every run of `M₀ + 1` consecutive blocks (cyclically) holds a marked one; (I) every cyclic
window of `G′` positions holds at most `N₁` tops. The fields mirror the design's `TilePar.IsGood` (module
`DesignOrbits`) for the position set `TT.map Fin.valEmbedding`, field by field; `DesignOrbits` should instantiate
this definition rather than restate it. L6 uses it with `K = r − 1`.

**Frames** (N3; `FrameSys n′ r`): `J` and lifted positions `f j i` (`j ∈ ℤ`, `i < r`), the rows of the frame `j`;
`z j = f j (r − 1)` is its end. With `TT` fixed:
* `seg j` = the tops in `[f (j − 1) 0, z j]`; its letters `≤ z (j − 1)` are the *W-letters* (inherited: the rows of
  the frame `j − 1`), the others the *late* letters `late j`; `loose j` = the tops strictly between `z (j − 1)` and
  `f j 0`, `nL j` their number, `looseAt j l` the `l`-th of them (from `0`, increasing).
* `lateAt j u` (`posN(j, u)` of the readers) is the `u`-th late letter from `0`: the loose letters for `u < nL j`, then
  the frame rows, `lateAt j (nL j + i) = f j i` (`lateAt_nL_add`). In `ChainData` the frame row `m` of the segment `j`
  is `f j (r − 1 − m)`, so `m = 0` is `z j`: chain order index `nL j + (r − 1 − m)`.
* `push j x = z j − x` (as a natural number); `rows j x` = the `r` most recent even letters of `seg j` strictly before
  `x`, increasing; `anchor j x = rows j x 0`, the oldest of them.
* `Proper TT L₁` (V1–V7, V9 of the L6 sub-spec): `1 ≤ J`; periodicity `f (j + J) i = f j i + n′`; rows strictly
  increasing; `z j < f (j + 1) 0`; rows are even tops; no top strictly between consecutive rows; `r ≤ nL j`; the first
  and the last `r` loose letters are even, with every earlier letter of the segment more than `L₁` before them; every
  letter of the segment before `f j 0` is more than `L₁` before it; `x − anchor j x > L₁` at every late `x`.
  `Bounded TT G′ Ns`: `z j − f (j − 1) 0 < G′` and `#seg j ≤ Ns`.

**Main results** (the well-definedness and the counts the pieces read).
* `prevVDist_spec`: the distance back to the previous V-top is attained, in `[1, n′]`.
* Rows (`rows_mem`, `rows_strictMono`, `Proper.le_card_evBefore`, `Proper.anchor_mem_seg`,
  `card_evBefore_ge_anchor`, `Proper.anchor_lt_f`): for a late letter `x` the rows are `r` distinct even letters of
  `seg j` before `x`, and they are all the even letters of `seg j` in `[anchor j x, x)`; the anchor is a W-letter or a
  loose letter. The `r` rows of the previous frame witness `r` even letters before `x`.
* Pushes (`push_le_push_first`, `Proper.push_add_lt_push_anchor`): the first letter of a segment has the largest push,
  and the anchor is pushed more than `L₁` further than its letter.
* Decompositions (`Proper.late_eq`, `Proper.seg_eq`, `Proper.card_late`): `late j = loose j ⊔ {f j i}` and
  `seg j = {f (j − 1) i} ⊔ late j`, since a top between the first and the last row of a frame is a row
  (`Proper.exists_row_of_top`).
* The enumeration (`Proper.lateAt_strictMono`, `Proper.lateAt_mem_late`): `lateAt j` is strictly increasing on
  `[0, nL j + r)`, into `late j`.
* Periodicity (`Proper.seg_add_J`, `Proper.late_add_J`, `Proper.loose_add_J`, `Proper.nL_add_J`,
  `Proper.push_add_J`).
* Tiling (`Proper.sum_late`, `Proper.sum_card_late`): the late letters of the segments `j < J` read every top exactly
  once, `Σ_{j<J} Σ_{x ∈ late j} φ(x mod n′) = Σ_{t ∈ TT} φ(t)`: the late letters of `j` are the tops in
  `(z (j − 1), z j]`, these windows tile `(z (−1), z (−1) + n′]`, and reduction mod `n′` is a bijection from the tops
  of a window of length `n′` onto `TT`.
* Number of frames (`Proper.lt_J_mul`, `Proper.three_lt_J`): `n′ < J·G′`, so `3G′ ≤ n′` gives `J ≥ 4`.

**Readings of the planning statements.** The L5/L6 spec's scratch `IsGoodSet` reads (T) non-cyclically and over
all block indices, which no finite orbit satisfies (a block beyond `n′` has empty cells); the cyclic reading over the
`⌊n′/((6r + 1)u)⌋` full blocks is the design's. The L6 sub-spec's `J ≥ 3` from `3G′ ≤ n′` is in fact `J ≥ 4`. Its
"gap `> L₁` to the predecessor" of a loose letter is read as "every earlier letter of the segment is more than `L₁`
before it" (the predecessor is the latest of them). The construction of frames from a good set (N3) and the
implication good set ⇒ `SegOK` are not part of this module.
-/

namespace LocalOrbit

open Finset

/-! ## Orbits: V-tops, the previous V-top, segments and the tile condition -/

section Orbit

variable {n' : ℕ}

/-- **The V-tops**: the tops at even positions. -/
def vTops (TT : Finset (Fin n')) : Finset (Fin n') := TT.filter fun s => Even s.val

/-- **`y` lies `d` positions after a V-top** (cyclically). -/
def AfterV (TT : Finset (Fin n')) (y : Fin n') (d : ℕ) : Prop := ∃ x ∈ vTops TT, (x.val + d) % n' = y.val

/-- **The distance back to the previous V-top**: the least `d ≥ 1` with `y` lying `d` positions after a V-top
(`0` if there is no V-top); the design's `prevV n′ P y` for `P = TT.map Fin.valEmbedding`. -/
noncomputable def prevVDist (TT : Finset (Fin n')) (y : Fin n') : ℕ := sInf {d | 1 ≤ d ∧ AfterV TT y d}

/-- **The previous V-top is attained**: with a V-top, `prevVDist TT y ∈ [1, n′]` and `y` lies `prevVDist TT y`
positions after a V-top. -/
theorem prevVDist_spec {TT : Finset (Fin n')} (h : (vTops TT).Nonempty) (y : Fin n') :
    1 ≤ prevVDist TT y ∧ prevVDist TT y ≤ n' ∧ AfterV TT y (prevVDist TT y) := by
  obtain ⟨x, hx⟩ := h
  have hy := y.isLt
  have hxn := x.isLt
  set t := y.val + n' - x.val - 1 with ht
  have hdiv := Nat.mod_add_div t n'
  have hq : t / n' < 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  have hrem := Nat.mod_lt t (show 0 < n' by omega)
  have hmem : 1 ≤ t % n' + 1 ∧ AfterV TT y (t % n' + 1) := by
    refine ⟨by omega, x, hx, ?_⟩
    interval_cases hq' : t / n'
    · rw [show x.val + (t % n' + 1) = y.val + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
    · rw [show x.val + (t % n' + 1) = y.val by omega, Nat.mod_eq_of_lt hy]
  have hS : prevVDist TT y ∈ {d | 1 ≤ d ∧ AfterV TT y d} := Nat.sInf_mem ⟨_, hmem⟩
  exact ⟨hS.1, (Nat.sInf_le hmem).trans (by omega), hS.2⟩

open Classical in
/-- **L5's segment condition**: at least two V-tops; after every V-top `x` the next V-top is at a distance
`d ∈ [1, G′]`, with no V-top and at most `N₁` tops strictly between. -/
def SegOK (TT : Finset (Fin n')) (G' N₁ : ℕ) : Prop :=
  2 ≤ (vTops TT).card ∧ ∀ x ∈ vTops TT, ∃ d, 1 ≤ d ∧ d ≤ G' ∧ (∃ y ∈ vTops TT, y.val = (x.val + d) % n') ∧
    (∀ d' ∈ Ico 1 d, ∀ y ∈ vTops TT, y.val ≠ (x.val + d') % n') ∧
    (TT.filter fun y : Fin n' => ∃ d' ∈ Ico 1 d, y.val = (x.val + d') % n').card ≤ N₁

/-- **The tops in a cyclic window**: `#{i < L : (s + i) mod n′ is a top}`. -/
def winCount (TT : Finset (Fin n')) (s L : ℕ) : ℕ :=
  ((range L).filter fun i => (s + i) % n' ∈ TT.map Fin.valEmbedding).card

/-- **The length of a block** of the tile condition: `6r + 1` cells of length `u`. -/
def blockLen (r u : ℕ) : ℕ := (6 * r + 1) * u

/-- **The tops in the cell `i` of the block `b`**: the positions in `[b(6r + 1)u + iu, b(6r + 1)u + (i + 1)u)`. -/
def cellTops (TT : Finset (Fin n')) (r u b i : ℕ) : Finset ℕ :=
  (Ico (b * blockLen r u + i * u) (b * blockLen r u + (i + 1) * u)).filter (· ∈ TT.map Fin.valEmbedding)

/-- **A marked block**: its odd cells hold no top, and each even cell exactly one, at an even position. -/
def Marked (TT : Finset (Fin n')) (r u b : ℕ) : Prop :=
  ∀ i < 6 * r + 1, (Odd i → cellTops TT r u b i = ∅) ∧ (Even i → ∃ q, Even q ∧ cellTops TT r u b i = {q})

/-- **The tile condition** (a good set of tops on an orbit of length `n′`), with the windows read cyclically and the
blocks cyclically among the `⌊n′/((6r + 1)u)⌋` full ones. Field by field it is the design's `TilePar.IsGood n′ P`
(`DesignOrbits`) for `P = TT.map Fin.valEmbedding`; the design should instantiate this definition. -/
structure IsGoodSet (TT : Finset (Fin n')) (L₂ K r u M₀ G' N₁ : ℕ) : Prop where
  /-- (A) Every cyclic window of `L₂` positions holds at most `K` tops. -/
  window : ∀ s < n', winCount TT s L₂ ≤ K
  /-- (T) Every run of `M₀ + 1` consecutive blocks holds a marked one. -/
  tile : ∀ b₀ < n' / blockLen r u, ∃ i ≤ M₀, Marked TT r u ((b₀ + i) % (n' / blockLen r u))
  /-- (I) Every cyclic window of `G′` positions holds at most `N₁` tops. -/
  dense : ∀ s < n', winCount TT s G' ≤ N₁

end Orbit

/-! ## Lifted positions -/

section Lifted

variable {n' : ℕ} [NeZero n']

/-- **The position of a lifted position**: `x mod n′`. -/
def posOf (n' : ℕ) [NeZero n'] (x : ℤ) : Fin n' :=
  ⟨(x % (n' : ℤ)).toNat, by
    have h0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have h1 := Int.emod_lt_of_pos x h0
    have h2 := Int.emod_nonneg x h0.ne'
    omega⟩

/-- **A lifted top**: `x mod n′` is a top. -/
abbrev IsTop (TT : Finset (Fin n')) (x : ℤ) : Prop := posOf n' x ∈ TT

/-- **The position as an integer** is the remainder `x mod n′`. -/
theorem posOf_val (x : ℤ) : ((posOf n' x).val : ℤ) = x % n' :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (by exact_mod_cast NeZero.ne n'))

/-- **Positions are periodic.** -/
theorem posOf_add_mul (x m : ℤ) : posOf n' (x + n' * m) = posOf n' x :=
  Fin.ext (by simp [posOf, Int.add_mul_emod_self_left])

/-- **A position lifts to itself.** -/
theorem posOf_natCast (s : Fin n') : posOf n' (s.val : ℤ) = s :=
  Fin.ext (by
    have h := posOf_val (n' := n') (s.val : ℤ)
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.isLt)] at h
    exact_mod_cast h)

/-- **A shifted letter is a top iff the letter is.** -/
theorem isTop_add_iff (TT : Finset (Fin n')) (x : ℤ) : IsTop TT (x + n') ↔ IsTop TT x := by
  simp only [IsTop]
  rw [show x + (n' : ℤ) = x + n' * 1 by ring, posOf_add_mul]

/-- **Parity is well defined on positions** for even `n′`. -/
theorem even_posOf_iff (hn : Even n') (x : ℤ) : Even (posOf n' x).val ↔ Even x := by
  rw [← Int.even_coe_nat, posOf_val]
  have h := Int.mul_ediv_add_emod x n'
  have hn' : Even (n' : ℤ) := by exact_mod_cast hn
  constructor
  · intro he
    rw [← h]
    exact (hn'.mul_right _).add he
  · intro he
    have : x % n' = x - n' * (x / n') := by omega
    rw [this]
    exact he.sub (hn'.mul_right _)

end Lifted

/-! ## Windows of lifted positions -/

section Windows

variable {n' : ℕ} [NeZero n']

/-- **Consecutive windows**: for monotone `z`, the windows `(z (j − 1), z j]`, `j < m`, tile `(z (−1), z (m − 1)]`. -/
theorem sum_Ioc_consec {M : Type*} [AddCommMonoid M] {z : ℤ → ℤ} (hz : Monotone z) (P : ℤ → Prop) [DecidablePred P]
    (g : ℤ → M) (m : ℕ) :
    ∑ j ∈ range m, ∑ x ∈ (Ioc (z ((j : ℤ) - 1)) (z j)).filter P, g x =
      ∑ x ∈ (Ioc (z (-1)) (z ((m : ℤ) - 1))).filter P, g x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, ← sum_union (disjoint_filter_filter (Ioc_disjoint_Ioc_of_le le_rfl)), ← filter_union,
      Ioc_union_Ioc_eq_Ioc (hz (by omega)) (hz (by omega))]
    push_cast
    ring_nf

/-- **A window of length `n′` reads every top once**: `Σ_{x ∈ (a, a + n′], x top} φ(x mod n′) = Σ_{t ∈ TT} φ(t)`. -/
theorem sum_Ioc_period {M : Type*} [AddCommMonoid M] (TT : Finset (Fin n')) (a : ℤ) (φ : Fin n' → M) :
    ∑ x ∈ (Ioc a (a + n')).filter (IsTop TT), φ (posOf n' x) = ∑ t ∈ TT, φ t := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have back : ∀ t : Fin n', posOf n' (a + 1 + ((t.val : ℤ) - a - 1) % n') = t := fun t => by
    have h := Int.mul_ediv_add_emod ((t.val : ℤ) - a - 1) n'
    rw [show a + 1 + ((t.val : ℤ) - a - 1) % n' = t.val + n' * (-(((t.val : ℤ) - a - 1) / n')) by linarith,
      posOf_add_mul, posOf_natCast]
  refine sum_nbij' (fun x => posOf n' x) (fun t => a + 1 + ((t.val : ℤ) - a - 1) % n') ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact (mem_filter.1 hx).2
  · intro t ht
    have h1 := Int.emod_nonneg ((t.val : ℤ) - a - 1) hn.ne'
    have h2 := Int.emod_lt_of_pos ((t.val : ℤ) - a - 1) hn
    refine mem_filter.2 ⟨mem_Ioc.2 ⟨by linarith, by linarith⟩, ?_⟩
    show posOf n' _ ∈ TT
    rw [back]
    exact ht
  · intro x hx
    have hx' := mem_Ioc.1 (mem_filter.1 hx).1
    have hv := posOf_val (n' := n') x
    have h := Int.mul_ediv_add_emod x n'
    have e : ((posOf n' x).val : ℤ) - a - 1 = (x - a - 1) + n' * (-(x / n')) := by rw [hv]; linarith
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by linarith) (by linarith)]
    ring
  · intro t _
    exact back t
  · intro x _
    rfl

omit [NeZero n'] in
/-- **A shifted finset**: `s` translated by `n′`, from a membership criterion. -/
theorem eq_map_of_mem_add {s t : Finset ℤ} (h : ∀ x : ℤ, x + (n' : ℤ) ∈ t ↔ x ∈ s) :
    t = s.map (addRightEmbedding (n' : ℤ)) := by
  ext y
  simp only [mem_map, addRightEmbedding_apply]
  constructor
  · intro hy
    exact ⟨y - n', (h _).1 (by simpa using hy), by ring⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h x).2 hx

end Windows

/-! ## Frame systems -/

/-- **A frame system** (N3): `J` frames per period and the lifted positions `f j i` of the rows `i < r` of the frame
`j ∈ ℤ`. -/
structure FrameSys (n' r : ℕ) where
  /-- The number of frames per period. -/
  J : ℕ
  /-- The rows of the frames, as lifted positions. -/
  f : ℤ → Fin r → ℤ

/-- **The last row index** `r − 1`. -/
def lastRow (r : ℕ) [NeZero r] : Fin r := ⟨r - 1, Nat.sub_lt (NeZero.pos r) Nat.one_pos⟩

namespace FrameSys

variable {n' r : ℕ} [NeZero n'] [NeZero r] (F : FrameSys n' r) (TT : Finset (Fin n'))

/-- **The end of the frame `j`**: its last row `z j = f j (r − 1)`. -/
def z (j : ℤ) : ℤ := F.f j (lastRow r)

/-- **The letters of the segment `j`**: the tops in `[f (j − 1) 0, z j]`. -/
def seg (j : ℤ) : Finset ℤ := (Icc (F.f (j - 1) 0) (F.z j)).filter (IsTop TT)

/-- **The late letters of the segment `j`**: its letters after the previous frame, `> z (j − 1)`. -/
def late (j : ℤ) : Finset ℤ := (F.seg TT j).filter (F.z (j - 1) < ·)

/-- **The loose letters of the segment `j`**: the tops strictly between `z (j − 1)` and `f j 0`. -/
def loose (j : ℤ) : Finset ℤ := (F.seg TT j).filter fun x => F.z (j - 1) < x ∧ x < F.f j 0

/-- **The number of loose letters** of the segment `j`. -/
def nL (j : ℤ) : ℕ := (F.loose TT j).card

/-- **The loose letters in increasing order**, from `0`. -/
noncomputable def looseAt (j : ℤ) : Fin (F.nL TT j) ↪o ℤ := (F.loose TT j).orderEmbOfFin rfl

/-- **The `u`-th late letter** (`posN(j, u)`, from `0`): the loose letters for `u < nL j`, then the frame rows,
`lateAt j (nL j + i) = f j i` (and `z j` beyond `nL j + r`). -/
noncomputable def lateAt (j : ℤ) (u : ℕ) : ℤ :=
  if h : u < F.nL TT j then F.looseAt TT j ⟨u, h⟩
  else if h' : u - F.nL TT j < r then F.f j ⟨u - F.nL TT j, h'⟩ else F.z j

/-- **The push** `z j − x` of a letter of the segment `j`, as a natural number. -/
def push (j x : ℤ) : ℕ := (F.z j - x).toNat

/-- **The even letters of the segment `j` strictly before `x`.** -/
def evBefore (j x : ℤ) : Finset ℤ := (F.seg TT j).filter fun y => Even y ∧ y < x

/-- **The rows of `x`** in the segment `j`: the `r` most recent even letters of `seg j` strictly before `x`,
increasing (`0` if there are fewer than `r`). -/
noncomputable def rows (j x : ℤ) (i : Fin r) : ℤ :=
  if h : r ≤ (F.evBefore TT j x).card then
    (F.evBefore TT j x).orderEmbOfFin rfl ⟨(F.evBefore TT j x).card - r + i, by omega⟩
  else 0

/-- **The anchor of `x`**: the oldest of its rows, the `r`-th most recent even letter of `seg j` before `x`. -/
noncomputable def anchor (j x : ℤ) : ℤ := F.rows TT j x 0

/-- **Proper frames** (V1–V7, V9): periodic, strictly increasing rows that are even tops with no top between
consecutive rows, at least `r` loose letters per segment, the first and last `r` of them even and far (`> L₁`) from
the earlier letters of the segment, the first row far from the earlier letters, and every late letter far from its
anchor. -/
structure Proper (L₁ : ℕ) : Prop where
  /-- (V1) -/
  one_le_J : 1 ≤ F.J
  /-- (V2) -/
  periodic : ∀ j i, F.f (j + F.J) i = F.f j i + n'
  /-- (V3) -/
  strictMono : ∀ j, StrictMono (F.f j)
  /-- (V4) -/
  z_lt : ∀ j, F.z j < F.f (j + 1) 0
  /-- (V5) -/
  row_top : ∀ j i, IsTop TT (F.f j i) ∧ Even (F.f j i)
  /-- (V6) -/
  no_top_between : ∀ j (i i' : Fin r), i.val + 1 = i'.val → ∀ x, F.f j i < x → x < F.f j i' → ¬ IsTop TT x
  /-- (V7, count) -/
  le_nL : ∀ j, r ≤ F.nL TT j
  /-- (V7, the first and last `r` loose letters) -/
  loose_far : ∀ j, ∀ x ∈ F.loose TT j,
    (((F.loose TT j).filter (· < x)).card < r ∨ ((F.loose TT j).filter (x < ·)).card < r) →
      Even x ∧ ∀ y ∈ F.seg TT j, y < x → y + L₁ < x
  /-- (V7, the first row) -/
  frame_far : ∀ j, ∀ y ∈ F.seg TT j, y < F.f j 0 → y + L₁ < F.f j 0
  /-- (V9) -/
  anchor_far : ∀ j, ∀ x ∈ F.late TT j, F.anchor TT j x + L₁ < x

/-- **Bounded frames**: every segment spans fewer than `G′` positions and has at most `Ns` letters. -/
structure Bounded (G' Ns : ℕ) : Prop where
  /-- The span of a segment. -/
  span : ∀ j, F.z j - F.f (j - 1) 0 < G'
  /-- The number of letters of a segment. -/
  card_seg : ∀ j, (F.seg TT j).card ≤ Ns

/-! ### Rows and anchors -/

/-- **The rows are even letters of the segment before `x`.** -/
theorem rows_mem {j x : ℤ} (h : r ≤ (F.evBefore TT j x).card) (i : Fin r) :
    F.rows TT j x i ∈ F.evBefore TT j x := by
  rw [rows, dite_eq_left h]
  exact orderEmbOfFin_mem _ _ _

/-- **The rows are strictly increasing.** -/
theorem rows_strictMono {j x : ℤ} (h : r ≤ (F.evBefore TT j x).card) : StrictMono (F.rows TT j x) := by
  intro i i' hii'
  simp only [rows, dite_eq_left h]
  exact (OrderEmbedding.lt_iff_lt _).2 (Fin.mk_lt_mk.2 (by have := Fin.lt_def.1 hii'; omega))

/-- **The rows are all the even letters of the segment from the anchor on**: `#{y ∈ evBefore j x : anchor ≤ y} = r`. -/
theorem card_evBefore_ge_anchor {j x : ℤ} (h : r ≤ (F.evBefore TT j x).card) :
    ((F.evBefore TT j x).filter (F.anchor TT j x ≤ ·)).card = r := by
  set s := F.evBefore TT j x with hs
  set e := s.orderEmbOfFin rfl
  have hA : F.anchor TT j x = e ⟨s.card - r, by have := NeZero.pos r; omega⟩ := by
    rw [anchor, rows, dite_eq_left h]
    congr 1
  have h1 : (Ico (s.card - r) s.card).card = (s.filter (F.anchor TT j x ≤ ·)).card := by
    refine card_bij (fun n hn => e ⟨n, (mem_Ico.1 hn).2⟩) ?_ ?_ ?_
    · intro n hn
      refine mem_filter.2 ⟨orderEmbOfFin_mem _ _ _, ?_⟩
      rw [hA, OrderEmbedding.le_iff_le, Fin.le_def]
      exact (mem_Ico.1 hn).1
    · intro a ha b hb hab
      exact Fin.mk.inj_iff.1 (e.injective hab)
    · intro y hy
      rw [mem_filter] at hy
      have hy' : y ∈ Set.range e := by rw [range_orderEmbOfFin]; exact hy.1
      obtain ⟨a, rfl⟩ := hy'
      have h2 := hy.2
      rw [hA, OrderEmbedding.le_iff_le, Fin.le_def] at h2
      exact ⟨a.val, mem_Ico.2 ⟨h2, a.isLt⟩, rfl⟩
  rw [← h1, Nat.card_Ico]
  omega

/-- **The first `nL j` late letters are the loose ones.** -/
theorem lateAt_of_lt {j : ℤ} {u : ℕ} (h : u < F.nL TT j) : F.lateAt TT j u = F.looseAt TT j ⟨u, h⟩ := by
  rw [lateAt, dite_eq_left h]

/-- **The late letter of index `nL j + i` is the row `i` of the frame `j`.** -/
theorem lateAt_nL_add (j : ℤ) (i : Fin r) : F.lateAt TT j (F.nL TT j + i) = F.f j i := by
  rw [lateAt, dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  exact Fin.ext (by simp)

/-- **A loose letter is loose.** -/
theorem looseAt_mem (j : ℤ) (l : Fin (F.nL TT j)) : F.looseAt TT j l ∈ F.loose TT j := orderEmbOfFin_mem _ _ _

/-- **The first letter of a segment has the largest push** (S1.6). -/
theorem push_le_push_first {j y : ℤ} (hy : y ∈ F.seg TT j) : F.push j y ≤ F.push j (F.f (j - 1) 0) := by
  have h := (mem_Icc.1 (mem_filter.1 hy).1).1
  simp only [push]
  omega

/-! ### Proper frames -/

namespace Proper

variable {F TT} {L₁ : ℕ} (hF : F.Proper TT L₁)
include hF

/-- **Every row is at most the frame end.** -/
theorem f_le_z (j : ℤ) (i : Fin r) : F.f j i ≤ F.z j :=
  (hF.strictMono j).monotone (Fin.le_def.2 (by simp only [lastRow]; have := i.isLt; omega))

/-- **Every row is at least the first row.** -/
theorem f_zero_le (j : ℤ) (i : Fin r) : F.f j 0 ≤ F.f j i :=
  (hF.strictMono j).monotone (Fin.le_def.2 (by simp))

/-- **Frame ends are strictly increasing.** -/
theorem z_strictMono : StrictMono F.z :=
  strictMono_int_of_lt_succ fun j => (hF.z_lt j).trans_le (hF.f_le_z _ 0)

/-- **A frame end is before every row of a later frame.** -/
theorem z_lt_f {j j' : ℤ} (h : j < j') (i : Fin r) : F.z j < F.f j' i := by
  have h1 : F.z j ≤ F.z (j' - 1) := hF.z_strictMono.monotone (by omega)
  have h2 := hF.z_lt (j' - 1)
  rw [sub_add_cancel] at h2
  exact h1.trans_lt (h2.trans_le (hF.f_zero_le _ _))

/-- **The rows of the previous frame are letters of the segment** (its W-letters). -/
theorem prev_row_mem_seg (j : ℤ) (i : Fin r) : F.f (j - 1) i ∈ F.seg TT j :=
  mem_filter.2 ⟨mem_Icc.2 ⟨hF.f_zero_le _ _,
    ((hF.f_le_z _ _).trans_lt (hF.z_lt_f (by omega : j - 1 < j) (lastRow r))).le⟩, (hF.row_top _ _).1⟩

/-- **The rows of the frame are late letters of its segment.** -/
theorem row_mem_late (j : ℤ) (i : Fin r) : F.f j i ∈ F.late TT j :=
  mem_filter.2 ⟨mem_filter.2 ⟨mem_Icc.2 ⟨((hF.f_le_z _ _).trans_lt (hF.z_lt_f (by omega : j - 1 < j) i)).le,
    hF.f_le_z _ _⟩, (hF.row_top _ _).1⟩, hF.z_lt_f (by omega) i⟩

/-- **A late letter has at least `r` even letters of its segment before it**: the rows of the previous frame. -/
theorem le_card_evBefore {j x : ℤ} (hx : F.z (j - 1) < x) : r ≤ (F.evBefore TT j x).card := by
  have hsub : univ.image (F.f (j - 1)) ⊆ F.evBefore TT j x := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    exact mem_filter.2 ⟨hF.prev_row_mem_seg j i, (hF.row_top _ _).2, (hF.f_le_z _ _).trans_lt hx⟩
  calc r = (univ.image (F.f (j - 1))).card := by
        rw [card_image_of_injective _ (hF.strictMono _).injective, card_univ, Fintype.card_fin]
    _ ≤ _ := card_le_card hsub

/-- **The anchor of a late letter is an even letter of the segment before it.** -/
theorem anchor_mem_evBefore {j x : ℤ} (hx : x ∈ F.late TT j) : F.anchor TT j x ∈ F.evBefore TT j x :=
  F.rows_mem TT (hF.le_card_evBefore (mem_filter.1 hx).2) 0

/-- **The anchor of a late letter is a letter of the segment.** -/
theorem anchor_mem_seg {j x : ℤ} (hx : x ∈ F.late TT j) : F.anchor TT j x ∈ F.seg TT j :=
  (mem_filter.1 (hF.anchor_mem_evBefore hx)).1

/-- **A top between the first and the last row of a frame is a row.** -/
theorem exists_row_of_top {j x : ℤ} (h0 : F.f j 0 ≤ x) (h1 : x ≤ F.z j) (ht : IsTop TT x) :
    ∃ i, F.f j i = x := by
  set s := univ.filter fun i : Fin r => F.f j i ≤ x
  have hs : s.Nonempty := ⟨0, mem_filter.2 ⟨mem_univ _, h0⟩⟩
  have hi : F.f j (s.max' hs) ≤ x := (mem_filter.1 (s.max'_mem hs)).2
  refine ⟨s.max' hs, le_antisymm hi ?_⟩
  by_contra hlt
  push Not at hlt
  by_cases hlast : (s.max' hs).val + 1 < r
  · have hx' : x < F.f j ⟨(s.max' hs).val + 1, hlast⟩ := by
      by_contra hge
      push Not at hge
      have hle := s.le_max' _ (mem_filter.2 ⟨mem_univ _, hge⟩)
      rw [Fin.le_def] at hle
      simp at hle
    exact hF.no_top_between j _ _ rfl x hlt hx' ht
  · have he : s.max' hs = lastRow r := Fin.ext (by simp only [lastRow]; have := (s.max' hs).isLt; omega)
    rw [he] at hlt
    exact absurd h1 (not_le.2 hlt)

/-- **The anchor is not a row of the frame** (S1.5): it is a W-letter or a loose letter. Otherwise all `r` rows of
`x` would be rows `f j i < x ≤ z j`, of which there are at most `r − 1`. -/
theorem anchor_lt_f {j x : ℤ} (hx : x ∈ F.late TT j) : F.anchor TT j x < F.f j 0 := by
  by_contra hge
  push Not at hge
  have hr := hF.le_card_evBefore (mem_filter.1 hx).2
  have hxz : x ≤ F.z j := (mem_Icc.1 (mem_filter.1 (mem_filter.1 hx).1).1).2
  have hrow : ∀ i : Fin r, ∃ i' : Fin r, F.f j i' = F.rows TT j x i ∧ F.f j i' < x := fun i => by
    have hm := mem_filter.1 (F.rows_mem TT hr i)
    have hge' : F.f j 0 ≤ F.rows TT j x i :=
      hge.trans ((F.rows_strictMono TT hr).monotone (Fin.le_def.2 (by simp)))
    obtain ⟨i', hi'⟩ := hF.exists_row_of_top hge' (hm.2.2.le.trans hxz) (mem_filter.1 hm.1).2
    exact ⟨i', hi', hi' ▸ hm.2.2⟩
  choose g hg using hrow
  have hg_inj : Function.Injective g := fun i₁ i₂ h =>
    (F.rows_strictMono TT hr).injective (by rw [← (hg i₁).1, ← (hg i₂).1, h])
  have hsub : univ.image g ⊆ (univ : Finset (Fin r)).erase (lastRow r) := by
    intro i' hi'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hi'
    refine mem_erase.2 ⟨fun h => ?_, mem_univ _⟩
    have := (hg i).2
    rw [h] at this
    exact absurd hxz (not_le.2 this)
  have := card_le_card hsub
  rw [card_image_of_injective _ hg_inj, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
  have := NeZero.pos r
  omega

/-- **The anchor is pushed at least `L₁ + 1` further than the letter** (S1.6, from V9). -/
theorem push_add_lt_push_anchor {j x : ℤ} (hx : x ∈ F.late TT j) :
    F.push j x + L₁ < F.push j (F.anchor TT j x) := by
  have h1 := hF.anchor_far j x hx
  have hxz : x ≤ F.z j := (mem_Icc.1 (mem_filter.1 (mem_filter.1 hx).1).1).2
  simp only [push]
  omega

/-- **The late letters are the loose letters and the rows of the frame.** -/
theorem late_eq (j : ℤ) : F.late TT j = F.loose TT j ∪ univ.image (F.f j) := by
  ext x
  simp only [late, loose, mem_filter, mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hs, hx⟩
    by_cases h : x < F.f j 0
    · exact Or.inl ⟨hs, hx, h⟩
    · right
      have hs' := mem_filter.1 hs
      exact hF.exists_row_of_top (not_lt.1 h) (mem_Icc.1 hs'.1).2 hs'.2
  · rintro (⟨hs, hx, -⟩ | ⟨i, rfl⟩)
    · exact ⟨hs, hx⟩
    · exact mem_filter.1 (hF.row_mem_late j i)

/-- **Loose letters are not rows.** -/
theorem disjoint_loose_rows (j : ℤ) : Disjoint (F.loose TT j) (univ.image (F.f j)) := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨i, -, rfl⟩ := mem_image.1 hx'
  exact absurd (mem_filter.1 hx).2.2 (not_lt.2 (hF.f_zero_le j i))

/-- **A segment has `nL j + r` late letters.** -/
theorem card_late (j : ℤ) : (F.late TT j).card = F.nL TT j + r := by
  rw [hF.late_eq, card_union_of_disjoint (hF.disjoint_loose_rows j),
    card_image_of_injective _ (hF.strictMono j).injective, card_univ, Fintype.card_fin]
  rfl

/-- **The letters of a segment are the rows of the previous frame and the late letters.** -/
theorem seg_eq (j : ℤ) : F.seg TT j = univ.image (F.f (j - 1)) ∪ F.late TT j := by
  ext x
  simp only [late, mem_union, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · intro hs
    by_cases h : F.z (j - 1) < x
    · exact Or.inr ⟨hs, h⟩
    · left
      have hs' := mem_filter.1 hs
      exact hF.exists_row_of_top (mem_Icc.1 hs'.1).1 (not_lt.1 h) hs'.2
  · rintro (⟨i, rfl⟩ | ⟨hs, -⟩)
    · exact hF.prev_row_mem_seg j i
    · exact hs

/-- **The late letters in order are late letters.** -/
theorem lateAt_mem_late {j : ℤ} {u : ℕ} (hu : u < F.nL TT j + r) : F.lateAt TT j u ∈ F.late TT j := by
  by_cases h : u < F.nL TT j
  · rw [F.lateAt_of_lt TT h, hF.late_eq]
    exact mem_union_left _ (F.looseAt_mem TT j _)
  · obtain ⟨i, rfl⟩ : ∃ i : Fin r, u = F.nL TT j + i := ⟨⟨u - F.nL TT j, by omega⟩, by simp; omega⟩
    rw [F.lateAt_nL_add]
    exact hF.row_mem_late j i

/-- **The late letters are enumerated in increasing order.** -/
theorem lateAt_strictMono {j : ℤ} {u v : ℕ} (huv : u < v) (hv : v < F.nL TT j + r) :
    F.lateAt TT j u < F.lateAt TT j v := by
  by_cases hv' : v < F.nL TT j
  · rw [F.lateAt_of_lt TT hv', F.lateAt_of_lt TT (huv.trans hv')]
    exact (OrderEmbedding.lt_iff_lt _).2 (Fin.mk_lt_mk.2 huv)
  · obtain ⟨i, rfl⟩ : ∃ i : Fin r, v = F.nL TT j + i := ⟨⟨v - F.nL TT j, by omega⟩, by simp; omega⟩
    rw [F.lateAt_nL_add]
    by_cases hu : u < F.nL TT j
    · rw [F.lateAt_of_lt TT hu]
      exact (mem_filter.1 (F.looseAt_mem TT j _)).2.2.trans_le (hF.f_zero_le j i)
    · obtain ⟨i', rfl⟩ : ∃ i' : Fin r, u = F.nL TT j + i' := ⟨⟨u - F.nL TT j, by omega⟩, by simp; omega⟩
      rw [F.lateAt_nL_add]
      exact hF.strictMono j (Fin.lt_def.2 (by omega))

/-! ### Periodicity -/

/-- **Frame ends are periodic.** -/
theorem z_add_J (j : ℤ) : F.z (j + F.J) = F.z j + n' := hF.periodic j _

/-- **Shifting a letter by `n′` shifts its segment by `J`.** -/
theorem mem_seg_add_J {j x : ℤ} : x + n' ∈ F.seg TT (j + F.J) ↔ x ∈ F.seg TT j := by
  have e : j + (F.J : ℤ) - 1 = (j - 1) + F.J := by ring
  simp only [seg, mem_filter, mem_Icc, e, hF.periodic, hF.z_add_J, isTop_add_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-- **Shifting a late letter by `n′` shifts its segment by `J`.** -/
theorem mem_late_add_J {j x : ℤ} : x + n' ∈ F.late TT (j + F.J) ↔ x ∈ F.late TT j := by
  have e : j + (F.J : ℤ) - 1 = (j - 1) + F.J := by ring
  simp only [late, mem_filter, hF.mem_seg_add_J, e, hF.z_add_J, add_lt_add_iff_right]

/-- **Shifting a loose letter by `n′` shifts its segment by `J`.** -/
theorem mem_loose_add_J {j x : ℤ} : x + n' ∈ F.loose TT (j + F.J) ↔ x ∈ F.loose TT j := by
  have e : j + (F.J : ℤ) - 1 = (j - 1) + F.J := by ring
  simp only [loose, mem_filter, hF.mem_seg_add_J, e, hF.z_add_J, hF.periodic, add_lt_add_iff_right]

/-- **Segments are periodic.** -/
theorem seg_add_J (j : ℤ) : F.seg TT (j + F.J) = (F.seg TT j).map (addRightEmbedding (n' : ℤ)) :=
  eq_map_of_mem_add fun _ => hF.mem_seg_add_J

/-- **Late letters are periodic.** -/
theorem late_add_J (j : ℤ) : F.late TT (j + F.J) = (F.late TT j).map (addRightEmbedding (n' : ℤ)) :=
  eq_map_of_mem_add fun _ => hF.mem_late_add_J

/-- **Loose letters are periodic.** -/
theorem loose_add_J (j : ℤ) : F.loose TT (j + F.J) = (F.loose TT j).map (addRightEmbedding (n' : ℤ)) :=
  eq_map_of_mem_add fun _ => hF.mem_loose_add_J

/-- **The number of loose letters is periodic.** -/
theorem nL_add_J (j : ℤ) : F.nL TT (j + F.J) = F.nL TT j := by
  rw [nL, hF.loose_add_J, card_map, nL]

/-- **Pushes are periodic.** -/
theorem push_add_J (j x : ℤ) : F.push (j + F.J) (x + n') = F.push j x := by
  rw [push, push, hF.z_add_J]
  congr 1
  ring

/-! ### Tiling and the number of frames -/

/-- **The late letters of a segment are the tops after the previous frame end, up to the frame end.** -/
theorem late_eq_Ioc (j : ℤ) : F.late TT j = (Ioc (F.z (j - 1)) (F.z j)).filter (IsTop TT) := by
  ext x
  simp only [late, seg, mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨-, h2⟩, h3⟩, h4⟩
    exact ⟨⟨h4, h2⟩, h3⟩
  · rintro ⟨⟨h4, h2⟩, h3⟩
    exact ⟨⟨⟨(hF.f_le_z _ _).trans h4.le, h2⟩, h3⟩, h4⟩

/-- **The late letters of one period read every top once**: `Σ_{j<J} Σ_{x ∈ late j} φ(x mod n′) = Σ_{t ∈ TT} φ(t)`. -/
theorem sum_late {M : Type*} [AddCommMonoid M] (φ : Fin n' → M) :
    ∑ j ∈ range F.J, ∑ x ∈ F.late TT (j : ℤ), φ (posOf n' x) = ∑ t ∈ TT, φ t := by
  simp_rw [hF.late_eq_Ioc]
  rw [sum_Ioc_consec hF.z_strictMono.monotone (IsTop TT) (fun x => φ (posOf n' x)) F.J,
    show (F.J : ℤ) - 1 = -1 + F.J by ring, hF.z_add_J, sum_Ioc_period]

/-- **The late letters of one period are as many as the tops.** -/
theorem sum_card_late : ∑ j ∈ range F.J, (F.late TT (j : ℤ)).card = TT.card := by
  have h := hF.sum_late (M := ℕ) (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at h
  exact h

/-- **The number of frames**: a period is covered by `J` segments of span `< G′`, so `n′ < J·G′`. -/
theorem lt_J_mul {G' Ns : ℕ} (hB : F.Bounded TT G' Ns) : n' < F.J * G' := by
  have htel : ∑ j ∈ range F.J, (F.z (j : ℤ) - F.z ((j : ℤ) - 1)) = n' := by
    have h := Finset.sum_range_sub (fun i : ℕ => F.z ((i : ℤ) - 1)) F.J
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.cast_zero, zero_sub] at h
    rw [h, show (F.J : ℤ) - 1 = -1 + F.J by ring, hF.z_add_J]
    ring
  have hlt : ∀ j ∈ range F.J, F.z (j : ℤ) - F.z ((j : ℤ) - 1) < G' := fun j _ => by
    have h1 := hB.span j
    have h2 : F.f ((j : ℤ) - 1) 0 ≤ F.z ((j : ℤ) - 1) := hF.f_le_z _ _
    linarith
  have hne : (range F.J).Nonempty := nonempty_range_iff.2 (by have := hF.one_le_J; omega)
  have h : (n' : ℤ) < F.J * G' := by
    calc (n' : ℤ) = ∑ j ∈ range F.J, (F.z (j : ℤ) - F.z ((j : ℤ) - 1)) := htel.symm
      _ < ∑ _j ∈ range F.J, (G' : ℤ) := sum_lt_sum_of_nonempty hne hlt
      _ = F.J * G' := by simp
  exact_mod_cast h

/-- **At least four frames** when `3G′ ≤ n′`. -/
theorem three_lt_J {G' Ns : ℕ} (hB : F.Bounded TT G' Ns) (hG : 3 * G' ≤ n') : 3 < F.J :=
  Nat.lt_of_mul_lt_mul_right (hG.trans_lt (hF.lt_J_mul hB))

end Proper

end FrameSys

end LocalOrbit
