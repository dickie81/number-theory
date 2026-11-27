import SharpInputs
import DesignScale
import PairSetting

/-!
# The tile condition and the 2-adic clause: the definitions of the Stage-2 clauses

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain` and the design's Stage 2): the definitions
that the Stage-2 clauses of an admissible design read, so that `SharpAdm` can state them (G1, `SharpDesign.Adm.G1`,
and the 2-adic clause, `Setting.DesignAdm.twoAdic`). The facts about them are downstream: the orbit combinatorics
in `DesignOrbits`, the sums in `GainSums`, the random tops that meet G1 in `TopsSelect`.

**Orbits** (generic in a finite abelian group). The base point of the `⟨σ⟩`-orbit of `t` (`basePoint`, a fixed
element of the orbit), and the positions of the tops on the orbit of `t₀`, `P(t₀) = {i < ord σ : t₀σ^i ∈ TT}`
(`topPositions`). At a prime `p` with the twist `c`, the step on `A` is `σ_p = h_p` for inert `p` and `h_p²` for
signal `p`, `h_p = hP_c(p)` (`Setting.orbitStep`).

**The tile condition** (`TilePar.IsGood`), for a set `P` of positions in `[0, n′)` read cyclically and parameters
`(L₂, K, r, u, M₀, G′, N₁)` (`TilePar`): (A) every cyclic window of `L₂` positions holds at most `K` points
(`winCard`); (T) cutting `[0, n′)` into `B = ⌊n′/((6r + 1)u)⌋` blocks of `6r + 1` cells of `u` positions
(`TilePar.blockLen`, `TilePar.cellPts`), every run of `M₀ + 1` consecutive blocks (cyclically) holds a marked one
(`TilePar.Marked`: its odd cells are empty and each even cell holds exactly one point, at an even position); (I) every
cyclic window of `G′` positions holds at most `N₁` points. The design's parameters are `tilePar x ε k`.

**The design-level sets.** The primes `PR = {p < X′ prime, inert, ord h_p ≥ x^{ε/4}}` (`Setting.PR`); a top is good
at `p` (`SharpDesign.IsGoodAt`) when the position set of its base point for `σ_p` is good, with `n′ = ord σ_p`; the
bad tops (`SharpDesign.badTops`). **(G1)** is `Σ_{p ∈ PR} (log p/p)·|badTops p| ≤ |TT|·x^{−2+ε}`
(`SharpDesign.FewBadTops`); it reads the design only through `k` and `TT`, so it has a design-free form
(`Setting.FewBadTopsAt`, `SharpDesign.fewBadTops_iff`), the one that the builder of `SharpParams` carries.

**The 2-adic structure** (`Setting.TwoAdic`, the gain spec §4.5): `2^{e+2} ∣ QS`, `K` lies in the classes
`≡ ±1 (mod 2^{e+2})`, and `|A₀| ≤ 2^e`; the settings of pairs have it (`pairSetting_twoAdic`).

**Moved, not changed.** The definitions are those of `DesignOrbits` and `GainSums`, moved here unchanged (same names,
same binders) so that `SharpAdm` sees them; the lemmas about them stay where they were. `Setting.FewBadTopsAt` and
`SharpDesign.fewBadTops_iff` are new.
-/

open Finset

namespace ZetaBalance

/-! ## Orbits and positions -/

section Orbits

variable {A : Type*} [CommGroup A] [Finite A]

/-- **The base point** of the `⟨σ⟩`-orbit of `t`: a fixed element of the orbit (the representative of its class),
the same for the whole orbit (`basePoint_mul_pow`). -/
noncomputable def basePoint (σ t : A) : A :=
  (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) A) t).out

variable [DecidableEq A]

/-- **The positions of the tops** on the orbit of `t₀`: `P(t₀) = {i < ord σ : t₀σ^i ∈ TT}`. -/
noncomputable def topPositions (TT : Finset A) (σ t₀ : A) : Finset ℕ :=
  (range (orderOf σ)).filter fun i => t₀ * σ ^ i ∈ TT

end Orbits

namespace Setting

variable (S : Setting)

/-- **The step on `A`** at `p` with the twist `c`: `σ_p = h_p` at inert `p`, `h_p²` at signal `p`, where
`h_p = hP_c(p)`. -/
noncomputable def orbitStep (c : S.A) (p : ℕ) : S.A :=
  if S.cls p = .signal then S.hPtw c p ^ 2 else S.hPtw c p

end Setting

/-! ## The tile condition -/

/-- **The parameters of the tile condition**: the window `L₂` and its bound `K`, the number `6r + 1` of cells of a
block and their length `u`, the run `M₀ + 1` of blocks, and the window `G′` with its bound `N₁`. -/
structure TilePar where
  /-- The window of (A). -/
  L₂ : ℕ
  /-- The bound of (A). -/
  K : ℕ
  /-- A block has `6r + 1` cells. -/
  r : ℕ
  /-- The length of a cell. -/
  u : ℕ
  /-- Every `M₀ + 1` consecutive blocks hold a marked one. -/
  M₀ : ℕ
  /-- The window of (I). -/
  G' : ℕ
  /-- The bound of (I). -/
  N₁ : ℕ

/-- **The points of `P` in a cyclic window**: `#{j < L : (s + j) mod n′ ∈ P}`. -/
def winCard (n' : ℕ) (P : Finset ℕ) (s L : ℕ) : ℕ := ((range L).filter fun j => (s + j) % n' ∈ P).card

namespace TilePar

variable (T : TilePar)

/-- **The length of a block**, `(6r + 1)u`. -/
def blockLen : ℕ := (6 * T.r + 1) * T.u

/-- **The points of `P` in the cell `i` of the block `b`**, `[b(6r + 1)u + iu, b(6r + 1)u + (i + 1)u)`. -/
def cellPts (P : Finset ℕ) (b i : ℕ) : Finset ℕ :=
  (Ico (b * T.blockLen + i * T.u) (b * T.blockLen + (i + 1) * T.u)).filter (· ∈ P)

/-- **A marked block**: its odd cells hold no point of `P`, and each even cell exactly one, at an even position. -/
def Marked (P : Finset ℕ) (b : ℕ) : Prop :=
  ∀ i < 6 * T.r + 1, (Odd i → T.cellPts P b i = ∅) ∧ (Even i → ∃ q, Even q ∧ T.cellPts P b i = {q})

/-- **The tile condition** on a set `P` of positions in `[0, n′)`, read cyclically. -/
structure IsGood (n' : ℕ) (P : Finset ℕ) : Prop where
  /-- (A) Every cyclic window of `L₂` positions holds at most `K` points. -/
  window : ∀ s < n', winCard n' P s T.L₂ ≤ T.K
  /-- (T) Every run of `M₀ + 1` consecutive blocks, cyclically among the `⌊n′/((6r + 1)u)⌋`, holds a marked one. -/
  tile : ∀ b₀ < n' / T.blockLen, ∃ j ≤ T.M₀, T.Marked P ((b₀ + j) % (n' / T.blockLen))
  /-- (I) Every cyclic window of `G′` positions holds at most `N₁` points. -/
  dense : ∀ s < n', winCard n' P s T.G' ≤ T.N₁

end TilePar

/-- **The tile parameters of the design** at `(x, ε)` and rank `k` (the gain spec, §2.5), with `h* = 2 + 8ε`:
`K = ⌈8(h* + 2)/ε⌉`, `r = K + 1`, `u = ⌈1/δ₁⌉`, `M₀ = ⌈(h* + 3)·10^{6r+1}·log x⌉`, `G′ = (M₀ + 5)(6r + 1)u`,
`N₁ = ⌈max(6e·G′δ₁, (h* + 3)·log₂ x)⌉ + 1` and `L₂ = 2⌈log_{x^{ε/10}}((kx^{26})⁴)⌉`. -/
noncomputable def tilePar (x ε : ℝ) (k : ℕ) : TilePar :=
  let K := ⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊
  let u := ⌈(scδ₁ x ε)⁻¹⌉₊
  let M₀ := ⌈((2 + 8 * ε) + 3) * 10 ^ (6 * (K + 1) + 1) * Real.log x⌉₊
  let G' := (M₀ + 5) * ((6 * (K + 1) + 1) * u)
  { L₂ := 2 * ⌈Real.logb (x ^ (ε / 10)) (((k : ℝ) * x ^ 26) ^ 4)⌉₊
    K := K
    r := K + 1
    u := u
    M₀ := M₀
    G' := G'
    N₁ := ⌈max (6 * Real.exp 1 * G' * scδ₁ x ε) (((2 + 8 * ε) + 3) * Real.logb 2 x)⌉₊ + 1 }

/-! ## The design-level sets and G1 -/

namespace Setting

variable (S : Setting)

/-- **The primes of the tile condition** `PR = {p < X′ prime, inert, ord h_p ≥ x^{ε/4}}`, with `h_p = hP_c(p)` at the
twist `c = twA κ`. -/
noncomputable def PR (κ : S.A →* ℂˣ) (x ε : ℝ) : Finset ℕ :=
  (range ⌈scX' x ε⌉₊).filter fun p => p.Prime ∧ S.cls p = .inert ∧ x ^ (ε / 4) ≤ orderOf (S.hPtw (S.twA κ) p)

open scoped Classical in
/-- **G1 for a set of tops** (design-free): `Σ_{p ∈ PR} (log p/p)·#{t ∈ TT bad at p} ≤ |TT|·x^{−2+ε}`, with the tile
parameters at rank `k`. `SharpDesign.FewBadTops Dg` is this at `k = Dg.R.k` and `TT = Dg.TT`
(`SharpDesign.fewBadTops_iff`). -/
def FewBadTopsAt (κ : S.A →* ℂˣ) (x ε : ℝ) (k : ℕ) (TT : Finset S.A) : Prop :=
  ∑ p ∈ S.PR κ x ε, (Real.log p / p) * ((TT.filter fun t => ¬ (tilePar x ε k).IsGood
    (orderOf (S.orbitStep (S.twA κ) p)) (topPositions TT (S.orbitStep (S.twA κ) p)
      (basePoint (S.orbitStep (S.twA κ) p) t))).card : ℝ) ≤ TT.card * x ^ (-2 + ε)

end Setting

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-- **A top is good at `p`**: the positions of the tops on its orbit, from its base point, satisfy the tile condition
with the design's parameters and `n′ = ord σ_p`. -/
def IsGoodAt (p : ℕ) (t : S.A) : Prop :=
  (tilePar x ε Dg.R.k).IsGood (orderOf (S.orbitStep (S.twA κ) p))
    (topPositions Dg.TT (S.orbitStep (S.twA κ) p) (basePoint (S.orbitStep (S.twA κ) p) t))

open scoped Classical in
/-- **The bad tops at `p`**: the tops that are not good at `p`. -/
noncomputable def badTops (p : ℕ) : Finset S.A := Dg.TT.filter fun t => ¬ Dg.IsGoodAt p t

end SharpDesign

/-- **(G1)**, the Stage-2 clause of `Adm`: `Σ_{p ∈ PR} (log p/p)·|badTops p| ≤ |TT|·x^{−2+ε}`. -/
def SharpDesign.FewBadTops {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) : Prop :=
  ∑ p ∈ S.PR κ x ε, (Real.log p / p) * ((Dg.badTops p).card : ℝ) ≤ Dg.TT.card * x ^ (-2 + ε)

/-- **G1 is design-free**: `FewBadTops` reads the design only through its rank `k` and its tops `TT`. -/
theorem SharpDesign.fewBadTops_iff {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) :
    Dg.FewBadTops ↔ S.FewBadTopsAt κ x ε Dg.R.k Dg.TT := Iff.rfl

/-! ## The 2-adic structure -/

/-- **The 2-adic structure of a setting** at level `e` (the clause that the small-order sparsity needs): `2^{e+2}`
divides `QS`, `K` lies in the classes `≡ ±1 (mod 2^{e+2})`, so that `A` maps to `H_e = (ℤ/2^{e+2})ˣ/±1`, and
`|A₀| ≤ 2^e`. -/
structure Setting.TwoAdic (S : Setting) (κ : S.A →* ℂˣ) (e : ℕ) : Prop where
  /-- `2^{e+2} ∣ QS`. -/
  dvd : 2 ^ (e + 2) ∣ S.QS
  /-- `K` lies in the kernel of `(ℤ/QS)ˣ → H_e`. -/
  K_le : S.K ≤ ((QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))).comp (ZMod.unitsMap dvd)).ker
  /-- `|A₀| ≤ 2^e`. -/
  card_A₀_le : (A₀ κ).card ≤ 2 ^ e

/-- **The settings of pairs are 2-adic**: `QS = lcm(2^{e+2}, f)`, `K` is the kernel of `u ↦ ([u], χ(u))`, and
`|A₀| ≤ 2^e` (`card_A₀_le`). -/
theorem pairSetting_twoAdic {f q d : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (h : PairArith f q d) (e : ℕ) :
    (pairSetting χ h e).TwoAdic (pairChar χ h e) e where
  dvd := Nat.dvd_lcm_left _ _
  K_le u hu := by
    have hu' : pairMap χ e u = 1 := hu
    rw [MonoidHom.mem_ker]
    exact congrArg Prod.fst hu'
  card_A₀_le := card_A₀_le χ h e

end ZetaBalance
