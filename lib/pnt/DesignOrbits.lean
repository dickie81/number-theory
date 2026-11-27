import SharpAdm
import GainConsts

/-!
# The orbit combinatorics of the design

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain` and the design's Stage 2): the
design-level definitions that the gain's local exponents and the Stage 2 conditions G1 and G2 read (the gain spec,
§2.4, §2.5 and §4.2), and the combinatorial facts about them that the gain's per-orbit inequality and its losses use.
Nothing here changes `SharpAdm`: the Stage 2 clauses are added there later, from these definitions.

**Orbits** (generic in a finite abelian group). At an inert or signal prime `p`, with the twist `c = twA κ` and
`h_p = hP_c(p)` (`Setting.hPtw`), the step on `A` is `σ_p = h_p` for inert `p` and `h_p²` for signal `p`
(`Setting.orbitStep`): the positions `pos_p(1, t; s)` of `CMHost` at the sign `1` are `(1, t·σ_p^i)`. Each
`⟨σ_p⟩`-orbit has a base point (`basePoint`, a fixed element of the orbit, the same for all of it:
`basePoint_mul_pow`), and `t` sits at the position `orbitPos σ t < ord σ` from it
(`basePoint_mul_orbitPos`). The tops on the orbit of `t₀` are at the positions `P(t₀) = {i < ord σ : t₀σ^i ∈ TT}`
(`topPositions`; `orbitPos_mem_topPositions`), and a top is *V-type* when its position is even (`IsVType`). The
partner of `t` at step `e` is `pos_p(1, t; e)`; a *collision* at `(s, e)` (`Setting.Collides`) is an odd `e` below the
period `nP(p)` at which the partner is a top: within one period every place is hit once, so this is the first hit.
Signal primes have none (`Setting.not_collides_of_signal`: odd partners have sign `−1`), and at inert primes a
collision is a top at `s·h_p^e` (`Setting.collides_iff_of_inert`).

**The tile condition** (`TilePar.IsGood`), for a set `P` of positions in `[0, n′)` read cyclically and parameters
`(L₂, K, r, u, M₀, G′, N₁)` (`TilePar`): (A) every cyclic window of `L₂` positions holds at most `K` points
(`winCard`); (T) cutting `[0, n′)` into `B = ⌊n′/((6r + 1)u)⌋` blocks of `6r + 1` cells of `u` positions
(`TilePar.blockLen`, `TilePar.cellPts`), a block is *marked* (`TilePar.Marked`) when its odd cells are empty and each
even cell holds exactly one point, at an even position, and every run of `M₀ + 1` consecutive blocks (cyclically)
holds a marked one; (I) every cyclic window of `G′` positions holds at most `N₁` points.

**What a good set gives the per-orbit inequality** (the spacing of the V-tops):
* fewer than `r` tops in any window of at most `L₂` positions (`TilePar.IsGood.winCard_le_K`, with `K < r`), in
  particular in the `L₁(p) ≤ L₂/2` positions before any top (`Setting.DesignAdm.two_mul_scL1_le`);
* at most `N₁` tops in any window of at most `G′` positions (`TilePar.IsGood.winCard_le_N₁`);
* before every position `i` there is a V-top at distance `1 ≤ d < G′` (`TilePar.IsGood.prevV_spec`), and
  `prevV n′ P i` (the distance to the nearest one, `prevV`) is such a `d`. The proof takes the cell `0` point of a
  marked block among the `M₀ + 1` blocks before the block of `i` when `n′ > G′ ≥ (M₀ + 3)(6r + 1)u`, so at distance
  `< (M₀ + 3)(6r + 1)u`, and otherwise the cell `0` or cell `2` point of any marked block that is not `i`.

**The design's parameters** (`tilePar x ε k`): `h* = 2 + 8ε`, `K = ⌈8(h* + 2)/ε⌉`, `r = K + 1`, `u = ⌈1/δ₁⌉`,
`M₀ = ⌈(h* + 3)·10^{6r+1}·log x⌉`, `G′ = (M₀ + 5)(6r + 1)u`, `N₁ = ⌈max(6e·G′δ₁, (h* + 3)·log₂ x)⌉ + 1` and
`L₂ = 2⌈log_{x^{ε/10}}((kx^{26})⁴)⌉`; and `L₁(p) = ⌈log_p((kx^{26})⁴)⌉` (`scL1`). Every non-split prime exceeds
`x^{ε/10}` at an admissible design (`Setting.DesignAdm.lt_of_cls_ne_split`: `(−d/p) = (p/d) = −1` by reciprocity, as
`d ≡ 3 (mod 4)`, against A3), so `2L₁(p) ≤ L₂` there.

**The design-level sets.** At a design `Dg`: goodness of a top at `p` (`SharpDesign.IsGoodAt`: the position set of
its base point for the step `σ_p` at `twA κ` is good, with `n′ = ord σ_p`) and the bad tops (`SharpDesign.badTops`); the
primes `PR = {p < X′ prime, inert, ord h_p ≥ x^{ε/4}}` (`Setting.PR`), the band (`InBand`, with
`ρ_B = 4N_⋆x^ε·La/k + c_ρc_N·log x·La/k`, `scRhoB`, `N_⋆ = 2|A|δ₁`, `scNstar`, `La = c_La·N₁²·log a`, `scLa`), the
threshold `p₀ = k²x^{26}` (`scP0`), the candidates (`Setting.cand`: the primes of `PR` of even order not in the band
when `p ≥ p₀`), and the windows `W_a = ℤ ∩ [a, a + a/(kx^{13})]` (`scWa`, A7's window: `SharpDesign.FamAt.aZ_mem_scWa`)
and `W_b = ℤ ∩ [b′, b′ + N_⋆x^ε·La·b′/k]` (`scWb`). The constants are the package `Kg` (`GainConsts`).

**Small orders are sparse** (`Setting.TwoAdic.sum_log_div_le`). The clause the gain needs of the setting
(`Setting.TwoAdic`, the gain spec §4.5): `2^{e+2} ∣ QS`, `K` lies in the classes `≡ ±1 (mod 2^{e+2})`, so `A` maps to
`H_e = (ℤ/2^{e+2})ˣ/±1`, and `|A₀| ≤ 2^e`; the settings of pairs have it (`pairSetting_twoAdic`). For a non-split
prime `p` with `ord(c·[p]_A) ≤ y` or odd, the image `[p]` in `H_e` (the twist maps to the class of `−1`, which is
trivial) has order `2^s ∣ 2^e` with `2^s ≤ y`, so `p^{2^s} ≡ ±1 (mod 2^{e+2})`, and then `p ≡ ±1 (mod 2^{e+2−s})`
(`two_pow_dvd_sub_or_add`: squaring an odd `w ≢ ±1 (mod 2^{j+1})` cannot reach `±1 (mod 2^{j+2})`). So all such
`p < X` lie in the classes `±1` modulo one `Q ≥ 2` with `Qy ≥ 2^{e+2} ≥ 4|A|/ord κ`, and a harmonic sum over those
classes (`sum_log_div_le_of_dvd`) gives `Σ log p/p ≤ 3·ord κ·y·log X(1 + log X)/(4|A|)`. At an admissible design and
`X = X′` this is at most `y·(log X′)²·x^{−(2+7ε)}` (`Setting.DesignAdm.sum_log_div_smallOrder_le`).

**Against the spec.**
* The sparsity bound has `x^{−(2+7ε)}`, not `x^{−(2+8ε)}`, and `y`, not `y²`: the clauses give `2^e ≥ |A|/ord κ ≥
  x^{2+8ε−ε/100}` only (the builder's level has `2^e ≥ x^{2+8ε}`, which `Setting.TwoAdic` does not record); either
  is far below the gain's `x^{−2}`. The sum is over the non-split primes: a prime dividing `QS` (such as `2`) has
  `[p]_A = 1` by convention and would break any such bound. It covers odd orders too.
* `L₂` is the closed form above, at least `2L₁(p)` for every non-split `p`, in place of `2·max_{p inert} L₁(p)`.
* The candidates ask the order of `h_p` to be even, which the served gain needs (the tile condition reads even
  positions); odd orders are sparse by the bound above.
* `PR`, the band, `p₀`, the windows and the candidates are functions of the setting, `κ`, `x`, `ε` and `k`, not of the
  design; `tilePar` reads `k` only. The tile condition bundles its parameters (`TilePar`) in place of
  `IsGoodSet n′ P L₂ K r u M₀ G′ N₁`.
* The 2-adic clause is a hypothesis (`Setting.TwoAdic`), not a clause of `SharpDesign.Adm`, which this file leaves
  alone; `pairSetting_twoAdic` discharges it for the settings that the design is built on.
-/

open Finset

namespace ZetaBalance

/-! ## The prime classes -/

namespace Setting

variable (S : Setting)

/-- **A prime that is not split has `(p/d) = −1`**: the first coordinate of its Frobenius is `sgn_d(p) ≠ 1`. -/
theorem legendreSym_eq_neg_one_of_cls {p : ℕ} (h : S.cls p ≠ .split) : legendreSym S.d p = -1 := by
  by_contra hne
  exact h (by simp [cls, frob, sgn, hne])

/-- **A non-split prime does not divide `N`**: the primes of `QS` and `q` have `(p/d) = 1`, and `(d/d) = 0`. -/
theorem not_dvd_N_of_cls {p : ℕ} (hp : p.Prime) (h : S.cls p ≠ .split) : ¬ p ∣ S.N := by
  have hl := S.legendreSym_eq_neg_one_of_cls h
  intro hdvd
  have hdvd' : p ∣ S.QS * S.q * S.d := hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd' with h1 | hd
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with hQ | hq
    · rw [S.split p hp hQ] at hl
      norm_num at hl
    · rw [(Nat.prime_dvd_prime_iff_eq hp Fact.out).1 hq, S.q_mod_d] at hl
      norm_num at hl
  · rw [(Nat.prime_dvd_prime_iff_eq hp Fact.out).1 hd, (legendreSym.eq_zero_iff _ _).2 (by simp)] at hl
    norm_num at hl

/-- **`(−d/p) = −1` at a non-split prime**, for `d ≡ 3 (mod 4)`: `(−d/p) = (−1/p)(d/p)` and reciprocity gives
`(d/p) = (−1/p)(p/d)`, with `(p/d) = −1`. -/
theorem jacobiSym_neg_d_of_cls {p : ℕ} (hp : p.Prime) (hd : S.d % 4 = 3) (h : S.cls p ≠ .split) :
    jacobiSym (-(S.d : ℤ)) p = -1 := by
  have hl := S.legendreSym_eq_neg_one_of_cls h
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, S.two_mod_d] at hl
    norm_num at hl
  rw [← jacobiSym.legendreSym.to_jacobiSym, show (-(S.d : ℤ)) = -1 * S.d by ring, legendreSym.mul,
    legendreSym.at_neg_one hp2]
  rcases Nat.Prime.eq_two_or_odd hp with h2 | h2
  · exact absurd h2 hp2
  · rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h4 | h4
    · rw [legendreSym.quadratic_reciprocity_one_mod_four h4 S.d_ne_two] at hl
      rw [ZMod.χ₄_nat_one_mod_four h4, hl]
      norm_num
    · rw [legendreSym.quadratic_reciprocity_three_mod_four h4 hd] at hl
      rw [ZMod.χ₄_nat_three_mod_four h4]
      linarith

/-- **Non-split primes are large** at an admissible design: `(−d/p) = −1` (`jacobiSym_neg_d_of_cls`, as
`d ≡ 7 (mod 16)`), while A3 has `(−d/p) = 1` for `p ≤ x^{ε/10}`. -/
theorem DesignAdm.lt_of_cls_ne_split {S : Setting} {κ : S.A →* ℂˣ} {x ε : ℝ} (hS : S.DesignAdm κ x ε) {p : ℕ}
    (hp : p.Prime) (h : S.cls p ≠ .split) : x ^ (ε / 10) < p := by
  by_contra hle
  have h1 := hS.leg_small p hp (not_lt.1 hle)
  rw [S.jacobiSym_neg_d_of_cls hp (by have := hS.d_mod; omega) h] at h1
  norm_num at h1

end Setting

/-! ## Orbits and positions -/

section Orbits

variable {A : Type*} [CommGroup A] [Finite A]

/-- **The base point** of the `⟨σ⟩`-orbit of `t`: a fixed element of the orbit (the representative of its class),
the same for the whole orbit (`basePoint_mul_pow`). -/
noncomputable def basePoint (σ t : A) : A :=
  (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) A) t).out

/-- **Every element is on its base point's orbit**: `t = basePoint σ t · σ^i` for some `i < ord σ`. -/
theorem exists_basePoint_mul_pow (σ t : A) : ∃ i < orderOf σ, basePoint σ t * σ ^ i = t := by
  classical
  obtain ⟨⟨g, hg⟩, hgt⟩ := MulAction.mem_orbit_iff.1
    (MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers σ) A) t))
  have hgt' : g * t = basePoint σ t := hgt
  obtain ⟨i, hi, hgi⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 (inv_mem hg))
  refine ⟨i, Finset.mem_range.1 hi, ?_⟩
  rw [hgi, ← hgt', mul_comm g t, mul_inv_cancel_right]

omit [Finite A] in
/-- **The base point is constant on orbits**: `basePoint σ (tσ^i) = basePoint σ t`. -/
theorem basePoint_mul_pow (σ t : A) (i : ℕ) : basePoint σ (t * σ ^ i) = basePoint σ t := by
  unfold basePoint
  congr 1
  exact Quotient.sound (MulAction.orbitRel_apply.2
    ⟨⟨σ ^ i, pow_mem (Subgroup.mem_zpowers σ) i⟩, by simp [mul_comm]⟩)

/-- **The position of `t` on its orbit**: the `i < ord σ` with `basePoint σ t · σ^i = t`. -/
noncomputable def orbitPos (σ t : A) : ℕ := (exists_basePoint_mul_pow σ t).choose

/-- **The position is below the period** `ord σ`. -/
theorem orbitPos_lt (σ t : A) : orbitPos σ t < orderOf σ := (exists_basePoint_mul_pow σ t).choose_spec.1

/-- **`t` sits at its position**: `basePoint σ t · σ^{orbitPos σ t} = t`. -/
theorem basePoint_mul_orbitPos (σ t : A) : basePoint σ t * σ ^ orbitPos σ t = t :=
  (exists_basePoint_mul_pow σ t).choose_spec.2

/-- **A top is V-type** at the step `σ` when it sits at an even position from its base point. -/
def IsVType (σ t : A) : Prop := Even (orbitPos σ t)

variable [DecidableEq A]

/-- **The positions of the tops** on the orbit of `t₀`: `P(t₀) = {i < ord σ : t₀σ^i ∈ TT}`. -/
noncomputable def topPositions (TT : Finset A) (σ t₀ : A) : Finset ℕ :=
  (range (orderOf σ)).filter fun i => t₀ * σ ^ i ∈ TT

/-- **A top sits at its position**: `orbitPos σ t ∈ P(basePoint σ t)` exactly when `t ∈ TT`. -/
theorem orbitPos_mem_topPositions (TT : Finset A) (σ t : A) :
    orbitPos σ t ∈ topPositions TT σ (basePoint σ t) ↔ t ∈ TT := by
  simp [topPositions, orbitPos_lt, basePoint_mul_orbitPos]

end Orbits

namespace Setting

variable (S : Setting)

/-- **The step on `A`** at `p` with the twist `c`: `σ_p = h_p` at inert `p`, `h_p²` at signal `p`, where
`h_p = hP_c(p)`. -/
noncomputable def orbitStep (c : S.A) (p : ℕ) : S.A :=
  if S.cls p = .signal then S.hPtw c p ^ 2 else S.hPtw c p

/-- **A collision at `(s, e)`**: `e` is odd and below the period `nP(p)`, and the partner `pos_p(1, s; e)` is a top
(a place `(1, t)` with `t ∈ TT`). -/
def Collides (c : S.A) (p : ℕ) (TT : Finset S.A) (s : S.A) (e : ℕ) : Prop :=
  Odd e ∧ e < S.nP c p ∧ (S.pos c p (1, s) e).1 = 1 ∧ (S.pos c p (1, s) e).2 ∈ TT

variable {S}

/-- **No collisions at signal primes**: the partners at odd steps have sign `−1`. -/
theorem not_collides_of_signal {c : S.A} {p : ℕ} (h : S.cls p = .signal) (TT : Finset S.A) (s : S.A) (e : ℕ) :
    ¬ S.Collides c p TT s e := by
  rintro ⟨he, -, h1, -⟩
  simp [pos, h, he] at h1

/-- **Collisions at inert primes**: an odd `e < ord h_p` with `s·h_p^e ∈ TT`. -/
theorem collides_iff_of_inert {c : S.A} {p : ℕ} (h : S.cls p = .inert) (TT : Finset S.A) (s : S.A) (e : ℕ) :
    S.Collides c p TT s e ↔ Odd e ∧ e < orderOf (S.hPtw c p) ∧ s * S.hPtw c p ^ e ∈ TT := by
  simp [Collides, pos, nP, h]

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

/-- **A longer window holds at least as many points.** -/
theorem winCard_mono {n' : ℕ} {P : Finset ℕ} {s L L' : ℕ} (h : L ≤ L') : winCard n' P s L ≤ winCard n' P s L' :=
  card_le_card (filter_subset_filter _ (range_subset_range.2 h))

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

variable {T}

/-- **An even cell of a marked block holds a point** of `P`, at an even position. -/
theorem Marked.exists_mem {P : Finset ℕ} {b : ℕ} (h : T.Marked P b) {i : ℕ} (hi : i < 6 * T.r + 1)
    (he : Even i) : ∃ q, Even q ∧ q ∈ P ∧ b * T.blockLen + i * T.u ≤ q ∧ q < b * T.blockLen + (i + 1) * T.u := by
  obtain ⟨q, hq, hc⟩ := (h i hi).2 he
  have hm : q ∈ T.cellPts P b i := hc ▸ mem_singleton_self q
  simp only [cellPts, mem_filter, mem_Ico] at hm
  exact ⟨q, hq, hm.2, hm.1.1, hm.1.2⟩

/-- **Fewer than `r` tops nearby**: a good set has at most `K` points in any window of at most `L₂` positions. -/
theorem IsGood.winCard_le_K {n' : ℕ} {P : Finset ℕ} (h : T.IsGood n' P) {s L : ℕ} (hs : s < n') (hL : L ≤ T.L₂) :
    winCard n' P s L ≤ T.K :=
  (winCard_mono hL).trans (h.window s hs)

/-- **At most `N₁` tops nearby**: a good set has at most `N₁` points in any window of at most `G′` positions. -/
theorem IsGood.winCard_le_N₁ {n' : ℕ} {P : Finset ℕ} (h : T.IsGood n' P) {s L : ℕ} (hs : s < n') (hL : L ≤ T.G') :
    winCard n' P s L ≤ T.N₁ :=
  (winCard_mono hL).trans (h.dense s hs)

end TilePar

/-- **The distance back to the nearest V-position**: the least `d ∈ [1, n′]` such that the position `i − d`
(mod `n′`) is an even point of `P`, and `0` if there is none. -/
noncomputable def prevV (n' : ℕ) (P : Finset ℕ) (i : ℕ) : ℕ :=
  if h : ((Icc 1 n').filter fun d => (i + n' - d) % n' ∈ P ∧ Even ((i + n' - d) % n')).Nonempty then
    ((Icc 1 n').filter fun d => (i + n' - d) % n' ∈ P ∧ Even ((i + n' - d) % n')).min' h
  else 0

/-- **`prevV` is the nearest V-position**: a V-position at distance `d ∈ [1, n′]` back from `i` bounds
`prevV n′ P i`, which is then the distance to a V-position. -/
theorem prevV_spec_of {n' : ℕ} {P : Finset ℕ} {i d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n') (hP : (i + n' - d) % n' ∈ P)
    (he : Even ((i + n' - d) % n')) :
    1 ≤ prevV n' P i ∧ prevV n' P i ≤ d ∧ (i + n' - prevV n' P i) % n' ∈ P ∧
      Even ((i + n' - prevV n' P i) % n') := by
  have hmem : d ∈ (Icc 1 n').filter (fun d => (i + n' - d) % n' ∈ P ∧ Even ((i + n' - d) % n')) :=
    mem_filter.2 ⟨mem_Icc.2 ⟨hd1, hdn⟩, hP, he⟩
  have hne : ((Icc 1 n').filter fun d => (i + n' - d) % n' ∈ P ∧ Even ((i + n' - d) % n')).Nonempty := ⟨d, hmem⟩
  rw [prevV, dite_eq_left hne]
  have hm := min'_mem _ hne
  rw [mem_filter, mem_Icc] at hm
  exact ⟨hm.1.1, min'_le _ _ hmem, hm.2.1, hm.2.2⟩

namespace TilePar

variable {T : TilePar}

/-- **A V-position behind every position** of a good set: some even point `q ≠ i` of `P` lies at backward distance
`< G′` from `i`. With `c = (6r + 1)u` and `B = ⌊n′/c⌋`: if `n′ ≤ G′`, the cell `0` or cell `2` point of a marked block
that is not `i`; otherwise `B ≥ M₀ + 3`, and the cell `0` point of a marked block `b − k`, `1 ≤ k ≤ M₀ + 1`, for the
block `b = ⌊i/c⌋ ≤ B` of `i`, at distance `< (k + 2)c`. -/
theorem IsGood.exists_prev {n' : ℕ} {P : Finset ℕ} (h : T.IsGood n' P) (hu : 1 ≤ T.u) (hr : 1 ≤ T.r)
    (hG : (T.M₀ + 3) * T.blockLen ≤ T.G') (hB : T.blockLen ≤ n') {i : ℕ} (hi : i < n') :
    ∃ q < n', q ∈ P ∧ Even q ∧ ((q < i ∧ i - q < T.G') ∨ (i < q ∧ i + n' - q < T.G')) := by
  obtain ⟨c, hc_def⟩ : ∃ c, T.blockLen = c := ⟨_, rfl⟩
  have htile := h.tile
  rw [hc_def] at htile hG hB
  obtain ⟨B, hB_def⟩ : ∃ B, n' / c = B := ⟨_, rfl⟩
  rw [hB_def] at htile
  have hc : 1 ≤ c := by
    rw [← hc_def, blockLen]
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hcu : 3 * T.u ≤ c := by
    rw [← hc_def, blockLen]
    nlinarith
  have hB1 : 1 ≤ B := hB_def ▸ (Nat.le_div_iff_mul_le hc).2 (by omega)
  have hBc : B * c ≤ n' := hB_def ▸ Nat.div_mul_le_self n' c
  have hBc' : n' < B * c + c := hB_def ▸ Nat.lt_div_mul_add hc
  -- a marked block below `B` has points in its cells `0` and `2`, below `n′`
  have hpts : ∀ b' < B, T.Marked P b' → ∃ q₀ q₂, Even q₀ ∧ q₀ ∈ P ∧ b' * c ≤ q₀ ∧ q₀ < b' * c + T.u ∧
      Even q₂ ∧ q₂ ∈ P ∧ b' * c + 2 * T.u ≤ q₂ ∧ q₂ < n' := by
    intro b' hb' hm
    obtain ⟨q₀, he₀, hq₀, h0l, h0u⟩ := hm.exists_mem (i := 0) (by omega) (by decide)
    obtain ⟨q₂, he₂, hq₂, h2l, h2u⟩ := hm.exists_mem (i := 2) (by omega) (by decide)
    rw [hc_def] at h0l h0u h2l h2u
    have hb'c : b' * c + c ≤ B * c := by
      have := Nat.mul_le_mul_right c (show b' + 1 ≤ B by omega)
      rwa [add_mul, one_mul] at this
    refine ⟨q₀, q₂, he₀, hq₀, by simpa using h0l, by simpa using h0u, he₂, hq₂, by simpa using h2l, ?_⟩
    have : (2 + 1) * T.u = 3 * T.u := by ring
    rw [this] at h2u
    omega
  by_cases hn : n' ≤ T.G'
  · -- a marked block, and one of its two points that is not `i`
    obtain ⟨j, -, hm⟩ := htile 0 (by omega)
    obtain ⟨q₀, q₂, he₀, hq₀, h0l, h0u, he₂, hq₂, h2l, h2n⟩ := hpts _ (Nat.mod_lt _ (by omega)) hm
    by_cases hq : q₀ = i
    · exact ⟨q₂, h2n, hq₂, he₂, by omega⟩
    · have hb : ((0 + j) % B) * c + c ≤ B * c := by
        have := Nat.mul_le_mul_right c (show (0 + j) % B + 1 ≤ B from Nat.mod_lt (0 + j) (by omega))
        rwa [add_mul, one_mul] at this
      exact ⟨q₀, by omega, hq₀, he₀, by omega⟩
  · -- `B ≥ M₀ + 3`: a marked block among the `M₀ + 1` blocks before the block of `i`
    have hBM : T.M₀ + 3 ≤ B := hB_def ▸ (Nat.le_div_iff_mul_le hc).2 (by omega)
    obtain ⟨b, hb_def⟩ : ∃ b, i / c = b := ⟨_, rfl⟩
    have hbc : b * c ≤ i := hb_def ▸ Nat.div_mul_le_self i c
    have hbc' : i < b * c + c := hb_def ▸ Nat.lt_div_mul_add hc
    have hbB : b ≤ B := by
      by_contra hlt
      have := Nat.mul_le_mul_right c (show B + 1 ≤ b by omega)
      rw [add_mul, one_mul] at this
      omega
    obtain ⟨j, hj, hm⟩ := htile ((b + B - (T.M₀ + 1)) % B) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod] at hm
    obtain ⟨k, hk_def⟩ : ∃ k, k = T.M₀ + 1 - j := ⟨_, rfl⟩
    have hk : b + B - (T.M₀ + 1) + j = b + B - k := by omega
    rw [hk] at hm
    by_cases hkb : k ≤ b
    · -- the marked block `b − k` lies before `i`
      have hb' : (b + B - k) % B = b - k := by
        rw [show b + B - k = b - k + B by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hb'] at hm
      obtain ⟨q₀, -, he₀, hq₀, h0l, h0u, -⟩ := hpts _ (by omega) hm
      have h1 : (b - k) * c + c ≤ b * c := by
        have := Nat.mul_le_mul_right c (show b - k + 1 ≤ b by omega)
        rwa [add_mul, one_mul] at this
      have h2 : b * c + c ≤ (b - k) * c + (T.M₀ + 3) * c := by
        have := Nat.mul_le_mul_right c (show b + 1 ≤ b - k + (T.M₀ + 3) by omega)
        rwa [add_mul, add_mul, one_mul] at this
      exact ⟨q₀, by omega, hq₀, he₀, Or.inl ⟨by omega, by omega⟩⟩
    · -- the marked block `b + B − k` lies after `i`, reached by going round
      have hb' : (b + B - k) % B = b + B - k := Nat.mod_eq_of_lt (by omega)
      rw [hb'] at hm
      obtain ⟨q₀, -, he₀, hq₀, h0l, h0u, -⟩ := hpts _ (by omega) hm
      have h1 : b * c + c ≤ (b + B - k) * c := by
        have := Nat.mul_le_mul_right c (show b + 1 ≤ b + B - k by omega)
        rwa [add_mul, one_mul] at this
      have h2 : b * c + c + (B * c + c) ≤ (b + B - k) * c + (T.M₀ + 3) * c := by
        have := Nat.mul_le_mul_right c (show b + 1 + (B + 1) ≤ b + B - k + (T.M₀ + 3) by omega)
        rwa [add_mul, add_mul, add_mul, add_mul, one_mul] at this
      have h3 : (b + B - k) * c + c ≤ B * c := by
        have := Nat.mul_le_mul_right c (show b + B - k + 1 ≤ B by omega)
        rwa [add_mul, one_mul] at this
      exact ⟨q₀, by omega, hq₀, he₀, Or.inr ⟨by omega, by omega⟩⟩

/-- **The spacing of the V-tops**: in a good set, before every position `i < n′` there is a V-position (an even
point of `P`) at distance `prevV n′ P i ∈ [1, G′)`, the nearest one; the tile condition holds with blocks of length
`(6r + 1)u ≤ n′`, `u, r ≥ 1` and `G′ ≥ (M₀ + 3)(6r + 1)u` (`tilePar_ok` for the design). -/
theorem IsGood.prevV_spec {n' : ℕ} {P : Finset ℕ} (h : T.IsGood n' P) (hu : 1 ≤ T.u) (hr : 1 ≤ T.r)
    (hG : (T.M₀ + 3) * T.blockLen ≤ T.G') (hB : T.blockLen ≤ n') {i : ℕ} (hi : i < n') :
    1 ≤ prevV n' P i ∧ prevV n' P i < T.G' ∧ (i + n' - prevV n' P i) % n' ∈ P ∧
      Even ((i + n' - prevV n' P i) % n') := by
  obtain ⟨q, hqn, hqP, hqe, hq⟩ := h.exists_prev hu hr hG hB hi
  rcases hq with ⟨hlt, hd⟩ | ⟨hlt, hd⟩
  · have e : (i + n' - (i - q)) % n' = q := by
      rw [show i + n' - (i - q) = q + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hqn]
    obtain ⟨h1, h2, h3, h4⟩ := prevV_spec_of (n' := n') (P := P) (i := i) (d := i - q) (by omega) (by omega)
      (by rw [e]; exact hqP) (by rw [e]; exact hqe)
    exact ⟨h1, by omega, h3, h4⟩
  · have e : (i + n' - (i + n' - q)) % n' = q := by
      rw [show i + n' - (i + n' - q) = q by omega, Nat.mod_eq_of_lt hqn]
    obtain ⟨h1, h2, h3, h4⟩ := prevV_spec_of (n' := n') (P := P) (i := i) (d := i + n' - q) (by omega) (by omega)
      (by rw [e]; exact hqP) (by rw [e]; exact hqe)
    exact ⟨h1, by omega, h3, h4⟩

end TilePar

/-! ## The design's parameters -/

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

/-- **The side conditions of `TilePar.IsGood.prevV_spec`** for the design's parameters: `u ≥ 1` (for `x > 0`),
`r ≥ 1` and `G′ ≥ (M₀ + 3)(6r + 1)u`; and `K < r`. -/
theorem tilePar_ok {x : ℝ} (ε : ℝ) (k : ℕ) (hx : 0 < x) :
    1 ≤ (tilePar x ε k).u ∧ 1 ≤ (tilePar x ε k).r ∧
      ((tilePar x ε k).M₀ + 3) * (tilePar x ε k).blockLen ≤ (tilePar x ε k).G' ∧
      (tilePar x ε k).K < (tilePar x ε k).r := by
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (inv_pos.2 (Real.rpow_pos_of_pos hx _)))),
    Nat.le_add_left 1 _, Nat.mul_le_mul_right _ (by simp [tilePar]), Nat.lt_succ_self _⟩

/-- **The depth window at `p`**, `L₁(p) = ⌈log_p((kx^{26})⁴)⌉`. -/
noncomputable def scL1 (x : ℝ) (k p : ℕ) : ℕ := ⌈Real.logb p (((k : ℝ) * x ^ 26) ^ 4)⌉₊

/-- **`2L₁(p) ≤ L₂` for `p > x^{ε/10} > 1`**: `log_p` decreases in the base on arguments `≥ 1`. -/
theorem two_mul_scL1_le_of_lt {x ε : ℝ} {k p : ℕ} (hx : 1 ≤ x) (hk : 1 ≤ k) (h1 : 1 < x ^ (ε / 10))
    (hp : x ^ (ε / 10) < p) : 2 * scL1 x k p ≤ (tilePar x ε k).L₂ := by
  have hy : 1 ≤ ((k : ℝ) * x ^ 26) ^ 4 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk) (one_le_pow₀ hx))
  have hl1 : 0 < Real.log (x ^ (ε / 10)) := Real.log_pos h1
  show 2 * ⌈Real.logb p _⌉₊ ≤ 2 * ⌈Real.logb (x ^ (ε / 10)) _⌉₊
  gcongr
  exact div_le_div_of_nonneg_left (Real.log_nonneg hy) hl1 (Real.log_le_log (by linarith) hp.le)

/-- **`2L₁(p) ≤ L₂` at every non-split prime** of an admissible design (`lt_of_cls_ne_split`, and
`x^{ε/10} ≥ 4096`). -/
theorem Setting.DesignAdm.two_mul_scL1_le {S : Setting} {κ : S.A →* ℂˣ} {x ε : ℝ} (hS : S.DesignAdm κ x ε) {p : ℕ}
    (hp : p.Prime) (h : S.cls p ≠ .split) {k : ℕ} (hk : 1 ≤ k) : 2 * scL1 x k p ≤ (tilePar x ε k).L₂ :=
  two_mul_scL1_le_of_lt hS.big.one_lt.le hk
    (by linarith [hS.big.le_rpow (c := ε / 10) (by linarith [hS.big.ε_pos])]) (hS.lt_of_cls_ne_split hp h)

/-! ## The design-level sets -/

/-- **Twice the expected number of tops**, `N_⋆ = 2|A|δ₁`. -/
noncomputable def scNstar (S : Setting) (x ε : ℝ) : ℝ := 2 * Fintype.card S.A * scδ₁ x ε

/-- **The loss factor** of the band and of `W_b`, `La = c_La·N₁²·log a`. -/
noncomputable def scLa (x ε : ℝ) (k : ℕ) : ℝ := Kg.cLa * ((tilePar x ε k).N₁ : ℝ) ^ 2 * Real.log (scA x ε)

/-- **The relative width of the band**, `ρ_B = 4N_⋆x^ε·La/k + c_ρc_N·log x·La/k`. -/
noncomputable def scRhoB (S : Setting) (x ε : ℝ) (k : ℕ) : ℝ :=
  4 * scNstar S x ε * x ^ ε * scLa x ε k / k + Kg.cρ * Kg.cN * Real.log x * scLa x ε k / k

/-- **The band**: some power `p^i`, `i ≥ 1`, lies in `[X′(1 − ρ_B), X′(1 + ρ_B)]`. -/
def InBand (S : Setting) (x ε : ℝ) (k p : ℕ) : Prop :=
  ∃ i, 1 ≤ i ∧ scX' x ε * (1 - scRhoB S x ε k) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ scX' x ε * (1 + scRhoB S x ε k)

/-- **The threshold of the local theorems**, `p₀ = k²x^{26}`: the first holds from `p₀` on, the second below. -/
noncomputable def scP0 (x : ℝ) (k : ℕ) : ℝ := (k : ℝ) ^ 2 * x ^ 26

/-- **The window of the scales** `W_a = ℤ ∩ [a, a + a/(kx^{13})]`. -/
noncomputable def scWa (x ε : ℝ) (k : ℕ) : Finset ℤ := Icc ⌈scA x ε⌉ ⌊scA x ε + scA x ε / (k * x ^ 13)⌋

/-- **The window of the top shifts** `W_b = ℤ ∩ [b′, b′ + N_⋆x^ε·La·b′/k]`. -/
noncomputable def scWb (S : Setting) (x ε : ℝ) (k : ℕ) : Finset ℤ :=
  Icc ⌈scB' x ε⌉ ⌊scB' x ε + scNstar S x ε * x ^ ε * scLa x ε k * scB' x ε / k⌋

/-- **Membership in `W_a`**: `a ≤ z ≤ a + a/(kx^{13})`. -/
theorem mem_scWa {x ε : ℝ} {k : ℕ} {z : ℤ} :
    z ∈ scWa x ε k ↔ scA x ε ≤ z ∧ (z : ℝ) ≤ scA x ε + scA x ε / (k * x ^ 13) := by
  rw [scWa, mem_Icc, Int.ceil_le, Int.le_floor]

/-- **Membership in `W_b`**: `b′ ≤ z ≤ b′ + N_⋆x^ε·La·b′/k`. -/
theorem mem_scWb {S : Setting} {x ε : ℝ} {k : ℕ} {z : ℤ} :
    z ∈ scWb S x ε k ↔ scB' x ε ≤ z ∧ (z : ℝ) ≤ scB' x ε + scNstar S x ε * x ^ ε * scLa x ε k * scB' x ε / k := by
  rw [scWb, mem_Icc, Int.ceil_le, Int.le_floor]

namespace Setting

variable (S : Setting)

/-- **The primes of the tile condition** `PR = {p < X′ prime, inert, ord h_p ≥ x^{ε/4}}`, with `h_p = hP_c(p)` at the
twist `c = twA κ`. -/
noncomputable def PR (κ : S.A →* ℂˣ) (x ε : ℝ) : Finset ℕ :=
  (range ⌈scX' x ε⌉₊).filter fun p => p.Prime ∧ S.cls p = .inert ∧ x ^ (ε / 4) ≤ orderOf (S.hPtw (S.twA κ) p)

open scoped Classical in
/-- **The candidates**: the primes of `PR` with `ord h_p` even that are not in the band when `p ≥ p₀`. -/
noncomputable def cand (κ : S.A →* ℂˣ) (x ε : ℝ) (k : ℕ) : Finset ℕ :=
  (S.PR κ x ε).filter fun p => Even (orderOf (S.hPtw (S.twA κ) p)) ∧ (scP0 x k ≤ p → ¬ InBand S x ε k p)

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

/-- **The scales lie in `W_a`** (A7). -/
theorem FamAt.aZ_mem_scWa {pr : DesignPar S} (hF : Dg.FamAt pr) {t : S.A} (ht : t ∈ Dg.TT) :
    pr.aZ t ∈ scWa x ε Dg.R.k :=
  mem_scWa.2 (hF.a_mem t ht)

end SharpDesign

/-! ## Small orders are sparse -/

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

/-- **Squaring in the 2-adic integers**: for odd `w`, `2^{j+2} ∣ w² − 1` gives `2^{j+1} ∣ w − 1` or `2^{j+1} ∣ w + 1`.
With `w = 2m + 1`, `w² − 1 = 4m(m + 1)` and one of `m`, `m + 1` is odd. -/
theorem two_pow_dvd_of_sq {w : ℤ} (hw : Odd w) {j : ℕ} (h : (2 : ℤ) ^ (j + 2) ∣ w ^ 2 - 1) :
    (2 : ℤ) ^ (j + 1) ∣ w - 1 ∨ (2 : ℤ) ^ (j + 1) ∣ w + 1 := by
  obtain ⟨m, rfl⟩ := hw
  have e1 : (2 * m + 1) ^ 2 - 1 = 2 ^ 2 * (m * (m + 1)) := by ring
  rw [e1, pow_add, mul_comm ((2 : ℤ) ^ j)] at h
  have h' : (2 : ℤ) ^ j ∣ m * (m + 1) := (mul_dvd_mul_iff_left (by norm_num)).1 h
  rw [pow_succ', show 2 * m + 1 - 1 = 2 * m by ring, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
  rcases Int.even_or_odd m with ⟨l, hl⟩ | ⟨l, hl⟩
  · have hc : IsCoprime ((2 : ℤ) ^ j) (m + 1) := IsCoprime.pow_left ⟨-l, 1, by rw [hl]; ring⟩
    exact Or.inl (mul_dvd_mul_left 2 (hc.dvd_of_dvd_mul_right h'))
  · have hc : IsCoprime ((2 : ℤ) ^ j) m := IsCoprime.pow_left ⟨-l, 1, by rw [hl]; ring⟩
    exact Or.inr (mul_dvd_mul_left 2 (hc.dvd_of_dvd_mul_left h'))

/-- **Elements of 2-power order in `(ℤ/2^{e+2})ˣ/±1`**: for odd `u` and `r ≤ e`, `u^{2^r} ≡ ±1 (mod 2^{e+2})` gives
`u ≡ ±1 (mod 2^{e+2−r})`. By induction on `r`: `w = u^{2^{r−1}}` is odd, so `w² ≢ −1 (mod 4)`, and
`two_pow_dvd_of_sq`. -/
theorem two_pow_dvd_sub_or_add {u : ℤ} (hu : Odd u) : ∀ r e : ℕ, r ≤ e →
    ((2 : ℤ) ^ (e + 2) ∣ u ^ 2 ^ r - 1 ∨ (2 : ℤ) ^ (e + 2) ∣ u ^ 2 ^ r + 1) →
    (2 : ℤ) ^ (e + 2 - r) ∣ u - 1 ∨ (2 : ℤ) ^ (e + 2 - r) ∣ u + 1
  | 0, e, _, h => by simpa using h
  | r + 1, e, hr, h => by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hw : Odd (u ^ 2 ^ r) := hu.pow
    rw [show (2 : ℕ) ^ (r + 1) = 2 ^ r * 2 from pow_succ 2 r, pow_mul] at h
    have h1 : (2 : ℤ) ^ (e' + 1 + 2) ∣ (u ^ 2 ^ r) ^ 2 - 1 := by
      rcases h with h | h
      · exact h
      · exfalso
        obtain ⟨m, hm⟩ := hw
        have h4 : (4 : ℤ) ∣ (u ^ 2 ^ r) ^ 2 + 1 :=
          (show (4 : ℤ) = 2 ^ 2 by norm_num) ▸ (pow_dvd_pow 2 (by omega)).trans h
        rw [hm, show (2 * m + 1) ^ 2 + 1 = 4 * (m ^ 2 + m) + 2 by ring] at h4
        omega
    have := two_pow_dvd_sub_or_add hu r e' (by omega) (two_pow_dvd_of_sq hw h1)
    rwa [show e' + 2 - r = e' + 1 + 2 - (r + 1) by omega] at this

/-- **The harmonic bound** `Σ_{k ∈ [1, M]} 1/k ≤ 1 + log M` (Mathlib's `harmonic_le_one_add_log`). -/
theorem sum_Icc_one_div_le (M : ℕ) : ∑ k ∈ Icc 1 M, (1 : ℝ) / k ≤ 1 + Real.log M := by
  have := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  simpa [one_div] using this

/-- **A harmonic sum along an injection**: if `g` maps `P` injectively into `[1, M]` and `f(n) ≤ C/g(n)`, then
`Σ_P f ≤ C·Σ_{k ≤ M} 1/k`. -/
theorem sum_le_mul_sum_Icc {P : Finset ℕ} {M : ℕ} {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (g : ℕ → ℕ)
    (hg : ∀ n ∈ P, 1 ≤ g n ∧ g n ≤ M ∧ f n ≤ C / g n) (hinj : Set.InjOn g P) :
    ∑ n ∈ P, f n ≤ C * ∑ k ∈ Icc 1 M, (1 : ℝ) / k := by
  calc ∑ n ∈ P, f n ≤ ∑ n ∈ P, C / g n := sum_le_sum fun n hn => (hg n hn).2.2
    _ = ∑ k ∈ P.image g, C / k := (sum_image (f := fun k : ℕ => C / (k : ℝ)) hinj).symm
    _ ≤ ∑ k ∈ Icc 1 M, C / k := sum_le_sum_of_subset_of_nonneg
        (image_subset_iff.2 fun n hn => mem_Icc.2 ⟨(hg n hn).1, (hg n hn).2.1⟩) fun k _ _ => by positivity
    _ = C * ∑ k ∈ Icc 1 M, (1 : ℝ) / k := by rw [mul_sum]; simp only [mul_one_div]

/-- **`log n/n` over the classes `±1 (mod Q)`**: for `Q ≥ 2` and `X ≥ 1`, if every `n ∈ P` has `2 ≤ n < X` and
`n ≡ ±1 (mod Q)`, then `Σ_P log n/n ≤ 3·log X·(1 + log X)/Q`. Write `n = kQ + 1` or `n = kQ − 1` with
`1 ≤ k ≤ X`: then `1/n ≤ 1/(kQ)`, resp. `2/(kQ)`. -/
theorem sum_log_div_le_of_dvd {P : Finset ℕ} {Q : ℕ} {X : ℝ} (hQ : 2 ≤ Q) (hX : 1 ≤ X)
    (hP : ∀ n ∈ P, 2 ≤ n ∧ (n : ℝ) < X ∧ (Q ∣ n - 1 ∨ Q ∣ n + 1)) :
    ∑ n ∈ P, Real.log n / n ≤ 3 * Real.log X * (1 + Real.log X) / Q := by
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hH : ∑ k ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / k ≤ 1 + Real.log X := by
    have h1 : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast Nat.floor_pos.2 hX
    exact (sum_Icc_one_div_le _).trans (by gcongr; exact Nat.floor_le (by linarith))
  have hH0 : 0 ≤ ∑ k ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / k := sum_nonneg fun k _ => by positivity
  have hle : ∀ {n k : ℕ}, (n : ℝ) < X → k ≤ n → k ≤ ⌊X⌋₊ := fun {n k} hn hk =>
    Nat.le_floor (by linarith [show (k : ℝ) ≤ n by exact_mod_cast hk])
  -- the classes `+1` and `−1`, each through `n ↦ (n ∓ 1)/Q`
  have h1 : ∑ n ∈ P.filter (fun n => Q ∣ n - 1), (1 : ℝ) / n ≤ 1 / Q * (1 + Real.log X) := by
    refine (sum_le_mul_sum_Icc (M := ⌊X⌋₊) (C := 1 / Q) (by positivity) (fun n => (n - 1) / Q) (fun n hn => ?_)
      fun n hn n' hn' hnn' => ?_).trans (mul_le_mul_of_nonneg_left hH (by positivity))
    · obtain ⟨hn, hdvd⟩ := mem_filter.1 hn
      obtain ⟨h2, hX', -⟩ := hP n hn
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · omega
        · exact h
      have hdiv : (n - 1) / Q = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
      have hkQ : k ≤ Q * k := Nat.le_mul_of_pos_left k (by omega)
      refine ⟨by omega, hle hX' (by omega), ?_⟩
      rw [hdiv, div_div, one_div_le_one_div (by positivity) (by positivity)]
      have : (n : ℝ) = Q * k + 1 := by
        have : n = Q * k + 1 := by omega
        exact_mod_cast this
      rw [this]
      linarith
    · obtain ⟨k, hk⟩ := (mem_filter.1 hn).2
      obtain ⟨k', hk'⟩ := (mem_filter.1 hn').2
      have := (hP n (mem_filter.1 hn).1).1
      have := (hP n' (mem_filter.1 hn').1).1
      simp only [hk, hk', Nat.mul_div_cancel_left _ (show 0 < Q by omega)] at hnn'
      subst hnn'
      omega
  have h2 : ∑ n ∈ P.filter (fun n => ¬ Q ∣ n - 1), (1 : ℝ) / n ≤ 2 / Q * (1 + Real.log X) := by
    refine (sum_le_mul_sum_Icc (M := ⌊X⌋₊) (C := 2 / Q) (by positivity) (fun n => (n + 1) / Q) (fun n hn => ?_)
      fun n hn n' hn' hnn' => ?_).trans (mul_le_mul_of_nonneg_left hH (by positivity))
    · obtain ⟨hn, hndvd⟩ := mem_filter.1 hn
      obtain ⟨h2, hX', hdvd⟩ := hP n hn
      obtain ⟨k, hk⟩ := hdvd.resolve_left hndvd
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · omega
        · exact h
      have hdiv : (n + 1) / Q = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
      have hkQ : 2 * k ≤ Q * k := Nat.mul_le_mul_right k hQ
      refine ⟨by omega, hle hX' (by omega), ?_⟩
      rw [hdiv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (Q : ℝ) * k = n + 1 := by exact_mod_cast hk.symm
      rw [this]
      have : (2 : ℝ) ≤ n := by exact_mod_cast h2
      linarith
    · obtain ⟨k, hk⟩ := (hP n (mem_filter.1 hn).1).2.2.resolve_left (mem_filter.1 hn).2
      obtain ⟨k', hk'⟩ := (hP n' (mem_filter.1 hn').1).2.2.resolve_left (mem_filter.1 hn').2
      simp only [hk, hk', Nat.mul_div_cancel_left _ (show 0 < Q by omega)] at hnn'
      subst hnn'
      omega
  calc ∑ n ∈ P, Real.log n / n ≤ ∑ n ∈ P, Real.log X * ((1 : ℝ) / n) := by
        refine sum_le_sum fun n hn => ?_
        obtain ⟨h2, hX', -⟩ := hP n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (Real.log_le_log hn0 hX'.le) hn0.le
    _ = Real.log X * (∑ n ∈ P.filter (fun n => Q ∣ n - 1), (1 : ℝ) / n +
          ∑ n ∈ P.filter (fun n => ¬ Q ∣ n - 1), (1 : ℝ) / n) := by
        rw [sum_filter_add_sum_filter_not, mul_sum]
    _ ≤ Real.log X * (1 / Q * (1 + Real.log X) + 2 / Q * (1 + Real.log X)) := by gcongr
    _ = 3 * Real.log X * (1 + Real.log X) / Q := by ring

/-- **Small orders are sparse**: for a 2-adic setting (`Setting.TwoAdic`), `y ≥ 1` and `X ≥ 1`, the non-split
primes `p < X` with `ord(c·[p]_A) ≤ y` or odd, `c = twA κ`, have `Σ log p/p ≤ 3·ord κ·y·log X(1 + log X)/(4|A|)`.
The image `[p]` of `c·[p]_A` in `H_e` has order `2^s ≤ y` (it divides `ord(c·[p]_A)` and `|H_e| = 2^e`), so
`p ≡ ±1 (mod 2^{e+2−s})` (`two_pow_dvd_sub_or_add`), hence `p ≡ ±1 (mod Q)` for `Q = 2^{max(1, e+2−log₂ y)}`, with
`Qy ≥ 2^{e+2} ≥ 4|A₀| = 4|A|/ord κ`; then `sum_log_div_le_of_dvd`. -/
theorem Setting.TwoAdic.sum_log_div_le {S : Setting} {κ : S.A →* ℂˣ} {e : ℕ} (h : S.TwoAdic κ e) {y : ℕ}
    (hy : 1 ≤ y) {X : ℝ} (hX : 1 ≤ X) :
    ∑ p ∈ (range ⌈X⌉₊).filter (fun p => p.Prime ∧ S.cls p ≠ .split ∧
        (orderOf (S.hPtw (S.twA κ) p) ≤ y ∨ Odd (orderOf (S.hPtw (S.twA κ) p)))), Real.log p / p ≤
      3 * orderOf κ * y * (Real.log X * (1 + Real.log X)) / (4 * Fintype.card S.A) := by
  -- the map `A → H_e`
  let ψ : S.A →* He e := QuotientGroup.lift S.K _ h.K_le
  have hψ (u : (ZMod S.QS)ˣ) : ψ (S.mkA u) = (QuotientGroup.mk (ZMod.unitsMap h.dvd u) : He e) := rfl
  have hψc : ψ (S.twA κ) = 1 := by
    unfold twA
    split_ifs
    · exact map_one ψ
    · have hneg : ZMod.unitsMap h.dvd (-1) = -1 := Units.ext (by
        rw [ZMod.unitsMap_val, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, ZMod.cast_neg h.dvd,
          ZMod.cast_one h.dvd])
      rw [hψ, hneg, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_zpowers _
  set s₀ := Nat.log 2 y
  set Q := 2 ^ max 1 (e + 2 - s₀) with hQ_def
  have hQ2 : 2 ≤ Q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ Q := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have hQy : 2 ^ (e + 2) ≤ Q * y := by
    have hs₀ : 2 ^ s₀ ≤ y := Nat.pow_log_le_self 2 (by omega)
    calc 2 ^ (e + 2) ≤ 2 ^ (max 1 (e + 2 - s₀) + s₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = Q * 2 ^ s₀ := by rw [pow_add]
      _ ≤ Q * y := Nat.mul_le_mul_left _ hs₀
  -- each prime of the sum is `≡ ±1 (mod Q)`
  have key : ∀ p ∈ (range ⌈X⌉₊).filter (fun p => p.Prime ∧ S.cls p ≠ .split ∧
      (orderOf (S.hPtw (S.twA κ) p) ≤ y ∨ Odd (orderOf (S.hPtw (S.twA κ) p)))),
      2 ≤ p ∧ (p : ℝ) < X ∧ (Q ∣ p - 1 ∨ Q ∣ p + 1) := by
    intro p hp
    obtain ⟨hpX, hp, hcls, hord⟩ := mem_filter.1 hp
    refine ⟨hp.two_le, Nat.lt_ceil.1 (mem_range.1 hpX), ?_⟩
    have hpQS : ¬ p ∣ S.QS := fun hd => S.not_dvd_N_of_cls hp hcls (hd.trans S.QS_dvd_N)
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hpQS ((dvd_pow_self 2 (by omega)).trans h.dvd)
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hunit : IsUnit (p : ZMod S.QS) :=
      (ZMod.isUnit_iff_coprime p S.QS).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpQS)
    set v := ZMod.unitsMap h.dvd hunit.unit with hv_def
    have hv : (v : ZMod (2 ^ (e + 2))) = p := by
      rw [hv_def, ZMod.unitsMap_val, IsUnit.unit_spec, ZMod.cast_natCast h.dvd]
    have himg : ψ (S.hPtw (S.twA κ) p) = (QuotientGroup.mk v : He e) := by
      have h1 : ψ (S.hP p) = (QuotientGroup.mk v : He e) := by rw [hP, frob, clsA, dite_eq_left hunit, hψ]
      rw [hPtw, map_mul, hψc, h1]
      exact one_mul (QuotientGroup.mk v : He e)
    -- the order of the image is `2^s ≤ y`
    have hdvd1 : orderOf (QuotientGroup.mk v : He e) ∣ orderOf (S.hPtw (S.twA κ) p) :=
      himg ▸ orderOf_map_dvd ψ _
    have hdvd2 : orderOf (QuotientGroup.mk v : He e) ∣ 2 ^ e := card_He e ▸ orderOf_dvd_natCard _
    obtain ⟨s, hse, hos⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    have h2s : 2 ^ s ≤ y := by
      rcases hord with hle | hodd'
      · exact hos ▸ (Nat.le_of_dvd (orderOf_pos _) hdvd1).trans hle
      · have : s = 0 := by
          by_contra hs
          obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
          have h2 : 2 ∣ orderOf (S.hPtw (S.twA κ) p) := (hos ▸ (dvd_pow_self 2 (by omega))).trans hdvd1
          exact (Nat.not_even_iff_odd.2 hodd') (even_iff_two_dvd.2 h2)
        rw [this, pow_zero]
        exact hy
    -- so `p^{2^s} ≡ ±1 (mod 2^{e+2})`
    have hpow : (QuotientGroup.mk (v ^ 2 ^ s) : He e) = 1 := by
      rw [QuotientGroup.mk_pow, ← hos, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hpow
    obtain ⟨m, hm⟩ := hpow
    have hpm : (p : ZMod (2 ^ (e + 2))) ^ 2 ^ s = 1 ∨ (p : ZMod (2 ^ (e + 2))) ^ 2 ^ s = -1 := by
      have hm' := congrArg (fun w : (ZMod (2 ^ (e + 2)))ˣ => (w : ZMod (2 ^ (e + 2)))) hm
      simp only [Units.val_pow_eq_pow_val, hv] at hm'
      rw [← hm']
      rcases Int.even_or_odd m with hm2 | hm2
      · left
        rw [hm2.neg_one_zpow, Units.val_one]
      · right
        rw [hm2.neg_one_zpow, Units.val_neg, Units.val_one]
    have hdvdZ : (2 : ℤ) ^ (e + 2) ∣ (p : ℤ) ^ 2 ^ s - 1 ∨ (2 : ℤ) ^ (e + 2) ∣ (p : ℤ) ^ 2 ^ s + 1 := by
      have hc (z : ℤ) (hz : (z : ZMod (2 ^ (e + 2))) = 0) : (2 : ℤ) ^ (e + 2) ∣ z := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd z (2 ^ (e + 2))).1 hz
        exact_mod_cast this
      rcases hpm with h1 | h1
      · exact Or.inl (hc _ (by push_cast; rw [h1, sub_self]))
      · exact Or.inr (hc _ (by push_cast; rw [h1, neg_add_cancel]))
    have hpm' := two_pow_dvd_sub_or_add (by exact_mod_cast hodd) s e hse hdvdZ
    -- and `Q ∣ 2^{e+2−s}`, or `Q = 2`
    have hs₀ : s ≤ s₀ := Nat.le_log_of_pow_le (by norm_num) h2s
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by have := hp.two_le; omega
    by_cases he : 1 ≤ e + 2 - s₀
    · have hQd : (Q : ℤ) ∣ (2 : ℤ) ^ (e + 2 - s) := by
        rw [hQ_def, max_eq_right he]
        push_cast
        exact pow_dvd_pow 2 (by omega)
      rcases hpm' with h1 | h1
      · left
        exact Int.natCast_dvd_natCast.1 (hp1 ▸ hQd.trans h1)
      · right
        exact Int.natCast_dvd_natCast.1 (by push_cast; exact hQd.trans h1)
    · have hQ : Q = 2 := by rw [hQ_def, max_eq_left (by omega), pow_one]
      rw [hQ]
      left
      obtain ⟨l, hl⟩ := hodd
      exact ⟨l, by omega⟩
  -- the harmonic sum, and `4|A| ≤ ord κ·y·Q`
  have hA : 4 * Fintype.card S.A ≤ orderOf κ * y * Q := by
    calc 4 * Fintype.card S.A = orderOf κ * (4 * (A₀ κ).card) := by rw [card_A_eq κ]; ring
      _ ≤ orderOf κ * 2 ^ (e + 2) := Nat.mul_le_mul_left _ (by rw [pow_add]; nlinarith [h.card_A₀_le])
      _ ≤ orderOf κ * (Q * y) := Nat.mul_le_mul_left _ hQy
      _ = orderOf κ * y * Q := by ring
  have hA' : (4 * Fintype.card S.A : ℝ) ≤ orderOf κ * y * Q := by exact_mod_cast hA
  have hA0 : (0 : ℝ) < 4 * Fintype.card S.A := by have := Fintype.card_pos (α := S.A); positivity
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hLL : 0 ≤ Real.log X * (1 + Real.log X) := by have := Real.log_nonneg hX; positivity
  refine (sum_log_div_le_of_dvd hQ2 hX key).trans ?_
  rw [div_le_div_iff₀ hQ0 hA0]
  calc 3 * Real.log X * (1 + Real.log X) * (4 * Fintype.card S.A) =
      3 * (Real.log X * (1 + Real.log X)) * (4 * Fintype.card S.A) := by ring
    _ ≤ 3 * (Real.log X * (1 + Real.log X)) * (orderOf κ * y * Q) :=
        mul_le_mul_of_nonneg_left hA' (mul_nonneg (by norm_num) hLL)
    _ = 3 * orderOf κ * y * (Real.log X * (1 + Real.log X)) * Q := by ring

/-- **Small orders are sparse at an admissible design**: the non-split primes `p < X′` with `ord(c·[p]_A) ≤ y` or
odd have `Σ log p/p ≤ y·(log X′)²·x^{−(2+7ε)}`, from `Setting.TwoAdic.sum_log_div_le` with `ord κ ≤ x^{ε/100}`,
`|A| ≥ x^{2+8ε}`, `1 ≤ log X′ = x^{ε/3}` and `x^{99ε/100} ≥ 4096`. -/
theorem Setting.DesignAdm.sum_log_div_smallOrder_le {S : Setting} {κ : S.A →* ℂˣ} {x ε : ℝ}
    (hS : S.DesignAdm κ x ε) {e : ℕ} (h : S.TwoAdic κ e) {y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ (range ⌈scX' x ε⌉₊).filter (fun p => p.Prime ∧ S.cls p ≠ .split ∧
        (orderOf (S.hPtw (S.twA κ) p) ≤ y ∨ Odd (orderOf (S.hPtw (S.twA κ) p)))), Real.log p / p ≤
      y * Real.log (scX' x ε) ^ 2 * x ^ (-(2 + 7 * ε)) := by
  have hx0 : 0 < x := hS.big.pos
  have hε := hS.big.ε_pos
  have hL : Real.log (scX' x ε) = x ^ (ε / 3) := Real.log_exp _
  have hL1 : 1 ≤ x ^ (ε / 3) := Real.one_le_rpow hS.big.one_lt.le (by positivity)
  refine (h.sum_log_div_le (X := scX' x ε) hy (Real.one_le_exp (by positivity))).trans ?_
  rw [hL]
  set L := x ^ (ε / 3)
  have ho : (orderOf κ : ℝ) ≤ x ^ (ε / 100) := hS.orderOf_le
  have hA : x ^ (2 + 8 * ε) ≤ Fintype.card S.A := hS.card_ge
  have hxe : x ^ (-(2 + 7 * ε)) * x ^ (2 + 8 * ε) = x ^ (ε / 100) * x ^ (99 * ε / 100) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have h99 : 4096 ≤ x ^ (99 * ε / 100) := hS.big.le_rpow (by linarith)
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hX1 : 0 < x ^ (ε / 100) := Real.rpow_pos_of_pos hx0 _
  have hX3 : 0 < x ^ (2 + 8 * ε) := Real.rpow_pos_of_pos hx0 _
  calc 3 * orderOf κ * y * (L * (1 + L)) / (4 * Fintype.card S.A) ≤
      3 * x ^ (ε / 100) * y * (2 * L ^ 2) / (4 * x ^ (2 + 8 * ε)) := by
        have hLL : L * (1 + L) ≤ 2 * L ^ 2 := by nlinarith
        refine div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ho (by norm_num)) hy0) hLL (by positivity) (by positivity)) (by positivity)
          (by linarith)
    _ ≤ y * L ^ 2 * x ^ (-(2 + 7 * ε)) := by
        rw [div_le_iff₀ (by positivity)]
        have hyL : 0 ≤ y * L ^ 2 * x ^ (ε / 100) := by positivity
        calc 3 * x ^ (ε / 100) * y * (2 * L ^ 2) = 6 * (y * L ^ 2 * x ^ (ε / 100)) := by ring
          _ ≤ 4 * x ^ (99 * ε / 100) * (y * L ^ 2 * x ^ (ε / 100)) := by gcongr; linarith
          _ = y * L ^ 2 * (x ^ (-(2 + 7 * ε)) * x ^ (2 + 8 * ε)) * 4 := by rw [hxe]; ring
          _ = y * L ^ 2 * x ^ (-(2 + 7 * ε)) * (4 * x ^ (2 + 8 * ε)) := by ring

end ZetaBalance

#print axioms ZetaBalance.Setting.DesignAdm.lt_of_cls_ne_split
#print axioms ZetaBalance.orbitPos_mem_topPositions
#print axioms ZetaBalance.TilePar.IsGood.prevV_spec
#print axioms ZetaBalance.Setting.DesignAdm.two_mul_scL1_le
#print axioms ZetaBalance.pairSetting_twoAdic
#print axioms ZetaBalance.Setting.TwoAdic.sum_log_div_le
#print axioms ZetaBalance.Setting.DesignAdm.sum_log_div_smallOrder_le
