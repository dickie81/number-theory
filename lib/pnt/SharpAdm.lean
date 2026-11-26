import DesignPrimes
import DesignHC
import DesignScale
import RelationFree

/-!
# Admissible designs

A step of the proof of the sharp frontier (`SharpInputs`): the field `SharpPieces.adm`, the conditions a design at
`x` (`SharpDesign`) must meet for the pieces, and the facts about admissible designs that the pieces consume. The
design is the archive's, read in the repo's coordinates; `SharpParams` builds one at every `x` of the frontier's
windows (`sharpParams`).

**The clauses** (`SharpDesign.Adm`, Stage 1 of the design spec: A1–A11). The setting-level ones, which do not read
the design, are a structure of their own that `Adm` extends (`Setting.DesignAdm`): the growth package `DesignBig ε x`
(A1), the window `x^{2+8ε} ≤ |A| ≤ 2x^{2+8ε+ε/100}`, `ord κ ≤ x^{ε/100}`, `QS ≤ 4|A|x^{ε/100}` (A2), the pair
(`d ≡ 7 (mod 16)`, `q ≡ 3 (mod 8)`, `log q, log d > x^{ε/10}/2`, `(−d/q) = 1`, `(−d/p) = 1` for `p ≤ x^{ε/10}`,
`log N ≤ 3x^{ε/5}log² x`, A3) and `|Re L′/L(1, χ_d)| ≤ x^ε` (A4). The design-level ones: `X = (Nx)^{log x}` (A1),
the ranks `k`, `m`, `t` of `designRanks` (A6), the window and the coset counts of the tops (A7), the margin
`P > (k − 1)/2 + 3` (A9), the root-of-unity condition (A10) and the split primes (A11). The parameters that
`SharpDesign` does not record (`DesignPar`: the integer scales `a_t`, the top shifts `b_t`, the generator `a₀` of
`A₀`, the exponents `T` of the thick set, `s*` and the shifts `σ`) are bound by one existential (`Adm.fam`), with the
clauses that read them (`SharpDesign.FamAt`): the windows of `a_t` and `b_t` (A7), `a₀` generates `A₀` (A2),
`T2 = {a₀^s : s ∈ T}` with `T` relation-free at level `L_w`, in range and dense (A8), and the families are the
formulas of `DesignHC` at the design's integers (`designFam`, A9): `Δ = ⌈x⌉` (`c_D = 1`), `H = w_E⌈x^{402}⌉`,
`B = ⌈b⌉`, `W = ⌈w″⌉`, `P = ⌊b′/x⌋` and `ρ*(u) = (−1, a₀^{s*}u)`. Each field's docstring names the pieces that read
it.

**The sizes** (`DesignBig.*`, `Setting.DesignAdm.*`): `x ≥ 4096`, `|A| ≤ x³`, `k ≤ 2x^5`, `m ≤ 2x`, `Δ ≤ 2x`,
`w_E ≤ 32x^6`, `x^{402} ≤ H ≤ 64x^{408}`, so `η + 1 = 2mH + 1 ≤ x^{410}`; and `X′ ≥ x^{410}`, `b ≥ X′²x^{30}`, so
`b/X′ ≥ x^{440}`, `b′ ≥ x^{441}`, `w″ ≥ x^{437}` and `b ≥ x^{850}`: every polynomial size of the design is far below
the weights. The windows of `DesignHC` then put every `e_j` in `[w″, 2b]`, with `e_j ≤ 3b′` at a top and
`e_j ≤ 2w″` at a thin place (`Setting.DesignAdm.e_window`).

**The API** (`SharpDesign.Adm.*`):
* the pair: `d ≡ 3 (mod 4)`, `d ≥ 100`, `4tr + 1 < q` and `< d` (as `4tr + 1 ≤ 2^{12}x^{406} < e^{x^{ε/10}/2}`);
* the ranks: the windows of `k` and `m`, `t ≤ x^{401}`, `r ≤ 3x^{9/2+10ε}`, `log k ≤ 6 log x`; and `log x ≤ x^ε/1000`;
* the scales: `|TT|·x·e^{x^ε} ≤ Σ_t a_t`, `[E:ℚ] ≤ Σ_t a_t/x` (as `[E:ℚ] = 4|A| ≤ b`), the weights in `[w″, 2b]`;
* (T): `16x^ε ≤ log(g₀g₁) ≤ 17x^ε`, `mx^ε/2 ≤ Λ_u ≤ 24mx^ε` (each term `log(w·v_E/π)` of `Λ_u` is in `[0, 2x^ε]`, as
  `v_E ≥ 1/2` and `2v_E ≤ N`), `Λ_u ≤ x/2`, `Λ_u + log 2 ≤ x` and `(log 4dM²)³ ≤ Λ_u` for `M = QS·q·d·(g₀g₁)²`;
* (F), for the step-0 weights `λ_ρ = wt_0(⌊u − ½⌋, e)` (`Setting.Ranks.wt0`, the archive's step-0 weights) of
  **every** word family pinned to `u` (`SharpDesign.PinnedTo`, the archive's word families): `λ_ρ` is antitone (`wt0_antitone`, for every Harish-Chandra family), `|ν| = Σ_{ρ,i} ν_{ρ,i} ≤ 2Σ_t a_t`
  (`sum_natW_le`) and `(Σ_{ρ,i} λ_{ρ,i})⁺ ≤ 2Σ_t a_t` (`sum_wt0_le`).

**Route of the (F) bounds.** Interlacing gives `u_{i+1} + 1 ≤ u_i` (half-integers around an integer,
`HC.succ_add_one_le`), so `λ_{ρ,i} = u_i + ½ + i − k/2` is antitone and `ν_{ρ,i} = λ_{ρ,i} − λ_{ρ,k−1} ≤ u_i − u_{k−1}`.
A pinned family shares `v` and the ends `u_0`, `u_{k−1}` with `hc u`, so `u_i ≤ u_1 < v_0 = 4Δ(k − 2)` for `i ≥ 1`: at
one place both sums are at most `[ρ top]·a_t + k(8Δk + 2b′ + k + 1)` (`place_le`), from `u_0 = a_t + (k − 1)/2`,
`u_{k−1} = −b_t − (k − 1)/2` at a top and `u_0 ≤ 8Δk`, `u_{k−1} = −½` elsewhere. Summed over `Φ` the tops give
`Σ_t a_t` (`sum_top`) and the rest `2|A|·k(8Δk + 2b′ + k + 1) ≤ a ≤ Σ_t a_t` (`places_le`).

**What is the construction's.** The objects' step-0 data (`SharpObj.n0`, `lam0`), their `ST`, `T` and `c_F` are
not the design's: the API bounds the step-0 weights of every family pinned to `u` on `Fin n` with
`n = k + 0·(t + 1)`, and the construction sets `n0`, `lam0` to them, and bounds `|ST|`,
`Σ_{P ∈ ST} log N(P)` to `[E:ℚ]` and `log T`.

**Deviations from the spec.**
* A5 (`log(2v_E) ≤ log N`) holds for every setting (`log_vE_le`), so it is not a clause.
* A3's `100 ≤ d` is a lemma (`hundred_le_d`), from the stronger clauses `log q, log d > x^{ε/10}/2`, which also
  put `q` and `d` beyond every polynomial size of the design (`4tr + 1 < q, d`).
* A6 pins `k`, `m`, `t` to `designRanks`' values; their windows are lemmas.
* A9 states the families as `hcFam` at the design's integers (`designFam`), which carries every formula of the spec;
  the windows and the cloud are lemmas of `DesignHC`.
* The Stage-2 clauses G1, G2 (the gain's random choices) are not here.
-/

open NumberField

namespace ZetaBalance

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}

/-! ## The design's integers -/

/-- `Δ = ⌈x^{c_D}⌉`, the step of the Harish-Chandra cloud, with `c_D = 1`. -/
noncomputable def designΔ (x : ℝ) : ℕ := ⌈x⌉₊

/-- `H = w_E⌈x^{402}⌉`, the gap of the Harish-Chandra parameters (`h₀ = 2H`), with `w_E` the number of roots of
unity of `E`. -/
noncomputable def designH (S : Setting) (x : ℝ) : ℕ := Units.torsionOrder S.E * ⌈x ^ 402⌉₊

/-- The place `ρ*(u) = (−1, a₀^{s*}u)` that carries the root-of-unity shift at the translate `u`. -/
noncomputable def designStar (a₀ : S.A) (s : ℕ) (u : S.A) : Φ S.A := (-1, a₀ ^ s * u)

/-- **The inequalities of the design's families** (`HCHyp`) at the design's integers: `Δ`, `H`, `B = ⌈b⌉`,
`W = ⌈w″⌉` and `P = ⌊b′/x⌋`. -/
abbrev DesignHyp (S : Setting) (x ε : ℝ) (R : S.Ranks) (TT : Finset S.A) (aZ bT : S.A → ℤ) : Prop :=
  HCHyp R TT aZ bT (designΔ x) (designH S x) ⌈scB x ε⌉ ⌈scW'' S x ε⌉ ⌊scB' x ε / x⌋

/-- **The design's families** (`hcFam`) at the design's integers. -/
noncomputable abbrev designFam (S : Setting) (x ε : ℝ) (R : S.Ranks) (TT T2 : Finset S.A) (aZ bT : S.A → ℤ)
    (ρstar : S.A → Φ S.A) (σ : S.A → ℕ) (hyp : DesignHyp S x ε R TT aZ bT) : S.A → R.HCFamily :=
  hcFam R TT T2 aZ bT (designΔ x) (designH S x) ⌈scB x ε⌉ ⌈scW'' S x ε⌉ ⌊scB' x ε / x⌋ ρstar σ hyp

/-! ## The clauses -/

/-- **The setting-level clauses of an admissible design** at `(x, ε)`: those that do not read the design. -/
structure Setting.DesignAdm (S : Setting) (κ : S.A →* ℂˣ) (x ε : ℝ) : Prop where
  /-- (A1) The growth package, with `0 < ε < 1/52` and `x > 1`. All pieces. -/
  big : DesignBig ε x
  /-- (A2) `|A| ≥ x^{2+8ε}`. The ranks, the gain, the sizes. -/
  card_ge : x ^ (2 + 8 * ε) ≤ Fintype.card S.A
  /-- (A2) `|A| ≤ 2x^{2+8ε+ε/100}`. The ranks, the gain, the sizes. -/
  card_le : (Fintype.card S.A : ℝ) ≤ 2 * x ^ (2 + 8 * ε + ε / 100)
  /-- (A2) `ord κ ≤ x^{ε/100}`. The gain, (G↑). -/
  orderOf_le : (orderOf κ : ℝ) ≤ x ^ (ε / 100)
  /-- (A2) `QS ≤ 4|A|x^{ε/100}`. The gain, (G↑). -/
  QS_le : (S.QS : ℝ) ≤ 4 * Fintype.card S.A * x ^ (ε / 100)
  /-- (A3) `d ≡ 7 (mod 16)`. (T), the gain, the pins. -/
  d_mod : S.d % 16 = 7
  /-- (A3) `q ≡ 3 (mod 8)`. The gain, the pins. -/
  q_mod : S.q % 8 = 3
  /-- (A3) `log q > x^{ε/10}/2`: `q` beyond every polynomial size of the design. The gain, the pins. -/
  q_large : x ^ (ε / 10) / 2 < Real.log S.q
  /-- (A3) `log d > x^{ε/10}/2`: `d ≥ 100` and `d` beyond every polynomial size. (T), the pins. -/
  d_large : x ^ (ε / 10) / 2 < Real.log S.d
  /-- (A3) `(−d/q) = 1`. The gain, the pins. -/
  leg_q : jacobiSym (-(S.d : ℤ)) S.q = 1
  /-- (A3) `(−d/p) = 1` for every prime `p ≤ x^{ε/10}`. The gain. -/
  leg_small : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (ε / 10) → jacobiSym (-(S.d : ℤ)) p = 1
  /-- (A3) `log N ≤ 3x^{ε/5}log² x`. (T), (F), the sizes. -/
  log_N_le : Real.log S.N ≤ 3 * x ^ (ε / 5) * Real.log x ^ 2
  /-- (A4) `|Re L′/L(1, χ_d)| ≤ x^ε`, the term of `MAIN`. (G↑). -/
  logDeriv_le : |(logDeriv (DirichletCharacter.LFunction (legChar S.d)) 1).re| ≤ x ^ ε

/-- **The parameters of a design that `SharpDesign` does not record**: the integer scales `a_t` and top shifts `b_t`,
the generator `a₀` of `A₀`, the exponents `T` of the thick set, the place index `s*` and the root-of-unity shifts
`σ`. -/
structure DesignPar (S : Setting) where
  /-- The integer scales `a_t`. -/
  aZ : S.A → ℤ
  /-- The top shifts `b_t`. -/
  bT : S.A → ℤ
  /-- The generator `a₀` of `A₀`. -/
  a₀ : S.A
  /-- The exponents `T`, with `T2 = {a₀^s : s ∈ T}`. -/
  T : Finset ℕ
  /-- The exponent `s*` of the shifted place `ρ*(u) = (−1, a₀^{s*}u)`. -/
  sstar : ℕ
  /-- The root-of-unity shifts `σ(u)`. -/
  σ : S.A → ℕ

namespace SharpDesign

variable (Dg : SharpDesign S κ x ε X)

/-- **The clauses of a design with given parameters** (A2's generator, A7's scales, A8, A9). -/
structure FamAt (pr : DesignPar S) : Prop where
  /-- (A7) The scales are the integers `a_t`. The gain, (G↑), (F). -/
  a_eq : ∀ t, Dg.a t = pr.aZ t
  /-- (A7) `a ≤ a_t ≤ a + a/(kx^{13})`. (Z), the gain, (G↑), (F). -/
  a_mem : ∀ t ∈ Dg.TT, scA x ε ≤ pr.aZ t ∧ (pr.aZ t : ℝ) ≤ scA x ε + scA x ε / (Dg.R.k * x ^ 13)
  /-- (A7) `b′ ≤ b_t ≤ b′(1 + x^{−1/4})`. The gain, (F). -/
  bT_mem : ∀ t ∈ Dg.TT, scB' x ε ≤ pr.bT t ∧ (pr.bT t : ℝ) ≤ scB' x ε * (1 + x ^ (-(1 / 4 : ℝ)))
  /-- (A2) `a₀ ∈ A₀`. The gain. -/
  a₀_mem : pr.a₀ ∈ A₀ κ
  /-- (A2) `a₀` has order `|A₀|`, so it generates `A₀`. The gain. -/
  a₀_order : orderOf pr.a₀ = (A₀ κ).card
  /-- (A8) `T2 = {a₀^s : s ∈ T}`. The gain. -/
  T2_eq : Dg.T2 = pr.T.image (pr.a₀ ^ ·)
  /-- (A8) (range) `4L_w s < |A₀|` for `s ∈ T`. The gain. -/
  T_range : ∀ s ∈ pr.T, 4 * scLw x ε * s < (A₀ κ).card
  /-- (A8) `T` is relation-free at level `L_w`. The gain. -/
  T_relFree : RelFree pr.T (scLw x ε)
  /-- (A8) (density) `|T| ≥ x^{−ε}|A|`. The gain. -/
  T_card : x ^ (-ε) * Fintype.card S.A ≤ pr.T.card
  /-- (A9) `s* ∈ T`, so `ρ*(u)` is thick. The pins. -/
  sstar_mem : pr.sstar ∈ pr.T
  /-- (A9) `σ(u) < w_E`. The pins, the gain. -/
  σ_lt : ∀ u, pr.σ u < Units.torsionOrder S.E
  /-- (A9) The inequalities of the families. The gain, (G↑), (F), the pins. -/
  hyp : DesignHyp S x ε Dg.R Dg.TT pr.aZ pr.bT
  /-- (A9) **The families are the design's formulas** (`hcFam`). The gain, (G↑), (F), the pins. -/
  hc_eq : ∀ u, Dg.hc u = designFam S x ε Dg.R Dg.TT Dg.T2 pr.aZ pr.bT (designStar pr.a₀ pr.sstar) pr.σ hyp u

/-- **An admissible design** (the field `adm` of `SharpPieces`): the clauses A1–A11 of the design spec. -/
structure Adm : Prop extends S.DesignAdm κ x ε where
  /-- (A1) `X = (Nx)^{log x}`. (Z), the gain. -/
  X_eq : X = ((S.N : ℝ) * x) ^ Real.log x
  /-- (A6) `k = 2⌈x^{9/2+10ε}/2⌉`. (S), (R), the gain, (F). -/
  k_eq : Dg.R.k = designK x ε
  /-- (A6) `m = 2⌈x^{1/2−ε/16}/2⌉`. (S), (R), the gain, (F). -/
  m_eq : Dg.R.m = designM x ε
  /-- (A6) `t = 8fr + 4 + TO·nW − r`. (S), (R), the gain. -/
  t_eq : Dg.R.t = designT S x ε
  /-- (A7) `|TT| ≥ δ₁|A|/2`. The gain, (G↑). -/
  TT_ge : scδ₁ x ε * Fintype.card S.A / 2 ≤ Dg.TT.card
  /-- (A7) `|TT| ≤ 2δ₁|A|`. The gain, (G↑). -/
  TT_le : (Dg.TT.card : ℝ) ≤ 2 * scδ₁ x ε * Fintype.card S.A
  /-- (A7) The coset counts: `|#(TT ∩ γA₀) − λ(γ)|TT|| ≤ x^{ε−1}|TT|`, `λ = 4/(3o + 1)` on `A₀` and `3/(3o + 1)`
  off it. The gain, (G↑). -/
  TT_counts : ∀ γ : S.A, |((Dg.TT.filter fun t => γ⁻¹ * t ∈ A₀ κ).card : ℝ) -
    (if γ ∈ A₀ κ then 4 else 3) / (3 * orderOf κ + 1) * Dg.TT.card| ≤ x ^ (ε - 1) * Dg.TT.card
  /-- (A9) The margin `P > (k − 1)/2 + 3` at the tops, `P = ⌊b′/x⌋`. The gain. -/
  P_margin : (Dg.R.k : ℤ) + 5 < 2 * ⌊scB' x ε / x⌋
  /-- (A2, A7, A8, A9) The design's parameters and the formulas of its families. The gain, (G↑), (F), the pins. -/
  fam : ∃ pr : DesignPar S, Dg.FamAt pr
  /-- (A10) The root-of-unity condition `∏_ρ τ_ρ(ζ)^{e_j(ρ)} = 1`. The pins. -/
  ru : ∀ u j (ζ : S.E), (∃ n, 0 < n ∧ ζ ^ n = 1) → ∏ ρ, (S.τ ρ ζ) ^ ((Dg.hc u ρ).e j) = 1
  /-- (A11) `g ∈ [(kb)^8, 2(kb)^8]` of norm one mod `N`: `4g = α² + dβ²`, `N ∣ β`, `α ≡ β + 2 (mod 2N)`. The gain,
  the pins, (T). -/
  split : ∀ g ∈ [Dg.g₀, Dg.g₁], ((Dg.R.k : ℝ) * scB x ε) ^ 8 ≤ g ∧ (g : ℝ) ≤ 2 * ((Dg.R.k : ℝ) * scB x ε) ^ 8 ∧
    ∃ α β : ℤ, 4 * (g : ℤ) = α ^ 2 + S.d * β ^ 2 ∧ (S.N : ℤ) ∣ β ∧ α ≡ β + 2 [ZMOD 2 * S.N]
  /-- (A11) `Exc_r(g₀) ∩ Exc_r(g₁) = ∅`. The gain. -/
  exc : Disjoint (ExcSet Dg.R.r Dg.g₀) (ExcSet Dg.R.r Dg.g₁)

end SharpDesign

/-! ## Sizes -/

/-- `b′ = x·(b/X′)`. -/
theorem scB'_eq (x ε : ℝ) : scB' x ε = x * (scB x ε / scX' x ε) := by
  unfold scB' scA
  ring

namespace DesignBig

variable (h : DesignBig ε x)
include h

/-- `x ≥ 4096`. -/
theorem x_ge : 4096 ≤ x := by
  have := h.le_rpow (c := 1) (by linarith [h.ε_lt])
  rwa [Real.rpow_one] at this

/-- `log x ≥ 1`. -/
theorem one_le_log : 1 ≤ Real.log x := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9, h.x_ge])

/-- `x^c ≤ x^n` for a real `c ≤ n`. -/
theorem rpow_le_npow {c : ℝ} (n : ℕ) (hc : c ≤ n) : x ^ c ≤ x ^ n := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le h.one_lt.le hc

/-- `1 ≤ k ≤ 2x^5`. -/
theorem designK_le : 1 ≤ (designK x ε : ℝ) ∧ (designK x ε : ℝ) ≤ 2 * x ^ 5 := by
  obtain ⟨h1, h2⟩ := designK_mem h
  have h3 := h.rpow_le_npow 5 (c := 9 / 2 + 10 * ε) (by push_cast; linarith [h.ε_lt])
  have h4 := Real.one_le_rpow h.one_lt.le (show (0 : ℝ) ≤ 9 / 2 + 10 * ε by linarith [h.ε_pos])
  constructor <;> linarith

/-- `m ≤ 2x`. -/
theorem designM_le : (designM x ε : ℝ) ≤ 2 * x := by
  have h3 := h.rpow_le_npow 1 (c := 1 / 2 - ε / 16) (by push_cast; linarith [h.ε_pos])
  rw [pow_one] at h3
  linarith [(designM_mem h).2]

/-- `X′ ≥ x^{410}`. -/
theorem X'_ge : x ^ 410 ≤ scX' x ε := h.poly

/-- `b ≥ X′²x^{30}`: `x^ε ≥ 2x^{ε/3} + 30 log x`. -/
theorem b_ge : scX' x ε ^ 2 * x ^ 30 ≤ scB x ε := by
  have e : scX' x ε ^ 2 * x ^ 30 = Real.exp (2 * x ^ (ε / 3) + 30 * Real.log x) := by
    rw [Real.exp_add, show (2 : ℝ) * x ^ (ε / 3) = ((2 : ℕ) : ℝ) * x ^ (ε / 3) by norm_num, Real.exp_nat_mul,
      show (30 : ℝ) * Real.log x = ((30 : ℕ) : ℝ) * Real.log x by norm_num, Real.exp_nat_mul, Real.exp_log h.pos]
    rfl
  rw [e]
  exact Real.exp_le_exp.2 h.gap

/-- `b/X′ ≥ x^{440}`. -/
theorem bX'_ge : x ^ 440 ≤ scB x ε / scX' x ε := by
  have h0 : 0 < scX' x ε := Real.exp_pos _
  rw [le_div_iff₀ h0]
  calc x ^ 440 * scX' x ε ≤ scX' x ε * x ^ 30 * scX' x ε := by
        gcongr
        calc x ^ 440 = x ^ 410 * x ^ 30 := by ring
          _ ≤ scX' x ε * x ^ 30 := by gcongr; exact h.X'_ge
    _ = scX' x ε ^ 2 * x ^ 30 := by ring
    _ ≤ scB x ε := h.b_ge

/-- `b′ ≥ x^{441}`. -/
theorem b'_ge : x ^ 441 ≤ scB' x ε := by
  rw [scB'_eq, pow_succ, mul_comm]
  exact mul_le_mul_of_nonneg_left h.bX'_ge h.pos.le

/-- `b ≥ x^{850}`. -/
theorem b_ge' : x ^ 850 ≤ scB x ε := by
  refine le_trans ?_ h.b_ge
  calc x ^ 850 = (x ^ 410) ^ 2 * x ^ 30 := by ring
    _ ≤ scX' x ε ^ 2 * x ^ 30 := by gcongr; exact h.X'_ge

/-- `2b′ ≤ b`, as `X′ ≥ 2x`. -/
theorem two_b'_le : 2 * scB' x ε ≤ scB x ε := by
  have h0 : 0 < scX' x ε := Real.exp_pos _
  have hb : 0 < scB x ε := Real.exp_pos _
  have hx := h.x_ge
  have h1 : x ^ 2 ≤ x ^ 410 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h2 : 2 * x ≤ scX' x ε := le_trans (by nlinarith) h.X'_ge
  rw [scB'_eq, ← mul_assoc, mul_div_assoc', div_le_iff₀ h0]
  nlinarith

/-- `b ≤ b′(1 + x^{−1/4})` gives `b ≤ 2b′`. -/
theorem le_two_mul_scB' {b : ℝ} (hb : b ≤ scB' x ε * (1 + x ^ (-(1 / 4 : ℝ)))) : b ≤ 2 * scB' x ε := by
  have h3 : x ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.one_lt.le (by norm_num)
  have h4 := scB'_pos ε h.pos
  nlinarith

/-- `1 ≤ Δ ≤ 2x`. -/
theorem designΔ_mem : 1 ≤ designΔ x ∧ (designΔ x : ℝ) ≤ 2 * x := by
  have h1 := Nat.ceil_lt_add_one h.pos.le
  have hx := h.x_ge
  exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 h.pos)), by unfold designΔ; linarith⟩

end DesignBig

/-- `w″ = (b/X′)/|A|`. -/
theorem scW''_eq (S : Setting) {x : ℝ} (ε : ℝ) (hx : 0 < x) :
    scW'' S x ε = scB x ε / scX' x ε / Fintype.card S.A := by
  have h2 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  unfold scW''
  rw [scB'_eq]
  field_simp

namespace Setting.DesignAdm

variable (hS : S.DesignAdm κ x ε)
include hS

/-- `|A| ≤ x³`. -/
theorem card_le_cube : (Fintype.card S.A : ℝ) ≤ x ^ 3 := by
  have h := hS.big
  have h1 := h.le_rpow (c := 1 - 8 * ε - ε / 100) (by linarith [h.ε_lt])
  have e : x ^ 3 = x ^ (2 + 8 * ε + ε / 100) * x ^ (1 - 8 * ε - ε / 100) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add h.pos]
    congr 1
    push_cast
    ring
  have h2 : 0 < x ^ (2 + 8 * ε + ε / 100) := Real.rpow_pos_of_pos h.pos _
  rw [e]
  nlinarith [hS.card_le]

/-- `w_E ≤ 32x^6`, from `w_E ≤ 32|A|²` (`torsionOrder_le`). -/
theorem torsion_le : (Units.torsionOrder S.E : ℝ) ≤ 32 * x ^ 6 := by
  have h1 : (Units.torsionOrder S.E : ℝ) ≤ 32 * (Fintype.card S.A : ℝ) ^ 2 := by exact_mod_cast torsionOrder_le S
  have h0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  calc _ ≤ 32 * (Fintype.card S.A : ℝ) ^ 2 := h1
    _ ≤ 32 * (x ^ 3) ^ 2 := by gcongr; exact hS.card_le_cube
    _ = 32 * x ^ 6 := by ring

/-- `w_E ≤ H`, `x^{402} ≤ H ≤ 64x^{408}`. -/
theorem designH_mem : (Units.torsionOrder S.E : ℝ) ≤ designH S x ∧ x ^ 402 ≤ (designH S x : ℝ) ∧
    (designH S x : ℝ) ≤ 64 * x ^ 408 := by
  have hx := hS.big.x_ge
  have hw1 : (1 : ℝ) ≤ Units.torsionOrder S.E := by exact_mod_cast Units.torsionOrder_pos S.E
  have hc1 := Nat.le_ceil (x ^ 402)
  have hc2 := Nat.ceil_lt_add_one (pow_nonneg hS.big.pos.le 402)
  have hx1 : 1 ≤ x ^ 402 := one_le_pow₀ (by linarith)
  have ht := hS.torsion_le
  unfold designH
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · calc (Units.torsionOrder S.E : ℝ) * ⌈x ^ 402⌉₊ ≤ (32 * x ^ 6) * (2 * x ^ 402) := by
          gcongr; linarith
      _ = 64 * x ^ 408 := by ring

/-- `η + 1 ≤ x^{410}`, for `η = 2mH` and `m ≤ 2x`. -/
theorem eta_le {m : ℕ} (hm : (m : ℝ) ≤ 2 * x) : (m : ℝ) * (2 * designH S x) + 1 ≤ x ^ 410 := by
  have hx := hS.big.x_ge
  have hH := hS.designH_mem.2.2
  have h1 : (1 : ℝ) ≤ x ^ 409 := one_le_pow₀ (by linarith)
  calc (m : ℝ) * (2 * designH S x) + 1 ≤ (2 * x) * (2 * (64 * x ^ 408)) + x ^ 409 := by
        gcongr
    _ = 257 * x ^ 409 := by ring
    _ ≤ x * x ^ 409 := by gcongr; linarith
    _ = x ^ 410 := by ring

/-- `w″ ≥ x^{437}`. -/
theorem w''_ge : x ^ 437 ≤ scW'' S x ε := by
  have h2 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  rw [scW''_eq S ε hS.big.pos, le_div_iff₀ h2]
  calc x ^ 437 * Fintype.card S.A ≤ x ^ 437 * x ^ 3 :=
        mul_le_mul_of_nonneg_left hS.card_le_cube (pow_nonneg hS.big.pos.le _)
    _ = x ^ 440 := by ring
    _ ≤ _ := hS.big.bX'_ge

/-- `w″ ≤ b′`, as `x|A| ≥ 1`. -/
theorem w''_le_b' : scW'' S x ε ≤ scB' x ε := by
  have h2 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hx := hS.big.x_ge
  unfold scW''
  exact div_le_self (scB'_pos ε hS.big.pos).le (by nlinarith)

/-- `2^{12}x^{406} < p` for `log p > x^{ε/10}/2`. -/
theorem lt_of_log {p : ℕ} (hp : x ^ (ε / 10) / 2 < Real.log p) : 2 ^ 12 * x ^ 406 < (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by
    by_contra h0
    have : (p : ℝ) = 0 := le_antisymm (not_lt.1 h0) (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hp
    linarith [Real.rpow_pos_of_pos hS.big.pos (ε / 10)]
  calc 2 ^ 12 * x ^ 406 ≤ Real.exp (x ^ (ε / 10) / 2) := hS.big.tq
    _ < Real.exp (Real.log p) := Real.exp_lt_exp.2 hp
    _ = p := Real.exp_log hp0

/-- `d ≥ 100`. -/
theorem hundred_le_d : 100 ≤ S.d := by
  have h1 := hS.lt_of_log hS.d_large
  have hx := hS.big.x_ge
  have h2 : (1 : ℝ) ≤ x ^ 406 := one_le_pow₀ (by linarith)
  have : (100 : ℝ) ≤ S.d := by nlinarith
  exact_mod_cast this

/-- **The windows of the design's families**: for `m ≤ 2x`, shifts `σ < w_E` and top shifts `b′ ≤ b_t ≤ 2b′`, every
`e_j` lies in `[w″, 2b]`, with `e_j ≤ 3b′` at a top and `e_j ≤ 2w″` at a thin place (`hcFam_windows`, with
`η + 1 ≤ x^{410}`). -/
theorem e_window {R : S.Ranks} (hRm : (R.m : ℝ) ≤ 2 * x) {TT T2 : Finset S.A} {aZ bT : S.A → ℤ}
    {ρstar : S.A → Φ S.A} {σ : S.A → ℕ} (hσ : ∀ u, σ u < Units.torsionOrder S.E)
    (hbT : ∀ t ∈ TT, scB' x ε ≤ bT t ∧ (bT t : ℝ) ≤ 2 * scB' x ε) (hyp : DesignHyp S x ε R TT aZ bT) (u : S.A)
    (ρ : Φ S.A) (j : Fin R.m) :
    (placeKind TT T2 u ρ = .top → ((designFam S x ε R TT T2 aZ bT ρstar σ hyp u ρ).e j : ℝ) ≤ 3 * scB' x ε) ∧
    (placeKind TT T2 u ρ = .thin → ((designFam S x ε R TT T2 aZ bT ρstar σ hyp u ρ).e j : ℝ) ≤
      2 * scW'' S x ε) ∧
    scW'' S x ε ≤ ((designFam S x ε R TT T2 aZ bT ρstar σ hyp u ρ).e j : ℝ) ∧
    ((designFam S x ε R TT T2 aZ bT ρstar σ hyp u ρ).e j : ℝ) ≤ 2 * scB x ε := by
  have hx := hS.big.x_ge
  have hη := hS.eta_le hRm
  have hHσ : ∀ u, σ u ≤ designH S x := fun u => by
    have h1 : (σ u : ℝ) < designH S x := lt_of_lt_of_le (by exact_mod_cast hσ u) hS.designH_mem.1
    exact_mod_cast h1.le
  obtain ⟨Wt, Wk, Wn, -⟩ := hcFam_windows hyp (T2 := T2) (ρstar := ρstar) (bR := scB x ε) (wR := scW'' S x ε)
    (pR := scB' x ε / x) rfl rfl rfl hHσ u ρ j
  have hw := hS.w''_ge
  have hwb := hS.w''_le_b'
  have hb' := hS.big.b'_ge
  have h2b := hS.big.two_b'_le
  have hb0 := scB'_pos ε hS.big.pos
  have hbx : 0 ≤ scB' x ε / x := div_nonneg hb0.le hS.big.pos.le
  have hbx2 : scB' x ε / x ≤ scB' x ε / 2 := div_le_div_of_nonneg_left hb0.le (by norm_num) (by linarith)
  have h1 : x ^ 410 ≤ x ^ 437 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h2 : 2 * x ^ 410 ≤ x ^ 441 := by
    have : x ^ 410 * x ≤ x ^ 441 := by rw [← pow_succ]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith [pow_pos hS.big.pos 410]
  rcases hpk : placeKind TT T2 u ρ
  · obtain ⟨e1, e2⟩ := Wt hpk
    obtain ⟨b1, b2⟩ := hbT _ (placeKind_eq_top.1 hpk).2
    exact ⟨fun _ => by linarith, fun h => absurd h (by decide), by linarith, by linarith⟩
  · obtain ⟨e1, e2⟩ := Wk hpk
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), by linarith, by linarith⟩
  · obtain ⟨e1, e2⟩ := Wn hpk
    exact ⟨fun h => absurd h (by decide), fun _ => by linarith, by linarith, by linarith⟩

end Setting.DesignAdm

/-! ## The step-0 weights of a Harish-Chandra family -/

namespace Setting.Ranks

variable {R : S.Ranks}

/-- **Interlacing gaps**: `u_{i+1} + 1 ≤ u_i`, as `u_{i+1} < v_i < u_i` with `u_i ∈ ℤ + ½` and `v_i ∈ ℤ`. -/
theorem HC.succ_add_one_le (H : R.HC) (i : ℕ) (hi : i + 1 < R.k) :
    H.u ⟨i + 1, hi⟩ + 1 ≤ H.u ⟨i, by omega⟩ := by
  have h1 : (H.v ⟨i, by omega⟩ : ℚ) < H.u ⟨i, by omega⟩ := H.v_lt ⟨i, by omega⟩
  have h2 : H.u ⟨i + 1, hi⟩ < H.v ⟨i, by omega⟩ := H.lt_v ⟨i, by omega⟩
  obtain ⟨n₁, hn₁⟩ := H.u_half ⟨i + 1, hi⟩
  obtain ⟨n₂, hn₂⟩ := H.u_half ⟨i, by omega⟩
  rw [hn₂] at h1
  rw [hn₁] at h2
  have e1 : n₁ < H.v ⟨i, by omega⟩ := by
    have : (n₁ : ℚ) < H.v ⟨i, by omega⟩ := by linarith
    exact_mod_cast this
  have e2 : H.v ⟨i, by omega⟩ < n₂ + 1 := by
    have : (H.v ⟨i, by omega⟩ : ℚ) < n₂ + 1 := by linarith
    exact_mod_cast this
  have e3 : (n₁ : ℚ) + 1 ≤ n₂ := by exact_mod_cast (by omega : n₁ + 1 ≤ n₂)
  rw [hn₁, hn₂]
  linarith

/-- **`u` drops by at least `1` per step**: `u_j + (j − i) ≤ u_i` for `i ≤ j < k`. -/
theorem HC.u_add_le (H : R.HC) {i : ℕ} (j : ℕ) (hij : i ≤ j) (hj : j < R.k) :
    H.u ⟨j, hj⟩ + ((j : ℚ) - i) ≤ H.u ⟨i, by omega⟩ := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h1 := H.succ_add_one_le n hj
    have h2 := ih (by omega)
    push_cast
    linarith

/-- **The step-0 weights** `λ_ρ = wt_0(⌊u − ½⌋, e)` of a family, on `Fin n` with `n = k + 0·(t + 1)`: the weights
`WeylFock.wt` at step `j = 0`, the archive's step-0 weights of an object. -/
def wt0 (R : S.Ranks) (hw : R.HCFamily) {n : ℕ} (h : n = R.k + 0 * (R.t + 1)) : Φ S.A → Fin n → ℤ :=
  fun ρ i => WeylFock.wt R.k R.t 0 (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ (Fin.cast h i)

/-- `i < k` for `i : Fin n`, `n = k + 0·(t + 1)`. -/
theorem lt_k_of {n : ℕ} (h : n = R.k + 0 * (R.t + 1)) (i : Fin n) : (i : ℕ) < R.k := by
  rw [zero_mul, add_zero] at h
  omega

/-- `λ_{ρ,i} = u_i + ½ + i − k/2`. -/
theorem wt0_eq (hw : R.HCFamily) {n : ℕ} (h : n = R.k + 0 * (R.t + 1)) (ρ : Φ S.A) (i : Fin n) :
    ((R.wt0 hw h ρ i : ℤ) : ℚ) = (hw ρ).u ⟨i, lt_k_of h i⟩ + 1 / 2 + i - R.k / 2 := by
  have hi := lt_k_of h i
  obtain ⟨z, hz⟩ := (hw ρ).u_half ⟨i, hi⟩
  have hfl : ⌊(hw ρ).u ⟨i, hi⟩ - 1 / 2⌋ = z := by rw [hz]; simp
  obtain ⟨c, hc⟩ := R.k_even
  have hk2 : R.k / 2 = c := by omega
  have hkc : (R.k : ℚ) = c + c := by exact_mod_cast hc
  simp only [wt0, WeylFock.wt, Fin.val_cast, dite_eq_left hi, hfl, hk2, Nat.cast_zero, zero_mul, sub_zero]
  push_cast
  rw [hz, hkc]
  ring

/-- **The step-0 weights are antitone**, for every Harish-Chandra family (`HC.succ_add_one_le`): the hypothesis
`hlam` of `SharpObj.slopeFV_exact`. -/
theorem wt0_antitone (hw : R.HCFamily) {n : ℕ} (h : n = R.k + 0 * (R.t + 1)) (ρ : Φ S.A) :
    Antitone (R.wt0 hw h ρ) := by
  intro i j hij
  have h1 := (hw ρ).u_add_le j hij (lt_k_of h j)
  have h2 := wt0_eq hw h ρ i
  have h3 := wt0_eq hw h ρ j
  have : ((R.wt0 hw h ρ j : ℤ) : ℚ) ≤ R.wt0 hw h ρ i := by
    rw [h2, h3]
    linarith
  exact_mod_cast this

end Setting.Ranks

/-! ## The `Adm` API -/

/-- `v_E ≥ 1/2`, as `|d_E| ≥ 1`. -/
theorem Setting.half_le_vE (S : Setting) : 1 / 2 ≤ S.vE := by
  unfold Setting.vE
  have h1 : (1 : ℝ) ≤ |(discr S.E : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (discr_ne_zero S.E)
  have := Real.one_le_rpow h1 (inv_nonneg.2 (Nat.cast_nonneg (Module.finrank ℚ S.E)))
  linarith

namespace SharpDesign

/-- **A word family pinned to the translate `u`**: the same `v`, `b`, `e`, `u_0` and `u_{k−1}` as `hc u` at every
place, as the archive's word families are. -/
def PinnedTo (Dg : SharpDesign S κ x ε X) (u : S.A) (hw : Dg.R.HCFamily) : Prop :=
  ∀ ρ, (hw ρ).v = (Dg.hc u ρ).v ∧ (hw ρ).b = (Dg.hc u ρ).b ∧ (hw ρ).e = (Dg.hc u ρ).e ∧
    ∀ i : Fin Dg.R.k, ((i : ℕ) = 0 ∨ (i : ℕ) = Dg.R.k - 1) → (hw ρ).u i = (Dg.hc u ρ).u i

/-- `Σ_ρ [ρ top at u]·a_{ρ.2} = Σ_{t ∈ TT} a_t`: the tops are the places `(1, t)`, `t ∈ TT`. -/
theorem sum_top (Dg : SharpDesign S κ x ε X) (u : S.A) :
    ∑ ρ : Φ S.A, (if placeKind Dg.TT Dg.T2 u ρ = .top then Dg.a ρ.2 else 0) = ∑ t ∈ Dg.TT, Dg.a t := by
  simp only [placeKind_eq_top]
  rw [Fintype.sum_prod_type]
  have e : ∀ s : ℤˣ, ∑ t : S.A, (if s = 1 ∧ t ∈ Dg.TT then Dg.a t else 0) =
      if s = 1 then ∑ t ∈ Dg.TT, Dg.a t else 0 := by
    intro s
    by_cases hs : s = 1
    · simp [hs, Finset.sum_ite_mem]
    · simp [hs]
  rw [Finset.sum_congr rfl fun s _ => e s]
  simp

namespace Adm

variable {Dg : SharpDesign S κ x ε X} (hA : Dg.Adm)
include hA

/-- `m ∈ [x^{1/2−ε/16}, 2x^{1/2−ε/16}]`. -/
theorem m_mem : (Dg.R.m : ℝ) ∈ Set.Icc (x ^ (1 / 2 - ε / 16)) (2 * x ^ (1 / 2 - ε / 16)) := by
  rw [hA.m_eq]
  exact designM_mem hA.big

/-- `log k ≤ 6 log x`. -/
theorem log_k_le : Real.log Dg.R.k ≤ 6 * Real.log x := by
  obtain ⟨h1, h2⟩ := hA.big.designK_le
  rw [← hA.k_eq] at h1 h2
  have hx := hA.big.x_ge
  have h3 : 2 * x ^ 5 ≤ x ^ 6 := by rw [pow_succ x 5]; nlinarith [pow_pos hA.big.pos 5]
  calc Real.log Dg.R.k ≤ Real.log (x ^ 6) := Real.log_le_log (by linarith) (by linarith)
    _ = 6 * Real.log x := by rw [Real.log_pow]; norm_num

/-- `log x ≤ x^ε/1000`. -/
theorem log_le : Real.log x ≤ x ^ ε / 1000 := hA.big.log_le

/-- `b′ ≤ b_t ≤ 2b′` at the tops. -/
theorem bT_le {pr : DesignPar S} (hF : Dg.FamAt pr) :
    ∀ t ∈ Dg.TT, scB' x ε ≤ pr.bT t ∧ (pr.bT t : ℝ) ≤ 2 * scB' x ε := fun t ht =>
  ⟨(hF.bT_mem t ht).1, hA.big.le_two_mul_scB' (hF.bT_mem t ht).2⟩

/-- **The windows**: every `e_j` of every `hc u` lies in `[w″, 2b]` (`e_window`). -/
theorem e_mem (u : S.A) (ρ : Φ S.A) (j : Fin Dg.R.m) :
    scW'' S x ε ≤ ((Dg.hc u ρ).e j : ℝ) ∧ ((Dg.hc u ρ).e j : ℝ) ≤ 2 * scB x ε := by
  obtain ⟨pr, hF⟩ := hA.fam
  have hm : (Dg.R.m : ℝ) ≤ 2 * x := by rw [hA.m_eq]; exact hA.big.designM_le
  rw [hF.hc_eq u]
  exact (hA.toDesignAdm.e_window hm hF.σ_lt (hA.bT_le hF) hF.hyp u ρ j).2.2

/-- **The weights** `w_{u,j}(ρ) = e_j(ρ)` lie in `[w″, 2b]`. -/
theorem w_mem (u : S.A) (j : Fin Dg.m) (ρ : Φ S.A) : scW'' S x ε ≤ Dg.w u j ρ ∧ Dg.w u j ρ ≤ 2 * scB x ε := by
  rw [Dg.hw]
  exact hA.e_mem u ρ _

/-- `|TT|·x·e^{x^ε} ≤ Σ_t a_t`. -/
theorem sum_a_ge : Dg.TT.card * (x * Real.exp (x ^ ε)) ≤ ∑ t ∈ Dg.TT, Dg.a t := by
  obtain ⟨pr, hF⟩ := hA.fam
  have h := Finset.card_nsmul_le_sum Dg.TT Dg.a (x * Real.exp (x ^ ε)) fun t ht => by
    rw [hF.a_eq]
    exact (hF.a_mem t ht).1
  rwa [nsmul_eq_mul] at h

/-- `a = x·e^{x^ε} ≤ Σ_t a_t`, as `TT ≠ ∅`. -/
theorem scA_le_sum : scA x ε ≤ ∑ t ∈ Dg.TT, Dg.a t := by
  have h1 : (1 : ℝ) ≤ Dg.TT.card := by exact_mod_cast Dg.TT_nonempty.card_pos
  have h2 : 0 < x * Real.exp (x ^ ε) := mul_pos hA.big.pos (Real.exp_pos _)
  have := hA.sum_a_ge
  calc scA x ε = 1 * (x * Real.exp (x ^ ε)) := by rw [one_mul]; rfl
    _ ≤ _ := by nlinarith

/-- `[E:ℚ] ≤ Σ_t a_t/x`: `[E:ℚ] = 4|A| ≤ 4x³ ≤ b`. -/
theorem card_E_le : (Module.finrank ℚ S.E : ℝ) ≤ (∑ t ∈ Dg.TT, Dg.a t) / x := by
  have hE : Module.finrank ℚ S.E = 4 * Fintype.card S.A := by
    rw [← IsGalois.card_aut_eq_finrank, S.card_gal]
  have hx := hA.big.x_ge
  have hb := hA.big.b_ge'
  have h1 : 4 * x ^ 3 ≤ x ^ 850 := by
    have : x ^ 3 * x ^ 847 = x ^ 850 := by ring
    have h2 : 4 ≤ x ^ 847 := le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
    nlinarith [pow_pos hA.big.pos 3]
  rw [le_div_iff₀ hA.big.pos, hE]
  push_cast
  calc 4 * (Fintype.card S.A : ℝ) * x ≤ 4 * x ^ 3 * x := by gcongr; exact hA.card_le_cube
    _ ≤ scB x ε * x := by gcongr; linarith
    _ = scA x ε := by unfold scA; ring
    _ ≤ _ := hA.scA_le_sum

/-- `log N ≤ x^{ε/3} ≤ x^ε`. -/
theorem log_N_le' : Real.log S.N ≤ x ^ (ε / 3) ∧ x ^ (ε / 3) ≤ x ^ ε := by
  have hl := hA.big.one_le_log
  have h1 := hA.big.thin
  have h2 : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hA.big.pos.le _
  have h3 : Real.log x ^ 2 ≤ Real.log x ^ 3 := pow_le_pow_right₀ hl (by norm_num)
  refine ⟨le_trans hA.log_N_le (by nlinarith [sq_nonneg (Real.log x)]),
    Real.rpow_le_rpow_of_exponent_le hA.big.one_lt.le (by linarith [hA.big.ε_pos])⟩

/-- `16x^ε ≤ log(g₀g₁) ≤ 17x^ε`, from `g_i ∈ [(kb)^8, 2(kb)^8]`. -/
theorem log_g_mem : 16 * x ^ ε ≤ Real.log (Dg.g₀ * Dg.g₁) ∧ Real.log (Dg.g₀ * Dg.g₁) ≤ 17 * x ^ ε := by
  obtain ⟨g0l, g0u, -⟩ := hA.split Dg.g₀ (by simp)
  obtain ⟨g1l, g1u, -⟩ := hA.split Dg.g₁ (by simp)
  have hk1 : 1 ≤ (Dg.R.k : ℝ) := by rw [hA.k_eq]; exact hA.big.designK_le.1
  set K := (Dg.R.k : ℝ) * scB x ε with hKdef
  have hK0 : 0 < K := mul_pos (by linarith) (Real.exp_pos _)
  have hlogK : Real.log K = Real.log Dg.R.k + x ^ ε := by
    rw [hKdef]
    unfold scB scL
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hlk0 : 0 ≤ Real.log Dg.R.k := Real.log_nonneg hk1
  have hlk := hA.log_k_le
  have hlx := hA.log_le
  have hxe : 4096 ≤ x ^ ε := hA.big.le_rpow (by linarith [hA.big.ε_pos])
  have hK8 : 0 < K ^ 8 := by positivity
  have hpl : K ^ 16 ≤ (Dg.g₀ : ℝ) * Dg.g₁ := by
    calc K ^ 16 = K ^ 8 * K ^ 8 := by ring
      _ ≤ _ := mul_le_mul g0l g1l hK8.le (by linarith)
  have hpu : (Dg.g₀ : ℝ) * Dg.g₁ ≤ 4 * K ^ 16 := by
    calc (Dg.g₀ : ℝ) * Dg.g₁ ≤ (2 * K ^ 8) * (2 * K ^ 8) := mul_le_mul g0u g1u (Nat.cast_nonneg _) (by positivity)
      _ = 4 * K ^ 16 := by ring
  have hl16 : Real.log (K ^ 16) = 16 * Real.log K := by rw [Real.log_pow]; norm_num
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  constructor
  · calc 16 * x ^ ε ≤ 16 * Real.log K := by rw [hlogK]; linarith
      _ = Real.log (K ^ 16) := hl16.symm
      _ ≤ _ := Real.log_le_log (by positivity) hpl
  · calc Real.log ((Dg.g₀ : ℝ) * Dg.g₁) ≤ Real.log (4 * K ^ 16) :=
          Real.log_le_log (lt_of_lt_of_le (by positivity) hpl) hpu
      _ = Real.log 4 + 16 * Real.log K := by rw [Real.log_mul (by norm_num) (by positivity), hl16]
      _ ≤ 17 * x ^ ε := by rw [hlogK]; linarith

/-- Each term of `Λ_u`: `0 ≤ log(w_{u,j}(ρ)·v_E/π) ≤ 2x^ε`, as `w ∈ [w″, 2b]`, `v_E ≥ 1/2` and `2v_E ≤ N`. -/
theorem lam_term_mem (u : S.A) (j : Fin Dg.m) (ρ : Φ S.A) :
    0 ≤ Real.log (Dg.w u j ρ * S.vE / Real.pi) ∧ Real.log (Dg.w u j ρ * S.vE / Real.pi) ≤ 2 * x ^ ε := by
  obtain ⟨w1, w2⟩ := hA.w_mem u j ρ
  have hw := hA.w''_ge
  have hx := hA.big.x_ge
  have hv := S.half_le_vE
  have hN0 : (0 : ℝ) < S.N := Nat.cast_pos.2 (NeZero.pos _)
  have hvN : 2 * S.vE ≤ S.N := (Real.log_le_log_iff (by linarith) hN0).1 (log_vE_le S)
  have hπ := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have h1 : (8 : ℝ) ≤ x ^ 437 := le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
  have hw0 : 0 < Dg.w u j ρ := by linarith
  have e1 : Dg.w u j ρ * (1 / 2) ≤ Dg.w u j ρ * S.vE := mul_le_mul_of_nonneg_left hv hw0.le
  have e2 : Dg.w u j ρ * S.vE ≤ 2 * scB x ε * S.vE := mul_le_mul_of_nonneg_right w2 (by linarith)
  have e3 : scB x ε * (2 * S.vE) ≤ scB x ε * S.N := mul_le_mul_of_nonneg_left hvN hb0.le
  obtain ⟨hN1, hN2⟩ := hA.log_N_le'
  have e4 : 0 ≤ scB x ε * S.N := by positivity
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  · calc Real.log (Dg.w u j ρ * S.vE / Real.pi) ≤ Real.log (scB x ε * S.N) := by
          apply Real.log_le_log (by positivity)
          rw [div_le_iff₀ (by linarith)]
          nlinarith
      _ = x ^ ε + Real.log S.N := by
          rw [Real.log_mul hb0.ne' hN0.ne']
          unfold scB scL
          rw [Real.log_exp]
      _ ≤ 2 * x ^ ε := by linarith

/-- `Λ_u ≥ 16mx^ε`: every term is nonnegative and `log(g₀g₁) ≥ 16x^ε`. -/
theorem lam_ge (u : S.A) : 16 * Dg.m * x ^ ε ≤ S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) := by
  unfold Setting.lam
  have h0 : 0 ≤ ∑ j, (Fintype.card (Φ S.A) : ℝ)⁻¹ * ∑ ρ, Real.log (Dg.w u j ρ * S.vE / Real.pi) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => (hA.lam_term_mem u j ρ).1)
  have := hA.log_g_mem.1
  have hm : (0 : ℝ) ≤ Dg.m := Nat.cast_nonneg _
  nlinarith

/-- **The size of `Λ_u`**: `mx^ε/2 ≤ Λ_u ≤ 24mx^ε` (`lam_ge`, `lam_term_mem`, `log_g_mem`). -/
theorem lam_bounds (u : S.A) :
    Dg.m * x ^ ε / 2 ≤ S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) ∧
      S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) ≤ 24 * Dg.m * x ^ ε := by
  have hm : (0 : ℝ) ≤ Dg.m := Nat.cast_nonneg _
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hA.big.pos.le _
  refine ⟨le_trans (by nlinarith) (hA.lam_ge u), ?_⟩
  unfold Setting.lam
  have hΦ : (0 : ℝ) < Fintype.card (Φ S.A) := Nat.cast_pos.2 Fintype.card_pos
  have hj : ∀ j, (Fintype.card (Φ S.A) : ℝ)⁻¹ * ∑ ρ, Real.log (Dg.w u j ρ * S.vE / Real.pi) ≤ 2 * x ^ ε := by
    intro j
    rw [inv_mul_le_iff₀ hΦ]
    calc ∑ ρ, Real.log (Dg.w u j ρ * S.vE / Real.pi) ≤ ∑ _ρ : Φ S.A, 2 * x ^ ε :=
          Finset.sum_le_sum fun ρ _ => (hA.lam_term_mem u j ρ).2
      _ = _ := by simp
  have h1 : ∑ j, (Fintype.card (Φ S.A) : ℝ)⁻¹ * ∑ ρ, Real.log (Dg.w u j ρ * S.vE / Real.pi) ≤
      Dg.m * (2 * x ^ ε) := by
    calc _ ≤ ∑ _j : Fin Dg.m, 2 * x ^ ε := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  have := hA.log_g_mem.2
  nlinarith

/-- `x^{1/2} ≤ x^{1/2−ε/16}·x^ε ≤ mx^ε` and `96x^{1/2−ε/16}·x^ε ≤ x`. -/
theorem m_mul_rpow : x ^ (1 / 2 : ℝ) ≤ Dg.m * x ^ ε ∧ 96 * (x ^ (1 / 2 - ε / 16) * x ^ ε) ≤ x := by
  have hx0 := hA.big.pos
  have he : x ^ (1 / 2 - ε / 16) * x ^ ε = x ^ (1 / 2 + 15 * ε / 16) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hm : x ^ (1 / 2 - ε / 16) ≤ Dg.m := by rw [Dg.hm]; exact hA.m_mem.1
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le _
  constructor
  · calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 + 15 * ε / 16) :=
          Real.rpow_le_rpow_of_exponent_le hA.big.one_lt.le (by linarith [hA.big.ε_pos])
      _ = x ^ (1 / 2 - ε / 16) * x ^ ε := he.symm
      _ ≤ _ := by gcongr
  · have h1 := hA.big.le_rpow (c := 1 / 2 - 15 * ε / 16) (by linarith [hA.big.ε_lt])
    have h2 : x = x ^ (1 / 2 + 15 * ε / 16) * x ^ (1 / 2 - 15 * ε / 16) := by
      rw [← Real.rpow_add hx0]; ring_nf; rw [Real.rpow_one]
    rw [he]
    nlinarith [Real.rpow_pos_of_pos hx0 (1 / 2 + 15 * ε / 16)]

/-- **`Λ_u ≤ x/2`**: `24mx^ε ≤ 48x^{1/2+15ε/16} ≤ x/2`. -/
theorem lam_le (u : S.A) : S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) ≤ x / 2 := by
  have h1 := (hA.lam_bounds u).2
  have hm : (Dg.m : ℝ) ≤ 2 * x ^ (1 / 2 - ε / 16) := by rw [Dg.hm]; exact hA.m_mem.2
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hA.big.pos.le _
  have h2 := hA.m_mul_rpow.2
  nlinarith

/-- **`Λ_u + log 2 ≤ x`**, so a prime `T` with `log T ∈ (Λ_u, Λ_u + log 2]` has `log T ≤ x`. -/
theorem lam_add_log_two_le (u : S.A) : S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) + Real.log 2 ≤ x := by
  have h1 := hA.lam_le u
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith [hA.big.x_ge]

/-- **`(log 4dM²)³ ≤ Λ_u`** for `M = QS·q·d·(g₀g₁)²`: `log 4dM² ≤ log 4 + 3 log N + 4 log(g₀g₁) ≤ 100x^ε`, and
`10⁶x^{3ε} ≤ x^{1/2} ≤ mx^ε`. -/
theorem logM_cube_le (u : S.A) :
    Real.log (4 * S.d * ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℝ) ^ 2) ^ 3 ≤
      S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) := by
  have hx0 := hA.big.pos
  have hN0 : (0 : ℝ) < S.N := Nat.cast_pos.2 (NeZero.pos _)
  have hd1 : (1 : ℝ) ≤ S.d := by exact_mod_cast (Fact.out : S.d.Prime).one_lt.le
  have hdN : (S.d : ℝ) ≤ S.N := by exact_mod_cast Nat.le_of_dvd (NeZero.pos _) S.d_dvd_N
  have hN1 : (1 : ℝ) ≤ S.N := by exact_mod_cast NeZero.one_le
  have hg0 : (1 : ℝ) ≤ Dg.g₀ := by exact_mod_cast Dg.g₀_prime.one_lt.le
  have hg1 : (1 : ℝ) ≤ Dg.g₁ := by exact_mod_cast Dg.g₁_prime.one_lt.le
  set G := (Dg.g₀ : ℝ) * Dg.g₁ with hG
  have hG1 : 1 ≤ G := by nlinarith
  have hM : ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℝ) = S.N * G ^ 2 := by
    rw [hG]; push_cast; rw [Setting.N]; push_cast; ring
  rw [hM]
  set Y := Real.log (4 * S.d * (S.N * G ^ 2) ^ 2) with hY
  have hY0 : 0 ≤ Y := Real.log_nonneg (by nlinarith [one_le_pow₀ hG1 (n := 4), one_le_pow₀ hN1 (n := 2)])
  have hY1 : Y ≤ 100 * x ^ ε := by
    have e1 : Y ≤ Real.log (4 * S.N ^ 3 * G ^ 4) := by
      apply Real.log_le_log (by positivity)
      have : (S.N * G ^ 2) ^ 2 = S.N ^ 2 * G ^ 4 := by ring
      rw [this]
      have h4 : 0 ≤ S.N ^ 2 * G ^ 4 := by positivity
      nlinarith
    have e2 : Real.log (4 * S.N ^ 3 * G ^ 4) = Real.log 4 + 3 * Real.log S.N + 4 * Real.log G := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        Real.log_pow]
      push_cast
      ring
    have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    obtain ⟨hn1, hn2⟩ := hA.log_N_le'
    have hg := hA.log_g_mem.2
    have hxe : 4096 ≤ x ^ ε := hA.big.le_rpow (by linarith [hA.big.ε_pos])
    linarith
  have hcube : Y ^ 3 ≤ 10 ^ 6 * x ^ (3 * ε) := by
    have e : x ^ (3 * ε) = (x ^ ε) ^ 3 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
    rw [e]
    calc Y ^ 3 ≤ (100 * x ^ ε) ^ 3 := pow_le_pow_left₀ hY0 hY1 3
      _ = 10 ^ 6 * (x ^ ε) ^ 3 := by ring
  have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le _
  have hm : (0 : ℝ) ≤ Dg.m := Nat.cast_nonneg _
  calc Y ^ 3 ≤ 10 ^ 6 * x ^ (3 * ε) := hcube
    _ ≤ x ^ (1 / 2 : ℝ) := hA.big.cube
    _ ≤ Dg.m * x ^ ε := hA.m_mul_rpow.1
    _ ≤ 16 * Dg.m * x ^ ε := by nlinarith
    _ ≤ _ := hA.lam_ge u

/-- **One place of a pinned family**: `Σ_i ν_{ρ,i}` and `Σ_i λ_{ρ,i}` are at most
`[ρ top]·a_t + k(8Δk + 2b′ + k + 1)`. Interlacing gives `u_i ≤ u_1 < v_0 ≤ 4Δk` for `i ≥ 1`, and the pin gives the
ends `u_0`, `u_{k−1}` of `hc u` (`hcFam_u_top`, `hcFam_u_ntop`); then `ν_{ρ,i} = λ_{ρ,i} − λ_{ρ,k−1} ≤ u_i − u_{k−1}`
and `λ_{ρ,i} ≤ u_i + k/2` (`wt0_eq`). -/
theorem place_le {u : S.A} {hw : Dg.R.HCFamily} (hp : Dg.PinnedTo u hw) {n : ℕ}
    (h : n = Dg.R.k + 0 * (Dg.R.t + 1)) (ρ : Φ S.A) :
    ((∑ i, WeylFock.natW (Dg.R.wt0 hw h ρ) i : ℕ) : ℝ) ≤
        (if placeKind Dg.TT Dg.T2 u ρ = .top then Dg.a ρ.2 else 0) +
          Dg.R.k * (8 * designΔ x * Dg.R.k + 2 * scB' x ε + Dg.R.k + 1) ∧
      ∑ i, (Dg.R.wt0 hw h ρ i : ℝ) ≤ (if placeKind Dg.TT Dg.T2 u ρ = .top then Dg.a ρ.2 else 0) +
        Dg.R.k * (8 * designΔ x * Dg.R.k + 2 * scB' x ε + Dg.R.k + 1) := by
  obtain ⟨pr, hF⟩ := hA.fam
  have hk5 : 5 ≤ Dg.R.k := by have := Dg.R.m_add_three_le; have := Dg.R.two_le_m; omega
  have hn : n = Dg.R.k := by rw [h, zero_mul, add_zero]
  have hn0 : 0 < n := by omega
  obtain ⟨hv, -, -, hu⟩ := hp ρ
  have hΔ1 : (1 : ℝ) ≤ designΔ x := by exact_mod_cast hA.big.designΔ_mem.1
  have hK5 : (5 : ℝ) ≤ Dg.R.k := by exact_mod_cast hk5
  have hb'0 := (scB'_pos ε hA.big.pos).le
  set U0 : ℝ := ((hw ρ).u ⟨0, by omega⟩ : ℝ) with hU0
  set Uk : ℝ := ((hw ρ).u ⟨Dg.R.k - 1, by omega⟩ : ℝ) with hUk
  -- the middle entries: `u_i ≤ u_1 < v_0 = 4Δ(k − 2)`
  have hmid : ∀ (i : ℕ) (hi : i < Dg.R.k), 1 ≤ i → ((hw ρ).u ⟨i, hi⟩ : ℝ) ≤ 4 * designΔ x * Dg.R.k := by
    intro i hi h1
    have e1 := (hw ρ).u_add_le (i := 1) i h1 hi
    have e2 : (hw ρ).u ⟨1, by omega⟩ < (hw ρ).v ⟨0, by omega⟩ := (hw ρ).lt_v ⟨0, by omega⟩
    have e3 : (hw ρ).v ⟨0, by omega⟩ = 4 * designΔ x * ((Dg.R.k : ℤ) - 2 - ((0 : ℕ) : ℤ)) := by
      rw [hv, hF.hc_eq u]
      rfl
    rw [e3] at e2
    push_cast at e2
    push_cast at e1
    have e4 : (1 : ℚ) ≤ i := by exact_mod_cast h1
    have e5 : ((hw ρ).u ⟨i, hi⟩ : ℚ) ≤ 4 * designΔ x * Dg.R.k := by
      have : (0 : ℚ) ≤ designΔ x := by positivity
      have : 4 * (designΔ x : ℚ) * ((Dg.R.k : ℚ) - 2 - 0) ≤ 4 * designΔ x * Dg.R.k := by nlinarith
      linarith
    exact_mod_cast e5
  -- the last entry: `u_{k−1} + (k − 1 − i) ≤ u_i`
  have hlast : ∀ (i : ℕ) (hi : i < Dg.R.k), Uk + ((Dg.R.k : ℝ) - 1 - i) ≤ ((hw ρ).u ⟨i, hi⟩ : ℝ) := by
    intro i hi
    have e1 := (hw ρ).u_add_le (i := i) (Dg.R.k - 1) (by omega) (by omega)
    have e2 : ((Dg.R.k - 1 : ℕ) : ℚ) = (Dg.R.k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [e2] at e1
    rw [hUk]
    exact_mod_cast e1
  -- the weights
  have hlam : ∀ i : Fin n, ((Dg.R.wt0 hw h ρ i : ℤ) : ℝ) =
      ((hw ρ).u ⟨i, Setting.Ranks.lt_k_of h i⟩ : ℝ) + 1 / 2 + (i : ℕ) - (Dg.R.k : ℝ) / 2 := by
    intro i
    have := congrArg (fun q : ℚ => (q : ℝ)) (Setting.Ranks.wt0_eq hw h ρ i)
    push_cast at this
    exact this
  have hl : ((Dg.R.wt0 hw h ρ ⟨n - 1, by omega⟩ : ℤ) : ℝ) = Uk + 1 / 2 + ((Dg.R.k : ℝ) - 1) - (Dg.R.k : ℝ) / 2 := by
    rw [hlam, hUk]
    have e : (⟨n - 1, Setting.Ranks.lt_k_of h ⟨n - 1, by omega⟩⟩ : Fin Dg.R.k) = ⟨Dg.R.k - 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    have e2 : ((n - 1 : ℕ) : ℝ) = (Dg.R.k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), hn]; norm_num
    simp only [e, e2]
  have hdet : WeylFock.detShift (Dg.R.wt0 hw h ρ) = Dg.R.wt0 hw h ρ ⟨n - 1, by omega⟩ := by
    simp [WeylFock.detShift, hn0]
  have hnat : ∀ i : Fin n, ((WeylFock.natW (Dg.R.wt0 hw h ρ) i : ℕ) : ℝ) =
      (Dg.R.wt0 hw h ρ i : ℝ) - Dg.R.wt0 hw h ρ ⟨n - 1, by omega⟩ := by
    intro i
    have hle : Dg.R.wt0 hw h ρ ⟨n - 1, by omega⟩ ≤ Dg.R.wt0 hw h ρ i :=
      Setting.Ranks.wt0_antitone hw h ρ (Fin.le_iff_val_le_val.2 (by simp; omega))
    simp only [WeylFock.natW, hdet]
    rw [show ((Int.toNat (Dg.R.wt0 hw h ρ i - Dg.R.wt0 hw h ρ ⟨n - 1, by omega⟩) : ℕ) : ℝ) =
      ((Int.toNat (Dg.R.wt0 hw h ρ i - Dg.R.wt0 hw h ρ ⟨n - 1, by omega⟩) : ℤ) : ℝ) by norm_cast,
      Int.toNat_of_nonneg (by linarith)]
    push_cast
    ring
  -- `u_i ≤ 4Δk + [i = 0]u_0`
  have hui : ∀ i : Fin n, ((hw ρ).u ⟨i, Setting.Ranks.lt_k_of h i⟩ : ℝ) ≤
      4 * designΔ x * Dg.R.k + (if (i : ℕ) = 0 then U0 else 0) := by
    intro i
    have h0 : (0 : ℝ) ≤ 4 * designΔ x * Dg.R.k := by positivity
    by_cases hi0 : (i : ℕ) = 0
    · have e : (⟨i, Setting.Ranks.lt_k_of h i⟩ : Fin Dg.R.k) = ⟨0, by omega⟩ := Fin.ext hi0
      rw [ite_eq_left hi0, e]
      linarith
    · rw [ite_eq_right hi0]
      linarith [hmid i (Setting.Ranks.lt_k_of h i) (by omega)]
  have hsum0 : ∑ i : Fin n, (if (i : ℕ) = 0 then U0 else 0) = U0 := by
    rw [Finset.sum_eq_single ⟨0, hn0⟩ (fun b _ hb => ite_eq_right fun h' => hb (Fin.ext h'))
      (fun h' => absurd (Finset.mem_univ _) h')]
    simp
  have hcard : ∀ c : ℝ, ∑ _i : Fin n, c = Dg.R.k * c := fun c => by simp [hn]
  -- the sums
  have hS1 : ((∑ i, WeylFock.natW (Dg.R.wt0 hw h ρ) i : ℕ) : ℝ) ≤ Dg.R.k * (4 * designΔ x * Dg.R.k - Uk) + U0 := by
    push_cast
    calc ∑ i, ((WeylFock.natW (Dg.R.wt0 hw h ρ) i : ℕ) : ℝ)
        ≤ ∑ i : Fin n, (4 * designΔ x * Dg.R.k - Uk + (if (i : ℕ) = 0 then U0 else 0)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hnat, hlam, hl]
          have := hui i
          have := hlast i (Setting.Ranks.lt_k_of h i)
          have : ((i : ℕ) : ℝ) ≤ (Dg.R.k : ℝ) - 1 := by
            have := Setting.Ranks.lt_k_of h i
            have : ((i : ℕ) : ℝ) + 1 ≤ Dg.R.k := by exact_mod_cast this
            linarith
          linarith
      _ = _ := by rw [Finset.sum_add_distrib, hsum0, hcard]
  have hS2 : ∑ i, (Dg.R.wt0 hw h ρ i : ℝ) ≤ Dg.R.k * (4 * designΔ x * Dg.R.k + Dg.R.k / 2) + U0 := by
    calc ∑ i, (Dg.R.wt0 hw h ρ i : ℝ)
        ≤ ∑ i : Fin n, (4 * designΔ x * Dg.R.k + Dg.R.k / 2 + (if (i : ℕ) = 0 then U0 else 0)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hlam]
          have := hui i
          have : ((i : ℕ) : ℝ) ≤ (Dg.R.k : ℝ) - 1 := by
            have := Setting.Ranks.lt_k_of h i
            have : ((i : ℕ) : ℝ) + 1 ≤ Dg.R.k := by exact_mod_cast this
            linarith
          linarith
      _ = _ := by rw [Finset.sum_add_distrib, hsum0, hcard]
  -- the ends, by the kind of the place
  have hu0 := hu ⟨0, by omega⟩ (Or.inl rfl)
  have huk := hu ⟨Dg.R.k - 1, by omega⟩ (Or.inr rfl)
  have hΔK : (0 : ℝ) ≤ designΔ x * Dg.R.k * Dg.R.k := by positivity
  by_cases hpk : placeKind Dg.TT Dg.T2 u ρ = .top
  · have e0 : (Dg.hc u ρ).u ⟨0, by omega⟩ = pr.aZ ρ.2 + ((Dg.R.k : ℚ) - 1) / 2 := by
      rw [hF.hc_eq u]; exact (hcFam_u_top hF.hyp hpk).1
    have ek : (Dg.hc u ρ).u ⟨Dg.R.k - 1, by omega⟩ = -pr.bT ρ.2 - ((Dg.R.k : ℚ) - 1) / 2 := by
      rw [hF.hc_eq u]; exact (hcFam_u_top hF.hyp hpk).2
    have hU0' : U0 = pr.aZ ρ.2 + ((Dg.R.k : ℝ) - 1) / 2 := by rw [hU0, hu0, e0]; push_cast; ring
    have hUk' : Uk = -pr.bT ρ.2 - ((Dg.R.k : ℝ) - 1) / 2 := by rw [hUk, huk, ek]; push_cast; ring
    obtain ⟨b1, b2⟩ := hA.bT_le hF ρ.2 (placeKind_eq_top.1 hpk).2
    have hkb : (Dg.R.k : ℝ) * pr.bT ρ.2 ≤ Dg.R.k * (2 * scB' x ε) := mul_le_mul_of_nonneg_left b2 (by linarith)
    rw [ite_eq_left hpk, hF.a_eq]
    constructor <;> nlinarith
  · have e0 : (Dg.hc u ρ).u ⟨0, by omega⟩ = 4 * designΔ x * (2 * (Dg.R.k : ℚ) - 2) + 1 / 2 := by
      rw [hF.hc_eq u]; exact (hcFam_u_ntop hF.hyp hpk).1
    have ek : (Dg.hc u ρ).u ⟨Dg.R.k - 1, by omega⟩ = -1 / 2 := by
      rw [hF.hc_eq u]; exact (hcFam_u_ntop hF.hyp hpk).2
    have hU0' : U0 = 4 * designΔ x * (2 * (Dg.R.k : ℝ) - 2) + 1 / 2 := by rw [hU0, hu0, e0]; push_cast; ring
    have hUk' : Uk = -1 / 2 := by rw [hUk, huk, ek]; push_cast; ring
    have hΔk : designΔ x * (2 * (Dg.R.k : ℝ) - 2) ≤ designΔ x * Dg.R.k * Dg.R.k := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [ite_eq_right hpk]
    constructor <;> nlinarith

/-- `2|A|·k(8Δk + 2b′ + k + 1) ≤ a`: with `|A| ≤ x³`, `k ≤ 2x^5`, `Δ ≤ 2x` the polynomial part is at most
`140x^{14} ≤ xb/2`, and `8|A|kb′ ≤ 16x^9·b/X′ ≤ xb/2` as `X′ ≥ x^{410}`. -/
theorem places_le :
    2 * (Fintype.card S.A : ℝ) * (Dg.R.k * (8 * designΔ x * Dg.R.k + 2 * scB' x ε + Dg.R.k + 1)) ≤ scA x ε := by
  have hx := hA.big.x_ge
  have hx0 := hA.big.pos
  obtain ⟨hk1, hk2⟩ := hA.big.designK_le
  rw [← hA.k_eq] at hk1 hk2
  have hn := hA.card_le_cube
  have hn0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have hΔ := hA.big.designΔ_mem.2
  have hX := hA.big.X'_ge
  have hb := hA.big.b_ge'
  have hX0 : 0 < scX' x ε := Real.exp_pos _
  set B := scB x ε / scX' x ε with hB
  have hB0 : 0 ≤ B := div_nonneg (Real.exp_pos _).le hX0.le
  have hbB : scB x ε = B * scX' x ε := by rw [hB, div_mul_cancel₀ _ hX0.ne']
  have hnk : (Fintype.card S.A : ℝ) * Dg.R.k ≤ 2 * x ^ 8 := by
    calc (Fintype.card S.A : ℝ) * Dg.R.k ≤ x ^ 3 * (2 * x ^ 5) := mul_le_mul hn hk2 (by linarith) (by positivity)
      _ = 2 * x ^ 8 := by ring
  have hx56 : x ^ 5 ≤ x ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hx16 : 1 ≤ x ^ 6 := one_le_pow₀ (by linarith)
  have hinner : 8 * (designΔ x : ℝ) * Dg.R.k + Dg.R.k + 1 ≤ 35 * x ^ 6 := by
    have : (designΔ x : ℝ) * Dg.R.k ≤ (2 * x) * (2 * x ^ 5) := mul_le_mul hΔ hk2 (by linarith) (by linarith)
    nlinarith
  have hP1 : 2 * ((Fintype.card S.A : ℝ) * Dg.R.k) * (8 * designΔ x * Dg.R.k + Dg.R.k + 1) ≤ 140 * x ^ 14 := by
    calc _ ≤ 2 * (2 * x ^ 8) * (35 * x ^ 6) := by gcongr
      _ = 140 * x ^ 14 := by ring
  have hP2 : 140 * x ^ 14 ≤ x * scB x ε / 2 := by
    have : x ^ 13 * 280 ≤ x ^ 13 * x ^ 837 :=
      mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num)))
        (by positivity)
    have e : x ^ 13 * x ^ 837 = x ^ 850 := by ring
    nlinarith [pow_pos hx0 13]
  have hQ1 : 4 * ((Fintype.card S.A : ℝ) * Dg.R.k) * scB' x ε ≤ 8 * x ^ 9 * B := by
    rw [scB'_eq, ← hB]
    calc 4 * ((Fintype.card S.A : ℝ) * Dg.R.k) * (x * B) ≤ 4 * (2 * x ^ 8) * (x * B) := by gcongr
      _ = 8 * x ^ 9 * B := by ring
  have hQ2 : 8 * x ^ 9 * B ≤ x * scB x ε / 2 := by
    have h8 : 16 * x ^ 8 ≤ scX' x ε := by
      have : x ^ 8 * 16 ≤ x ^ 8 * x ^ 402 :=
        mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num)))
          (by positivity)
      nlinarith [pow_pos hx0 8]
    rw [hbB]
    nlinarith [mul_le_mul_of_nonneg_left h8 (mul_nonneg hx0.le hB0)]
  have e : 2 * (Fintype.card S.A : ℝ) * (Dg.R.k * (8 * designΔ x * Dg.R.k + 2 * scB' x ε + Dg.R.k + 1)) =
      2 * ((Fintype.card S.A : ℝ) * Dg.R.k) * (8 * designΔ x * Dg.R.k + Dg.R.k + 1) +
        4 * ((Fintype.card S.A : ℝ) * Dg.R.k) * scB' x ε := by ring
  rw [e]
  unfold scA
  linarith

/-- **Summing over the places**: a function bounded by `[ρ top]·a_{ρ.2} + k(8Δk + 2b′ + k + 1)` at every place
sums to at most `2Σ_t a_t` (`sum_top`, `places_le`, `|Φ| = 2|A|`). -/
theorem sum_places_le (u : S.A) (c : Φ S.A → ℝ)
    (hc : ∀ ρ, c ρ ≤ (if placeKind Dg.TT Dg.T2 u ρ = .top then Dg.a ρ.2 else 0) +
      Dg.R.k * (8 * designΔ x * Dg.R.k + 2 * scB' x ε + Dg.R.k + 1)) :
    ∑ ρ, c ρ ≤ 2 * ∑ t ∈ Dg.TT, Dg.a t := by
  calc ∑ ρ, c ρ ≤ ∑ ρ : Φ S.A, ((if placeKind Dg.TT Dg.T2 u ρ = .top then Dg.a ρ.2 else 0) +
        Dg.R.k * (8 * designΔ x * Dg.R.k + 2 * scB' x ε + Dg.R.k + 1)) := Finset.sum_le_sum fun ρ _ => hc ρ
    _ = ∑ t ∈ Dg.TT, Dg.a t +
        2 * (Fintype.card S.A : ℝ) * (Dg.R.k * (8 * designΔ x * Dg.R.k + 2 * scB' x ε + Dg.R.k + 1)) := by
      rw [Finset.sum_add_distrib, sum_top Dg u, Finset.sum_const, Finset.card_univ, card_Φ, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ 2 * ∑ t ∈ Dg.TT, Dg.a t := by linarith [hA.places_le, hA.scA_le_sum]

/-- **(F): `|ν| = Σ_{ρ,i} ν_{ρ,i} ≤ 2Σ_t a_t`** for the step-0 weights of every word family pinned to `u`. -/
theorem sum_natW_le {u : S.A} {hw : Dg.R.HCFamily} (hp : Dg.PinnedTo u hw) {n : ℕ}
    (h : n = Dg.R.k + 0 * (Dg.R.t + 1)) :
    ((∑ ρ, ∑ i, WeylFock.natW (Dg.R.wt0 hw h ρ) i : ℕ) : ℝ) ≤ 2 * ∑ t ∈ Dg.TT, Dg.a t := by
  rw [Nat.cast_sum]
  exact hA.sum_places_le u _ fun ρ => (hA.place_le hp h ρ).1

/-- **(F): `(ΣΛ)⁺ = max(0, Σ_{ρ,i} λ_{ρ,i}) ≤ 2Σ_t a_t`** for the step-0 weights of every word family pinned to
`u`. -/
theorem sum_wt0_le {u : S.A} {hw : Dg.R.HCFamily} (hp : Dg.PinnedTo u hw) {n : ℕ}
    (h : n = Dg.R.k + 0 * (Dg.R.t + 1)) :
    max 0 (∑ ρ, ∑ i, (Dg.R.wt0 hw h ρ i : ℝ)) ≤ 2 * ∑ t ∈ Dg.TT, Dg.a t := by
  have h0 : 0 ≤ ∑ t ∈ Dg.TT, Dg.a t := le_trans (scA_pos ε hA.big.pos).le hA.scA_le_sum
  exact max_le (by linarith) (hA.sum_places_le u _ fun ρ => (hA.place_le hp h ρ).2)

end Adm

end SharpDesign

end ZetaBalance

#print axioms ZetaBalance.Setting.Ranks.wt0_antitone
#print axioms ZetaBalance.SharpDesign.Adm.sum_natW_le
#print axioms ZetaBalance.SharpDesign.Adm.sum_wt0_le
#print axioms ZetaBalance.SharpDesign.Adm.lam_bounds
#print axioms ZetaBalance.SharpDesign.Adm.lam_add_log_two_le
#print axioms ZetaBalance.SharpDesign.Adm.logM_cube_le
#print axioms ZetaBalance.SharpDesign.Adm.card_E_le
