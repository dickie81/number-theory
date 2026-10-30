/-
# The decomposition at `x = q^L`, and its leaves for large `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. Throughout, `L`, `w₁` and `w₂` are a route's parameters (`SieveRoute.Route`) and the grid is one of
`SieveCert.Grid`; where the Lean takes them, the route has `RouteOK`, the grid `GridOK`, and the two fit (`Fits`): with
`u₁ = U1/DEN` and `u₂ = U2/DEN`, `w₁ < u₁`, `u₂ < w₂` and `Lu₂ > 1`. `parQ q` is the decomposition's parameters at
`x = q^L`: `z₀ = ⌈q^{a₀}⌉` with `a₀ = L·V/DEN`, `z_top = ⌊√N₂⌋ + 1`, `X' = ⌊q^{b₀}⌋` with `b₀ = L(DEN − U2)/DEN`,
`N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`. `LargeQ q` lists the facts about `q` that the proofs use, as powers of `q`. The
decomposition's rule (`SieveCert.Rule`) splits a box at `X'` when `limOK` passes it and takes it whole otherwise
(`SieveBuch.Par.Xs`); `IBFits` says that the bilinear rule's exponent `Lnum/Lden` is the route's `L`.

* `a0_b0`, `b0_gt`, `b0_lt`: `a₀ + b₀ < (1 − w₁)L` and `(1 − w₂)L < b₀ < L − 1`, Proposition 6's conditions, and
  `a0_lt_W`: `a₀ < (w₂ − w₁)L`, Proposition 6-ib's. They come from `Fits`.
* `largeQ_ev`, `good_of_large`: eventually `LargeQ q`, and then `(parQ q).Good`.
* `box_leaf_gen`, `box_leaf`: a surely evaluable box is estimated by the lower window, or by the reflected one (`TRat`)
  for the set of its primes whose product it puts there.
* `famI_whole_gt`: a whole box's part above `N₁` is empty when its upper sum is below `DEN`.
* `P6IB_box`, `P6IB_boxes`: for a box that the bilinear Type I test passes, `ibOK_sound`'s witnesses are
  `SieveP6ib.prop6ib`'s conditions, so Proposition 6-ib holds on its families (`P6IBat`); uniformly over finitely many
  boxes.
* `leaves_ev`: for a rule with `RuleIB`, given the route's Type II estimate (`hII`), for `η > 0` there are `δ > 0` and
  `q₀` such that for `q ≥ q₀` and `a` a unit mod `q`, `LargeQ q` holds and every leaf of `(parQ q).Leaves` is within
  `Err η δ q = ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)`.

The proof of `leaves_ev`: for the tuple lengths of the tree, `SieveLeaves.TL_spec` (one to six primes), `TU_spec` (two
to five), `TR_spec` (two to six), `P6_spec` (none to five) and `P6IB_boxes` (the grid's boxes of two to five cells)
give `δ` and `q₀`; `δ` is at most each of theirs and `q₀` is their sum. Each leaf is then one of those estimates
(`lf_j0` … `lf_e6`): its family has at most `40` atoms with thresholds in `[1, q^{L+1}]` (`len_*`, `thrOK_*`), and its
windows are the integer ranges `P₁ = ⌊x^{u₁}⌋`, `P₂ = ⌊x^{u₂}⌋`, `W₀ = X'` and `W₁ = ⌊x^{1−u₁}⌋` (`P1_ok`, `P2_ok`,
`W1_div`, `W0_div`). A split box's term above `X'` goes by the upper window and its term at or below `X'` by
Proposition 6; a whole box's term above `N₁` is empty, and its term at or below `N₁` goes by Proposition 6-ib.

The route's numbers, the certificate's grid parameters and the Type II estimate are hypotheses (`hII`); the case
of the library's theorem is `Linnik22000E.route22000D` and `SieveCert.grid22000E` (`Linnik22000E.fits22000E`),
with `Linnik22000E.typeII22000d` for `hII`.

The file imports `SieveLeaves.lean`.
-/
import SieveLeaves

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveRoute
open SieveCert (V DEN H U1 U2 cand decR inKK ne3 counted4 surelyEval cell inside lim limOK nbOK)

namespace SieveQ

open Classical

/-! ### The route and the grid -/

/-- **The route and the grid fit**: the grid's window `(u₁, u₂) = (U1/DEN, U2/DEN)` lies strictly inside the route's
window `(w₁, w₂)`, and `L·u₂ > 1`. -/
class Fits [Route] [SieveCert.Grid] : Prop where
  w₁_lt : w₁ * DEN < U1
  U2_lt : (U2 : ℝ) < w₂ * DEN
  DEN_lt : (DEN : ℝ) < L * U2

/-- **The bilinear Type I rule's exponent is the route's**: `Lnum/Lden = L`. -/
class IBFits [Route] [SieveCert.IBPar] : Prop where
  L_eq : (SieveCert.IBPar.Lnum : ℝ) / SieveCert.IBPar.Lden = L

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-! ### The exponents -/

/-- The sieve's floor exponent, `a₀ = L·V/DEN`. -/
noncomputable def a0 : ℝ := L * ((V : ℝ) / DEN)

/-- Proposition 6's exponent, `b₀ = L(DEN − U2)/DEN`. -/
noncomputable def b0 : ℝ := L * (((DEN - U2 : ℕ) : ℝ) / DEN)

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem DEN_pos : (0 : ℝ) < DEN := SieveCert.DEN_pos'

omit [Fits] in
theorem a0_pos : 0 < a0 := by
  have : (0 : ℝ) < V := by exact_mod_cast SieveCert.V_pos
  have := (L_pos : (0 : ℝ) < L)
  unfold a0
  have := DEN_pos
  positivity

omit [Route] [RouteOK] [Fits] in
theorem V_cast : (V : ℝ) = U2 - U1 := by
  unfold V
  rw [Nat.cast_sub SieveCert.U1_lt_U2.le]

omit [Route] [RouteOK] [Fits] in
theorem DU2_cast : ((DEN - U2 : ℕ) : ℝ) = DEN - U2 := Nat.cast_sub SieveCert.U2_le_DEN

omit [RouteOK] [SieveCert.GridOK] in
/-- `w₁ < u₁`, from `Fits`. -/
theorem w₁_lt_u₁ : w₁ < (U1 : ℝ) / DEN := by
  rw [lt_div_iff₀ DEN_pos]
  exact Fits.w₁_lt

omit [RouteOK] [SieveCert.GridOK] in
/-- `u₂ < w₂`, from `Fits`. -/
theorem u₂_lt_w₂ : (U2 : ℝ) / DEN < w₂ := by
  rw [div_lt_iff₀ DEN_pos]
  exact Fits.U2_lt

theorem a0_b0 : a0 + b0 < (1 - w₁) * L := by
  have hD := DEN_pos
  have hL := (L_pos : (0 : ℝ) < L)
  have h := w₁_lt_u₁
  unfold a0 b0
  rw [← mul_add, ← add_div, V_cast, DU2_cast, show (U2 : ℝ) - U1 + (DEN - U2) = DEN - U1 by ring, sub_div,
    div_self hD.ne']
  nlinarith

theorem b0_gt : (1 - w₂) * L < b0 := by
  have hD := DEN_pos
  have hL := (L_pos : (0 : ℝ) < L)
  have h := u₂_lt_w₂
  unfold b0
  rw [DU2_cast, sub_div, div_self hD.ne']
  nlinarith

theorem b0_pos : 0 < b0 := by
  have := b0_gt
  have := (L_pos : (0 : ℝ) < L)
  have := (w₂_lt_one : w₂ < 1)
  nlinarith

omit [RouteOK] in
theorem b0_lt : b0 < L - 1 := by
  have h1 : (DEN : ℝ) < L * U2 := Fits.DEN_lt
  have hD := DEN_pos
  unfold b0
  rw [DU2_cast, mul_div_assoc', div_lt_iff₀ hD]
  linarith

/-! ### The parameters at `x = q^L` -/

/-- The parameters of the decomposition at `x = q^L`. -/
noncomputable def parQ (q : ℕ) : Par where
  x := (q : ℝ) ^ L
  z₀ := ⌈(q : ℝ) ^ a0⌉₊
  ztop := Nat.sqrt (N2 q) + 1
  Xp := ⌊(q : ℝ) ^ b0⌋₊
  N₁ := N1 q
  N₂ := N2 q

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem xpow (q : ℕ) (s : ℝ) : ((q : ℝ) ^ L) ^ s = (q : ℝ) ^ (L * s) :=
  (Real.rpow_mul (Nat.cast_nonneg q) _ _).symm

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem ev_rpow {c : ℝ} (hc : 0 < c) (B : ℝ) : ∀ᶠ q : ℕ in atTop, B ≤ (q : ℝ) ^ c :=
  ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- For `q > 0`, `q^a = q^b · q^{a − b}`. -/
theorem rpow_split {q : ℝ} (hq : 0 < q) (a b : ℝ) : q ^ a = q ^ b * q ^ (a - b) := by
  rw [← Real.rpow_add hq]
  congr 1
  ring

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- For `q > 0`: if `q^{a−b} ≥ 3` and `q^b ≥ 1`, then `q^a ≥ q^b + 2`. -/
theorem rpow_gap {q : ℝ} (hq : 0 < q) {a b : ℝ} (h3 : 3 ≤ q ^ (a - b)) (h1 : 1 ≤ q ^ b) : q ^ b + 2 ≤ q ^ a := by
  rw [rpow_split hq a b]
  nlinarith

/-! ### `q` large -/

/-- The facts about `q` that the decomposition and its leaves use, as powers of `q`. -/
structure LargeQ (q : ℕ) : Prop where
  q3 : 3 ≤ q
  hhalf : 4 ≤ (q : ℝ) ^ (L / 2 : ℝ)
  hz : 3 ≤ (q : ℝ) ^ (L / 2 - a0)
  hX : 3 ≤ (q : ℝ) ^ (L - b0 * (3 / 2))
  hDEN : 3 ≤ (q : ℝ) ^ (L / (DEN : ℝ))
  hw₁ : 3 ≤ (q : ℝ) ^ (L * ((U1 : ℝ) / DEN) - w₁ * L)
  hw₂ : 2 ≤ (q : ℝ) ^ (w₂ * L - L * ((U2 : ℝ) / DEN))
  hb : 3 ≤ (q : ℝ) ^ (b0 - L / 2)

theorem largeQ_ev : ∀ᶠ q : ℕ in atTop, LargeQ q := by
  have hD := DEN_pos
  have hL := (L_pos : (0 : ℝ) < L)
  have e2 : (0 : ℝ) < L / 2 := by positivity
  have e3 : (0 : ℝ) < L / 2 - a0 := by
    have h : (2 : ℝ) * V < DEN := by exact_mod_cast SieveCert.two_V_lt
    have : (V : ℝ) / DEN < 1 / 2 := by rw [div_lt_iff₀ hD]; linarith
    unfold a0
    nlinarith
  have e4 : (0 : ℝ) < L - b0 * (3 / 2) := by
    have := b0_lt
    have := (L_le : L ≤ 5 / 2)
    linarith
  have e5 : (0 : ℝ) < L / (DEN : ℝ) := by positivity
  have e6 : (0 : ℝ) < L * ((U1 : ℝ) / DEN) - w₁ * L := by
    have := w₁_lt_u₁
    nlinarith
  have e7 : (0 : ℝ) < w₂ * L - L * ((U2 : ℝ) / DEN) := by
    have := u₂_lt_w₂
    nlinarith
  have e8 : (0 : ℝ) < b0 - L / 2 := by
    have h : (2 : ℝ) * U2 < DEN := by exact_mod_cast SieveCert.two_U2_lt
    have : (U2 : ℝ) / DEN < 1 / 2 := by rw [div_lt_iff₀ hD]; linarith
    unfold b0
    rw [DU2_cast, sub_div, div_self hD.ne']
    nlinarith
  filter_upwards [eventually_ge_atTop 3, ev_rpow e2 4, ev_rpow e3 3, ev_rpow e4 3, ev_rpow e5 3,
    ev_rpow e6 3, ev_rpow e7 2, ev_rpow e8 3] with q h1 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h3, h4, h5, h6, h7, h8, h9⟩

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem sqrt_x (q : ℕ) : Real.sqrt ((q : ℝ) ^ L) = (q : ℝ) ^ (L / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  ring

omit [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem N2_ge (q : ℕ) (hq : 1 ≤ q) : (q : ℝ) ^ L ≤ (N2 q : ℝ) := by
  have hy : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by exact_mod_cast hq) (by route_num)
  have := Nat.sub_one_lt_floor (2 * (q : ℝ) ^ L)
  unfold N2
  linarith

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem N2_le (q : ℕ) : (N2 q : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)

/-- **The decomposition's hypotheses hold for large `q`.** For a route with `RouteOK` and a grid with `GridOK` that fit
(`Fits`), `LargeQ q` gives `(parQ q).Good`. -/
theorem good_of_large {q : ℕ} (hL : LargeQ q) : (parQ q).Good := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hL.q3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hD := DEN_pos
  have hy1 : 1 < (q : ℝ) ^ L := Real.one_lt_rpow (by linarith) (by route_num)
  have hN₂y := N2_ge q (by have := hL.q3; omega)
  have hN₂le := N2_le q
  have hsy := sqrt_x q
  refine ⟨hy1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((q : ℝ) ^ L) ^ ((V : ℝ) / DEN) ≤ (⌈(q : ℝ) ^ a0⌉₊ : ℝ)
    rw [xpow]
    exact Nat.le_ceil _
  · show ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ≤ ((q : ℝ) ^ L) ^ (((V : ℝ) + SieveCert.n * H) / DEN)
    have hexp : L / 2 + L / DEN ≤ L * (((V : ℝ) + SieveCert.n * H) / DEN) := by
      have h2 : DEN + 2 ≤ 2 * (V + SieveCert.n * H) := by
        have h1 := SieveCert.DEN_lt_top
        have h0 : DEN % 2 = 0 := by decide
        omega
      have h : (DEN : ℝ) + 2 ≤ 2 * ((V : ℝ) + SieveCert.n * H) := by exact_mod_cast h2
      have hD0 : (DEN : ℝ) ≠ 0 := hD.ne'
      have hLD : L / 2 + L / DEN = L * ((DEN / 2 + 1) / DEN) := by
        field_simp
      rw [hLD]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hD.le) L_pos.le
    have h5 : (q : ℝ) ^ (L / 2 : ℝ) * (q : ℝ) ^ (L / (DEN : ℝ)) ≤
        ((q : ℝ) ^ L) ^ (((V : ℝ) + SieveCert.n * H) / DEN) := by
      rw [xpow, ← Real.rpow_add hq0]
      exact Real.rpow_le_rpow_of_exponent_le hq1 hexp
    have h1 : (Nat.sqrt (N2 q) : ℝ) ≤ Real.sqrt (N2 q) := Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt (N2 q) ≤ Real.sqrt (2 * (q : ℝ) ^ L) := Real.sqrt_le_sqrt hN₂le
    have h3 : Real.sqrt (2 * (q : ℝ) ^ L) =
        Real.sqrt 2 * (q : ℝ) ^ (L / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), hsy]
    have h4 : Real.sqrt 2 < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hh := hL.hhalf
    have hd := hL.hDEN
    have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ (L / 2 : ℝ) := by positivity
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hd hq2, mul_le_mul_of_nonneg_right h4.le hq2]
  · show ⌈(q : ℝ) ^ a0⌉₊ ≤ Nat.sqrt (N2 q) + 1
    have h1 : (⌈(q : ℝ) ^ a0⌉₊ : ℝ) < (q : ℝ) ^ a0 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 := rpow_gap hq0 hL.hz (Real.one_le_rpow hq1 a0_pos.le)
    have h3 : Real.sqrt (N2 q) ≤ Nat.sqrt (N2 q) + 1 := Real.real_sqrt_le_nat_sqrt_succ
    have h4 : (q : ℝ) ^ (L / 2 : ℝ) ≤ Real.sqrt (N2 q) := by
      rw [← hsy]
      exact Real.sqrt_le_sqrt hN₂y
    have : (⌈(q : ℝ) ^ a0⌉₊ : ℝ) < ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this.le
  · show Nat.sqrt (N2 q) + 1 ≤ N2 q + 1
    exact Nat.add_le_add_right (Nat.sqrt_le_self _) 1
  · show (⌊(q : ℝ) ^ b0⌋₊ : ℝ) * Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (N1 q : ℝ)
    have hw : (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ b0 := Nat.floor_le (by positivity)
    have hsq : Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ (b0 / 2) := by
      calc Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ Real.sqrt ((q : ℝ) ^ b0) := Real.sqrt_le_sqrt hw
        _ = (q : ℝ) ^ (b0 / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]
          congr 1
          ring
    have hprod : (⌊(q : ℝ) ^ b0⌋₊ : ℝ) * Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ (b0 * (3 / 2)) := by
      calc (⌊(q : ℝ) ^ b0⌋₊ : ℝ) * Real.sqrt (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ (q : ℝ) ^ b0 * (q : ℝ) ^ (b0 / 2) :=
            mul_le_mul hw hsq (Real.sqrt_nonneg _) (by positivity)
        _ = (q : ℝ) ^ (b0 * (3 / 2)) := by
          rw [← Real.rpow_add hq0]
          congr 1
          ring
    have hgap := rpow_gap hq0 hL.hX (Real.one_le_rpow hq1 (by nlinarith [b0_pos]))
    have hN₁ : (q : ℝ) ^ L - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    linarith
  · show (N2 q : ℝ) < ((q : ℝ) ^ L) ^ (((DEN : ℝ) + 1) / DEN)
    have h1 : ((q : ℝ) ^ L) ^ (((DEN : ℝ) + 1) / DEN) =
        (q : ℝ) ^ L * (q : ℝ) ^ (L / (DEN : ℝ)) := by
      rw [xpow, ← Real.rpow_add hq0]
      congr 1
      field_simp
    have h2 := hL.hDEN
    have h3 : 0 < (q : ℝ) ^ L := by positivity
    rw [h1]
    nlinarith
  · show ((q : ℝ) ^ L) ^ (((DEN : ℝ) - 1) / DEN) ≤ (N1 q : ℝ)
    have h1 : ((q : ℝ) ^ L) ^ (((DEN : ℝ) - 1) / DEN) * (q : ℝ) ^ (L / (DEN : ℝ)) = (q : ℝ) ^ L := by
      rw [xpow, ← Real.rpow_add hq0]
      congr 1
      field_simp
      ring
    have h2 := hL.hDEN
    have h3 : 1 ≤ ((q : ℝ) ^ L) ^ (((DEN : ℝ) - 1) / DEN) := Real.one_le_rpow hy1.le (by
      have : (1 : ℝ) ≤ DEN := by exact_mod_cast SieveCert.DEN_pos
      positivity)
    have h4 : (q : ℝ) ^ L - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    have h5 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ ((q : ℝ) ^ L) ^ (((DEN : ℝ) - 1) / DEN) by positivity)
    linarith

/-! ### The families' atoms: thresholds, nonzero coefficients, lengths -/

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem thrOK_append {q k : ℕ} {s₁ s₂ : List (Atom k)} (h₁ : ThrOK q s₁) (h₂ : ThrOK q s₂) :
    ThrOK q (s₁ ++ s₂) := by
  intro A hA
  rcases List.mem_append.1 hA with h | h
  · exact h₁ A h
  · exact h₂ A h

omit [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem thrOK_extS {q k' : ℕ} {spec : List (Atom (k' + 1))} {z : ℝ} (h : ThrOK q spec) (hz1 : 1 ≤ z)
    (hz2 : z ≤ (q : ℝ) ^ (L + 1 : ℝ)) (hq : 1 ≤ q) : ThrOK q (extS z spec) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := Real.one_le_rpow (by exact_mod_cast hq) (by route_num)
  intro A hA
  simp only [extS, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with ⟨A', hA', rfl⟩ | rfl | rfl
  · rw [Atom.lift_thr]
    exact h A' hA'
  · exact ⟨le_rfl, hq1⟩
  · exact ⟨hz1, hz2⟩

omit [Fits] in
theorem thrOK_cellA {q k : ℕ} (hq : 1 ≤ q) (t : Fin k) {c : ℕ} (hc : c < SieveCert.n) :
    ThrOK q (cellA t ((q : ℝ) ^ L) c) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hD := DEN_pos
  have hy1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 (by route_num)
  have hyL : (q : ℝ) ^ L ≤ (q : ℝ) ^ (L + 1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by route_num)
  have hle : ((SieveCert.e c : ℝ) + H) / DEN ≤ 1 := by
    have h1 := SieveCert.e_add_H_le hc
    have h2 : ((V : ℝ) + SieveCert.n * H) ≤ DEN := by exact_mod_cast SieveCert.top_le_DEN
    rw [div_le_one hD]
    linarith
  have he0 : (0 : ℝ) ≤ (SieveCert.e c : ℝ) / DEN := by positivity
  have hle' : (SieveCert.e c : ℝ) / DEN ≤ 1 := le_trans (div_le_div_of_nonneg_right (by
    have : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    linarith) hD.le) hle
  intro A hA
  simp only [cellA, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl
  · exact ⟨Real.one_le_rpow hy1 he0,
      le_trans (le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_le hy1 hle') (Real.rpow_one _)) hyL⟩
  · exact ⟨Real.one_le_rpow hy1 (by positivity),
      le_trans (le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_le hy1 hle) (Real.rpow_one _)) hyL⟩

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem thrOK_single {q k : ℕ} {A : Atom k} (h1 : 1 ≤ A.thr) (h2 : A.thr ≤ (q : ℝ) ^ (L + 1 : ℝ)) :
    ThrOK q [A] := by
  intro A' hA'
  rw [List.mem_singleton] at hA'
  subst hA'
  exact ⟨h1, h2⟩

/-- For a route with `RouteOK` and a grid with `GridOK` that fit (`Fits`), and `LargeQ q`: the thresholds `z₀`, `z_top`
and `X'` lie in `[1, q^{L+1}]`. -/
theorem thr_bounds {q : ℕ} (hL : LargeQ q) :
    (1 ≤ ((parQ q).z₀ : ℝ) ∧ ((parQ q).z₀ : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ)) ∧
    (1 ≤ ((parQ q).ztop : ℝ) ∧ ((parQ q).ztop : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ)) ∧
    (1 ≤ ((parQ q).Xp : ℝ) ∧ ((parQ q).Xp : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ)) := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hL.q3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hsplit : (q : ℝ) ^ (L + 1 : ℝ) = (q : ℝ) ^ L * q := by
    rw [Real.rpow_add hq0, Real.rpow_one]
  have hy1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 (by route_num)
  have ha1 : (1 : ℝ) ≤ (q : ℝ) ^ a0 := Real.one_le_rpow hq1 a0_pos.le
  have hb1 : (1 : ℝ) ≤ (q : ℝ) ^ b0 := Real.one_le_rpow hq1 (by nlinarith [b0_pos])
  have haL : (q : ℝ) ^ a0 ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 (by
    have := hL.hz
    have e3 : (0 : ℝ) < L / 2 - a0 := by
      by_contra hc
      have : (q : ℝ) ^ (L / 2 - a0) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
      linarith
    linarith [(L_pos : (0 : ℝ) < L)])
  have hbL : (q : ℝ) ^ b0 ≤ (q : ℝ) ^ L :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith [b0_lt])
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ha1.trans (Nat.le_ceil _)
  · have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (q : ℝ) ^ a0 by positivity)
    show (⌈(q : ℝ) ^ a0⌉₊ : ℝ) ≤ _
    rw [hsplit]
    nlinarith
  · show (1 : ℝ) ≤ ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ)
    push_cast
    have : (0 : ℝ) ≤ Nat.sqrt (N2 q) := Nat.cast_nonneg _
    linarith
  · show ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ≤ _
    have h1 : Nat.sqrt (N2 q) + 1 ≤ N2 q + 1 := Nat.add_le_add_right (Nat.sqrt_le_self _) 1
    have h2 : ((Nat.sqrt (N2 q) + 1 : ℕ) : ℝ) ≤ (N2 q : ℝ) + 1 := by exact_mod_cast h1
    have h3 := N2_le q
    rw [hsplit]
    nlinarith
  · show (1 : ℝ) ≤ (⌊(q : ℝ) ^ b0⌋₊ : ℝ)
    exact_mod_cast Nat.le_floor (by exact_mod_cast hb1)
  · show (⌊(q : ℝ) ^ b0⌋₊ : ℝ) ≤ _
    have := Nat.floor_le (show (0 : ℝ) ≤ (q : ℝ) ^ b0 by positivity)
    rw [hsplit]
    nlinarith

/-- For `LargeQ q`, a split's threshold (`X'` or `N₁`) lies in `[1, q^{L+1}]`. -/
theorem thr_Xs {q : ℕ} (hL : LargeQ q) (s : Bool) :
    1 ≤ (parQ q).Xs s ∧ (parQ q).Xs s ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
  cases s with
  | true => simpa [Par.Xs] using (thr_bounds hL).2.2
  | false =>
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hL.q3
    have hq1 : (1 : ℝ) ≤ q := by linarith
    have hy3 : (3 : ℝ) ≤ (q : ℝ) ^ L := le_trans hq3 (le_of_eq_of_le (Real.rpow_one _).symm
      (Real.rpow_le_rpow_of_exponent_le hq1 (by route_num)))
    have hN : (q : ℝ) ^ L - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    have hN' : (N1 q : ℝ) ≤ (q : ℝ) ^ L := Nat.floor_le (by positivity)
    have hLL : (q : ℝ) ^ L ≤ (q : ℝ) ^ (L + 1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    simp only [Par.Xs, Bool.false_eq_true, ite_false]
    exact ⟨by show (1 : ℝ) ≤ (N1 q : ℝ); linarith, by show (N1 q : ℝ) ≤ _; linarith⟩

/-! ### The windows' thresholds for large `q` -/

/-- `x = q^L`. -/
noncomputable abbrev xq (q : ℕ) : ℝ := (q : ℝ) ^ L

/-- The lower window's lower end `P₁ = ⌊x^{u₁}⌋`. -/
noncomputable abbrev P1 (q : ℕ) : ℕ := ⌊xq q ^ ((U1 : ℝ) / DEN)⌋₊
/-- The lower window's upper end `P₂ = ⌊x^{u₂}⌋`. -/
noncomputable abbrev P2 (q : ℕ) : ℕ := ⌊xq q ^ ((U2 : ℝ) / DEN)⌋₊
/-- The upper window's upper end `W₁ = ⌊x^{1−u₁}⌋`. -/
noncomputable abbrev W1 (q : ℕ) : ℕ := ⌊xq q ^ (((DEN - U1 : ℕ) : ℝ) / DEN)⌋₊

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem Xp_eq (q : ℕ) : (parQ q).Xp = ⌊xq q ^ (((DEN - U2 : ℕ) : ℝ) / DEN)⌋₊ := by
  show ⌊(q : ℝ) ^ b0⌋₊ = _
  rw [xq, xpow]
  rfl

omit [SieveCert.GridOK] [Fits] in
theorem P1_ok {q : ℕ} (hL : LargeQ q) : (q : ℝ) ^ (w₁ * L) ≤ P1 q := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have h := rpow_gap hq0 hL.hw₁ (Real.one_le_rpow hq1 (by route_num))
  have h2 := Nat.sub_one_lt_floor (xq q ^ ((U1 : ℝ) / DEN))
  rw [xq, xpow] at h2
  unfold P1
  rw [xq, xpow]
  linarith

omit [SieveCert.GridOK] in
theorem P2_ok {q : ℕ} (hL : LargeQ q) : (P2 q : ℝ) ≤ (q : ℝ) ^ (w₂ * L) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hD := DEN_pos
  have hu : (U2 : ℝ) / DEN ≤ w₂ := u₂_lt_w₂.le
  have hL0 := (L_pos : (0 : ℝ) < L)
  unfold P2
  rw [xq, xpow]
  exact (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith))

omit [SieveCert.GridOK] [Fits] in
theorem W1_le {q : ℕ} (hL : LargeQ q) : W1 q ≤ N1 q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hy1 : (1 : ℝ) ≤ xq q := Real.one_le_rpow hq1 (by route_num)
  have hD := DEN_pos
  have hle : ((DEN - U1 : ℕ) : ℝ) / DEN ≤ 1 := by
    rw [div_le_one hD]
    exact_mod_cast Nat.sub_le DEN U1
  unfold W1 N1
  exact Nat.floor_le_floor (le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_le hy1 hle) (Real.rpow_one _))

omit [SieveCert.GridOK] [Fits] in
theorem W1_pos {q : ℕ} (hL : LargeQ q) : 1 ≤ W1 q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hy1 : (1 : ℝ) ≤ xq q := Real.one_le_rpow hq1 (by route_num)
  exact Nat.le_floor (by exact_mod_cast Real.one_le_rpow hy1 (by positivity))

omit [Fits] in
theorem W1_div {q : ℕ} (hL : LargeQ q) : (q : ℝ) ^ (w₁ * L) ≤ ((N1 q / W1 q : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  have hD := DEN_pos
  have hgap := rpow_gap hq0 hL.hw₁ (Real.one_le_rpow hq1 (by route_num))
  set w := xq q ^ (((DEN - U1 : ℕ) : ℝ) / DEN) with hw
  have hw1 : (1 : ℝ) ≤ w := Real.one_le_rpow (Real.one_le_rpow hq1 (by route_num)) (by positivity)
  have hW : (W1 q : ℝ) ≤ w := Nat.floor_le (by positivity)
  have hW0 : (0 : ℝ) < W1 q := by exact_mod_cast W1_pos hL
  have hyw : xq q / w = (q : ℝ) ^ (L * ((U1 : ℝ) / DEN)) := by
    rw [hw, xq, xpow, ← Real.rpow_sub hq0]
    congr 1
    rw [Nat.cast_sub SieveCert.U1_le_DEN]
    field_simp
    ring
  -- `N₁/W₁ ≥ (x − 1)/w ≥ x/w − 1`
  have hN₁ : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
  have hdiv : (N1 q : ℝ) / W1 q < ((N1 q / W1 q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hW0]
    have h := Nat.lt_div_mul_add (a := N1 q) (show 0 < W1 q from W1_pos hL)
    have : ((N1 q : ℕ) : ℝ) < ((N1 q / W1 q * W1 q + W1 q : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have h1 : xq q / w - 1 ≤ (N1 q : ℝ) / W1 q := by
    have : (xq q - 1) / w ≤ (N1 q : ℝ) / W1 q := by
      calc (xq q - 1) / w ≤ (N1 q : ℝ) / w := div_le_div_of_nonneg_right hN₁.le (by linarith)
        _ ≤ (N1 q : ℝ) / W1 q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hW0 hW
    have h2 : xq q / w - 1 ≤ (xq q - 1) / w := by
      rw [sub_div]
      have : 1 / w ≤ 1 := by rw [div_le_one (by linarith)]; exact hw1
      linarith
    linarith
  rw [hyw] at h1
  linarith

omit [RouteOK] [Fits] in
theorem W0_div {q : ℕ} (hL : LargeQ q) :
    ((N2 q / ((parQ q).Xp + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (w₂ * L) := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have h1 : ((N2 q / ((parQ q).Xp + 1) : ℕ) : ℝ) ≤ (N2 q : ℝ) / (((parQ q).Xp + 1 : ℕ) : ℝ) := Nat.cast_div_le
  have h2 : (q : ℝ) ^ b0 < (((parQ q).Xp + 1 : ℕ) : ℝ) := by
    show (q : ℝ) ^ b0 < ((⌊(q : ℝ) ^ b0⌋₊ + 1 : ℕ) : ℝ)
    push_cast
    exact Nat.lt_floor_add_one _
  have hb0 : (0 : ℝ) < (q : ℝ) ^ b0 := by positivity
  have h3 : (N2 q : ℝ) / (((parQ q).Xp + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ L / (q : ℝ) ^ b0 :=
    div_le_div₀ (by positivity) (N2_le q) hb0 h2.le
  have h4 : 2 * (q : ℝ) ^ L / (q : ℝ) ^ b0 =
      2 * (q : ℝ) ^ (L * ((U2 : ℝ) / DEN)) := by
    rw [mul_div_assoc, ← Real.rpow_sub hq0]
    congr 2
    unfold b0
    rw [Nat.cast_sub SieveCert.U2_le_DEN]
    have := DEN_pos
    field_simp
    ring
  have h5 := hL.hw₂
  have h6 : 2 * (q : ℝ) ^ (L * ((U2 : ℝ) / DEN)) ≤ (q : ℝ) ^ (w₂ * L) := by
    rw [rpow_split hq0 (w₂ * L) (L * ((U2 : ℝ) / DEN))]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (L * ((U2 : ℝ) / DEN)) := by positivity
    nlinarith
  linarith

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem ztop_le_Xp {q : ℕ} (hL : LargeQ q) : (parQ q).ztop ≤ (parQ q).Xp + 1 := by
  have hq0 : (0 : ℝ) < q := by have := hL.q3; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega)
  show Nat.sqrt (N2 q) + 1 ≤ ⌊(q : ℝ) ^ b0⌋₊ + 1
  refine Nat.add_le_add_right (Nat.le_floor ?_) 1
  have h1 : (Nat.sqrt (N2 q) : ℝ) ≤ Real.sqrt (N2 q) := Real.nat_sqrt_le_real_sqrt
  have h2 : Real.sqrt (N2 q) ≤ Real.sqrt (2 * (q : ℝ) ^ L) := Real.sqrt_le_sqrt (N2_le q)
  have h3 : Real.sqrt (2 * (q : ℝ) ^ L) = Real.sqrt 2 * (q : ℝ) ^ (L / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), sqrt_x]
  have h4 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h5 : (q : ℝ) ^ b0 = (q : ℝ) ^ (L / 2 : ℝ) * (q : ℝ) ^ (b0 - L / 2) :=
    rpow_split hq0 _ _
  have h6 := hL.hb
  have h7 : (0 : ℝ) ≤ (q : ℝ) ^ (L / 2 : ℝ) := by positivity
  nlinarith

/-! ### Each family of the tree: thresholds, coefficients, length -/

section Families

variable {q : ℕ} (hL : LargeQ q)
include hL

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem q1 : 1 ≤ q := by have := hL.q3; omega

theorem thrOK_S1 : ThrOK q (parQ q).S1 := by
  obtain ⟨⟨hz1, hz2⟩, ⟨ht1, ht2⟩, -⟩ := thr_bounds hL
  intro A hA
  simp only [Par.S1, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl
  · exact ⟨hz1, hz2⟩
  · exact ⟨ht1, ht2⟩

theorem thrOK_S1c {i : ℕ} (hi : i < SieveCert.n) : ThrOK q ((parQ q).S1c i) :=
  thrOK_append (thrOK_S1 hL) (thrOK_cellA (q1 hL) 0 hi)

theorem thrOK_S2 {i : ℕ} (hi : i < SieveCert.n) : ThrOK q ((parQ q).S2 i) :=
  thrOK_extS (thrOK_S1c hL hi) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S2c {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S2c i j) :=
  thrOK_append (thrOK_S2 hL hi) (thrOK_cellA (q1 hL) 1 hj)

theorem thrOK_S2le {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S2le i j) :=
  thrOK_append (thrOK_S2c hL hi hj) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S2gt {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S2gt i j) :=
  thrOK_append (thrOK_S2c hL hi hj) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S3 {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) : ThrOK q ((parQ q).S3 i j) :=
  thrOK_extS (thrOK_S2le hL hi hj) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S3c {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S3c i j k) :=
  thrOK_append (thrOK_S3 hL hi hj) (thrOK_cellA (q1 hL) 2 hk)

theorem thrOK_S3le {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S3le i j k) :=
  thrOK_append (thrOK_S3c hL hi hj hk) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S3gt {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S3gt i j k) :=
  thrOK_append (thrOK_S3c hL hi hj hk) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S4 {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n) :
    ThrOK q ((parQ q).S4 i j k) :=
  thrOK_extS (thrOK_S3le hL hi hj hk) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S4c {i j k l : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n)
    (hl : l < SieveCert.n) : ThrOK q ((parQ q).S4c i j k l) :=
  thrOK_append (thrOK_S4 hL hi hj hk) (thrOK_cellA (q1 hL) 3 hl)

end Families

omit [SieveCert.GridOK] [Fits] in
theorem thrOK_cellAC {q k : ℕ} [SieveCert.GridOKC] (hq : 1 ≤ q) (t : Fin k) {c : ℕ} (hc : c < SieveCert.nC) :
    ThrOK q (cellAC t ((q : ℝ) ^ L) c) := by
  have := @thrOK_cellA _ _ (SieveCert.Gc) SieveCert.GridOKC.ok q k hq t c
  exact this hc

section Families2

variable {q : ℕ} (hL : LargeQ q)
include hL

theorem thrOK_S4cle {i j k l : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n)
    (hl : l < SieveCert.n) : ThrOK q ((parQ q).S4cle i j k l) :=
  thrOK_append (thrOK_S4c hL hi hj hk hl) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S4cgt {i j k l : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n)
    (hl : l < SieveCert.n) : ThrOK q ((parQ q).S4cgt i j k l) :=
  thrOK_append (thrOK_S4c hL hi hj hk hl) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S5 {i j k l : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n)
    (hl : l < SieveCert.n) : ThrOK q ((parQ q).S5 i j k l) :=
  thrOK_extS (thrOK_S4cle hL hi hj hk hl) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S5c [SieveCert.GridOKC] {i j k l b : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < SieveCert.nC) : ThrOK q ((parQ q).S5c i j k l b) :=
  thrOK_append (thrOK_S5 hL hi hj hk hl) (thrOK_cellAC (q1 hL) 4 hb)

theorem thrOK_S5le [SieveCert.GridOKC] {i j k l b : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < SieveCert.nC) : ThrOK q ((parQ q).S5le i j k l b) :=
  thrOK_append (thrOK_S5c hL hi hj hk hl hb) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S5gt [SieveCert.GridOKC] {i j k l b : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < SieveCert.nC) : ThrOK q ((parQ q).S5gt i j k l b) :=
  thrOK_append (thrOK_S5c hL hi hj hk hl hb) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S6 [SieveCert.GridOKC] {i j k l b : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < SieveCert.nC) : ThrOK q ((parQ q).S6 i j k l b) :=
  thrOK_extS (thrOK_S5le hL hi hj hk hl hb) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S6c [SieveCert.GridOKC] {i j k l b c : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < SieveCert.nC) (hc : c < SieveCert.nC) :
    ThrOK q ((parQ q).S6c i j k l b c) :=
  thrOK_append (thrOK_S6 hL hi hj hk hl hb) (thrOK_cellAC (q1 hL) 5 hc)

end Families2

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem nz_lift {k : ℕ} (A : Atom k) (h : NZ A) : NZ A.lift := by
  cases A with
  | ge t b => trivial
  | lt t b => trivial
  | ltVar s t => exact fun h' => (show s ≠ t from h) (Fin.castSucc_injective _ h')
  | prodLe T b => exact (Finset.map_nonempty).2 (show T.Nonempty from h)
  | prodGt T b => exact (Finset.map_nonempty).2 (show T.Nonempty from h)

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem nz_append {k : ℕ} {s₁ s₂ : List (Atom k)} (h₁ : ∀ A ∈ s₁, NZ A) (h₂ : ∀ A ∈ s₂, NZ A) :
    ∀ A ∈ s₁ ++ s₂, NZ A := by
  intro A hA
  rcases List.mem_append.1 hA with h | h
  · exact h₁ A h
  · exact h₂ A h

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem nz_extS {k' : ℕ} {spec : List (Atom (k' + 1))} {z : ℝ} (h : ∀ A ∈ spec, NZ A) :
    ∀ A ∈ extS z spec, NZ A := by
  intro A hA
  simp only [extS, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with ⟨A', hA', rfl⟩ | rfl | rfl
  · exact nz_lift A' (h A' hA')
  · exact (Fin.castSucc_lt_last _).ne
  · trivial

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_cellA {k : ℕ} (t : Fin k) (x : ℝ) (c : ℕ) : ∀ A ∈ cellA t x c, NZ A := by
  intro A hA
  simp only [cellA, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl <;> trivial

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem nz_prodLe {k' : ℕ} (b : ℝ) : ∀ A ∈ [Atom.prodLe (Finset.univ : Finset (Fin (k' + 1))) b], NZ A := by
  intro A hA
  rw [List.mem_singleton] at hA
  subst hA
  exact Finset.univ_nonempty

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_S1c (q i : ℕ) : ∀ A ∈ (parQ q).S1c i, NZ A :=
  nz_append (by intro A hA; simp only [Par.S1, List.mem_cons, List.mem_nil_iff, or_false] at hA
                rcases hA with rfl | rfl <;> trivial) (nz_cellA _ _ _)

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_S2le (q i j : ℕ) : ∀ A ∈ (parQ q).S2le i j, NZ A :=
  nz_append (nz_append (nz_extS (nz_S1c q i)) (nz_cellA _ _ _)) (nz_prodLe _)

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_S3le (q i j k : ℕ) : ∀ A ∈ (parQ q).S3le i j k, NZ A :=
  nz_append (nz_append (nz_extS (nz_S2le q i j)) (nz_cellA _ _ _)) (nz_prodLe _)

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_S4cle (q i j k l : ℕ) : ∀ A ∈ (parQ q).S4cle i j k l, NZ A :=
  nz_append (nz_append (nz_extS (nz_S3le q i j k)) (nz_cellA _ _ _)) (nz_prodLe _)

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_S5le (q i j k l b : ℕ) : ∀ A ∈ (parQ q).S5le i j k l b, NZ A := by
  refine nz_append (nz_append (nz_extS (nz_S4cle q i j k l)) ?_) (nz_prodLe _)
  exact @nz_cellA (SieveCert.Gc) 5 4 ((q : ℝ) ^ L) b

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S1c (q i : ℕ) : ((parQ q).S1c i).length ≤ 40 := by
  simp [Par.S1c, Par.S1, cellA]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S2c (q i j : ℕ) : ((parQ q).S2c i j).length ≤ 40 := by
  simp [Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S2le (q i j : ℕ) : ((parQ q).S2le i j).length ≤ 40 := by
  simp [Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S2gt (q i j : ℕ) : ((parQ q).S2gt i j).length ≤ 40 := by
  simp [Par.S2gt, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S3c (q i j k : ℕ) : ((parQ q).S3c i j k).length ≤ 40 := by
  simp [Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S3le (q i j k : ℕ) : ((parQ q).S3le i j k).length ≤ 40 := by
  simp [Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S3gt (q i j k : ℕ) : ((parQ q).S3gt i j k).length ≤ 40 := by
  simp [Par.S3gt, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S4c (q i j k l : ℕ) : ((parQ q).S4c i j k l).length ≤ 40 := by
  simp [Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S4cle (q i j k l : ℕ) : ((parQ q).S4cle i j k l).length ≤ 40 := by
  simp [Par.S4cle, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S4cgt (q i j k l : ℕ) : ((parQ q).S4cgt i j k l).length ≤ 40 := by
  simp [Par.S4cgt, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S5c (q i j k l b : ℕ) : ((parQ q).S5c i j k l b).length ≤ 40 := by
  simp [Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c,
    Par.S1, cellAC, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S5le (q i j k l b : ℕ) : ((parQ q).S5le i j k l b).length ≤ 40 := by
  simp [Par.S5le, Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2,
    Par.S1c, Par.S1, cellAC, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S5gt (q i j k l b : ℕ) : ((parQ q).S5gt i j k l b).length ≤ 40 := by
  simp [Par.S5gt, Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2,
    Par.S1c, Par.S1, cellAC, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S6c (q i j k l b c : ℕ) : ((parQ q).S6c i j k l b c).length ≤ 40 := by
  simp [Par.S6c, Par.S6, Par.S5le, Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3, Par.S2le,
    Par.S2c, Par.S2, Par.S1c, Par.S1, cellAC, cellA, extS]

/-! ### The estimates at one `q` -/

/-- The lower window's estimate at `q`, with error `E`. -/
def TLat (q : ℕ) (a : ZMod q) (k' : ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom (k' + 1))) (S : Finset (Fin (k' + 1))) (P₁ P₂ : ℕ), spec.length ≤ 40 → ThrOK q spec →
    (q : ℝ) ^ (w₁ * L) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
    (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a0 ≤ rt i) ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂) →
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E

/-- The upper window's estimate at `q`, with error `E`. -/
def TUat (q : ℕ) (a : ZMod q) (k' : ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom (k' + 1))) (W₀ W₁ : ℕ), spec.length ≤ 40 → ThrOK q spec →
    (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a0 ≤ rt i) ∧ W₀ < ∏ i, rt i ∧ ∏ i, rt i ≤ W₁) →
    W₁ ≤ N1 q → (q : ℝ) ^ (w₁ * L) ≤ ((N1 q / W₁ : ℕ) : ℝ) →
    ((N2 q / (W₀ + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E

/-- The reflected window's estimate at `q`, for a set `U` of the primes, with error `E`. -/
def TRat (q : ℕ) (a : ZMod q) (k' : ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom (k' + 1))) (U : Finset (Fin (k' + 1))) (W₀ W₁ : ℕ), spec.length ≤ 40 → ThrOK q spec →
    (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a0 ≤ rt i) ∧ W₀ < ∏ i ∈ U, rt i ∧ ∏ i ∈ U, rt i ≤ W₁) →
    W₁ ≤ N1 q → (q : ℝ) ^ (w₁ * L) ≤ ((N1 q / W₁ : ℕ) : ℝ) →
    ((N2 q / (W₀ + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E

/-- Proposition 6's estimate at `q`, with error `E`. -/
def P6at (q : ℕ) (a : ZMod q) (j : ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom j)), spec.length ≤ 40 → ThrOK q spec → (∀ A ∈ spec, NZ A) →
    (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      (∀ i, ⌈(q : ℝ) ^ a0⌉₊ ≤ rt i) ∧ ∏ i, rt i ≤ ⌊(q : ℝ) ^ b0⌋₊) →
    |famJ (gA q a) (N1 q) (N2 q) ⌈(q : ℝ) ^ a0⌉₊ (famSet j (N2 q) spec) -
        famJ (gB q) (N1 q) (N2 q) ⌈(q : ℝ) ^ a0⌉₊ (famSet j (N2 q) spec)| ≤ E

/-- Proposition 6 with the bilinear estimate at `q`, for families in the box `f` (its `t`-th prime in
`[x^{(f t).1/DEN}, x^{(f t).2/DEN})`), with error `E`. -/
def P6IBat (q : ℕ) (a : ZMod q) {j : ℕ} (f : Fin j → ℕ × ℕ) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom j)), spec.length ≤ 40 → ThrOK q spec →
    (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, ⌈(q : ℝ) ^ a0⌉₊ ≤ rt i) ∧
        ∀ t, xq q ^ (((f t).1 : ℝ) / DEN) ≤ rt t ∧ (rt t : ℝ) < xq q ^ (((f t).2 : ℝ) / DEN)) →
    |famJ (gA q a) (N1 q) (N2 q) ⌈(q : ℝ) ^ a0⌉₊ (famSet j (N2 q) spec) -
        famJ (gB q) (N1 q) (N2 q) ⌈(q : ℝ) ^ a0⌉₊ (famSet j (N2 q) spec)| ≤ E

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem TLat.mono {q : ℕ} {a : ZMod q} {k' : ℕ} {E E' : ℝ} (h : TLat q a k' E) (hE : E ≤ E') : TLat q a k' E' :=
  fun spec S P₁ P₂ h1 h2 h3 h4 h5 => (h spec S P₁ P₂ h1 h2 h3 h4 h5).trans hE

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem TUat.mono {q : ℕ} {a : ZMod q} {k' : ℕ} {E E' : ℝ} (h : TUat q a k' E) (hE : E ≤ E') : TUat q a k' E' :=
  fun spec W₀ W₁ h1 h2 h3 h4 h5 h6 => (h spec W₀ W₁ h1 h2 h3 h4 h5 h6).trans hE

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem TRat.mono {q : ℕ} {a : ZMod q} {k' : ℕ} {E E' : ℝ} (h : TRat q a k' E) (hE : E ≤ E') : TRat q a k' E' :=
  fun spec U W₀ W₁ h1 h2 h3 h4 h5 h6 => (h spec U W₀ W₁ h1 h2 h3 h4 h5 h6).trans hE

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem P6at.mono {q : ℕ} {a : ZMod q} {j : ℕ} {E E' : ℝ} (h : P6at q a j E) (hE : E ≤ E') : P6at q a j E' :=
  fun spec h1 h2 h3 h4 => (h spec h1 h2 h3 h4).trans hE

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem P6IBat.mono {q : ℕ} {a : ZMod q} {j : ℕ} {f : Fin j → ℕ × ℕ} {E E' : ℝ} (h : P6IBat q a f E)
    (hE : E ≤ E') : P6IBat q a f E' :=
  fun spec h1 h2 h3 => (h spec h1 h2 h3).trans hE

/-- **A box surely evaluable, with boxes of any widths.** Let the route have `RouteOK` and the grid `GridOK`, let the
two fit (`Fits`), and let `LargeQ q` and the windows' estimates at `E` (`TLat`, `TRat`). Let a family of
`(k' + 1)`-tuples of primes be cut out by at most `40` atoms with thresholds as in `ThrOK`, each tuple strictly
decreasing, with entries at least `z₀` and its `t`-th prime in `[x^{(f t).1/DEN}, x^{(f t).2/DEN})`. If the box `f` is
surely evaluable, the family's `|A − B/φ(q)|` is at most `E`: a set of its primes has its product in the lower window,
or in the reflected one. -/
theorem box_leaf_gen {q : ℕ} (hL : LargeQ q) {a : ZMod q} {k' : ℕ} {E : ℝ} (hTL : TLat q a k' E)
    (hTR : TRat q a k' E) {spec : List (Atom (k' + 1))} (hlen : spec.length ≤ 40) (hthr : ThrOK q spec)
    (f : Fin (k' + 1) → ℕ × ℕ)
    (hsem : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (parQ q).z₀ ≤ rt i) ∧
        ∀ t, xq q ^ (((f t).1 : ℝ) / DEN) ≤ rt t ∧ (rt t : ℝ) < xq q ^ (((f t).2 : ℝ) / DEN))
    (hsE : surelyEval (List.ofFn f) = true) :
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have ha0 : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (parQ q).z₀ ≤ rt i) → ∀ i, (q : ℝ) ^ a0 ≤ rt i :=
    fun rt h i => (Nat.le_ceil _).trans (by exact_mod_cast h i)
  obtain ⟨T, hT⟩ := exists_inside f hsE
  simp only [inside, Bool.or_eq_true, Bool.and_eq_true] at hT
  rcases hT with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> replace hlo := of_decide_eq_true hlo <;>
    replace hhi := of_decide_eq_true hhi
  · refine hTL spec T (P1 q) (P2 q) hlen hthr (P1_ok hL) (P2_ok hL) fun rt hp hs => ?_
    obtain ⟨hsa, hz₀, hc⟩ := hsem rt hp hs
    exact ⟨hsa, ha0 rt hz₀, window_lo_gen hq1 (fun t => (hc t).1) hlo,
      window_hi_gen hq1 (fun t => (hc t).2) hhi⟩
  · refine hTR spec T (parQ q).Xp (W1 q) hlen hthr (fun rt hp hs => ?_) (W1_le hL) (W1_div hL) (W0_div hL)
    obtain ⟨hsa, hz₀, hc⟩ := hsem rt hp hs
    refine ⟨hsa, ha0 rt hz₀, ?_, window_hi_gen hq1 (fun t => (hc t).2) hhi⟩
    rw [Xp_eq]
    exact window_lo_gen hq1 (fun t => (hc t).1) hlo

/-- **A box of cells surely evaluable**: `box_leaf_gen` for the cells `c`. -/
theorem box_leaf {q : ℕ} (hL : LargeQ q) {a : ZMod q} {k' : ℕ} {E : ℝ} (hTL : TLat q a k' E)
    (hTR : TRat q a k' E) {spec : List (Atom (k' + 1))} (hlen : spec.length ≤ 40) (hthr : ThrOK q spec)
    (c : Fin (k' + 1) → ℕ)
    (hsem : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (parQ q).z₀ ≤ rt i) ∧ (∀ t, InC (xq q) (c t) (rt t)))
    (hsE : surelyEval (List.ofFn fun t => cell (c t)) = true) :
    |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
        famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤ E :=
  box_leaf_gen hL hTL hTR hlen hthr (fun t => cell (c t)) (fun rt hp hs => by
    obtain ⟨hsa, hz₀, hc⟩ := hsem rt hp hs
    exact ⟨hsa, hz₀, fun t => ⟨by simpa [cell] using (hc t).1, by simpa [cell] using (hc t).2⟩⟩) hsE

/-! ### The leaves -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem mem_famSet_sum {k : ℕ} {spec : List (Atom k)} {rt : Fin k → ℕ} (hp : ∀ i, (rt i).Prime)
    (hs : ∀ A ∈ spec, A.sem rt) : rt ∈ famSet k (∑ i, rt i) spec :=
  mem_famSet.2 ⟨fun i => ⟨Finset.single_le_sum (fun j _ => Nat.zero_le (rt j)) (Finset.mem_univ i), hp i⟩, hs⟩

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem J0_eq (P : Par) (g : ℕ → ℝ) : P.J0 g = famJ g P.N₁ P.N₂ P.z₀ (famSet 0 P.N₂ []) := by
  have h : famSet 0 P.N₂ [] = {fun i => Fin.elim0 i} := by
    ext x
    simp only [mem_famSet, IsEmpty.forall_iff, true_and, List.not_mem_nil, implies_true, Finset.mem_singleton]
    exact ⟨fun _ => funext fun i => Fin.elim0 i, fun _ => trivial⟩
  rw [h, famJ, Finset.sum_singleton]
  unfold Par.J0
  simp

/-- **A whole cell's part above `N₁` is empty**: for `LargeQ q`, a family whose tuples have product above `N₁` and
their `t`-th prime below `x^{u_t/DEN}`, with `Σ u_t < DEN`, has none. -/
theorem famI_whole_gt {q : ℕ} (hL : LargeQ q) (g : ℕ → ℝ) {k' : ℕ} {spec : List (Atom (k' + 1))}
    (u : Fin (k' + 1) → ℕ) (hu : ∑ t, u t < DEN)
    (hsem : ∀ rt ∈ famSet (k' + 1) (N2 q) spec,
      (N1 q : ℝ) < ∏ t, (rt t : ℝ) ∧ ∀ t, (rt t : ℝ) < xq q ^ ((u t : ℝ) / DEN)) :
    famI g (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) = 0 := by
  have hq1 : (1 : ℝ) ≤ xq q := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ q by have := hL.q3; omega))
    (by route_num)
  refine famI_eq_zero _ _ _ _ fun rt hrt => False.elim ?_
  obtain ⟨hN, hc⟩ := hsem rt hrt
  have h1 := box_hi_gen (by linarith) hc Finset.univ
  have h2 : xq q ^ (((∑ t, u t : ℕ) : ℝ) / DEN) ≤ xq q ^ (((DEN : ℝ) - 1) / DEN) :=
    Par.rpow_le_top hq1 le_rfl hu
  have h3 : xq q ^ (((DEN : ℝ) - 1) / DEN) ≤ (N1 q : ℝ) := (good_of_large hL).hN₁
  linarith

section Leaves

variable {q : ℕ} (hL : LargeQ q) {a : ZMod q} {E : ℝ}
include hL

omit hL in
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem ha0_of {k : ℕ} {rt : Fin k → ℕ} (h : ∀ i, (parQ q).z₀ ≤ rt i) : ∀ i, (q : ℝ) ^ a0 ≤ rt i :=
  fun i => (Nat.le_ceil _).trans (by exact_mod_cast h i)

theorem lf_j0 (hP : P6at q a 0 E) : |(parQ q).J0 (gA q a) - (parQ q).J0 (gB q)| ≤ E := by
  rw [J0_eq, J0_eq]
  refine hP [] (by simp) (fun A hA => absurd hA List.not_mem_nil) (fun A hA => absurd hA List.not_mem_nil)
    fun rt _ _ => ⟨fun i => Fin.elim0 i, ?_⟩
  rw [Finset.univ_eq_empty, Finset.prod_empty]
  exact (thr_bounds hL).2.2.1 |> fun h => by exact_mod_cast h

theorem lf_e1 (hT : TLat q a 0 E) {i : ℕ} (hi : i < SieveCert.n) (hW : Par.inW i) :
    |(parQ q).I (gA q a) ((parQ q).S1c i) - (parQ q).I (gB q) ((parQ q).S1c i)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  refine hT _ Finset.univ (P1 q) (P2 q) (len_S1c q i) (thrOK_S1c hL hi) (P1_ok hL) (P2_ok hL) fun rt hp hs => ?_
  have hrt := mem_famSet_sum hp hs
  have hc := (parQ q).chain_S1c i rt hrt
  have hC : InC (xq q) i (rt 0) := inC_of_mem hrt (t := 0) fun A hA => List.mem_append_right _ hA
  have hC' : ∀ t, InC (xq q) ((fun _ : Fin 1 => i) t) (rt t) := fun t => by rw [Fin.fin_one_eq_zero t]; exact hC
  refine ⟨hc.1, ha0_of hc.2.1, window_lo hq1 hC' ?_, window_hi hq1 hC' ?_⟩
  · simpa using hW.1
  · simpa using hW.2

theorem lf_p1 (hP : P6at q a 1 E) {i : ℕ} (hi : i < SieveCert.n) :
    |(parQ q).J (gA q a) ((parQ q).S1c i) - (parQ q).J (gB q) ((parQ q).S1c i)| ≤ E := by
  refine hP _ (len_S1c q i) (thrOK_S1c hL hi) (nz_S1c q i) fun rt hp hs => ?_
  have hc := (parQ q).chain_S1c i rt (mem_famSet_sum hp hs)
  refine ⟨hc.2.1, ?_⟩
  rw [Fin.prod_univ_one]
  have := hc.2.2 0
  have := ztop_le_Xp hL
  show rt 0 ≤ (parQ q).Xp
  omega

variable [SieveCert.Rule]

theorem lf_e2 [SieveCert.RuleNB] (hE : 0 ≤ E) (hT : TUat q a 1 E) {i j : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hok : SieveCert.Rule.ok [cell i, cell j] = true) :
    |(parQ q).I (gA q a) ((parQ q).S2gt i j) - (parQ q).I (gB q) ((parQ q).S2gt i j)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hfacts : ∀ {Y : ℕ} (rt : Fin 2 → ℕ), rt ∈ famSet 2 Y ((parQ q).S2gt i j) →
      (∀ t, InC (xq q) (![i, j] t) (rt t)) ∧ (parQ q).Xs (sp2 i j) < ∏ t ∈ Finset.univ, (rt t : ℝ) := by
    intro Y rt hrt
    obtain ⟨-, hCi, hCj⟩ := (parQ q).facts_S2c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    refine ⟨fun t => ?_, sem_of_mem hrt (A := Atom.prodGt Finset.univ ((parQ q).Xs (sp2 i j)))
      (List.mem_append_right _ (List.mem_singleton_self _))⟩
    fin_cases t
    · exact hCi
    · exact hCj
  by_cases hs : sp2 i j = true
  · have hlim : SieveCert.e i + H + (SieveCert.e j + H) < lim := by
      simpa [sp2, SieveCert.limOK_cells2] using hs
    refine hT _ (parQ q).Xp (W1 q) (len_S2gt q i j) (thrOK_S2gt hL hi hj) (fun rt hp hs' => ?_) (W1_le hL)
      (W1_div hL) (W0_div hL)
    have hrt := mem_famSet_sum hp hs'
    obtain ⟨hc, -, -⟩ := (parQ q).facts_S2c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    obtain ⟨hC, hgt⟩ := hfacts rt hrt
    rw [hs, Par.Xs_true] at hgt
    refine ⟨hc.1, ha0_of hc.2.1, by exact_mod_cast hgt, ?_⟩
    have := window_hi hq1 hC (T := Finset.univ) (B := DEN - U1) (by
      simpa [Fin.sum_univ_two, SieveCert.lim] using hlim)
    simpa using this
  · have hnb : nbOK [cell i, cell j] = true := (SieveCert.RuleNB.nb _ hok).resolve_left hs
    rw [SieveCert.nbOK_cells2, decide_eq_true_eq] at hnb
    have hs' : sp2 i j = false := by simpa using hs
    have hz : ∀ g, (parQ q).I g ((parQ q).S2gt i j) = 0 := fun g =>
      famI_whole_gt hL g ![SieveCert.e i + H, SieveCert.e j + H] (by simp [Fin.sum_univ_two]; omega)
        fun rt hrt => by
          obtain ⟨hC, hgt⟩ := hfacts rt hrt
          rw [hs', Par.Xs_false] at hgt
          refine ⟨hgt, fun t => ?_⟩
          fin_cases t
          · simpa using (hC 0).2
          · simpa using (hC 1).2
    rw [hz, hz, sub_zero, abs_zero]
    exact hE

theorem lf_p2 [SieveCert.IBPar] [SieveCert.RuleIB] (hP : P6at q a 2 E) {i j : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hok : SieveCert.Rule.ok [cell i, cell j] = true)
    (hIB : SieveCert.ibOK [cell i, cell j] = true → P6IBat q a ![cell i, cell j] E) :
    |(parQ q).J (gA q a) ((parQ q).S2le i j) - (parQ q).J (gB q) ((parQ q).S2le i j)| ≤ E := by
  by_cases hs : sp2 i j = true
  · refine hP _ (len_S2le q i j) (thrOK_S2le hL hi hj) (nz_S2le q i j) fun rt hp hs' => ?_
    obtain ⟨hc, -, -, hX⟩ := (parQ q).facts_S2le (mem_famSet_sum hp hs')
    rw [hs, Par.Xs_true] at hX
    refine ⟨hc.2.1, ?_⟩
    rw [Fin.prod_univ_two]
    exact_mod_cast hX
  · have hib := ((SieveCert.RuleIB.ib _ hok).resolve_left hs).1
    refine hIB hib _ (len_S2le q i j) (thrOK_S2le hL hi hj) fun rt hp hs' => ?_
    obtain ⟨hc, hCi, hCj, -⟩ := (parQ q).facts_S2le (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩

omit [SieveCert.Rule] in
theorem lf_e2' (hTL : TLat q a 1 E) (hTR : TRat q a 1 E) {i j : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hs : Par.sE2 i j = true) :
    |(parQ q).I (gA q a) ((parQ q).S2c i j) - (parQ q).I (gB q) ((parQ q).S2c i j)| ≤ E := by
  refine box_leaf hL hTL hTR (len_S2c q i j) (thrOK_S2c hL hi hj) ![i, j] (fun rt hp hs' => ?_) ?_
  · obtain ⟨hc, hCi, hCj⟩ := (parQ q).facts_S2c (mem_famSet_sum hp hs')
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact hCi
    · exact hCj
  · simpa [List.ofFn_succ, Par.sE2] using hs

theorem lf_e3 [SieveCert.RuleNB] (hE : 0 ≤ E) (hT : TUat q a 2 E) {i j k : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hk : k < SieveCert.n) (hok : SieveCert.Rule.ok [cell i, cell j, cell k] = true) :
    |(parQ q).I (gA q a) ((parQ q).S3gt i j k) - (parQ q).I (gB q) ((parQ q).S3gt i j k)| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hfacts : ∀ {Y : ℕ} (rt : Fin 3 → ℕ), rt ∈ famSet 3 Y ((parQ q).S3gt i j k) →
      (∀ t, InC (xq q) (![i, j, k] t) (rt t)) ∧ (parQ q).Xs (sp3 i j k) < ∏ t ∈ Finset.univ, (rt t : ℝ) := by
    intro Y rt hrt
    obtain ⟨-, hCi, hCj, hCk, -⟩ := (parQ q).facts_S3c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    refine ⟨fun t => ?_, sem_of_mem hrt (A := Atom.prodGt Finset.univ ((parQ q).Xs (sp3 i j k)))
      (List.mem_append_right _ (List.mem_singleton_self _))⟩
    fin_cases t
    · exact hCi
    · exact hCj
    · exact hCk
  by_cases hs : sp3 i j k = true
  · have hlim : SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) < lim := by
      simpa [sp3, SieveCert.limOK_cells3] using hs
    refine hT _ (parQ q).Xp (W1 q) (len_S3gt q i j k) (thrOK_S3gt hL hi hj hk) (fun rt hp hs' => ?_) (W1_le hL)
      (W1_div hL) (W0_div hL)
    have hrt := mem_famSet_sum hp hs'
    obtain ⟨hc, -⟩ := (parQ q).facts_S3c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    obtain ⟨hC, hgt⟩ := hfacts rt hrt
    rw [hs, Par.Xs_true] at hgt
    refine ⟨hc.1, ha0_of hc.2.1, by exact_mod_cast hgt, ?_⟩
    have := window_hi hq1 hC (T := Finset.univ) (B := DEN - U1) (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      simpa [SieveCert.lim] using hlim)
    simpa using this
  · have hs' : sp3 i j k = false := by simpa using hs
    have hnb : nbOK [cell i, cell j, cell k] = true :=
      (SieveCert.RuleNB.nb _ hok).resolve_left hs
    rw [SieveCert.nbOK_cells3, decide_eq_true_eq] at hnb
    have hz : ∀ g, (parQ q).I g ((parQ q).S3gt i j k) = 0 := fun g =>
      famI_whole_gt hL g ![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H]
        (by simp [Fin.sum_univ_three]; omega) fun rt hrt => by
          obtain ⟨hC, hgt⟩ := hfacts rt hrt
          rw [hs', Par.Xs_false] at hgt
          refine ⟨hgt, fun t => ?_⟩
          fin_cases t
          · simpa using (hC 0).2
          · simpa using (hC 1).2
          · simpa using (hC 2).2
    rw [hz, hz, sub_zero, abs_zero]
    exact hE

theorem lf_p3 [SieveCert.IBPar] [SieveCert.RuleIB] (hP : P6at q a 3 E) {i j k : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hk : k < SieveCert.n) (hok : SieveCert.Rule.ok [cell i, cell j, cell k] = true)
    (hIB : SieveCert.ibOK [cell i, cell j, cell k] = true → P6IBat q a ![cell i, cell j, cell k] E) :
    |(parQ q).J (gA q a) ((parQ q).S3le i j k) - (parQ q).J (gB q) ((parQ q).S3le i j k)| ≤ E := by
  by_cases hs : sp3 i j k = true
  · refine hP _ (len_S3le q i j k) (thrOK_S3le hL hi hj hk) (nz_S3le q i j k) fun rt hp hs' => ?_
    obtain ⟨hc, -, -, -, -, hX⟩ := (parQ q).facts_S3le (mem_famSet_sum hp hs')
    rw [hs, Par.Xs_true] at hX
    refine ⟨hc.2.1, ?_⟩
    rw [Fin.prod_univ_three]
    exact_mod_cast hX
  · have hib := ((SieveCert.RuleIB.ib _ hok).resolve_left hs).1
    refine hIB hib _ (len_S3le q i j k) (thrOK_S3le hL hi hj hk) fun rt hp hs' => ?_
    obtain ⟨hc, hCi, hCj, hCk, -⟩ := (parQ q).facts_S3le (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩
    · exact ⟨by simpa [cell] using hCk.1, by simpa [cell] using hCk.2⟩

omit [SieveCert.Rule] in
theorem lf_e3' (hTL : TLat q a 2 E) (hTR : TRat q a 2 E) {i j k : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hk : k < SieveCert.n) (hn3 : ne3 i j k = false) :
    |(parQ q).I (gA q a) ((parQ q).S3c i j k) - (parQ q).I (gB q) ((parQ q).S3c i j k)| ≤ E := by
  refine box_leaf hL hTL hTR (len_S3c q i j k) (thrOK_S3c hL hi hj hk) ![i, j, k] (fun rt hp hs' => ?_) ?_
  · obtain ⟨hc, hCi, hCj, hCk, -⟩ := (parQ q).facts_S3c (mem_famSet_sum hp hs')
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact hCi
    · exact hCj
    · exact hCk
  · simpa [List.ofFn_succ, ne3] using hn3

omit [SieveCert.Rule] in
theorem lf_e4 (hTL : TLat q a 3 E) (hTR : TRat q a 3 E) {i j k l : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hs : Par.sE4 i j k l = true) :
    |(parQ q).I (gA q a) ((parQ q).S4c i j k l) - (parQ q).I (gB q) ((parQ q).S4c i j k l)| ≤ E := by
  refine box_leaf hL hTL hTR (len_S4c q i j k l) (thrOK_S4c hL hi hj hk hl) ![i, j, k, l]
    (fun rt hp hs' => ?_) ?_
  · obtain ⟨hc, hCi, hCj, hCk, hCl, -⟩ := (parQ q).facts_S4c (mem_famSet_sum hp hs')
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact hCi
    · exact hCj
    · exact hCk
    · exact hCl
  · simpa [List.ofFn_succ, Par.sE4] using hs

omit hL in
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [SieveCert.Rule] in
theorem inCC_iff {x : ℝ} {b p : ℕ} : InCC x b p ↔
    x ^ ((SieveCert.eC b : ℝ) / DEN) ≤ p ∧ (p : ℝ) < x ^ (((SieveCert.eC b : ℝ) + SieveCert.HC) / DEN) := Iff.rfl

omit hL in
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The depth-4 prefix's data: all four indices are below `n`. -/
theorem Deep.idx {i j k l : ℕ} (h : Par.Deep i j k l) :
    i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n :=
  ⟨h.1.1.1, h.1.1.2.1, h.1.2.1, by have := h.1.2.1; have := h.2.1; omega⟩

theorem lf_e4gt [SieveCert.RuleNB] (hE : 0 ≤ E) (hT : TUat q a 3 E) {i j k l : ℕ}
    (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n)
    (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l] = true) :
    |(parQ q).I (gA q a) ((parQ q).S4cgt i j k l) - (parQ q).I (gB q) ((parQ q).S4cgt i j k l)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hfacts : ∀ {Y : ℕ} (rt : Fin 4 → ℕ), rt ∈ famSet 4 Y ((parQ q).S4cgt i j k l) →
      (∀ t, InC (xq q) (![i, j, k, l] t) (rt t)) ∧
        (parQ q).Xs (sp4 i j k l) < ∏ t ∈ Finset.univ, (rt t : ℝ) := by
    intro Y rt hrt
    obtain ⟨-, hCi, hCj, hCk, hCl, -⟩ :=
      (parQ q).facts_S4c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    refine ⟨fun t => ?_, sem_of_mem hrt (A := Atom.prodGt Finset.univ ((parQ q).Xs (sp4 i j k l)))
      (List.mem_append_right _ (List.mem_singleton_self _))⟩
    fin_cases t
    · exact hCi
    · exact hCj
    · exact hCk
    · exact hCl
  by_cases hs : sp4 i j k l = true
  · have hT4 : SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) < lim := by
      simpa [sp4, SieveCert.limOK_cells4] using hs
    refine hT _ (parQ q).Xp (W1 q) (len_S4cgt q i j k l) (thrOK_S4cgt hL hi hj hk hl) (fun rt hp hs' => ?_)
      (W1_le hL) (W1_div hL) (W0_div hL)
    have hrt := mem_famSet_sum hp hs'
    obtain ⟨hc, -⟩ := (parQ q).facts_S4c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    obtain ⟨hC, hgt⟩ := hfacts rt hrt
    rw [hs, Par.Xs_true] at hgt
    refine ⟨hc.1, ha0_of hc.2.1, by exact_mod_cast hgt, ?_⟩
    have := window_hi hq1 hC (T := Finset.univ) (B := DEN - U1) (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      simpa [SieveCert.lim] using hT4)
    simpa using this
  · have hs' : sp4 i j k l = false := by simpa using hs
    have hnb : nbOK [cell i, cell j, cell k, cell l] = true :=
      (SieveCert.RuleNB.nb _ hok).resolve_left hs
    rw [SieveCert.nbOK_cells4, decide_eq_true_eq] at hnb
    have hz : ∀ g, (parQ q).I g ((parQ q).S4cgt i j k l) = 0 := fun g =>
      famI_whole_gt hL g ![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H, SieveCert.e l + H]
        (by simp [Fin.sum_univ_four]; omega) fun rt hrt => by
          obtain ⟨hC, hgt⟩ := hfacts rt hrt
          rw [hs', Par.Xs_false] at hgt
          refine ⟨hgt, fun t => ?_⟩
          fin_cases t
          · simpa using (hC 0).2
          · simpa using (hC 1).2
          · simpa using (hC 2).2
          · simpa using (hC 3).2
    rw [hz, hz, sub_zero, abs_zero]
    exact hE

theorem lf_p4 [SieveCert.IBPar] [SieveCert.RuleIB] (hP : P6at q a 4 E) {i j k l : ℕ}
    (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n)
    (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l] = true)
    (hIB : SieveCert.ibOK [cell i, cell j, cell k, cell l] = true → P6IBat q a ![cell i, cell j, cell k, cell l] E) :
    |(parQ q).J (gA q a) ((parQ q).S4cle i j k l) - (parQ q).J (gB q) ((parQ q).S4cle i j k l)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  by_cases hs : sp4 i j k l = true
  · refine hP _ (len_S4cle q i j k l) (thrOK_S4cle hL hi hj hk hl) (nz_S4cle q i j k l) fun rt hp hs' => ?_
    obtain ⟨hc, -, -, -, -, -, -, hX⟩ := (parQ q).facts_S4cle (mem_famSet_sum hp hs')
    rw [hs, Par.Xs_true] at hX
    refine ⟨hc.2.1, ?_⟩
    rw [Fin.prod_univ_four]
    exact_mod_cast hX
  · have hib := ((SieveCert.RuleIB.ib _ hok).resolve_left hs).1
    refine hIB hib _ (len_S4cle q i j k l) (thrOK_S4cle hL hi hj hk hl) fun rt hp hs' => ?_
    obtain ⟨hc, hCi, hCj, hCk, hCl, -⟩ := (parQ q).facts_S4cle (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩
    · exact ⟨by simpa [cell] using hCk.1, by simpa [cell] using hCk.2⟩
    · exact ⟨by simpa [cell] using hCl.1, by simpa [cell] using hCl.2⟩

theorem lf_e5gt [SieveCert.GridOKC] [SieveCert.RuleNB] (hE : 0 ≤ E) (hT : TUat q a 4 E) {i j k l b : ℕ}
    (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < SieveCert.nC)
    (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, SieveCert.cellC b] = true) :
    |(parQ q).I (gA q a) ((parQ q).S5gt i j k l b) - (parQ q).I (gB q) ((parQ q).S5gt i j k l b)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hfacts : ∀ {Y : ℕ} (rt : Fin 5 → ℕ), rt ∈ famSet 5 Y ((parQ q).S5gt i j k l b) →
      (∀ t, (rt t : ℝ) < xq q ^ ((((![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H,
        SieveCert.e l + H, SieveCert.eC b + SieveCert.HC] : Fin 5 → ℕ) t : ℕ) : ℝ) / DEN)) ∧
        (parQ q).Xs (sp5 i j k l b) < ∏ t ∈ Finset.univ, (rt t : ℝ) := by
    intro Y rt hrt
    obtain ⟨-, hCi, hCj, hCk, hCl, hCb, -⟩ :=
      (parQ q).facts_S5c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb : InCC (xq q) b (rt 4) := hCb
    have hCb := inCC_iff.1 hCb
    refine ⟨fun t => ?_, sem_of_mem hrt (A := Atom.prodGt Finset.univ ((parQ q).Xs (sp5 i j k l b)))
      (List.mem_append_right _ (List.mem_singleton_self _))⟩
    fin_cases t
    · simpa using hCi.2
    · simpa using hCj.2
    · simpa using hCk.2
    · simpa using hCl.2
    · simpa using hCb.2
  by_cases hs : sp5 i j k l b = true
  · have hT5 : SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) +
        (SieveCert.eC b + SieveCert.HC) < lim := by
      simpa [sp5, SieveCert.limOK_cells5] using hs
    refine hT _ (parQ q).Xp (W1 q) (len_S5gt q i j k l b) (thrOK_S5gt hL hi hj hk hl hb) (fun rt hp hs' => ?_)
      (W1_le hL) (W1_div hL) (W0_div hL)
    have hrt := mem_famSet_sum hp hs'
    obtain ⟨hc, -⟩ := (parQ q).facts_S5c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    obtain ⟨hb5, hgt⟩ := hfacts rt hrt
    rw [hs, Par.Xs_true] at hgt
    refine ⟨hc.1, ha0_of hc.2.1, by exact_mod_cast hgt, ?_⟩
    have := window_hi_gen hq1 hb5 (T := Finset.univ) (B := DEN - U1) (by
      simp [Fin.sum_univ_five, SieveCert.lim] at hT5 ⊢
      omega)
    simpa using this
  · have hs' : sp5 i j k l b = false := by simpa using hs
    have hnb : nbOK [cell i, cell j, cell k, cell l, SieveCert.cellC b] = true :=
      (SieveCert.RuleNB.nb _ hok).resolve_left hs
    rw [SieveCert.nbOK_cells5, decide_eq_true_eq] at hnb
    have hz : ∀ g, (parQ q).I g ((parQ q).S5gt i j k l b) = 0 := fun g =>
      famI_whole_gt hL g ![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H, SieveCert.e l + H,
        SieveCert.eC b + SieveCert.HC] (by simp [Fin.sum_univ_five]; omega) fun rt hrt => by
          obtain ⟨hb5, hgt⟩ := hfacts rt hrt
          rw [hs', Par.Xs_false] at hgt
          exact ⟨hgt, hb5⟩
    rw [hz, hz, sub_zero, abs_zero]
    exact hE

theorem lf_p5 [SieveCert.GridOKC] [SieveCert.IBPar] [SieveCert.RuleIB] (hP : P6at q a 5 E) {i j k l b : ℕ}
    (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < SieveCert.nC)
    (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, SieveCert.cellC b] = true)
    (hIB : SieveCert.ibOK [cell i, cell j, cell k, cell l, SieveCert.cellC b] = true →
      P6IBat q a ![cell i, cell j, cell k, cell l, SieveCert.cellC b] E) :
    |(parQ q).J (gA q a) ((parQ q).S5le i j k l b) - (parQ q).J (gB q) ((parQ q).S5le i j k l b)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  by_cases hs : sp5 i j k l b = true
  · refine hP _ (len_S5le q i j k l b) (thrOK_S5le hL hi hj hk hl hb) (nz_S5le q i j k l b) fun rt hp hs' => ?_
    obtain ⟨hc, -, -, -, -, -, -, -, -, hX⟩ := (parQ q).facts_S5le (mem_famSet_sum hp hs')
    rw [hs, Par.Xs_true] at hX
    refine ⟨hc.2.1, ?_⟩
    rw [Fin.prod_univ_five]
    exact_mod_cast hX
  · have hib := ((SieveCert.RuleIB.ib _ hok).resolve_left hs).1
    refine hIB hib _ (len_S5le q i j k l b) (thrOK_S5le hL hi hj hk hl hb) fun rt hp hs' => ?_
    obtain ⟨hc, hCi, hCj, hCk, hCl, hCb, -⟩ := (parQ q).facts_S5le (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb : InCC (xq q) b (rt 4) := hCb
    have hCb := inCC_iff.1 hCb
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩
    · exact ⟨by simpa [cell] using hCk.1, by simpa [cell] using hCk.2⟩
    · exact ⟨by simpa [cell] using hCl.1, by simpa [cell] using hCl.2⟩
    · exact ⟨by simpa [SieveCert.cellC] using hCb.1, by simpa [SieveCert.cellC] using hCb.2⟩

omit [SieveCert.Rule] in
theorem lf_e5' [SieveCert.GridOKC] (hTL : TLat q a 4 E) (hTR : TRat q a 4 E) {i j k l b : ℕ}
    (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < SieveCert.nC)
    (hn : SieveCert.ne5 i j k l b = false) :
    |(parQ q).I (gA q a) ((parQ q).S5c i j k l b) - (parQ q).I (gB q) ((parQ q).S5c i j k l b)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  refine box_leaf_gen hL hTL hTR (len_S5c q i j k l b) (thrOK_S5c hL hi hj hk hl hb)
    ![cell i, cell j, cell k, cell l, SieveCert.cellC b] (fun rt hp hs' => ?_) ?_
  · obtain ⟨hc, hCi, hCj, hCk, hCl, hCb, -⟩ := (parQ q).facts_S5c (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb : InCC (xq q) b (rt 4) := hCb
    have hCb := inCC_iff.1 hCb
    refine ⟨hc.1, hc.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩
    · exact ⟨by simpa [cell] using hCk.1, by simpa [cell] using hCk.2⟩
    · exact ⟨by simpa [cell] using hCl.1, by simpa [cell] using hCl.2⟩
    · exact ⟨by simpa [SieveCert.cellC] using hCb.1, by simpa [SieveCert.cellC] using hCb.2⟩
  · simpa [List.ofFn_succ, SieveCert.ne5] using hn

omit [SieveCert.Rule] in
theorem lf_e6 [SieveCert.GridOKC] (hTL : TLat q a 5 E) (hTR : TRat q a 5 E) {i j k l b c : ℕ}
    (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < SieveCert.nC)
    (hc : c < SieveCert.nC) (hs : Par.sE6 i j k l b c = true) :
    |(parQ q).I (gA q a) ((parQ q).S6c i j k l b c) - (parQ q).I (gB q) ((parQ q).S6c i j k l b c)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  refine box_leaf_gen hL hTL hTR (len_S6c q i j k l b c) (thrOK_S6c hL hi hj hk hl hb hc)
    ![cell i, cell j, cell k, cell l, SieveCert.cellC b, SieveCert.cellC c] (fun rt hp hs' => ?_) ?_
  · obtain ⟨hch, hCi, hCj, hCk, hCl, hCb, hCc, -⟩ := (parQ q).facts_S6c (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb : InCC (xq q) b (rt 4) := hCb
    have hCc : InCC (xq q) c (rt 5) := hCc
    have hCb := inCC_iff.1 hCb
    have hCc := inCC_iff.1 hCc
    refine ⟨hch.1, hch.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩
    · exact ⟨by simpa [cell] using hCk.1, by simpa [cell] using hCk.2⟩
    · exact ⟨by simpa [cell] using hCl.1, by simpa [cell] using hCl.2⟩
    · exact ⟨by simpa [SieveCert.cellC] using hCb.1, by simpa [SieveCert.cellC] using hCb.2⟩
    · exact ⟨by simpa [SieveCert.cellC] using hCc.1, by simpa [SieveCert.cellC] using hCc.2⟩
  · simpa [List.ofFn_succ, Par.sE6] using hs

end Leaves

/-- The leaves' error at `q`: `ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)`. -/
noncomputable def Err (η δ : ℝ) (q : ℕ) : ℝ :=
  η * (q : ℝ) ^ L / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem Err_nonneg {η : ℝ} (hη : 0 < η) (δ : ℝ) (q : ℕ) (hq : 1 ≤ q) : 0 ≤ Err η δ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  unfold Err
  positivity

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem Err_ge {η : ℝ} (hη : 0 < η) {δ d : ℝ} (hδd : δ ≤ d) (q : ℕ) (hq : 1 ≤ q) :
    (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - d : ℝ) ≤ Err η δ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  have h1 : (q : ℝ) ^ (L - d : ℝ) ≤ (q : ℝ) ^ (L - δ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have h2 : 0 ≤ η * (q : ℝ) ^ L / (q.totient * Real.log q) := by positivity
  unfold Err
  have : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  nlinarith

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem Err_ge' {η : ℝ} {δ d : ℝ} (hδd : δ ≤ d) (q : ℕ) (hq : 1 ≤ q) :
    η * (q : ℝ) ^ L / (q.totient * Real.log q) + (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - d : ℝ)
      ≤ Err η δ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (L - d : ℝ) ≤ (q : ℝ) ^ (L - δ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  unfold Err
  have : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  nlinarith

/-- The sieve's floor is below the window's width: `a₀ < (w₂ − w₁)L`. -/
theorem a0_lt_W : a0 < (w₂ - w₁) * L := by
  have h1 := (Fits.w₁_lt : w₁ * DEN < U1)
  have h2 := (Fits.U2_lt : (U2 : ℝ) < w₂ * DEN)
  have hD := DEN_pos
  have hL : (0 : ℝ) < L := L_pos
  have hV : (V : ℝ) / DEN < w₂ - w₁ := by
    rw [div_lt_iff₀ hD, V_cast]
    linarith
  unfold a0
  nlinarith

/-- **Proposition 6-ib on a box the bilinear rule passes.** Let the route have `RouteOK`, the grid `GridOK`, the two
fit (`Fits`), and the bilinear rule's exponent be the route's (`IBFits`), and assume the route's Type II estimate
(`hII`). For a box `f` that `ibOK` passes and `η > 0` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a`
mod `q`, Proposition 6's estimate holds on the families in the box (`P6IBat`) with error `Err η δ q`: the witnesses of
`ibOK_sound`, at the exponents `L·lo/DEN`, `L·hi/DEN` and `t = L·T/DEN`, are `SieveP6ib.prop6ib`'s conditions. -/
theorem P6IB_box [SieveCert.IBPar] [IBFits] (hII : TypeIIAt) {j : ℕ} (f : Fin j → ℕ × ℕ)
    (hf : SieveCert.ibOK (List.ofFn f) = true) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      P6IBat q a f (Err η δ q) := by
  obtain ⟨S₀, T, h0, hlo, hmid, S₁, eIn₁, hD₁, hD₂⟩ := SieveCert.ibOK_sound f hf
  have hD := DEN_pos
  have hDne : (DEN : ℝ) ≠ 0 := hD.ne'
  have hLp : (0 : ℝ) < L := L_pos
  have hw₁ := (Fits.w₁_lt : w₁ * DEN < U1)
  have hw₂ := (Fits.U2_lt : (U2 : ℝ) < w₂ * DEN)
  have sc : ∀ {x y : ℝ}, x ≤ y → L * (x / DEN) ≤ L * (y / DEN) := fun h =>
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hD.le) hLp.le
  have sc' : ∀ {x y : ℝ}, x < y → L * (x / DEN) < L * (y / DEN) := fun h =>
    mul_lt_mul_of_pos_left (div_lt_div_of_pos_right h hD) hLp
  have hs : ∀ (S : Finset (Fin j)) (g : Fin j → ℕ), ∑ i ∈ S, L * ((g i : ℝ) / DEN) =
      L * (((∑ i ∈ S, g i : ℕ) : ℝ) / DEN) := fun S g => by
    rw [Nat.cast_sum, Finset.sum_div, Finset.mul_sum]
  -- the exponent `L = Lnum/Lden`
  have hLden : (0 : ℝ) < SieveCert.IBPar.Lden := by
    rcases Nat.eq_zero_or_pos SieveCert.IBPar.Lden with h | h
    · have := (IBFits.L_eq : (SieveCert.IBPar.Lnum : ℝ) / SieveCert.IBPar.Lden = L)
      rw [h, Nat.cast_zero, div_zero] at this
      linarith
    · exact_mod_cast h
  have hLnum : (SieveCert.IBPar.Lnum : ℝ) = L * SieveCert.IBPar.Lden := by
    rw [← (IBFits.L_eq : (SieveCert.IBPar.Lnum : ℝ) / SieveCert.IBPar.Lden = L), div_mul_cancel₀ _ hLden.ne']
  -- the split's sums
  set a₁ : ℕ := ∑ t ∈ S₁, (f t).2 + (if eIn₁ then T else 0) with ha₁
  set a₂ : ℕ := ∑ t ∈ S₁ᶜ, (f t).2 + (if eIn₁ then 0 else T) with ha₂
  have hA₁ : ∑ i ∈ S₁, L * (((f i).2 : ℝ) / DEN) + (if eIn₁ then L * ((T : ℝ) / DEN) else 0) =
      L * ((a₁ : ℝ) / DEN) := by
    rw [hs S₁ fun i => (f i).2, ha₁]
    cases eIn₁ <;> simp [add_div, mul_add]
  have hA₂ : ∑ i ∈ S₁ᶜ, L * (((f i).2 : ℝ) / DEN) + (if eIn₁ then 0 else L * ((T : ℝ) / DEN)) =
      L * ((a₂ : ℝ) / DEN) := by
    rw [hs S₁ᶜ fun i => (f i).2, ha₂]
    cases eIn₁ <;> simp [add_div, mul_add]
  have hS₀lo := hs S₀ fun i => (f i).1
  have hS₀hi := hs S₀ fun i => (f i).2
  -- `w₁L − Σ_{S₀} lo ≤ t`
  have c1 : w₁ * L - ∑ i ∈ S₀, L * (((f i).1 : ℝ) / DEN) ≤ L * ((T : ℝ) / DEN) := by
    have e1 : U1 ≤ T + ∑ t ∈ S₀, (f t).1 := by omega
    have r1 : (U1 : ℝ) ≤ T + ((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) := by exact_mod_cast e1
    rw [hS₀lo]
    calc w₁ * L - L * (((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) / DEN)
        = L * ((w₁ * DEN - ((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ)) / DEN) := by field_simp
      _ ≤ L * ((T : ℝ) / DEN) := sc (by linarith)
  have hw2L : w₂ * L = L * (w₂ * DEN / DEN) := by field_simp
  have hLL : L = L * ((DEN : ℝ) / DEN) := by field_simp
  -- the middle of the window
  have c2 : w₂ * L < ∑ i ∈ S₀, L * (((f i).2 : ℝ) / DEN) →
      L - w₂ * L - max (w₂ * L) (∑ i ∈ S₀, L * (((f i).1 : ℝ) / DEN)) ≤ L * ((T : ℝ) / DEN) := by
    rw [hS₀lo, hS₀hi]
    intro hW
    have hU : U2 ≤ ∑ t ∈ S₀, (f t).2 := by
      have h' : w₂ * DEN < ((∑ t ∈ S₀, (f t).2 : ℕ) : ℝ) := by
        by_contra hc
        have := sc (not_lt.1 hc)
        rw [← hw2L] at this
        linarith
      have : (U2 : ℝ) < ((∑ t ∈ S₀, (f t).2 : ℕ) : ℝ) := by linarith
      exact_mod_cast this.le
    have hm := hmid hU
    have hmax : w₂ * L ≤ max (w₂ * L) (L * (((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) / DEN)) := le_max_left _ _
    have hmax' : L * (((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) / DEN) ≤
        max (w₂ * L) (L * (((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) / DEN)) := le_max_right _ _
    rcases le_total (∑ t ∈ S₀, (f t).1) U2 with hA | hA
    · rw [max_eq_right hA] at hm
      have e2 : DEN ≤ T + U2 + U2 := by omega
      have r2 : (DEN : ℝ) ≤ T + U2 + U2 := by exact_mod_cast e2
      have : L * ((DEN : ℝ) / DEN) - L * (w₂ * DEN / DEN) - L * (w₂ * DEN / DEN) ≤ L * ((T : ℝ) / DEN) := by
        calc L * ((DEN : ℝ) / DEN) - L * (w₂ * DEN / DEN) - L * (w₂ * DEN / DEN)
            = L * (((DEN : ℝ) - w₂ * DEN - w₂ * DEN) / DEN) := by ring
          _ ≤ L * ((T : ℝ) / DEN) := sc (by linarith)
      rw [← hw2L, ← hLL] at this
      linarith
    · rw [max_eq_left hA] at hm
      have e2 : DEN ≤ T + U2 + ∑ t ∈ S₀, (f t).1 := by omega
      have r2 : (DEN : ℝ) ≤ T + U2 + ((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) := by exact_mod_cast e2
      have : L * ((DEN : ℝ) / DEN) - L * (w₂ * DEN / DEN) - L * (((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) / DEN) ≤
          L * ((T : ℝ) / DEN) := by
        calc L * ((DEN : ℝ) / DEN) - L * (w₂ * DEN / DEN) - L * (((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ) / DEN)
            = L * (((DEN : ℝ) - w₂ * DEN - ((∑ t ∈ S₀, (f t).1 : ℕ) : ℝ)) / DEN) := by ring
          _ ≤ L * ((T : ℝ) / DEN) := sc (by linarith)
      rw [← hw2L, ← hLL] at this
      linarith
  -- `Σ_{S₀} hi < L − w₁L`
  have c3 : ∑ i ∈ S₀, L * (((f i).2 : ℝ) / DEN) < L - w₁ * L := by
    rw [hS₀hi]
    have e3 : ∑ t ∈ S₀, (f t).2 + U1 < DEN := by omega
    have r3 : ((∑ t ∈ S₀, (f t).2 : ℕ) : ℝ) + U1 < DEN := by exact_mod_cast e3
    calc L * (((∑ t ∈ S₀, (f t).2 : ℕ) : ℝ) / DEN) < L * (((DEN : ℝ) - w₁ * DEN) / DEN) := sc' (by linarith)
      _ = L - w₁ * L := by field_simp
  -- `a₁ < L − 1`, at the upper ends
  have c4 : ∑ i ∈ S₁, L * (((f i).2 : ℝ) / DEN) + (if eIn₁ then L * ((T : ℝ) / DEN) else 0) < L - 1 := by
    rw [hA₁]
    have hN : SieveCert.IBPar.Lden < SieveCert.IBPar.Lnum := by
      by_contra hc
      rw [Nat.sub_eq_zero_of_le (not_lt.1 hc), zero_mul] at hD₁
      exact absurd hD₁ (Nat.not_lt_zero _)
    have r4 : (a₁ : ℝ) * SieveCert.IBPar.Lnum < ((SieveCert.IBPar.Lnum : ℝ) - SieveCert.IBPar.Lden) * DEN := by
      rw [← Nat.cast_sub hN.le]
      exact_mod_cast hD₁
    rw [hLnum] at r4
    have r5 : (a₁ : ℝ) * L < (L - 1) * DEN := by
      have : ((a₁ : ℝ) * L) * SieveCert.IBPar.Lden < ((L - 1) * DEN) * SieveCert.IBPar.Lden := by nlinarith
      exact lt_of_mul_lt_mul_right this hLden.le
    rw [mul_div_assoc', div_lt_iff₀ hD]
    linarith
  -- `a₁ + 2a₂ < 1`, at the upper ends
  have c5 : ∑ i ∈ S₁, L * (((f i).2 : ℝ) / DEN) + (if eIn₁ then L * ((T : ℝ) / DEN) else 0) +
      2 * (∑ i ∈ S₁ᶜ, L * (((f i).2 : ℝ) / DEN) + (if eIn₁ then 0 else L * ((T : ℝ) / DEN))) < L := by
    rw [hA₁, hA₂]
    have r6 : (a₁ : ℝ) + 2 * a₂ < DEN := by exact_mod_cast hD₂
    calc L * ((a₁ : ℝ) / DEN) + 2 * (L * ((a₂ : ℝ) / DEN)) = L * (((a₁ : ℝ) + 2 * a₂) / DEN) := by ring
      _ < L * ((DEN : ℝ) / DEN) := sc' r6
      _ = L := by field_simp
  obtain ⟨δ, hδ, q₀, hq₀⟩ := P6IB_spec a0 hII a0_pos a0_lt_W j (fun i => L * (((f i).1 : ℝ) / DEN))
    (fun i => L * (((f i).2 : ℝ) / DEN)) S₀ S₁ eIn₁ c1 c2 c3 c4 c5 hη
  refine ⟨δ, hδ, q₀, fun q _ hq a ha spec hlen hthr hsem => hq₀ q hq a ha spec hlen hthr fun rt hp hs' => ?_⟩
  obtain ⟨hsa, hz, hc⟩ := hsem rt hp hs'
  refine ⟨hsa, hz, fun i => ⟨?_, ?_⟩⟩
  · rw [Real.rpow_mul (Nat.cast_nonneg q)]
    exact (hc i).1
  · rw [Real.rpow_mul (Nat.cast_nonneg q)]
    exact (hc i).2.le

/-- **Proposition 6-ib, uniformly over finitely many boxes**: `P6IB_box` for each box of `B` that `ibOK` passes, with
the least `δ` and the largest `q₀`. -/
theorem P6IB_boxes [SieveCert.IBPar] [IBFits] (hII : TypeIIAt) {j : ℕ} (B : Finset (Fin j → ℕ × ℕ)) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ f ∈ B, SieveCert.ibOK (List.ofFn f) = true → P6IBat q a f (Err η δ q) := by
  classical
  induction B using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 0, fun q _ _ a _ f hf => absurd hf (Finset.notMem_empty f)⟩
  | insert f B _ ih =>
    obtain ⟨δ₁, hδ₁, q₁, h₁⟩ := ih
    by_cases hf : SieveCert.ibOK (List.ofFn f) = true
    · obtain ⟨δ₂, hδ₂, q₂, h₂⟩ := P6IB_box hII f hf hη
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max q₁ (max q₂ 1), fun q _ hq a ha g hg hgo => ?_⟩
      have hq1 : 1 ≤ q := le_of_max_le_right (le_of_max_le_right hq)
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact (h₂ q (le_of_max_le_left (le_of_max_le_right hq)) a ha).mono (Err_ge' (min_le_right _ _) q hq1)
      · exact (h₁ q (le_of_max_le_left hq) a ha g hg hgo).mono (Err_ge' (min_le_left _ _) q hq1)
    · refine ⟨δ₁, hδ₁, q₁, fun q _ hq a ha g hg hgo => ?_⟩
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact absurd hgo hf
      · exact h₁ q hq a ha g hg hgo

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- Some `δ > 0` is at most each of finitely many positive reals. -/
theorem exists_le_list (ds : List ℝ) (h : ∀ d ∈ ds, 0 < d) : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ ds, δ ≤ d := by
  induction ds with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons d ds ih =>
    obtain ⟨δ, hδ, hle⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨min d δ, lt_min (h d (by simp)) hδ, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle x hx)

/-- The boxes of depth 2 of the grid: `(cell i, cell j)` for `i, j < n`. -/
def boxes2 : Finset (Fin 2 → ℕ × ℕ) :=
  (Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n).image fun p => ![cell p.1, cell p.2]

/-- The boxes of depth 3 of the grid. -/
def boxes3 : Finset (Fin 3 → ℕ × ℕ) :=
  (Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n).image
    fun p => ![cell p.1, cell p.2.1, cell p.2.2]

/-- The boxes of depth 4 of the grid. -/
def boxes4 : Finset (Fin 4 → ℕ × ℕ) :=
  (Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n).image
    fun p => ![cell p.1, cell p.2.1, cell p.2.2.1, cell p.2.2.2]

/-- The boxes of depth 5 of the grid: four fine cells and a coarse one. -/
def boxes5 : Finset (Fin 5 → ℕ × ℕ) :=
  (Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ
    Finset.range SieveCert.nC).image
      fun p => ![cell p.1, cell p.2.1, cell p.2.2.1, cell p.2.2.2.1, SieveCert.cellC p.2.2.2.2]

/-- **The leaves, for large `q`.** For a route with `RouteOK` and a grid with `GridOK` and `GridOKC` that fit
(`Fits`), a rule that splits and decomposes a box only when `limOK` passes, or the bilinear Type I test with no boundary
term does (`RuleIB`), its exponent the route's (`IBFits`), and the route's Type II estimate (`hII`): for `η > 0` there
are `δ > 0` and `q₀` such that for `q ≥ q₀` and `a` a unit mod `q`, `q` is large and every leaf of the tree at
`x = q^L` is within `Err η δ q`. -/
theorem leaves_ev [SieveCert.GridOKC] [SieveCert.Rule] [SieveCert.IBPar] [SieveCert.RuleIB] [IBFits]
    (hII : TypeIIAt) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      LargeQ q ∧ (parQ q).Leaves (gA q a) (gB q) (Err η δ q) := by
  have : SieveCert.RuleNB := SieveCert.RuleIB.toRuleNB
  obtain ⟨d1, hd1, q1, h1⟩ := TL_spec a0 hII a0_pos 0
  obtain ⟨d2, hd2, q2, h2⟩ := TL_spec a0 hII a0_pos 1
  obtain ⟨d3, hd3, q3, h3⟩ := TL_spec a0 hII a0_pos 2
  obtain ⟨d4, hd4, q4, h4⟩ := TL_spec a0 hII a0_pos 3
  obtain ⟨d5, hd5, q5, h5⟩ := TL_spec a0 hII a0_pos 4
  obtain ⟨d6, hd6, q6, h6⟩ := TL_spec a0 hII a0_pos 5
  obtain ⟨d7, hd7, q7, h7⟩ := TU_spec a0 hII a0_pos 1
  obtain ⟨d8, hd8, q8, h8⟩ := TU_spec a0 hII a0_pos 2
  obtain ⟨d9, hd9, q9, h9⟩ := TU_spec a0 hII a0_pos 3
  obtain ⟨d10, hd10, q10, h10⟩ := TU_spec a0 hII a0_pos 4
  obtain ⟨d11, hd11, q11, h11⟩ := TR_spec a0 hII a0_pos 1
  obtain ⟨d12, hd12, q12, h12⟩ := TR_spec a0 hII a0_pos 2
  obtain ⟨d13, hd13, q13, h13⟩ := TR_spec a0 hII a0_pos 3
  obtain ⟨d14, hd14, q14, h14⟩ := TR_spec a0 hII a0_pos 4
  obtain ⟨d15, hd15, q15, h15⟩ := TR_spec a0 hII a0_pos 5
  obtain ⟨d16, hd16, q16, h16⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 0 hη
  obtain ⟨d17, hd17, q17, h17⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 1 hη
  obtain ⟨d18, hd18, q18, h18⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 2 hη
  obtain ⟨d19, hd19, q19, h19⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 3 hη
  obtain ⟨d20, hd20, q20, h20⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 4 hη
  obtain ⟨d21, hd21, q21, h21⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 5 hη
  obtain ⟨d22, hd22, q22, h22⟩ := P6IB_boxes hII boxes2 hη
  obtain ⟨d23, hd23, q23, h23⟩ := P6IB_boxes hII boxes3 hη
  obtain ⟨d24, hd24, q24, h24⟩ := P6IB_boxes hII boxes4 hη
  obtain ⟨d25, hd25, q25, h25⟩ := P6IB_boxes hII boxes5 hη
  obtain ⟨qL, hqL⟩ := Filter.eventually_atTop.1 (largeQ_ev)
  obtain ⟨δ, hδ0, hle⟩ := exists_le_list [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17,
    d18, d19, d20, d21, d22, d23, d24, d25]
    (by simp [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19,
      hd20, hd21, hd22, hd23, hd24, hd25])
  refine ⟨δ, hδ0, q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 + q16 + q17 + q18 +
    q19 + q20 + q21 + q22 + q23 + q24 + q25 + qL, fun q _ hq a ha => ?_⟩
  have hLq : LargeQ q := hqL q (by omega)
  have hq1 : 1 ≤ q := by have := hLq.q3; omega
  have hE0 := Err_nonneg hη δ q hq1
  have tl0 : TLat q a 0 (Err η δ q) := TLat.mono (h1 q (by omega) a ha) (Err_ge hη (hle d1 (by simp)) q hq1)
  have tl1 : TLat q a 1 (Err η δ q) := TLat.mono (h2 q (by omega) a ha) (Err_ge hη (hle d2 (by simp)) q hq1)
  have tl2 : TLat q a 2 (Err η δ q) := TLat.mono (h3 q (by omega) a ha) (Err_ge hη (hle d3 (by simp)) q hq1)
  have tl3 : TLat q a 3 (Err η δ q) := TLat.mono (h4 q (by omega) a ha) (Err_ge hη (hle d4 (by simp)) q hq1)
  have tl4 : TLat q a 4 (Err η δ q) := TLat.mono (h5 q (by omega) a ha) (Err_ge hη (hle d5 (by simp)) q hq1)
  have tl5 : TLat q a 5 (Err η δ q) := TLat.mono (h6 q (by omega) a ha) (Err_ge hη (hle d6 (by simp)) q hq1)
  have tu1 : TUat q a 1 (Err η δ q) := TUat.mono (h7 q (by omega) a ha) (Err_ge hη (hle d7 (by simp)) q hq1)
  have tu2 : TUat q a 2 (Err η δ q) := TUat.mono (h8 q (by omega) a ha) (Err_ge hη (hle d8 (by simp)) q hq1)
  have tu3 : TUat q a 3 (Err η δ q) := TUat.mono (h9 q (by omega) a ha) (Err_ge hη (hle d9 (by simp)) q hq1)
  have tu4 : TUat q a 4 (Err η δ q) := TUat.mono (h10 q (by omega) a ha) (Err_ge hη (hle d10 (by simp)) q hq1)
  have tr1 : TRat q a 1 (Err η δ q) := TRat.mono (h11 q (by omega) a ha) (Err_ge hη (hle d11 (by simp)) q hq1)
  have tr2 : TRat q a 2 (Err η δ q) := TRat.mono (h12 q (by omega) a ha) (Err_ge hη (hle d12 (by simp)) q hq1)
  have tr3 : TRat q a 3 (Err η δ q) := TRat.mono (h13 q (by omega) a ha) (Err_ge hη (hle d13 (by simp)) q hq1)
  have tr4 : TRat q a 4 (Err η δ q) := TRat.mono (h14 q (by omega) a ha) (Err_ge hη (hle d14 (by simp)) q hq1)
  have tr5 : TRat q a 5 (Err η δ q) := TRat.mono (h15 q (by omega) a ha) (Err_ge hη (hle d15 (by simp)) q hq1)
  have p0 : P6at q a 0 (Err η δ q) := P6at.mono (h16 q (by omega) a ha) (Err_ge' (η := η) (hle d16 (by simp)) q hq1)
  have p1 : P6at q a 1 (Err η δ q) := P6at.mono (h17 q (by omega) a ha) (Err_ge' (η := η) (hle d17 (by simp)) q hq1)
  have p2 : P6at q a 2 (Err η δ q) := P6at.mono (h18 q (by omega) a ha) (Err_ge' (η := η) (hle d18 (by simp)) q hq1)
  have p3 : P6at q a 3 (Err η δ q) := P6at.mono (h19 q (by omega) a ha) (Err_ge' (η := η) (hle d19 (by simp)) q hq1)
  have p4 : P6at q a 4 (Err η δ q) := P6at.mono (h20 q (by omega) a ha) (Err_ge' (η := η) (hle d20 (by simp)) q hq1)
  have p5 : P6at q a 5 (Err η δ q) := P6at.mono (h21 q (by omega) a ha) (Err_ge' (η := η) (hle d21 (by simp)) q hq1)
  have ib2 := fun f hf ho =>
    (h22 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d22 (by simp)) q hq1)
  have ib3 := fun f hf ho =>
    (h23 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d23 (by simp)) q hq1)
  have ib4 := fun f hf ho =>
    (h24 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d24 (by simp)) q hq1)
  have ib5 := fun f hf ho =>
    (h25 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d25 (by simp)) q hq1)
  refine ⟨hLq, ⟨lf_j0 hLq p0, fun i hi hW => lf_e1 hLq tl0 hi hW, fun i hi _ => lf_p1 hLq p1 hi,
    fun i hi j hj _ hd => lf_e2 hLq hE0 tu1 hi hj (SieveCert.ok2_of_decR hd),
    fun i hi j hj _ hd => lf_p2 hLq p2 hi hj (SieveCert.ok2_of_decR hd) fun hib =>
      ib2 _ (Finset.mem_image.2 ⟨(i, j), by simp [hi, hj], rfl⟩) (by simpa [List.ofFn_succ] using hib),
    fun i hi _ j hj _ hs => lf_e2' hLq tl1 tr1 hi hj hs,
    fun i hi j hj _ hd k hk hkk hn3 => lf_e3 hLq hE0 tu2 hi hj hk (SieveCert.ok3_of_decR hd hk hkk hn3),
    fun i hi j hj _ hd k hk hkk hn3 => lf_p3 hLq p3 hi hj hk (SieveCert.ok3_of_decR hd hk hkk hn3) fun hib =>
      ib3 _ (Finset.mem_image.2 ⟨(i, j, k), by simp [hi, hj, hk], rfl⟩) (by simpa [List.ofFn_succ] using hib),
    fun i hi j hj _ _ k hk _ hn3 => lf_e3' hLq tl2 tr2 hi hj hk hn3,
    fun i hi j hj _ _ k hk _ _ l hl _ hs => lf_e4 hLq tl3 tr3 hi hj hk (by omega) hs,
    fun i j k l hD => lf_e4gt hLq hE0 tu3 (Deep.idx hD) (SieveCert.ok4_of_dec4R hD.2.2.2),
    fun i j k l hD => lf_p4 hLq p4 (Deep.idx hD) (SieveCert.ok4_of_dec4R hD.2.2.2) fun hib => by
      obtain ⟨hi, hj, hk, hl⟩ := Deep.idx hD
      exact ib4 _ (Finset.mem_image.2 ⟨(i, j, k, l), by simp [hi, hj, hk, hl], rfl⟩)
        (by simpa [List.ofFn_succ] using hib),
    fun i j k l hD b hb hK hn => lf_e5gt hLq hE0 tu4 (Deep.idx hD) hb (SieveCert.ok5_of_dec4R hD.2.2.2 hb hK hn),
    fun i j k l hD b hb hK hn => lf_p5 hLq p5 (Deep.idx hD) hb (SieveCert.ok5_of_dec4R hD.2.2.2 hb hK hn)
      fun hib => by
        obtain ⟨hi, hj, hk, hl⟩ := Deep.idx hD
        exact ib5 _ (Finset.mem_image.2 ⟨(i, j, k, l, b), by simp [hi, hj, hk, hl, hb], rfl⟩)
          (by simpa [List.ofFn_succ] using hib),
    fun i j k l hD b hb _ hn => lf_e5' hLq tl4 tr4 (Deep.idx hD) hb hn,
    fun i j k l hD b hb _ _ c hc _ hs => lf_e6 hLq tl5 tr5 (Deep.idx hD) hb (by omega) hs⟩⟩

end SieveQ
