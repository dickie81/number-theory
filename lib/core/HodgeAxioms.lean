/-
# The Hodge index theorem from three axioms, and which of them Weil's form for `ζ` satisfies

Plain statement.
* **Abstract Hodge index** (`hodge_index`): let `B` be a symmetric bilinear form on a real vector space, `Eff` a set
  of "effective" classes and `h` a class such that (ample) `B(D, h) > 0` for every nonzero effective `D`, and
  (Riemann–Roch) `B(D, D) > 0` implies that `D` or `−D` is effective. Then `B(D, h) = 0` implies `B(D, D) ≤ 0`, and if
  `B(h, h) > 0`, `B(D, D)·B(h, h) ≤ B(D, h)²` for every `D` (`hodge_cs`): signature `(1, ·)`. This is the classical
  proof for surfaces, with `h^0` replaced by the dichotomy.
* **For Weil's form of `ζ`** (`BallWeil`), take `h = e₁ + e₂`, with `h² = 2` and `D·h = D·e₁ + D·e₂` (`dotH`).
  - RH holds if and only if `D·h = 0` implies `D² ≤ 0` (`rh_iff_hodge_h`): RH is the Hodge index theorem for `h`.
  - With the naive effective cone of classes with nonnegative coefficients, the ampleness axiom holds unconditionally
    (`ample_naive`).
  - But the Riemann–Roch axiom fails for that cone, unconditionally: `D = e₁ + e₂ − D_1/4` has `D² > 0` and neither
    `D` nor `−D` has nonnegative coefficients (`rr_fails_naive`).
  - With the positive cone `{D : D² ≥ 0, D·h ≥ 0}` the Riemann–Roch axiom is automatic, and the ampleness axiom for it
    is equivalent to RH (`rh_iff_ample_pos`): that cone is defined by the form, so it proves nothing.
So the single missing mechanism is a notion of effectivity, independent of the form, that is both ample-positive and
satisfies the Riemann–Roch dichotomy: on a surface it is `h^0(D) > 0`, supplied by Riemann–Roch.
-/
import Mathlib
import BallPole

open Finset

noncomputable section

namespace HodgeAxioms

/-! ## The abstract lemma -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Abstract Hodge index**: ampleness on the effective cone and the Riemann–Roch dichotomy give `D·h = 0 ⇒ D² ≤ 0`. -/
theorem hodge_index (B : LinearMap.BilinForm ℝ V) (Eff : Set V) (h : V)
    (ample : ∀ D ∈ Eff, D ≠ 0 → 0 < B D h) (rr : ∀ D, 0 < B D D → D ∈ Eff ∨ -D ∈ Eff)
    {D : V} (hD : B D h = 0) : B D D ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hD0 : D ≠ 0 := by rintro rfl; simp at hpos
  rcases rr D hpos with he | he
  · linarith [ample D he hD0]
  · have := ample (-D) he (neg_ne_zero.2 hD0)
    rw [LinearMap.map_neg₂, hD, neg_zero] at this
    exact lt_irrefl _ this

/-- **The reverse Cauchy–Schwarz inequality**: under the same axioms, with `B` symmetric and `B(h, h) > 0`,
`B(D, D)·B(h, h) ≤ B(D, h)²`. -/
theorem hodge_cs (B : LinearMap.BilinForm ℝ V) (hs : ∀ x y, B x y = B y x) (Eff : Set V) (h : V)
    (ample : ∀ D ∈ Eff, D ≠ 0 → 0 < B D h) (rr : ∀ D, 0 < B D D → D ∈ Eff ∨ -D ∈ Eff) (hh : 0 < B h h) (D : V) :
    B D D * B h h ≤ B D h ^ 2 := by
  set t := B D h / B h h
  have horth : B (D - t • h) h = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, t]
    field_simp
    ring
  have hle := hodge_index B Eff h ample rr horth
  have e : B (D - t • h) (D - t • h) = B D D - 2 * t * B D h + t ^ 2 * B h h := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hs h D]
    ring
  rw [e] at hle
  have ht : t * B h h = B D h := by simp only [t]; field_simp
  nlinarith [ht]

/-! ## Weil's form for `ζ` -/

open BallWeil BallPole

/-- `D·h` for `h = e₁ + e₂`: `D·e₁ + D·e₂`. -/
def dotH (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) : ℝ := deg₁ b N c + deg₂ a N c

/-- **RH is the Hodge index theorem for `h = e₁ + e₂`.** -/
theorem rh_iff_hodge_h : RiemannHypothesis ↔
    ∀ (a b : ℝ) (N : ℕ) (c : ℕ → ℝ), dotH a b N c = 0 → selfInt a b N c ≤ 0 := by
  constructor
  · intro hRH a b N c hd
    have h2 : deg₂ a N c = -deg₁ b N c := by unfold dotH at hd; linarith
    have := (rh_iff_hodge_index_real.1 hRH) _ _ N c (perp_orth a b N c)
    rw [selfInt_decomp a b N c]
    have e : 2 * deg₁ b N c * deg₂ a N c = -(2 * deg₁ b N c ^ 2) := by rw [h2]; ring
    nlinarith [sq_nonneg (deg₁ b N c)]
  · intro H
    refine rh_iff_hodge_index_real.2 fun a b N c hc => H a b N c ?_
    unfold dotH
    rw [hc.1, hc.2, add_zero]

/-- **Ampleness holds for the naive cone**: a nonzero class with nonnegative coefficients has `D·h > 0`. -/
theorem ample_naive {a b : ℝ} {N : ℕ} {c : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : ∀ n ∈ Icc 1 N, 0 ≤ c n)
    (hne : 0 < a ∨ 0 < b ∨ ∃ n ∈ Icc 1 N, 0 < c n) : 0 < dotH a b N c := by
  unfold dotH deg₁ deg₂
  have h1 : 0 ≤ ∑ n ∈ Icc 1 N, c n := sum_nonneg hc
  have h2 : 0 ≤ ∑ n ∈ Icc 1 N, c n * n := sum_nonneg fun n hn => mul_nonneg (hc n hn) (Nat.cast_nonneg n)
  rcases hne with h | h | ⟨m, hm, hcm⟩
  · linarith
  · linarith
  · have : 0 < ∑ n ∈ Icc 1 N, c n := by
      calc (0 : ℝ) < c m := hcm
        _ ≤ ∑ n ∈ Icc 1 N, c n := single_le_sum (f := c) hc hm
    linarith

/-- **Riemann–Roch fails for the naive cone**, unconditionally: `D = e₁ + e₂ − D_1/4` has `D² > 0`. -/
theorem rr_fails_naive : 0 < selfInt 1 1 1 (fun n => if n = 1 then -1 / 4 else 0) := by
  unfold selfInt
  have hK : inter 1 1 = 2 - (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) := inter_one
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl : 0 < Real.log (4 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  simp only [Icc_self, sum_singleton, ite_true, Nat.cast_one]
  rw [hK]
  nlinarith

/-- **The positive cone makes the axioms circular**: its ampleness is RH. -/
theorem rh_iff_ample_pos : RiemannHypothesis ↔
    ∀ (a b : ℝ) (N : ℕ) (c : ℕ → ℝ), 0 < selfInt a b N c → dotH a b N c ≠ 0 := by
  rw [rh_iff_hodge_h]
  refine ⟨fun H a b N c hpos hd => absurd (H a b N c hd) (not_le.2 hpos), fun H a b N c hd => ?_⟩
  by_contra hpos
  exact H a b N c (lt_of_not_ge hpos) hd

end HodgeAxioms

#print axioms HodgeAxioms.hodge_index
#print axioms HodgeAxioms.hodge_cs
#print axioms HodgeAxioms.rh_iff_hodge_h
#print axioms HodgeAxioms.ample_naive
#print axioms HodgeAxioms.rr_fails_naive
#print axioms HodgeAxioms.rh_iff_ample_pos
