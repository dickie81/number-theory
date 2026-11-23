import ZetaGap
import SlopeFrame

/-!
# From lattices to the inert-prime gap

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 4): the algebra of the archive's
`ch_top`. At each translate `u ∈ A`, a frame of lattices (`SlopeFrame.Frame`) that meets the hypotheses of the frame
inequality (`SlopeFrame.Frame.Spread`) bounds the slope `μ(C_u)` of its target from below. Two conditions finish:

* **(G)**: `Σ_u gap(u) ≤ Σ_u (s_u − μ(C_u)) + E`, the gain of the lattices over their targets covers the gap;
* **(Z)**: `E + Σ_u (α_u H_u + β_u U_u log(1 + H_u/U_u)) ≤ |A|·x^ε·Σ_t a_t`, the losses are small.

Then the gap averaged over translates is at most `x^ε Σ_t a_t`, which gives balance data
(`LatticeData.toBalanceData`). With the analytic inputs (`Setting.Thin`, `Setting.Twists`) it gives the Riemann
hypothesis (`riemannHypothesis_of_zetaLatticeBound`).

**What this frontier means.** Like every frontier of the rebuild, `ZetaLatticeBound` is equivalent to RH until the
construction is formalised. More than that: whenever the averaged gap bound holds, frames of one word of rank one
satisfy it, with `E` the gap. Its content is the shape of the argument: the gap is paid for by slopes of lattices,
through Bost's inequality and the frame inequality. Euclidean lattices give frames (`EuclidLattice.frame`). The
construction must supply (G) from vanishing at inert primes, and (Z) from the sizes of its lattices.
-/

namespace ZetaBalance

open SlopeFrame

/-- **Lattice data for `ζ` at `x`**: weights and, at each translate `u`, a frame that meets the hypotheses of the
frame inequality, whose gain covers the gap (G) with small losses (Z). -/
structure LatticeData (S : Setting) (x ε X : ℝ) extends Weights S x ε X where
  /-- The frame at each translate. -/
  frame : A S.e → Frame
  /-- The mean slopes `s_u`. -/
  s : A S.e → ℝ
  /-- The ranges `U_u`. -/
  U : A S.e → ℝ
  /-- The depths `H_u`. -/
  H : A S.e → ℝ
  /-- The fixed spreading losses `α_u`. -/
  α : A S.e → ℝ
  /-- The spreading slopes `β_u`. -/
  β : A S.e → ℝ
  /-- The error in the gain. -/
  E : ℝ
  /-- The hypotheses of the frame inequality at each translate. -/
  spread : ∀ u, (frame u).Spread (s u) (U u) (H u) (α u) (β u)
  /-- **(G)**: the gain of the lattices over their targets covers the gap. -/
  gain : ∑ u, S.gap TT m a w u ≤ ∑ u, (s u - (frame u).C.deg ⊤ / (frame u).C.rk ⊤) + E
  /-- **(Z)**: the losses are small. -/
  sizes : E + ∑ u, (α u * H u + β u * U u * Real.log (1 + H u / U u)) ≤
    Fintype.card (A S.e) * x ^ ε * ∑ t ∈ TT, a t

/-- **The frame inequality at each translate gives the averaged gap bound.** -/
def LatticeData.toBalanceData {S : Setting} {x ε X : ℝ} (D : LatticeData S x ε X) : BalanceData S x ε X where
  toWeights := D.toWeights
  gap_le := by
    have h u := (D.spread u).loss_le
    calc ∑ u, S.gap D.TT D.m D.a D.w u
        ≤ ∑ u, (D.s u - (D.frame u).C.deg ⊤ / (D.frame u).C.rk ⊤) + D.E := D.gain
      _ ≤ ∑ u, (D.α u * D.H u + D.β u * D.U u * Real.log (1 + D.H u / D.U u)) + D.E := by
          gcongr with u
          linarith [h u]
      _ ≤ _ := by linarith [D.sizes]

/-- **The frontier for `ζ` after step 4**: for every `ε > 0`, at every `x` of windows `[Y, Y^λ]` with `Y` arbitrarily
large, a setting thin at some `X`, with small twists, and lattice data. -/
def ZetaLatticeBound : Prop :=
  ∀ ε > 0, ∃ lam > (1 : ℝ), ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Set.Icc Y (Y ^ lam),
    ∃ (S : Setting) (X : ℝ), S.Thin x X ∧ S.Twists x ε ∧ Nonempty (LatticeData S x ε X)

/-- **The Riemann hypothesis from lattice data on windows.** -/
theorem riemannHypothesis_of_zetaLatticeBound (h : ZetaLatticeBound) : RiemannHypothesis :=
  riemannHypothesis_of_zetaBalanceBound fun ε hε => by
    obtain ⟨lam, hlam, hY⟩ := h ε hε
    refine ⟨lam, hlam, fun Y₀ => ?_⟩
    obtain ⟨Y, hY₀, hx⟩ := hY Y₀
    refine ⟨Y, hY₀, fun x hxY => ?_⟩
    obtain ⟨S, X, hthin, htw, hD⟩ := hx x hxY
    exact ⟨S, X, hthin, htw, hD.map LatticeData.toBalanceData⟩

end ZetaBalance

#print axioms ZetaBalance.riemannHypothesis_of_zetaLatticeBound
