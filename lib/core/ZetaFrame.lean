import ZetaGap
import SlopeFrame

/-!
# From lattices to the inert-prime gap

A step of the library's proof of the Riemann hypothesis for `ζ` and every Dirichlet `L`-function
(`docs/rh-rebuild.md`, step 4): the algebra of the archive's `ch_top`. At each translate `u` in the kernel `A₀` of a
character `κ` of `A`, a frame of lattices (`SlopeFrame.Frame`) has a mean slope `s_u` and a frame loss `L_u` with
`s_u − μ(C_u) ≤ L_u`: the conclusion of the frame inequality, which bounds the slope `μ(C_u)` of its target from
below. Two conditions finish:

* **(G)**: `Σ_{u ∈ A₀} gap(u) ≤ Σ_{u ∈ A₀} (s_u − μ(C_u)) + E`, the gain of the lattices over their targets covers the
  gap;
* **(Z)**: `E + Σ_{u ∈ A₀} L_u ≤ |A₀|·x^{4ε}·Σ_t a_t`, the losses are small.

Then the gap averaged over `A₀` is at most `x^{4ε} Σ_t a_t`, which gives balance data (`LatticeData.toBalanceData`).
Frames are needed only at `u ∈ A₀`. With the analytic inputs (`Setting.Thin`, `Setting.Twists`) it gives the Riemann
hypothesis from data for `κ = 1` (`riemannHypothesis_of_zetaLatticeBound`), and the Riemann hypothesis for `ζ` and
every Dirichlet `L`-function from data for a `κ` lifting each primitive `χ` (`rhAndGRH_of_latticeBound`).

**The frame inequality enters through its conclusion.** The reduction reads only `s_u − μ(C_u) ≤ L_u`, so lattice data
carry that inequality (`LatticeData.frame_le`), not the hypotheses of the frame inequality. A frame that meets those
hypotheses (`SlopeFrame.Frame.Spread`, with range `U`, depth `H` and spreading constants `α`, `β`) gives it with
`L_u = αH + βU log(1 + H/U)` (`SlopeFrame.Frame.Spread.frame_le`). A construction may bound the loss more cheaply,
for instance for a frame of one word.

**What these frontiers mean.** Like every frontier of the rebuild, `ZetaLatticeBound` and `LatticeBound` are
equivalent to what they prove until the construction is formalised. More than that: whenever the averaged gap bound
holds, frames of one word of rank one satisfy them, with `E` the gap and no loss. Their content is the shape of the
argument: the gap is paid for by slopes of lattices, through Bost's inequality and the frame loss. Euclidean lattices
give frames (`EuclidLattice.frame`). The construction must supply (G) from vanishing at inert primes, and (Z) from the
sizes of its lattices.
-/

namespace SlopeFrame

/-- **The frame inequality as a frame loss**: a frame that meets the hypotheses of the frame inequality at `s`, with
range `U`, depth `H` and constants `α`, `β`, has `s − μ(C) ≤ αH + βU log(1 + H/U)` (`Frame.Spread.loss_le`), the
clause `LatticeData.frame_le` with that loss. -/
theorem Frame.Spread.frame_le {F : Frame} {s U H α β : ℝ} (h : F.Spread s U H α β) :
    s - F.C.deg ⊤ / F.C.rk ⊤ ≤ α * H + β * U * Real.log (1 + H / U) := by
  linarith [h.loss_le]

end SlopeFrame

namespace ZetaBalance

open SlopeFrame

/-- **Lattice data at `x`**: weights for the kernel `A₀` of `κ` and, at each translate `u ∈ A₀`, a frame with a mean
slope `s_u` and a loss `L_u` bounding `s_u − μ(C_u)` (the conclusion of the frame inequality), whose gain covers the
gap (G) with small losses (Z). -/
structure LatticeData (S : Setting) (κ : S.A →* ℂˣ) (x ε X : ℝ) extends Weights S κ x ε X where
  /-- The frame at each translate. -/
  frame : S.A → Frame
  /-- The mean slopes `s_u`. -/
  s : S.A → ℝ
  /-- The frame losses `L_u`. -/
  L : S.A → ℝ
  /-- The error in the gain. -/
  E : ℝ
  /-- **The frame loss** at each translate of `A₀`: `s_u − μ(C_u) ≤ L_u`, the conclusion of the frame inequality
  (`Frame.Spread.frame_le`). -/
  frame_le : ∀ u ∈ A₀ κ, s u - (frame u).C.deg ⊤ / (frame u).C.rk ⊤ ≤ L u
  /-- **(G)**: the gain of the lattices over their targets covers the gap. -/
  gain : ∑ u ∈ A₀ κ, S.gap TT m a w u ≤ ∑ u ∈ A₀ κ, (s u - (frame u).C.deg ⊤ / (frame u).C.rk ⊤) + E
  /-- **(Z)**: the losses are small. -/
  sizes : E + ∑ u ∈ A₀ κ, L u ≤ (A₀ κ).card * x ^ (4 * ε) * ∑ t ∈ TT, a t

/-- **The frame losses at each translate give the averaged gap bound.** -/
def LatticeData.toBalanceData {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (D : LatticeData S κ x ε X) :
    BalanceData S κ x ε X where
  toWeights := D.toWeights
  gap_le := by
    calc ∑ u ∈ A₀ κ, S.gap D.TT D.m D.a D.w u
        ≤ ∑ u ∈ A₀ κ, (D.s u - (D.frame u).C.deg ⊤ / (D.frame u).C.rk ⊤) + D.E := D.gain
      _ ≤ ∑ u ∈ A₀ κ, D.L u + D.E := by gcongr with u hu; exact D.frame_le u hu
      _ ≤ _ := by linarith [D.sizes]

/-- **The frontier for `ζ` after step 4**: for every `ε > 0`, at every `x` of windows `[Y, Y^λ]` with `Y` arbitrarily
large, a setting thin at some `X`, with small twists, and lattice data for `κ = 1`. -/
def ZetaLatticeBound : Prop :=
  ∀ ε > 0, ∃ lam > (1 : ℝ), ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Set.Icc Y (Y ^ lam),
    ∃ (S : Setting) (X : ℝ), S.Thin x X ∧ S.Twists 1 x ε ∧ Nonempty (LatticeData S 1 x ε X)

/-- **The Riemann hypothesis from lattice data on windows.** -/
theorem riemannHypothesis_of_zetaLatticeBound (h : ZetaLatticeBound) : RiemannHypothesis :=
  riemannHypothesis_of_zetaBalanceBound fun ε hε => by
    obtain ⟨lam, hlam, hY⟩ := h ε hε
    refine ⟨lam, hlam, fun Y₀ => ?_⟩
    obtain ⟨Y, hY₀, hx⟩ := hY Y₀
    refine ⟨Y, hY₀, fun x hxY => ?_⟩
    obtain ⟨S, X, hthin, htw, hD⟩ := hx x hxY
    exact ⟨S, X, hthin, htw, hD.map LatticeData.toBalanceData⟩

/-- **The frontier for every primitive character after step 4**: for every primitive `χ` and `ε > 0`, at every `x`
of windows `[Y, Y^λ]` with `Y` arbitrarily large, a setting with a character `κ` of `A` lifting `χ`
(`Setting.Lifts`), thin at some `X`, with small twists, and lattice data. For `χ = 1` it is `ZetaLatticeBound`. -/
def LatticeBound : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε > 0, ∃ lam > (1 : ℝ), ∀ Y₀ : ℝ,
    ∃ Y ≥ Y₀, ∀ x ∈ Set.Icc Y (Y ^ lam), ∃ (S : Setting) (κ : S.A →* ℂˣ) (X : ℝ), S.Lifts κ χ ∧ S.Thin x X ∧
      S.Twists κ x ε ∧ Nonempty (LatticeData S κ x ε X)

/-- **The Riemann hypothesis for `ζ` and every Dirichlet `L`-function from lattice data on windows**, for every
primitive character. -/
theorem rhAndGRH_of_latticeBound (h : LatticeBound) : HalfPlaneGRH.RHandGRH :=
  rhAndGRH_of_balanceBound fun f _ χ hχ ε hε => by
    obtain ⟨lam, hlam, hY⟩ := h f χ hχ ε hε
    refine ⟨lam, hlam, fun Y₀ => ?_⟩
    obtain ⟨Y, hY₀, hx⟩ := hY Y₀
    refine ⟨Y, hY₀, fun x hxY => ?_⟩
    obtain ⟨S, κ, X, hL, hthin, htw, hD⟩ := hx x hxY
    exact ⟨S, κ, X, hL, hthin, htw, hD.map LatticeData.toBalanceData⟩

end ZetaBalance

#print axioms ZetaBalance.riemannHypothesis_of_zetaLatticeBound
#print axioms ZetaBalance.rhAndGRH_of_latticeBound
