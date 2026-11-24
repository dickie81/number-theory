import ZetaGap
import SlopeFrame

/-!
# From lattices to the inert-prime gap

A step of the library's proof of the Riemann hypothesis for `ζ` and every Dirichlet `L`-function
(`docs/rh-rebuild.md`, step 4): the algebra of the archive's `ch_top`. At each translate `u` in the kernel `A₀` of a
character `κ` of `A`, a frame of lattices (`SlopeFrame.Frame`) that meets the hypotheses of the frame inequality
(`SlopeFrame.Frame.Spread`) bounds the slope `μ(C_u)` of its target from below. Two conditions finish:

* **(G)**: `Σ_{u ∈ A₀} gap(u) ≤ Σ_{u ∈ A₀} (s_u − μ(C_u)) + E`, the gain of the lattices over their targets covers the
  gap;
* **(Z)**: `E + Σ_{u ∈ A₀} (α_u H_u + β_u U_u log(1 + H_u/U_u)) ≤ |A₀|·x^ε·Σ_t a_t`, the losses are small.

Then the gap averaged over `A₀` is at most `x^ε Σ_t a_t`, which gives balance data (`LatticeData.toBalanceData`).
Frames are needed only at `u ∈ A₀`. With the analytic inputs (`Setting.Thin`, `Setting.Twists`) it gives the Riemann
hypothesis from data for `κ = 1` (`riemannHypothesis_of_zetaLatticeBound`), and the Riemann hypothesis for `ζ` and
every Dirichlet `L`-function from data for a `κ` lifting each primitive `χ` (`rhAndGRH_of_latticeBound`).

**What these frontiers mean.** Like every frontier of the rebuild, `ZetaLatticeBound` and `LatticeBound` are
equivalent to what they prove until the construction is formalised. More than that: whenever the averaged gap bound
holds, frames of one word of rank one satisfy them, with `E` the gap. Their content is the shape of the argument: the
gap is paid for by slopes of lattices, through Bost's inequality and the frame inequality. Euclidean lattices give
frames (`EuclidLattice.frame`). The construction must supply (G) from vanishing at inert primes, and (Z) from the sizes
of its lattices.
-/

namespace ZetaBalance

open SlopeFrame

/-- **Lattice data at `x`**: weights for the kernel `A₀` of `κ` and, at each translate `u ∈ A₀`, a frame that meets
the hypotheses of the frame inequality, whose gain covers the gap (G) with small losses (Z). -/
structure LatticeData (S : Setting) (κ : S.A →* ℂˣ) (x ε X : ℝ) extends Weights S κ x ε X where
  /-- The frame at each translate. -/
  frame : S.A → Frame
  /-- The mean slopes `s_u`. -/
  s : S.A → ℝ
  /-- The ranges `U_u`. -/
  U : S.A → ℝ
  /-- The depths `H_u`. -/
  H : S.A → ℝ
  /-- The fixed spreading losses `α_u`. -/
  α : S.A → ℝ
  /-- The spreading slopes `β_u`. -/
  β : S.A → ℝ
  /-- The error in the gain. -/
  E : ℝ
  /-- The hypotheses of the frame inequality at each translate of `A₀`. -/
  spread : ∀ u ∈ A₀ κ, (frame u).Spread (s u) (U u) (H u) (α u) (β u)
  /-- **(G)**: the gain of the lattices over their targets covers the gap. -/
  gain : ∑ u ∈ A₀ κ, S.gap TT m a w u ≤ ∑ u ∈ A₀ κ, (s u - (frame u).C.deg ⊤ / (frame u).C.rk ⊤) + E
  /-- **(Z)**: the losses are small. -/
  sizes : E + ∑ u ∈ A₀ κ, (α u * H u + β u * U u * Real.log (1 + H u / U u)) ≤
    (A₀ κ).card * x ^ ε * ∑ t ∈ TT, a t

/-- **The frame inequality at each translate gives the averaged gap bound.** -/
def LatticeData.toBalanceData {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (D : LatticeData S κ x ε X) :
    BalanceData S κ x ε X where
  toWeights := D.toWeights
  gap_le := by
    have h u hu := (D.spread u hu).loss_le
    calc ∑ u ∈ A₀ κ, S.gap D.TT D.m D.a D.w u
        ≤ ∑ u ∈ A₀ κ, (D.s u - (D.frame u).C.deg ⊤ / (D.frame u).C.rk ⊤) + D.E := D.gain
      _ ≤ ∑ u ∈ A₀ κ, (D.α u * D.H u + D.β u * D.U u * Real.log (1 + D.H u / D.U u)) + D.E := by
          gcongr with u hu
          linarith [h u hu]
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
