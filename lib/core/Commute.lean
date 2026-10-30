import Mathlib
import GapCriterion

/-! # Weil's form commutes with `∂²` (Theorem B, formal)

For `C²` functions `f, k` supported in `[−a, a]` (with `f, f'` vanishing outside):

* `xcorr_deriv2`: `xcorr(f'', k)(u) = xcorr(f, k'')(u)` for every shift `u`, by two integrations by parts;
* `bil0_deriv2`: hence `B₀(f'', k) = B₀(f, k'')` for the pole-free bilinear form (constant, archimedean and
  prime terms are all functionals of the cross-correlation);
* `poleR_deriv2`: `poleR(f'') = ¼·poleR(f)`, because `(e^{−u/2})'' = ¼e^{−u/2}`, i.e. `(i/2)² = −¼` is real;
* `bilQ_deriv2`: the full bilinear form of `Q` satisfies `B(f'', k) = B(f, k'')`.

Theorem C itself (flat ⇒ degenerate) is proved in `H²` generality in TheoremC.lean, where the smooth
form `simple_not_flat` is derived as a corollary.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace WeilForm

/-- `f` is `C²` with derivatives `f₁, f₂`, and `f, f₁, f₂` vanish outside `[−r, r]`. -/
structure C2Supp (r : ℝ) (f f₁ f₂ : ℝ → ℝ) : Prop where
  d1 : ∀ x, HasDerivAt f (f₁ x) x
  d2 : ∀ x, HasDerivAt f₁ (f₂ x) x
  cont2 : Continuous f₂
  supp : ∀ x, r < |x| → f x = 0
  supp1 : ∀ x, r < |x| → f₁ x = 0
  supp2 : ∀ x, r < |x| → f₂ x = 0

/-- `g` is `C²` with derivatives `g₁, g₂` (no support condition). -/
structure C2Fun (g g₁ g₂ : ℝ → ℝ) : Prop where
  d1 : ∀ x, HasDerivAt g (g₁ x) x
  d2 : ∀ x, HasDerivAt g₁ (g₂ x) x
  cont2 : Continuous g₂

theorem C2Supp.toC2Fun {r : ℝ} {f f₁ f₂ : ℝ → ℝ} (h : C2Supp r f f₁ f₂) : C2Fun f f₁ f₂ :=
  ⟨h.d1, h.d2, h.cont2⟩

theorem C2Fun.cont1 {g g₁ g₂ : ℝ → ℝ} (h : C2Fun g g₁ g₂) : Continuous g₁ :=
  continuous_iff_continuousAt.2 fun x => (h.d2 x).continuousAt

/-! ## Flat ground states force a second ground state (Theorem C, smooth form) -/

theorem weilQ0_eq_bil0 {a : ℝ} {f : ℝ → ℝ} (hf : Probe a f) : weilQ0 a f = bil0 a f f := by
  have e := weilQ0_add_smul hf hf 1
  have e2 : (fun t => f t + 1 * f t) = fun t => (2 : ℝ) * f t := by funext t; ring
  rw [e2, weilQ0_smul] at e
  linarith

theorem normSq_eq_xcorr {f : ℝ → ℝ} (hf : MemLp f 2 volume) : normSq f = xcorr f f 0 := by
  have e := normSq_add_smul hf hf 1
  have e2 : (fun t => f t + 1 * f t) = fun t => (2 : ℝ) * f t := by funext t; ring
  rw [e2, normSq_smul] at e
  linarith

end WeilForm
