import SharpInputs
import HermFinite

/-!
# The pieces of the sharp frontier that are proved

The proof of the sharp frontier `ZetaBalance.SharpBoundPinned` is organised by `ZetaBalance.sharpBoundPinned_of_inputs`
(`SharpInputs`): the deep classical inputs as hypotheses (`ZetaBalance.SharpInputs`), and the statements to prove in
the library (`ZetaBalance.SharpPieces`). This module collects the pieces that are proved.

* `finiteClasses_proved`: the piece `ZetaBalance.FiniteClasses`. The decorated unimodular hermitian lattices of every
  rank and level fall into finitely many classes, each with a finite stabiliser (`HermClasses.finite_DCl`,
  `HermClasses.finite_stab`, in `HermFinite`, by Minkowski's theorem and a covolume bound through the trace dual).
-/

namespace ZetaBalance

/-- **The piece `FiniteClasses`, proved**: finitely many classes of decorated unimodular hermitian lattices, each
with a finite stabiliser (`HermClasses.finite_DCl`, `HermClasses.finite_stab`). -/
theorem finiteClasses_proved : FiniteClasses := fun E _ _ _ n ST SG Λ =>
  ⟨HermClasses.finite_DCl E n ST SG Λ, HermClasses.finite_stab E n ST SG Λ⟩

end ZetaBalance
