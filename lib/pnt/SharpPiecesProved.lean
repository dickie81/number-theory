import SharpInputs
import HermFinite
import HermFormsLattice

/-!
# The pieces of the sharp frontier that are proved

The proof of the sharp frontier `ZetaBalance.SharpBoundPinned` is organised by `ZetaBalance.sharpBoundPinned_of_inputs`
(`SharpInputs`): the deep classical inputs as hypotheses (`ZetaBalance.SharpInputs`), and the statements to prove in
the library (`ZetaBalance.SharpPieces`). This module collects the pieces that are proved.

* `finiteClasses_proved`: the piece `ZetaBalance.FiniteClasses`. The decorated unimodular hermitian lattices of every
  rank and level fall into finitely many classes, each with a finite stabiliser (`HermClasses.finite_DCl`,
  `HermClasses.finite_stab`, in `HermFinite`, by Minkowski's theorem and a covolume bound through the trace dual).
* `formsLattice_proved`: the piece `ZetaBalance.FormsLattice`. For an antitone weight, the forms are
  finite-dimensional, the integral forms of the cut are a lattice, and the Gram matrix of the Petersson form is positive
  definite at every complex place (`HermForms.formsLattice`, in `HermFormsLattice`, from `WeylFock.span_bidet` and
  the finiteness of the classes and stabilisers).
-/

namespace ZetaBalance

/-- **The piece `FiniteClasses`, proved**: finitely many classes of decorated unimodular hermitian lattices, each
with a finite stabiliser (`HermClasses.finite_DCl`, `HermClasses.finite_stab`). -/
theorem finiteClasses_proved : FiniteClasses := fun E _ _ _ n ST SG Λ =>
  ⟨HermClasses.finite_DCl E n ST SG Λ, HermClasses.finite_stab E n ST SG Λ⟩

/-- **The piece `FormsLattice`, proved**: the forms finite-dimensional, the integral forms of the cut a lattice, the
Petersson form positive definite at every complex place (`HermForms.formsLattice`). -/
theorem formsLattice_proved : FormsLattice := fun E _ _ _ n ST SG Λ Φ _ _ L _ _ τ χ lam hlam =>
  HermForms.formsLattice E n ST SG Λ Φ L τ χ lam hlam

end ZetaBalance
