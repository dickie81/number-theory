import HalfPlaneGRH
import LinnikGRH

/-!
# The rebuild's Riemann hypothesis, in the words of the Linnik results

A join between the library's rebuild of L. Alpöge's proof (`docs/rh-rebuild.md`) and its results under GRH. The
rebuild ends in `HalfPlaneGRH.RHandGRH`: the Riemann hypothesis for `ζ` and for the `L`-function of every Dirichlet
character, primitive or not. `HalfPlaneGRH` itself passes from the primitive characters to the others, whose
`L`-functions differ by Euler factors with no zero on `Re s > 0`. So `RHandGRH` gives `LinnikGRH.DirichletRH`, the
hypothesis of `LinnikGRH.linnik_two` and `LinnikAlmostAll.almostAll_one`, with its hypotheses in another order
(`LinnikGRH.dirichletRH_of_rhAndGRH`). With `ZetaBalance.rhAndGRH_of_pairBound`, the rebuild's frontier
`ZetaBalance.PairBound` gives those results, conditionally on the half-plane `Re s > 11/12`.
-/

namespace LinnikGRH

/-- **GRH from the rebuild, in the archive's words**: `HalfPlaneGRH.RHandGRH`, which covers every Dirichlet character,
gives `DirichletRH`. -/
theorem dirichletRH_of_rhAndGRH (h : HalfPlaneGRH.RHandGRH) : DirichletRH :=
  fun N _ χ s h0 h1 hz => h.2 N χ s hz h0 h1

end LinnikGRH

#print axioms LinnikGRH.dirichletRH_of_rhAndGRH
