import RHClaim

/-!
# The bridge file on the archive's pins

`RHClaim.lean` and the 346 modules of the library behind it, compiled on Lean `v4.33.1` and the Mathlib of
21 August 2026 (`tools/rh/README.md`, "What joining it to the library needs"). Each of its theorems is still
conditional here, on `RiemannHypothesis` or on `RHClaim.DirichletRH`. This file is an error unless each depends
on the three standard axioms only: that no proof of the port failed and was kept as `sorry`.
-/

#assert_standard_axioms RHClaim.zetaZerosOnLine RHClaim.lfunction_ne_zero_of_half_lt
  RHClaim.primitive_zeros_on_line RHClaim.grh_char RHClaim.zeta_ne_zero_of_half_lt RHClaim.psi RHClaim.mertens
  RHClaim.divisor RHClaim.squarefree RHClaim.lindelof RHClaim.densityHypothesis RHClaim.pivot_ge
  RHClaim.orbitLattice RHClaim.shortest RHClaim.balance RHClaim.psiChi RHClaim.linnik_two
