import SieveHint21500P1
import AxiomTools

/-!
# The axioms of the library's own certificates

The Linnik paper's Theorem 1.2 rests on 1552 kernel computations, the parts `SieveAd.tree21500_k`, each proved
by `decide +kernel` on natural numbers. This file asks what axioms one of them depends on, and through what.

It needs the library's module `SieveHint21500P1` (four minutes of the kernel), so `check.sh` does not run it:

    lake build SieveHint21500P1
    scratch/axiomless/check.sh
    LEAN_PATH="$(lake env printenv LEAN_PATH):scratch/axiomless/build" lean scratch/axiomless/CertAxioms.lean

Its output is in LOG.md, entry 11.
-/

#print axioms SieveAd.tree21500_0
#why SieveAd.tree21500_0
#entries SieveAd.tree21500_0
#without SieveAd.tree21500_0 Nat.bitwise
#without SieveAd.tree21500_0 Nat.div_lt_self

/-! Core's bitwise operations on `Nat` are definitions that depend on `propext`. -/
#why Nat.land
#why Nat.lor
#why Nat.xor
#why Nat.testBit
