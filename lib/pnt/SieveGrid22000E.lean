/-
# The grid of the certificate to depth 8 at `L = 11/5` with `n = 272`

The grid of `SieveTypeIIU22000D.typeII_22000d`'s window: `U1 = ⌈(43457/100000)DEN⌉`, `U2 = ⌊(46959/100000)DEN⌋`, `n
= 272` (`grid22000E`, `gridOK22000E`, `gridOKC22000E`), the window `route_limits.window` and `route_limits.corners`
give for `g7d` at `11/5`, and the bilinear Type I rule's exponent `11/5` (`ibPar22000E`). Its certificate to depth 8
(`SieveDeepDefs.totalD`) is checked by the kernel in 1136 parts, 114 files (`SieveCert22000EP1.lean` …
`SieveCert22000EP114.lean`, one `lean` process each): ranges of consecutive rows, and the 197 heavy rows in column
pieces (`SieveDeepDefs.rowsJD`); assembled in `SieveCert22000E.lean`.

The file imports `SieveDeepDefs.lean`, which imports `SieveRuleDefs.lean` only; so neither it nor the part files load
more of `Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveDeepDefs

namespace SieveCert

/-- **The grid at `L = 11/5` with `n = 272`**: `U1 = ⌈(43457/100000)DEN⌉`, `U2 = ⌊(46959/100000)DEN⌋`,
multiplier `1`. -/
@[instance_reducible] def grid22000E : Grid := ⟨(43457 * DEN + 99999) / 100000, 46959 * DEN / 100000, 272, 1⟩

theorem gridOK22000E : @GridOK grid22000E :=
  @GridOK.mk grid22000E (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The coarse grid `Gc` (`n / 4 = 68` cells) and the facts about it that the deepest levels use. -/
theorem gridOKC22000E : @GridOKC grid22000E :=
  @GridOKC.mk grid22000E
    (@GridOK.mk (@Gc grid22000E) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide)

/-- **The bilinear Type I rule's exponent** at `L = 11/5`: `11/5`. -/
@[instance_reducible] def ibPar22000E : IBPar := ⟨11, 5⟩

end SieveCert

#print axioms SieveCert.gridOK22000E
#print axioms SieveCert.gridOKC22000E
