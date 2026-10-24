/-
# The grid of the refined certificate at `L = 4467/2000` with `n = 300`

The grid of `SieveTypeIIU22335D.typeII_22335d`'s window: `U1 = ⌈(40993/100000)DEN⌉`, `U2 = ⌊(47746/100000)DEN⌋`,
`n = 300` (`grid22335R`, `gridOK22335R`), the window of `tools/linnik/route_limits.jsonl`'s rows for `g7d` at
`4467/2000`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 549 parts, 140 files
(`SieveCert22335RP1.lean` … `SieveCert22335RP140.lean`, one `lean` process each): ranges of consecutive rows, and the
119 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22335R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib`.
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 4467/2000` with `n = 300`**: `U1 = ⌈(40993/100000)DEN⌉`, `U2 = ⌊(47746/100000)DEN⌋`. -/
@[instance_reducible] def grid22335R : Grid := ⟨(40993 * DEN + 99999) / 100000, 47746 * DEN / 100000, 300⟩

theorem gridOK22335R : @GridOK grid22335R :=
  @GridOK.mk grid22335R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22335R
