/-
# The grid of the refined certificate at `L = 11161/5000` with `n = 300`

The grid of `SieveTypeIIU22322D.typeII_22322d`'s window: `U1 = ⌈(40981/100000)DEN⌉`, `U2 = ⌊(47725/100000)DEN⌋`,
`n = 300` (`grid22322R`, `gridOK22322R`), the window of `tools/linnik/route_limits.jsonl`'s rows for `g7d` at
`11161/5000`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 561 parts, 143 files
(`SieveCert22322RP1.lean` … `SieveCert22322RP143.lean`, one `lean` process each): ranges of consecutive rows, and the
119 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22322R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib`.
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 11161/5000` with `n = 300`**: `U1 = ⌈(40981/100000)DEN⌉`, `U2 = ⌊(47725/100000)DEN⌋`. -/
@[instance_reducible] def grid22322R : Grid := ⟨(40981 * DEN + 99999) / 100000, 47725 * DEN / 100000, 300⟩

theorem gridOK22322R : @GridOK grid22322R :=
  @GridOK.mk grid22322R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22322R
