/-
# The grid of the refined certificate at `L = 893/400` with `n = 300`

The grid of `SieveTypeIIU22325D.typeII_22325d`'s window: `U1 = ⌈(40980/100000)DEN⌉`, `U2 = ⌊(47731/100000)DEN⌋`,
`n = 300` (`grid22325R`, `gridOK22325R`), the window of `tools/linnik/route_limits.jsonl`'s rows for `g7d` at
`893/400`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 561 parts, 142 files
(`SieveCert22325RP1.lean` … `SieveCert22325RP142.lean`, one `lean` process each): ranges of consecutive rows, and the
119 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22325R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib`.
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 893/400` with `n = 300`**: `U1 = ⌈(40980/100000)DEN⌉`, `U2 = ⌊(47731/100000)DEN⌋`. -/
@[instance_reducible] def grid22325R : Grid := ⟨(40980 * DEN + 99999) / 100000, 47731 * DEN / 100000, 300⟩

theorem gridOK22325R : @GridOK grid22325R :=
  @GridOK.mk grid22325R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22325R
