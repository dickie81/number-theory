/-
# The grid of the refined certificate at `L = 2231/1000` with `n = 400`

The grid of `SieveTypeIIU22310D.typeII_22310d`'s window: `U1 = ⌈(41046/100000)DEN⌉`, `U2 = ⌊(47698/100000)DEN⌋`,
`n = 400` (`grid22310R`, `gridOK22310R`), the window of `tools/linnik/route_limits.jsonl`'s rows for `g7d` at
`2231/1000`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 1732 parts, 430 files
(`SieveCert22310RP1.lean` … `SieveCert22310RP430.lean`, one `lean` process each): ranges of consecutive rows, and the
187 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22310R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib`.
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 2231/1000` with `n = 400`**: `U1 = ⌈(41046/100000)DEN⌉`, `U2 = ⌊(47698/100000)DEN⌋`. -/
@[instance_reducible] def grid22310R : Grid := ⟨(41046 * DEN + 99999) / 100000, 47698 * DEN / 100000, 400⟩

theorem gridOK22310R : @GridOK grid22310R :=
  @GridOK.mk grid22310R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22310R
