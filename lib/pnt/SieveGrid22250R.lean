/-
# The grid of the refined certificate at `L = 89/40` with `n = 340`

The grid of `SieveTypeIIU22250D.typeII_22250d`'s window: `U1 = ⌈(41479/100000)DEN⌉`, `U2 = ⌊(47555/100000)DEN⌋`,
`n = 340` (`grid22250R`, `gridOK22250R`), the window of `tools/linnik/route_limits.jsonl`'s rows for `g7d` at
`89/40`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 4715 parts, 351 files
(`SieveCert22250RP1.lean` … `SieveCert22250RP351.lean`, one `lean` process each): ranges of consecutive rows, and the
187 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22250R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib`.
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 89/40` with `n = 340`**: `U1 = ⌈(41479/100000)DEN⌉`, `U2 = ⌊(47555/100000)DEN⌋`. -/
@[instance_reducible] def grid22250R : Grid := ⟨(41479 * DEN + 99999) / 100000, 47555 * DEN / 100000, 340⟩

theorem gridOK22250R : @GridOK grid22250R :=
  @GridOK.mk grid22250R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The coarse grid `Gc` (`n / 4 = 85` cells) and the facts about it that the deepest levels use. -/
theorem gridOKC22250R : @GridOKC grid22250R :=
  @GridOKC.mk grid22250R
    (@GridOK.mk (@Gc grid22250R) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22250R
#print axioms SieveCert.gridOKC22250R
