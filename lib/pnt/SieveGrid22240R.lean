/-
# The grid of the refined certificate at `L = 278/125` with `n = 340`

The grid of `SieveTypeIIU22240D.typeII_22240d`'s window: `U1 = ⌈(41556/100000)DEN⌉`, `U2 = ⌊(47531/100000)DEN⌋`,
`n = 340` (`grid22240R`, `gridOK22240R`), the window of `tools/linnik/route_limits.jsonl`'s rows for `g7d` at
`278/125`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 5066 parts, 387 files
(`SieveCert22240RP1.lean` … `SieveCert22240RP387.lean`, one `lean` process each): ranges of consecutive rows, and the
188 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22240R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, which imports only
`Mathlib.Data.Nat.Notation` from `Mathlib`; so neither it nor the part files load the rest of `Mathlib`.
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 278/125` with `n = 340`**: `U1 = ⌈(41556/100000)DEN⌉`, `U2 = ⌊(47531/100000)DEN⌋`,
multiplier `1`. -/
@[instance_reducible] def grid22240R : Grid := ⟨(41556 * DEN + 99999) / 100000, 47531 * DEN / 100000, 340, 1⟩

theorem gridOK22240R : @GridOK grid22240R :=
  @GridOK.mk grid22240R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The coarse grid `Gc` (`n / 4 = 85` cells) and the facts about it that the deepest levels use. -/
theorem gridOKC22240R : @GridOKC grid22240R :=
  @GridOKC.mk grid22240R
    (@GridOK.mk (@Gc grid22240R) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22240R
#print axioms SieveCert.gridOKC22240R
