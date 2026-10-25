/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1480–1483 of 1732

File 372 of 430: the parts `rows22310R_1480` … `rows22310R_1483` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27847 tests: row 177 columns 58–61, row 177 columns 62–65, row 177 columns
66–70, row 177 columns 71–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1480 : rowsJ2 177 178 58 62 ≤ 38000311990633 := by decide +kernel

theorem rows22310R_1481 : rowsJ2 177 178 62 66 ≤ 31512319495288 := by decide +kernel

theorem rows22310R_1482 : rowsJ2 177 178 66 71 ≤ 23705924011527 := by decide +kernel

theorem rows22310R_1483 : rowsJ2 177 178 71 77 ≤ 12291685410825 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1480
#print axioms SieveCert.rows22310R_1483
