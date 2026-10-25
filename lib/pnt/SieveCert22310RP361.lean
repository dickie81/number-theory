/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1436–1439 of 1732

File 361 of 430: the parts `rows22310R_1436` … `rows22310R_1439` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28482 tests: row 171 columns 59–62, row 171 columns 63–66, row 171 columns
67–70, row 171 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1436 : rowsJ2 171 172 59 63 ≤ 30300961886967 := by decide +kernel

theorem rows22310R_1437 : rowsJ2 171 172 63 67 ≤ 34352722899555 := by decide +kernel

theorem rows22310R_1438 : rowsJ2 171 172 67 71 ≤ 23393135073708 := by decide +kernel

theorem rows22310R_1439 : rowsJ2 171 172 71 76 ≤ 16611734831642 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1436
#print axioms SieveCert.rows22310R_1439
