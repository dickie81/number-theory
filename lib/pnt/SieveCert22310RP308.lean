/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1227–1230 of 1732

File 308 of 430: the parts `rows22310R_1227` … `rows22310R_1230` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26595 tests: row 150 columns 72–74, row 150 columns 75–77, row 150 columns
78–80, row 150 columns 81–83), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1227 : rowsJ2 150 151 72 75 ≤ 14743056646937 := by decide +kernel

theorem rows22310R_1228 : rowsJ2 150 151 75 78 ≤ 12181930952273 := by decide +kernel

theorem rows22310R_1229 : rowsJ2 150 151 78 81 ≤ 8476070071655 := by decide +kernel

theorem rows22310R_1230 : rowsJ2 150 151 81 84 ≤ 5467547033107 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1227
#print axioms SieveCert.rows22310R_1230
