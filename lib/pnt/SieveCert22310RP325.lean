/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1296–1299 of 1732

File 325 of 430: the parts `rows22310R_1296` … `rows22310R_1299` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26139 tests: row 156 columns 64–67, row 156 columns 68–70, row 156 columns
71–73, row 156 columns 74–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1296 : rowsJ2 156 157 64 68 ≤ 19432245030308 := by decide +kernel

theorem rows22310R_1297 : rowsJ2 156 157 68 71 ≤ 18584811588963 := by decide +kernel

theorem rows22310R_1298 : rowsJ2 156 157 71 74 ≤ 18661170849392 := by decide +kernel

theorem rows22310R_1299 : rowsJ2 156 157 74 77 ≤ 13913741895111 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1296
#print axioms SieveCert.rows22310R_1299
