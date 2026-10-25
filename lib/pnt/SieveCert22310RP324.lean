/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1292–1295 of 1732

File 324 of 430: the parts `rows22310R_1292` … `rows22310R_1295` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28160 tests: row 155 columns 90–94, row 155 columns 95–399, row 156 columns
0–57, row 156 columns 58–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1292 : rowsJ2 155 156 90 95 ≤ 698229447858 := by decide +kernel

theorem rows22310R_1293 : rowsJ2 155 156 95 400 ≤ 0 := by decide +kernel

theorem rows22310R_1294 : rowsJ2 156 157 0 58 ≤ 145406067423476 := by decide +kernel

theorem rows22310R_1295 : rowsJ2 156 157 58 64 ≤ 16515427330661 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1292
#print axioms SieveCert.rows22310R_1295
