/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1401–1404 of 1732

File 352 of 430: the parts `rows22310R_1401` … `rows22310R_1404` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24713 tests: row 166 columns 88–399, row 167 columns 0–54, row 167 columns
55–60, row 167 columns 61–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1401 : rowsJ2 166 167 88 400 ≤ 915700214525667 := by decide +kernel

theorem rows22310R_1402 : rowsJ2 167 168 0 55 ≤ 81950274116833 := by decide +kernel

theorem rows22310R_1403 : rowsJ2 167 168 55 61 ≤ 26287487676238 := by decide +kernel

theorem rows22310R_1404 : rowsJ2 167 168 61 65 ≤ 28662918460441 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1401
#print axioms SieveCert.rows22310R_1404
