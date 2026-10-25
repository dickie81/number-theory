/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1604–1607 of 1732

File 404 of 430: the parts `rows22310R_1604` … `rows22310R_1607` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27426 tests: row 202 columns 49–399, row 203 columns 0–41, row 203 columns
42–48, row 203 columns 49–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1604 : rowsJ2 202 203 49 400 ≤ 2228384592730423 := by decide +kernel

theorem rows22310R_1605 : rowsJ2 203 204 0 42 ≤ 35272964791125 := by decide +kernel

theorem rows22310R_1606 : rowsJ2 203 204 42 49 ≤ 91005775995948 := by decide +kernel

theorem rows22310R_1607 : rowsJ2 203 204 49 400 ≤ 2228404618460431 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1604
#print axioms SieveCert.rows22310R_1607
