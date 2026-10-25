/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1634–1637 of 1732

File 411 of 430: the parts `rows22310R_1634` … `rows22310R_1637` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23971 tests: row 214 columns 0–38, row 214 columns 39–399, row 215 columns
0–38, row 215 columns 39–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1634 : rowsJ2 214 215 0 39 ≤ 47186298742321 := by decide +kernel

theorem rows22310R_1635 : rowsJ2 214 215 39 400 ≤ 2746555204045475 := by decide +kernel

theorem rows22310R_1636 : rowsJ2 215 216 0 39 ≤ 51771061127799 := by decide +kernel

theorem rows22310R_1637 : rowsJ2 215 216 39 400 ≤ 2823829805949021 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1634
#print axioms SieveCert.rows22310R_1637
