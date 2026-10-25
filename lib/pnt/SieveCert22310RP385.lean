/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1530–1533 of 1732

File 385 of 430: the parts `rows22310R_1530` … `rows22310R_1533` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29181 tests: row 185 columns 55–59, row 185 columns 60–64, row 185 columns
65–399, row 186 columns 0–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1530 : rowsJ2 185 186 55 60 ≤ 52745343360683 := by decide +kernel

theorem rows22310R_1531 : rowsJ2 185 186 60 65 ≤ 33995280261120 := by decide +kernel

theorem rows22310R_1532 : rowsJ2 185 186 65 400 ≤ 2104041719803184 := by decide +kernel

theorem rows22310R_1533 : rowsJ2 186 187 0 48 ≤ 32530130755573 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1530
#print axioms SieveCert.rows22310R_1533
