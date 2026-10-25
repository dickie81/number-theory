/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1231–1234 of 1732

File 309 of 430: the parts `rows22310R_1231` … `rows22310R_1234` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29279 tests: row 150 columns 84–87, row 150 columns 88–91, row 150 columns
92–96, row 150 columns 97–102), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1231 : rowsJ2 150 151 84 88 ≤ 3751832149646 := by decide +kernel

theorem rows22310R_1232 : rowsJ2 150 151 88 92 ≤ 1040339693290 := by decide +kernel

theorem rows22310R_1233 : rowsJ2 150 151 92 97 ≤ 0 := by decide +kernel

theorem rows22310R_1234 : rowsJ2 150 151 97 103 ≤ 2290853305119 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1231
#print axioms SieveCert.rows22310R_1234
