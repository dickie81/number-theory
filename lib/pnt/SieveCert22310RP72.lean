/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 289–292 of 1732

File 72 of 430: the parts `rows22310R_289` … `rows22310R_292` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28721 tests: row 84 columns 44–49, row 84 columns 50–54, row 84 columns
55–59, row 84 columns 60–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_289 : rowsJ2 84 85 44 50 ≤ 88650692474771 := by decide +kernel

theorem rows22310R_290 : rowsJ2 84 85 50 55 ≤ 149718817880708 := by decide +kernel

theorem rows22310R_291 : rowsJ2 84 85 55 60 ≤ 193356577395605 := by decide +kernel

theorem rows22310R_292 : rowsJ2 84 85 60 66 ≤ 203410725681068 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_289
#print axioms SieveCert.rows22310R_292
