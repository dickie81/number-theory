/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1608–1611 of 1732

File 405 of 430: the parts `rows22310R_1608` … `rows22310R_1611` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27030 tests: row 204 columns 0–41, row 204 columns 42–48, row 204 columns
49–399, row 205 columns 0–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1608 : rowsJ2 204 205 0 42 ≤ 38846112139382 := by decide +kernel

theorem rows22310R_1609 : rowsJ2 204 205 42 49 ≤ 95147694993164 := by decide +kernel

theorem rows22310R_1610 : rowsJ2 204 205 49 400 ≤ 2229072965390901 := by decide +kernel

theorem rows22310R_1611 : rowsJ2 205 206 0 41 ≤ 33003257418650 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1608
#print axioms SieveCert.rows22310R_1611
