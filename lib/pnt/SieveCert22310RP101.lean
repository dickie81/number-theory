/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 403–406 of 1732

File 101 of 430: the parts `rows22310R_403` … `rows22310R_406` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28184 tests: row 97 columns 85–89, row 97 columns 90–92, row 97 columns
93–95, row 97 columns 96–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_403 : rowsJ2 97 98 85 90 ≤ 23140992764991 := by decide +kernel

theorem rows22310R_404 : rowsJ2 97 98 90 93 ≤ 9888633211165 := by decide +kernel

theorem rows22310R_405 : rowsJ2 97 98 93 96 ≤ 8938215896465 := by decide +kernel

theorem rows22310R_406 : rowsJ2 97 98 96 400 ≤ 6491729953844 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_403
#print axioms SieveCert.rows22310R_406
