/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1413–1416 of 1732

File 355 of 430: the parts `rows22310R_1413` … `rows22310R_1416` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29675 tests: row 168 columns 64–67, row 168 columns 68–71, row 168 columns
72–76, row 168 columns 77–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1413 : rowsJ2 168 169 64 68 ≤ 33757170937151 := by decide +kernel

theorem rows22310R_1414 : rowsJ2 168 169 68 72 ≤ 23701958332705 := by decide +kernel

theorem rows22310R_1415 : rowsJ2 168 169 72 77 ≤ 17096512531182 := by decide +kernel

theorem rows22310R_1416 : rowsJ2 168 169 77 82 ≤ 7328297671509 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1413
#print axioms SieveCert.rows22310R_1416
