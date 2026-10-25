/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1276–1279 of 1732

File 320 of 430: the parts `rows22310R_1276` … `rows22310R_1279` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28336 tests: row 154 columns 72–74, row 154 columns 75–77, row 154 columns
78–81, row 154 columns 82–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1276 : rowsJ2 154 155 72 75 ≤ 17116308231698 := by decide +kernel

theorem rows22310R_1277 : rowsJ2 154 155 75 78 ≤ 12634853265401 := by decide +kernel

theorem rows22310R_1278 : rowsJ2 154 155 78 82 ≤ 11179882791052 := by decide +kernel

theorem rows22310R_1279 : rowsJ2 154 155 82 86 ≤ 6209919375580 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1276
#print axioms SieveCert.rows22310R_1279
