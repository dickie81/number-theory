/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 185–188 of 1732

File 46 of 430: the parts `rows22310R_185` … `rows22310R_188` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28689 tests: row 72 columns 55–58, row 72 columns 59–62, row 72 columns
63–66, row 72 columns 67–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_185 : rowsJ2 72 73 55 59 ≤ 123872964346012 := by decide +kernel

theorem rows22310R_186 : rowsJ2 72 73 59 63 ≤ 168899534980803 := by decide +kernel

theorem rows22310R_187 : rowsJ2 72 73 63 67 ≤ 167716266027653 := by decide +kernel

theorem rows22310R_188 : rowsJ2 72 73 67 72 ≤ 191346373966477 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_185
#print axioms SieveCert.rows22310R_188
