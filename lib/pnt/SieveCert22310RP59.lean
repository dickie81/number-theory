/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 237–240 of 1732

File 59 of 430: the parts `rows22310R_237` … `rows22310R_240` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28795 tests: row 78 columns 44–49, row 78 columns 50–54, row 78 columns
55–58, row 78 columns 59–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_237 : rowsJ2 78 79 44 50 ≤ 81468892356466 := by decide +kernel

theorem rows22310R_238 : rowsJ2 78 79 50 55 ≤ 117501561727121 := by decide +kernel

theorem rows22310R_239 : rowsJ2 78 79 55 59 ≤ 149417998405961 := by decide +kernel

theorem rows22310R_240 : rowsJ2 78 79 59 64 ≤ 200293211611886 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_237
#print axioms SieveCert.rows22310R_240
