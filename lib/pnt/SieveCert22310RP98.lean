/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 391–394 of 1732

File 98 of 430: the parts `rows22310R_391` … `rows22310R_394` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27629 tests: row 96 columns 57–67, row 96 columns 68–83, row 96 columns
84–88, row 96 columns 89–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_391 : rowsJ2 96 97 57 68 ≤ 264777096644842 := by decide +kernel

theorem rows22310R_392 : rowsJ2 96 97 68 84 ≤ 207078588335003 := by decide +kernel

theorem rows22310R_393 : rowsJ2 96 97 84 89 ≤ 28498697108761 := by decide +kernel

theorem rows22310R_394 : rowsJ2 96 97 89 92 ≤ 12135239052227 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_391
#print axioms SieveCert.rows22310R_394
