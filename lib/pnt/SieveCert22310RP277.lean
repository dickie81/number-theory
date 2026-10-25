/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1105–1108 of 1732

File 277 of 430: the parts `rows22310R_1105` … `rows22310R_1108` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26659 tests: row 140 columns 106–399, row 141 columns 0–58, row 141 columns
59–67, row 141 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1105 : rowsJ2 140 141 106 400 ≤ 453311235710298 := by decide +kernel

theorem rows22310R_1106 : rowsJ2 141 142 0 59 ≤ 275653437375165 := by decide +kernel

theorem rows22310R_1107 : rowsJ2 141 142 59 68 ≤ 8653918048763 := by decide +kernel

theorem rows22310R_1108 : rowsJ2 141 142 68 72 ≤ 8249101677647 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1105
#print axioms SieveCert.rows22310R_1108
