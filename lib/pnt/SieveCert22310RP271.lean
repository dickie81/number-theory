/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1081–1084 of 1732

File 271 of 430: the parts `rows22310R_1081` … `rows22310R_1084` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28599 tests: row 139 columns 73–75, row 139 columns 76–78, row 139 columns
79–81, row 139 columns 82–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1081 : rowsJ2 139 140 73 76 ≤ 4738065045850 := by decide +kernel

theorem rows22310R_1082 : rowsJ2 139 140 76 79 ≤ 3380794665357 := by decide +kernel

theorem rows22310R_1083 : rowsJ2 139 140 79 82 ≤ 979615921481 := by decide +kernel

theorem rows22310R_1084 : rowsJ2 139 140 82 85 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1081
#print axioms SieveCert.rows22310R_1084
