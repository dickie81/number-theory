/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1085–1088 of 1732

File 272 of 430: the parts `rows22310R_1085` … `rows22310R_1088` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27807 tests: row 139 columns 85–87, row 139 columns 88–90, row 139 columns
91–93, row 139 columns 94–97), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1085 : rowsJ2 139 140 85 88 ≤ 0 := by decide +kernel

theorem rows22310R_1086 : rowsJ2 139 140 88 91 ≤ 0 := by decide +kernel

theorem rows22310R_1087 : rowsJ2 139 140 91 94 ≤ 0 := by decide +kernel

theorem rows22310R_1088 : rowsJ2 139 140 94 98 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1085
#print axioms SieveCert.rows22310R_1088
