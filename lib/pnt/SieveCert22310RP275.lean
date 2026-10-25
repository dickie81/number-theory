/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1097–1100 of 1732

File 275 of 430: the parts `rows22310R_1097` … `rows22310R_1100` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29095 tests: row 140 columns 78–80, row 140 columns 81–83, row 140 columns
84–86, row 140 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1097 : rowsJ2 140 141 78 81 ≤ 2850790585927 := by decide +kernel

theorem rows22310R_1098 : rowsJ2 140 141 81 84 ≤ 300778373500 := by decide +kernel

theorem rows22310R_1099 : rowsJ2 140 141 84 87 ≤ 0 := by decide +kernel

theorem rows22310R_1100 : rowsJ2 140 141 87 90 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1097
#print axioms SieveCert.rows22310R_1100
