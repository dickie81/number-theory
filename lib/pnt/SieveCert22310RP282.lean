/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1125–1128 of 1732

File 282 of 430: the parts `rows22310R_1125` … `rows22310R_1128` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28152 tests: row 142 columns 78–80, row 142 columns 81–83, row 142 columns
84–86, row 142 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1125 : rowsJ2 142 143 78 81 ≤ 4607003871369 := by decide +kernel

theorem rows22310R_1126 : rowsJ2 142 143 81 84 ≤ 1631777448837 := by decide +kernel

theorem rows22310R_1127 : rowsJ2 142 143 84 87 ≤ 0 := by decide +kernel

theorem rows22310R_1128 : rowsJ2 142 143 87 90 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1125
#print axioms SieveCert.rows22310R_1128
