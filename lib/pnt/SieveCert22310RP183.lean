/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 728–731 of 1732

File 183 of 430: the parts `rows22310R_728` … `rows22310R_731` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28780 tests: row 118 columns 74–79, row 118 columns 80–83, row 118 columns
84–86, row 118 columns 87–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_728 : rowsJ2 118 119 74 80 ≤ 1037979100080 := by decide +kernel

theorem rows22310R_729 : rowsJ2 118 119 80 84 ≤ 0 := by decide +kernel

theorem rows22310R_730 : rowsJ2 118 119 84 87 ≤ 118844535549 := by decide +kernel

theorem rows22310R_731 : rowsJ2 118 119 87 89 ≤ 493675741064 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_728
#print axioms SieveCert.rows22310R_731
