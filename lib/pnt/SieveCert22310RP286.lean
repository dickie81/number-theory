/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1140–1143 of 1732

File 286 of 430: the parts `rows22310R_1140` … `rows22310R_1143` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28336 tests: row 143 columns 83–85, row 143 columns 86–88, row 143 columns
89–92, row 143 columns 93–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1140 : rowsJ2 143 144 83 86 ≤ 729440361214 := by decide +kernel

theorem rows22310R_1141 : rowsJ2 143 144 86 89 ≤ 0 := by decide +kernel

theorem rows22310R_1142 : rowsJ2 143 144 89 93 ≤ 0 := by decide +kernel

theorem rows22310R_1143 : rowsJ2 143 144 93 97 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1140
#print axioms SieveCert.rows22310R_1143
