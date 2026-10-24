/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 293–296 of 549

File 76 of 140: the parts `rows22335R_293` … `rows22335R_296` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29244 tests: row 97 columns 0–52, row 97 columns 53–59, row 97 columns 60–64,
row 97 columns 65–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_293 : rowsJ2 97 98 0 53 ≤ 542993748726706 := by decide +kernel

theorem rows22335R_294 : rowsJ2 97 98 53 60 ≤ 0 := by decide +kernel

theorem rows22335R_295 : rowsJ2 97 98 60 65 ≤ 0 := by decide +kernel

theorem rows22335R_296 : rowsJ2 97 98 65 70 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_293
#print axioms SieveCert.rows22335R_296
