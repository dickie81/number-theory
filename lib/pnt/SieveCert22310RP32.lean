/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 128–131 of 1732

File 32 of 430: the parts `rows22310R_128` … `rows22310R_131` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28500 tests: row 65 columns 44–49, row 65 columns 50–54, row 65 columns
55–58, row 65 columns 59–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_128 : rowsJ2 65 66 44 50 ≤ 139203993690089 := by decide +kernel

theorem rows22310R_129 : rowsJ2 65 66 50 55 ≤ 113918576569620 := by decide +kernel

theorem rows22310R_130 : rowsJ2 65 66 55 59 ≤ 112736704032349 := by decide +kernel

theorem rows22310R_131 : rowsJ2 65 66 59 63 ≤ 148212494071850 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_128
#print axioms SieveCert.rows22310R_131
