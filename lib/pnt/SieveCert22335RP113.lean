/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 435–438 of 549

File 113 of 140: the parts `rows22335R_435` … `rows22335R_438` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24064 tests: row 124 columns 54–63, row 124 columns 64–299, row 125 columns
0–45, row 125 columns 46–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_435 : rowsJ2 124 125 54 64 ≤ 31787333166291 := by decide +kernel

theorem rows22335R_436 : rowsJ2 124 125 64 300 ≤ 1242021379396118 := by decide +kernel

theorem rows22335R_437 : rowsJ2 125 126 0 46 ≤ 150411000121621 := by decide +kernel

theorem rows22335R_438 : rowsJ2 125 126 46 53 ≤ 89652984553575 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_435
#print axioms SieveCert.rows22335R_438
