/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 316–319 of 549

File 82 of 140: the parts `rows22335R_316` … `rows22335R_319` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27952 tests: row 100 columns 65–70, row 100 columns 71–77, row 100 columns
78–299, row 101 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_316 : rowsJ2 100 101 65 71 ≤ 0 := by decide +kernel

theorem rows22335R_317 : rowsJ2 100 101 71 78 ≤ 5299380051616 := by decide +kernel

theorem rows22335R_318 : rowsJ2 100 101 78 300 ≤ 968859027802403 := by decide +kernel

theorem rows22335R_319 : rowsJ2 101 102 0 53 ≤ 460916569173850 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_316
#print axioms SieveCert.rows22335R_319
