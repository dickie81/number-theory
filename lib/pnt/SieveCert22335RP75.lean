/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 289–292 of 549

File 75 of 140: the parts `rows22335R_289` … `rows22335R_292` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24485 tests: row 96 columns 65–69, row 96 columns 70–75, row 96 columns
76–82, row 96 columns 83–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_289 : rowsJ2 96 97 65 70 ≤ 0 := by decide +kernel

theorem rows22335R_290 : rowsJ2 96 97 70 76 ≤ 554481694623 := by decide +kernel

theorem rows22335R_291 : rowsJ2 96 97 76 83 ≤ 31486373422048 := by decide +kernel

theorem rows22335R_292 : rowsJ2 96 97 83 300 ≤ 1229345413811893 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_289
#print axioms SieveCert.rows22335R_292
