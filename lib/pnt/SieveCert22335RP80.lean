/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 309–312 of 549

File 80 of 140: the parts `rows22335R_309` … `rows22335R_312` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28995 tests: row 99 columns 60–64, row 99 columns 65–70, row 99 columns
71–77, row 99 columns 78–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_309 : rowsJ2 99 100 60 65 ≤ 0 := by decide +kernel

theorem rows22335R_310 : rowsJ2 99 100 65 71 ≤ 0 := by decide +kernel

theorem rows22335R_311 : rowsJ2 99 100 71 78 ≤ 5012698373363 := by decide +kernel

theorem rows22335R_312 : rowsJ2 99 100 78 300 ≤ 983966061431357 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_309
#print axioms SieveCert.rows22335R_312
