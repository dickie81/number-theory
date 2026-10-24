/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 301–304 of 549

File 78 of 140: the parts `rows22335R_301` … `rows22335R_304` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28914 tests: row 98 columns 53–59, row 98 columns 60–64, row 98 columns
65–69, row 98 columns 70–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_301 : rowsJ2 98 99 53 60 ≤ 382737838485 := by decide +kernel

theorem rows22335R_302 : rowsJ2 98 99 60 65 ≤ 0 := by decide +kernel

theorem rows22335R_303 : rowsJ2 98 99 65 70 ≤ 0 := by decide +kernel

theorem rows22335R_304 : rowsJ2 98 99 70 76 ≤ 658868479321 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_301
#print axioms SieveCert.rows22335R_304
