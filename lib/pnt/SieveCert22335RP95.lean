/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 364–367 of 549

File 95 of 140: the parts `rows22335R_364` … `rows22335R_367` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29309 tests: row 109 columns 0–50, row 109 columns 51–56, row 109 columns
57–62, row 109 columns 63–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_364 : rowsJ2 109 110 0 51 ≤ 322297679780401 := by decide +kernel

theorem rows22335R_365 : rowsJ2 109 110 51 57 ≤ 36729286597452 := by decide +kernel

theorem rows22335R_366 : rowsJ2 109 110 57 63 ≤ 19199436701896 := by decide +kernel

theorem rows22335R_367 : rowsJ2 109 110 63 70 ≤ 1258809991589 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_364
#print axioms SieveCert.rows22335R_367
