/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 446–449 of 549

File 116 of 140: the parts `rows22335R_446` … `rows22335R_449` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28930 tests: row 127 columns 54–299, row 128 columns 0–44, row 128 columns
45–52, row 128 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_446 : rowsJ2 127 128 54 300 ≤ 1774788849292583 := by decide +kernel

theorem rows22335R_447 : rowsJ2 128 129 0 45 ≤ 135104432336465 := by decide +kernel

theorem rows22335R_448 : rowsJ2 128 129 45 53 ≤ 99843460834674 := by decide +kernel

theorem rows22335R_449 : rowsJ2 128 129 53 300 ≤ 1937020370701718 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_446
#print axioms SieveCert.rows22335R_449
