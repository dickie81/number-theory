/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 419–422 of 549

File 109 of 140: the parts `rows22335R_419` … `rows22335R_422` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28130 tests: row 120 columns 55–62, row 120 columns 63–299, row 121 columns
0–47, row 121 columns 48–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_419 : rowsJ2 120 121 55 63 ≤ 34808352220284 := by decide +kernel

theorem rows22335R_420 : rowsJ2 120 121 63 300 ≤ 499854060596758 := by decide +kernel

theorem rows22335R_421 : rowsJ2 121 122 0 48 ≤ 186541610731992 := by decide +kernel

theorem rows22335R_422 : rowsJ2 121 122 48 55 ≤ 81728781293262 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_419
#print axioms SieveCert.rows22335R_422
