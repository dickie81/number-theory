/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 387–390 of 549

File 101 of 140: the parts `rows22335R_387` … `rows22335R_390` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25885 tests: row 113 columns 63–71, row 113 columns 72–299, row 114 columns
0–49, row 114 columns 50–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_387 : rowsJ2 113 114 63 72 ≤ 5140076311318 := by decide +kernel

theorem rows22335R_388 : rowsJ2 113 114 72 300 ≤ 111849466946074 := by decide +kernel

theorem rows22335R_389 : rowsJ2 114 115 0 50 ≤ 255692492565566 := by decide +kernel

theorem rows22335R_390 : rowsJ2 114 115 50 56 ≤ 55199825015882 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_387
#print axioms SieveCert.rows22335R_390
