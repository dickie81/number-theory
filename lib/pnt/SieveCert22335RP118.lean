/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 454–457 of 549

File 118 of 140: the parts `rows22335R_454` … `rows22335R_457` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27189 tests: row 130 columns 45–52, row 130 columns 53–299, row 131 columns
0–43, row 131 columns 44–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_454 : rowsJ2 130 131 45 53 ≤ 95375921103039 := by decide +kernel

theorem rows22335R_455 : rowsJ2 130 131 53 300 ≤ 2232524752815559 := by decide +kernel

theorem rows22335R_456 : rowsJ2 131 132 0 44 ≤ 126674220005459 := by decide +kernel

theorem rows22335R_457 : rowsJ2 131 132 44 52 ≤ 102169882349937 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_454
#print axioms SieveCert.rows22335R_457
