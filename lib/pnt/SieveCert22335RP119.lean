/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 458–461 of 549

File 119 of 140: the parts `rows22335R_458` … `rows22335R_461` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24696 tests: row 131 columns 52–299, row 132 columns 0–43, row 132 columns
44–52, row 132 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_458 : rowsJ2 131 132 52 300 ≤ 2388165350811340 := by decide +kernel

theorem rows22335R_459 : rowsJ2 132 133 0 44 ≤ 130001936985466 := by decide +kernel

theorem rows22335R_460 : rowsJ2 132 133 44 53 ≤ 104814843223230 := by decide +kernel

theorem rows22335R_461 : rowsJ2 132 133 53 300 ≤ 2520572147169525 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_458
#print axioms SieveCert.rows22335R_461
