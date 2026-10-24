/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 439–442 of 549

File 114 of 140: the parts `rows22335R_439` … `rows22335R_442` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25166 tests: row 125 columns 53–62, row 125 columns 63–299, row 126 columns
0–45, row 126 columns 46–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_439 : rowsJ2 125 126 53 63 ≤ 36165894315653 := by decide +kernel

theorem rows22335R_440 : rowsJ2 125 126 63 300 ≤ 1418840553813068 := by decide +kernel

theorem rows22335R_441 : rowsJ2 126 127 0 46 ≤ 148540116322627 := by decide +kernel

theorem rows22335R_442 : rowsJ2 126 127 46 54 ≤ 96227579697007 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_439
#print axioms SieveCert.rows22335R_442
