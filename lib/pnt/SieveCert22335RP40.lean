/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 151–154 of 549

File 40 of 140: the parts `rows22335R_151` … `rows22335R_154` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 22612 tests: row 76 columns 61–67, row 76 columns 68–71, row 76 columns
72–75, row 76 columns 76–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_151 : rowsJ2 76 77 61 68 ≤ 25335617463835 := by decide +kernel

theorem rows22335R_152 : rowsJ2 76 77 68 72 ≤ 12918647108129 := by decide +kernel

theorem rows22335R_153 : rowsJ2 76 77 72 76 ≤ 22576878322738 := by decide +kernel

theorem rows22335R_154 : rowsJ2 76 77 76 300 ≤ 5022263214410 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_151
#print axioms SieveCert.rows22335R_154
