/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 654–657 of 1732

File 165 of 430: the parts `rows22310R_654` … `rows22310R_657` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26088 tests: row 114 columns 86–88, row 114 columns 89–90, row 114 columns
91–92, row 114 columns 93–94), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_654 : rowsJ2 114 115 86 89 ≤ 597329840488 := by decide +kernel

theorem rows22310R_655 : rowsJ2 114 115 89 91 ≤ 1151910371076 := by decide +kernel

theorem rows22310R_656 : rowsJ2 114 115 91 93 ≤ 2056041715676 := by decide +kernel

theorem rows22310R_657 : rowsJ2 114 115 93 95 ≤ 2067432908067 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_654
#print axioms SieveCert.rows22310R_657
