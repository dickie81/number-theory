/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 255–258 of 549

File 66 of 140: the parts `rows22335R_255` … `rows22335R_258` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28511 tests: row 91 columns 71–75, row 91 columns 76–81, row 91 columns
82–299, row 92 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_255 : rowsJ2 91 92 71 76 ≤ 431792732721 := by decide +kernel

theorem rows22335R_256 : rowsJ2 91 92 76 82 ≤ 15933606602407 := by decide +kernel

theorem rows22335R_257 : rowsJ2 91 92 82 300 ≤ 629403350583779 := by decide +kernel

theorem rows22335R_258 : rowsJ2 92 93 0 53 ≤ 669168843699218 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_255
#print axioms SieveCert.rows22335R_258
