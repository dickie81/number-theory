/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 126–129 of 549

File 33 of 140: the parts `rows22335R_126` … `rows22335R_129` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28403 tests: row 71 columns 0–34, row 71 columns 35–50, row 71 columns 51–67,
row 71 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_126 : rowsJ2 71 72 0 35 ≤ 560705712475688 := by decide +kernel

theorem rows22335R_127 : rowsJ2 71 72 35 51 ≤ 801780243186844 := by decide +kernel

theorem rows22335R_128 : rowsJ2 71 72 51 68 ≤ 311138753574228 := by decide +kernel

theorem rows22335R_129 : rowsJ2 71 72 68 300 ≤ 23293767076362 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_126
#print axioms SieveCert.rows22335R_129
