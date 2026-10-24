/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 274–276 of 549

File 71 of 140: the parts `rows22335R_274` … `rows22335R_276` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22807 tests: row 94 columns 61–65, row 94 columns 66–70, row 94 columns
71–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_274 : rowsJ2 94 95 61 66 ≤ 179440905801 := by decide +kernel

theorem rows22335R_275 : rowsJ2 94 95 66 71 ≤ 22777917802 := by decide +kernel

theorem rows22335R_276 : rowsJ2 94 95 71 77 ≤ 1533361018714 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_274
#print axioms SieveCert.rows22335R_276
