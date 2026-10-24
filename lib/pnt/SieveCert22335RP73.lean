/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 281–284 of 549

File 73 of 140: the parts `rows22335R_281` … `rows22335R_284` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29720 tests: row 95 columns 61–65, row 95 columns 66–70, row 95 columns
71–76, row 95 columns 77–83), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_281 : rowsJ2 95 96 61 66 ≤ 66780211171 := by decide +kernel

theorem rows22335R_282 : rowsJ2 95 96 66 71 ≤ 0 := by decide +kernel

theorem rows22335R_283 : rowsJ2 95 96 71 77 ≤ 1715602477028 := by decide +kernel

theorem rows22335R_284 : rowsJ2 95 96 77 84 ≤ 38009240970291 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_281
#print axioms SieveCert.rows22335R_284
