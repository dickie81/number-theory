/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 351–353 of 549

File 91 of 140: the parts `rows22335R_351` … `rows22335R_353` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23562 tests: row 106 columns 58–63, row 106 columns 64–70, row 106 columns
71–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_351 : rowsJ2 106 107 58 64 ≤ 6890854431891 := by decide +kernel

theorem rows22335R_352 : rowsJ2 106 107 64 71 ≤ 0 := by decide +kernel

theorem rows22335R_353 : rowsJ2 106 107 71 300 ≤ 576073709355507 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_351
#print axioms SieveCert.rows22335R_353
