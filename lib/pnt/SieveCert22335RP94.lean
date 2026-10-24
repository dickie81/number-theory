/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 361–363 of 549

File 94 of 140: the parts `rows22335R_361` … `rows22335R_363` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22744 tests: row 108 columns 57–62, row 108 columns 63–69, row 108 columns
70–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_361 : rowsJ2 108 109 57 63 ≤ 16829587966190 := by decide +kernel

theorem rows22335R_362 : rowsJ2 108 109 63 70 ≤ 478763737000 := by decide +kernel

theorem rows22335R_363 : rowsJ2 108 109 70 300 ≤ 451991549593052 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_361
#print axioms SieveCert.rows22335R_363
