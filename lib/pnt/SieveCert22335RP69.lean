/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 267–269 of 549

File 69 of 140: the parts `rows22335R_267` … `rows22335R_269` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23150 tests: row 93 columns 61–65, row 93 columns 66–70, row 93 columns
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

theorem rows22335R_267 : rowsJ2 93 94 61 66 ≤ 380413641428 := by decide +kernel

theorem rows22335R_268 : rowsJ2 93 94 66 71 ≤ 160228986744 := by decide +kernel

theorem rows22335R_269 : rowsJ2 93 94 71 77 ≤ 1427528883680 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_267
#print axioms SieveCert.rows22335R_269
