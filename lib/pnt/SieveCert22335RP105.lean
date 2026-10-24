/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 403–406 of 549

File 105 of 140: the parts `rows22335R_403` … `rows22335R_406` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23507 tests: row 116 columns 72–299, row 117 columns 0–48, row 117 columns
49–54, row 117 columns 55–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_403 : rowsJ2 116 117 72 300 ≤ 0 := by decide +kernel

theorem rows22335R_404 : rowsJ2 117 118 0 49 ≤ 221370668412474 := by decide +kernel

theorem rows22335R_405 : rowsJ2 117 118 49 55 ≤ 64467994371348 := by decide +kernel

theorem rows22335R_406 : rowsJ2 117 118 55 62 ≤ 37871986804186 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_403
#print axioms SieveCert.rows22335R_406
