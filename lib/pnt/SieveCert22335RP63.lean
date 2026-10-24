/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 243–246 of 549

File 63 of 140: the parts `rows22335R_243` … `rows22335R_246` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29255 tests: row 89 columns 82–299, row 90 columns 0–51, row 90 columns
52–60, row 90 columns 61–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_243 : rowsJ2 89 90 82 300 ≤ 248987723155754 := by decide +kernel

theorem rows22335R_244 : rowsJ2 90 91 0 52 ≤ 728172854233414 := by decide +kernel

theorem rows22335R_245 : rowsJ2 90 91 52 61 ≤ 1276103402365 := by decide +kernel

theorem rows22335R_246 : rowsJ2 90 91 61 66 ≤ 706928529564 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_243
#print axioms SieveCert.rows22335R_246
