/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 391–394 of 549

File 102 of 140: the parts `rows22335R_391` … `rows22335R_394` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24850 tests: row 114 columns 56–62, row 114 columns 63–71, row 114 columns
72–299, row 115 columns 0–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_391 : rowsJ2 114 115 56 63 ≤ 32853252533467 := by decide +kernel

theorem rows22335R_392 : rowsJ2 114 115 63 72 ≤ 5733938290524 := by decide +kernel

theorem rows22335R_393 : rowsJ2 114 115 72 300 ≤ 108764180617351 := by decide +kernel

theorem rows22335R_394 : rowsJ2 115 116 0 49 ≤ 238768118409867 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_391
#print axioms SieveCert.rows22335R_394
