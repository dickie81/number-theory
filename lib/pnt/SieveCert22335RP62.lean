/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 239–242 of 549

File 62 of 140: the parts `rows22335R_239` … `rows22335R_242` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29250 tests: row 89 columns 62–66, row 89 columns 67–70, row 89 columns
71–75, row 89 columns 76–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_239 : rowsJ2 89 90 62 67 ≤ 1530227047251 := by decide +kernel

theorem rows22335R_240 : rowsJ2 89 90 67 71 ≤ 2117003510001 := by decide +kernel

theorem rows22335R_241 : rowsJ2 89 90 71 76 ≤ 1074785337580 := by decide +kernel

theorem rows22335R_242 : rowsJ2 89 90 76 82 ≤ 13442173702793 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_239
#print axioms SieveCert.rows22335R_242
