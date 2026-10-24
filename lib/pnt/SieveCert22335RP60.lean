/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 232–235 of 549

File 60 of 140: the parts `rows22335R_232` … `rows22335R_235` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29580 tests: row 88 columns 62–66, row 88 columns 67–70, row 88 columns
71–75, row 88 columns 76–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_232 : rowsJ2 88 89 62 67 ≤ 1543210270945 := by decide +kernel

theorem rows22335R_233 : rowsJ2 88 89 67 71 ≤ 3096563983917 := by decide +kernel

theorem rows22335R_234 : rowsJ2 88 89 71 76 ≤ 1731297825971 := by decide +kernel

theorem rows22335R_235 : rowsJ2 88 89 76 82 ≤ 12303688707371 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_232
#print axioms SieveCert.rows22335R_235
