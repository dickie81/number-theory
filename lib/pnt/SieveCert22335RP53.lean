/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 204–207 of 549

File 53 of 140: the parts `rows22335R_204` … `rows22335R_207` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27872 tests: row 84 columns 67–70, row 84 columns 71–74, row 84 columns
75–79, row 84 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_204 : rowsJ2 84 85 67 71 ≤ 7266120934106 := by decide +kernel

theorem rows22335R_205 : rowsJ2 84 85 71 75 ≤ 5861345253019 := by decide +kernel

theorem rows22335R_206 : rowsJ2 84 85 75 80 ≤ 7021760271160 := by decide +kernel

theorem rows22335R_207 : rowsJ2 84 85 80 300 ≤ 19326528599997 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_204
#print axioms SieveCert.rows22335R_207
