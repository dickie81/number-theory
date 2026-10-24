/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 297–300 of 549

File 77 of 140: the parts `rows22335R_297` … `rows22335R_300` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24228 tests: row 97 columns 70–75, row 97 columns 76–83, row 97 columns
84–299, row 98 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_297 : rowsJ2 97 98 70 76 ≤ 643549642272 := by decide +kernel

theorem rows22335R_298 : rowsJ2 97 98 76 84 ≤ 44595696990786 := by decide +kernel

theorem rows22335R_299 : rowsJ2 97 98 84 300 ≤ 1086347023439757 := by decide +kernel

theorem rows22335R_300 : rowsJ2 98 99 0 53 ≤ 520373783319439 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_297
#print axioms SieveCert.rows22335R_300
