/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 263–266 of 549

File 68 of 140: the parts `rows22335R_263` … `rows22335R_266` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27539 tests: row 92 columns 76–81, row 92 columns 82–299, row 93 columns
0–52, row 93 columns 53–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_263 : rowsJ2 92 93 76 82 ≤ 17160056100373 := by decide +kernel

theorem rows22335R_264 : rowsJ2 92 93 82 300 ≤ 867278230062992 := by decide +kernel

theorem rows22335R_265 : rowsJ2 93 94 0 53 ≤ 642201147155202 := by decide +kernel

theorem rows22335R_266 : rowsJ2 93 94 53 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_263
#print axioms SieveCert.rows22335R_266
