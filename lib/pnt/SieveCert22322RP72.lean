/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 275–278 of 561

File 72 of 143: the parts `rows22322R_275` … `rows22322R_278` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27998 tests: row 93 columns 76–81, row 93 columns 82–299, row 94 columns
0–52, row 94 columns 53–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_275 : rowsJ2 93 94 76 82 ≤ 15107184717484 := by decide +kernel

theorem rows22322R_276 : rowsJ2 93 94 82 300 ≤ 976376427493802 := by decide +kernel

theorem rows22322R_277 : rowsJ2 94 95 0 53 ≤ 619231925826826 := by decide +kernel

theorem rows22322R_278 : rowsJ2 94 95 53 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_275
#print axioms SieveCert.rows22322R_278
