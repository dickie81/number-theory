/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 271–274 of 561

File 71 of 143: the parts `rows22322R_271` … `rows22322R_274` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29941 tests: row 93 columns 53–60, row 93 columns 61–65, row 93 columns
66–70, row 93 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_271 : rowsJ2 93 94 53 61 ≤ 0 := by decide +kernel

theorem rows22322R_272 : rowsJ2 93 94 61 66 ≤ 513960376454 := by decide +kernel

theorem rows22322R_273 : rowsJ2 93 94 66 71 ≤ 504121468634 := by decide +kernel

theorem rows22322R_274 : rowsJ2 93 94 71 76 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_271
#print axioms SieveCert.rows22322R_274
