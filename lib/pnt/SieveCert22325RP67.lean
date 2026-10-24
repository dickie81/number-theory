/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 257–260 of 561

File 67 of 142: the parts `rows22325R_257` … `rows22325R_260` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28332 tests: row 91 columns 53–60, row 91 columns 61–65, row 91 columns
66–69, row 91 columns 70–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_257 : rowsJ2 91 92 53 61 ≤ 0 := by decide +kernel

theorem rows22325R_258 : rowsJ2 91 92 61 66 ≤ 700351756458 := by decide +kernel

theorem rows22325R_259 : rowsJ2 91 92 66 70 ≤ 1667412119406 := by decide +kernel

theorem rows22325R_260 : rowsJ2 91 92 70 75 ≤ 521493003381 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_257
#print axioms SieveCert.rows22325R_260
