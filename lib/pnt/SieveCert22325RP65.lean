/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 249–252 of 561

File 65 of 142: the parts `rows22325R_249` … `rows22325R_252` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28494 tests: row 90 columns 52–60, row 90 columns 61–65, row 90 columns
66–69, row 90 columns 70–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_249 : rowsJ2 90 91 52 61 ≤ 1277703678818 := by decide +kernel

theorem rows22325R_250 : rowsJ2 90 91 61 66 ≤ 707386593650 := by decide +kernel

theorem rows22325R_251 : rowsJ2 90 91 66 70 ≤ 2536091719996 := by decide +kernel

theorem rows22325R_252 : rowsJ2 90 91 70 75 ≤ 1118104717744 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_249
#print axioms SieveCert.rows22325R_252
