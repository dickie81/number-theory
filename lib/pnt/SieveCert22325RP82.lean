/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 314–317 of 561

File 82 of 142: the parts `rows22325R_314` … `rows22325R_317` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29860 tests: row 99 columns 60–64, row 99 columns 65–69, row 99 columns
70–75, row 99 columns 76–87), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_314 : rowsJ2 99 100 60 65 ≤ 0 := by decide +kernel

theorem rows22325R_315 : rowsJ2 99 100 65 70 ≤ 0 := by decide +kernel

theorem rows22325R_316 : rowsJ2 99 100 70 76 ≤ 0 := by decide +kernel

theorem rows22325R_317 : rowsJ2 99 100 76 88 ≤ 522993937358755 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_314
#print axioms SieveCert.rows22325R_317
