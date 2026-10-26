/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 314–317 of 561

File 82 of 143: the parts `rows22322R_314` … `rows22322R_317` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29860 tests: row 99 columns 60–64, row 99 columns 65–69, row 99 columns
70–75, row 99 columns 76–87), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_314 : rowsJ2 99 100 60 65 ≤ 0 := by decide +kernel

theorem rows22322R_315 : rowsJ2 99 100 65 70 ≤ 0 := by decide +kernel

theorem rows22322R_316 : rowsJ2 99 100 70 76 ≤ 0 := by decide +kernel

theorem rows22322R_317 : rowsJ2 99 100 76 88 ≤ 523722121648695 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_314
#print axioms SieveCert.rows22322R_317
