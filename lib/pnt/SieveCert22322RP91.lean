/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 348–351 of 561

File 91 of 143: the parts `rows22322R_348` … `rows22322R_351` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26844 tests: row 104 columns 76–299, row 105 columns 0–51, row 105 columns
52–57, row 105 columns 58–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_348 : rowsJ2 104 105 76 300 ≤ 590953627427305 := by decide +kernel

theorem rows22322R_349 : rowsJ2 105 106 0 52 ≤ 389210829602678 := by decide +kernel

theorem rows22322R_350 : rowsJ2 105 106 52 58 ≤ 20445597246940 := by decide +kernel

theorem rows22322R_351 : rowsJ2 105 106 58 63 ≤ 4565693627822 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_348
#print axioms SieveCert.rows22322R_351
