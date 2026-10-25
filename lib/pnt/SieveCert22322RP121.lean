/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 466–469 of 561

File 121 of 143: the parts `rows22322R_466` … `rows22322R_469` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28050 tests: row 130 columns 45–52, row 130 columns 53–299, row 131 columns
0–43, row 131 columns 44–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_466 : rowsJ2 130 131 45 53 ≤ 106724693917140 := by decide +kernel

theorem rows22322R_467 : rowsJ2 130 131 53 300 ≤ 2240840424505336 := by decide +kernel

theorem rows22322R_468 : rowsJ2 131 132 0 44 ≤ 127011976645830 := by decide +kernel

theorem rows22322R_469 : rowsJ2 131 132 44 52 ≤ 112150190009962 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_466
#print axioms SieveCert.rows22322R_469
