/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 451–454 of 561

File 117 of 143: the parts `rows22322R_451` … `rows22322R_454` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24043 tests: row 126 columns 0–45, row 126 columns 46–52, row 126 columns
53–62, row 126 columns 63–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_451 : rowsJ2 126 127 0 46 ≤ 149256284381565 := by decide +kernel

theorem rows22322R_452 : rowsJ2 126 127 46 53 ≤ 96920803188537 := by decide +kernel

theorem rows22322R_453 : rowsJ2 126 127 53 63 ≤ 40987169943859 := by decide +kernel

theorem rows22322R_454 : rowsJ2 126 127 63 300 ≤ 1593891760828323 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_451
#print axioms SieveCert.rows22322R_454
