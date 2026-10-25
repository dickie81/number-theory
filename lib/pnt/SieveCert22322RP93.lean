/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 356–359 of 561

File 93 of 143: the parts `rows22322R_356` … `rows22322R_359` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29001 tests: row 106 columns 52–57, row 106 columns 58–62, row 106 columns
63–68, row 106 columns 69–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_356 : rowsJ2 106 107 52 58 ≤ 24448156517552 := by decide +kernel

theorem rows22322R_357 : rowsJ2 106 107 58 63 ≤ 7426540419120 := by decide +kernel

theorem rows22322R_358 : rowsJ2 106 107 63 69 ≤ 0 := by decide +kernel

theorem rows22322R_359 : rowsJ2 106 107 69 77 ≤ 1279773310697 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_356
#print axioms SieveCert.rows22322R_359
