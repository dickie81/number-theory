/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 340–343 of 561

File 89 of 143: the parts `rows22322R_340` … `rows22322R_343` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27030 tests: row 103 columns 64–69, row 103 columns 70–76, row 103 columns
77–299, row 104 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_340 : rowsJ2 103 104 64 70 ≤ 0 := by decide +kernel

theorem rows22322R_341 : rowsJ2 103 104 70 77 ≤ 1098973735813 := by decide +kernel

theorem rows22322R_342 : rowsJ2 103 104 77 300 ≤ 708435117475052 := by decide +kernel

theorem rows22322R_343 : rowsJ2 104 105 0 52 ≤ 405182818549349 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_340
#print axioms SieveCert.rows22322R_343
