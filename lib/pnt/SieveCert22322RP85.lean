/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 326–329 of 561

File 85 of 143: the parts `rows22322R_326` … `rows22322R_329` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27987 tests: row 101 columns 53–58, row 101 columns 59–63, row 101 columns
64–68, row 101 columns 69–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_326 : rowsJ2 101 102 53 59 ≤ 4659535856299 := by decide +kernel

theorem rows22322R_327 : rowsJ2 101 102 59 64 ≤ 0 := by decide +kernel

theorem rows22322R_328 : rowsJ2 101 102 64 69 ≤ 0 := by decide +kernel

theorem rows22322R_329 : rowsJ2 101 102 69 75 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_326
#print axioms SieveCert.rows22322R_329
