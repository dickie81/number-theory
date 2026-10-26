/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 455–458 of 561

File 118 of 143: the parts `rows22322R_455` … `rows22322R_458` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23285 tests: row 127 columns 0–45, row 127 columns 46–52, row 127 columns
53–62, row 127 columns 63–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_455 : rowsJ2 127 128 0 46 ≤ 149540021362196 := by decide +kernel

theorem rows22322R_456 : rowsJ2 127 128 46 53 ≤ 95873165073011 := by decide +kernel

theorem rows22322R_457 : rowsJ2 127 128 53 63 ≤ 37264992484678 := by decide +kernel

theorem rows22322R_458 : rowsJ2 127 128 63 300 ≤ 1754204777359391 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_455
#print axioms SieveCert.rows22322R_458
