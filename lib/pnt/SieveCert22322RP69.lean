/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 264–267 of 561

File 69 of 143: the parts `rows22322R_264` … `rows22322R_267` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28511 tests: row 92 columns 53–60, row 92 columns 61–65, row 92 columns
66–69, row 92 columns 70–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_264 : rowsJ2 92 93 53 61 ≤ 0 := by decide +kernel

theorem rows22322R_265 : rowsJ2 92 93 61 66 ≤ 695020657544 := by decide +kernel

theorem rows22322R_266 : rowsJ2 92 93 66 70 ≤ 984725010140 := by decide +kernel

theorem rows22322R_267 : rowsJ2 92 93 70 75 ≤ 165390496394 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_264
#print axioms SieveCert.rows22322R_267
