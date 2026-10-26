/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 303–306 of 561

File 79 of 143: the parts `rows22322R_303` … `rows22322R_306` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24704 tests: row 97 columns 76–82, row 97 columns 83–299, row 98 columns
0–52, row 98 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_303 : rowsJ2 97 98 76 83 ≤ 27901988368442 := by decide +kernel

theorem rows22322R_304 : rowsJ2 97 98 83 300 ≤ 1096652192062098 := by decide +kernel

theorem rows22322R_305 : rowsJ2 98 99 0 53 ≤ 523060840671096 := by decide +kernel

theorem rows22322R_306 : rowsJ2 98 99 53 60 ≤ 384046395822 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_303
#print axioms SieveCert.rows22322R_306
