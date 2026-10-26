/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 237–240 of 561

File 62 of 143: the parts `rows22322R_237` … `rows22322R_240` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24175 tests: row 88 columns 76–80, row 88 columns 81–86, row 88 columns
87–299, row 89 columns 0–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_237 : rowsJ2 88 89 76 81 ≤ 7096121820427 := by decide +kernel

theorem rows22322R_238 : rowsJ2 88 89 81 87 ≤ 37964855982278 := by decide +kernel

theorem rows22322R_239 : rowsJ2 88 89 87 300 ≤ 24517835145309 := by decide +kernel

theorem rows22322R_240 : rowsJ2 89 90 0 51 ≤ 766272478533469 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_237
#print axioms SieveCert.rows22322R_240
