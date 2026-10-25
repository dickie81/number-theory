/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 283–286 of 561

File 74 of 143: the parts `rows22322R_283` … `rows22322R_286` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28696 tests: row 94 columns 82–299, row 95 columns 0–52, row 95 columns
53–60, row 95 columns 61–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_283 : rowsJ2 94 95 82 300 ≤ 1082939581549850 := by decide +kernel

theorem rows22322R_284 : rowsJ2 95 96 0 53 ≤ 594257600916708 := by decide +kernel

theorem rows22322R_285 : rowsJ2 95 96 53 61 ≤ 0 := by decide +kernel

theorem rows22322R_286 : rowsJ2 95 96 61 66 ≤ 178700138710 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_283
#print axioms SieveCert.rows22322R_286
