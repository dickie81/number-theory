/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 249–252 of 561

File 65 of 143: the parts `rows22322R_249` … `rows22322R_252` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28494 tests: row 90 columns 52–60, row 90 columns 61–65, row 90 columns
66–69, row 90 columns 70–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_249 : rowsJ2 90 91 52 61 ≤ 1283323194738 := by decide +kernel

theorem rows22322R_250 : rowsJ2 90 91 61 66 ≤ 708992379647 := by decide +kernel

theorem rows22322R_251 : rowsJ2 90 91 66 70 ≤ 2541751218362 := by decide +kernel

theorem rows22322R_252 : rowsJ2 90 91 70 75 ≤ 1120699032741 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_249
#print axioms SieveCert.rows22322R_252
