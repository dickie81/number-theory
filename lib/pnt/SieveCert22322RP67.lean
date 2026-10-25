/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 257–260 of 561

File 67 of 143: the parts `rows22322R_257` … `rows22322R_260` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28332 tests: row 91 columns 53–60, row 91 columns 61–65, row 91 columns
66–69, row 91 columns 70–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_257 : rowsJ2 91 92 53 61 ≤ 0 := by decide +kernel

theorem rows22322R_258 : rowsJ2 91 92 61 66 ≤ 701919501979 := by decide +kernel

theorem rows22322R_259 : rowsJ2 91 92 66 70 ≤ 1671169489352 := by decide +kernel

theorem rows22322R_260 : rowsJ2 91 92 70 75 ≤ 522702321193 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_257
#print axioms SieveCert.rows22322R_260
