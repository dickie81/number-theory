/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 287–290 of 561

File 75 of 143: the parts `rows22322R_287` … `rows22322R_290` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25464 tests: row 95 columns 66–70, row 95 columns 71–76, row 95 columns
77–83, row 95 columns 84–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_287 : rowsJ2 95 96 66 71 ≤ 22684124393 := by decide +kernel

theorem rows22322R_288 : rowsJ2 95 96 71 77 ≤ 622225148113 := by decide +kernel

theorem rows22322R_289 : rowsJ2 95 96 77 84 ≤ 32580517769524 := by decide +kernel

theorem rows22322R_290 : rowsJ2 95 96 84 300 ≤ 1282399169995119 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_287
#print axioms SieveCert.rows22322R_290
