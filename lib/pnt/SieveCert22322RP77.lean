/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 295–298 of 561

File 77 of 143: the parts `rows22322R_295` … `rows22322R_298` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26314 tests: row 96 columns 70–75, row 96 columns 76–82, row 96 columns
83–299, row 97 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_295 : rowsJ2 96 97 70 76 ≤ 0 := by decide +kernel

theorem rows22322R_296 : rowsJ2 96 97 76 83 ≤ 26026371512619 := by decide +kernel

theorem rows22322R_297 : rowsJ2 96 97 83 300 ≤ 1114730917523322 := by decide +kernel

theorem rows22322R_298 : rowsJ2 97 98 0 53 ≤ 546450375532615 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_295
#print axioms SieveCert.rows22322R_298
