/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 360–363 of 561

File 94 of 143: the parts `rows22322R_360` … `rows22322R_363` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25300 tests: row 106 columns 77–299, row 107 columns 0–51, row 107 columns
52–57, row 107 columns 58–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_360 : rowsJ2 106 107 77 300 ≤ 463080715992151 := by decide +kernel

theorem rows22322R_361 : rowsJ2 107 108 0 52 ≤ 357795666635876 := by decide +kernel

theorem rows22322R_362 : rowsJ2 107 108 52 58 ≤ 28502791449781 := by decide +kernel

theorem rows22322R_363 : rowsJ2 107 108 58 63 ≤ 10339245042543 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_360
#print axioms SieveCert.rows22322R_363
