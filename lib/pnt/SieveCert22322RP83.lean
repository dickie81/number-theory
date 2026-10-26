/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 318–321 of 561

File 83 of 143: the parts `rows22322R_318` … `rows22322R_321` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23411 tests: row 99 columns 88–299, row 100 columns 0–52, row 100 columns
53–59, row 100 columns 60–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_318 : rowsJ2 99 100 88 300 ≤ 458015808043175 := by decide +kernel

theorem rows22322R_319 : rowsJ2 100 101 0 53 ≤ 481758644586391 := by decide +kernel

theorem rows22322R_320 : rowsJ2 100 101 53 60 ≤ 2637127730841 := by decide +kernel

theorem rows22322R_321 : rowsJ2 100 101 60 65 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_318
#print axioms SieveCert.rows22322R_321
