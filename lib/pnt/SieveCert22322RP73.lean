/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 279–282 of 561

File 73 of 143: the parts `rows22322R_279` … `rows22322R_282` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29349 tests: row 94 columns 61–65, row 94 columns 66–70, row 94 columns
71–75, row 94 columns 76–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_279 : rowsJ2 94 95 61 66 ≤ 378888785517 := by decide +kernel

theorem rows22322R_280 : rowsJ2 94 95 66 71 ≤ 159561545935 := by decide +kernel

theorem rows22322R_281 : rowsJ2 94 95 71 76 ≤ 0 := by decide +kernel

theorem rows22322R_282 : rowsJ2 94 95 76 82 ≤ 16127370938142 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_279
#print axioms SieveCert.rows22322R_282
