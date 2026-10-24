/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 276–279 of 561

File 72 of 142: the parts `rows22325R_276` … `rows22325R_279` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28542 tests: row 93 columns 82–299, row 94 columns 0–52, row 94 columns
53–60, row 94 columns 61–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_276 : rowsJ2 93 94 82 300 ≤ 975152790739980 := by decide +kernel

theorem rows22325R_277 : rowsJ2 94 95 0 53 ≤ 614902815026413 := by decide +kernel

theorem rows22325R_278 : rowsJ2 94 95 53 61 ≤ 0 := by decide +kernel

theorem rows22325R_279 : rowsJ2 94 95 61 66 ≤ 378043435641 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_276
#print axioms SieveCert.rows22325R_279
