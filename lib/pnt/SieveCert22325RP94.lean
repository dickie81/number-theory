/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 360–363 of 561

File 94 of 142: the parts `rows22325R_360` … `rows22325R_363` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24678 tests: row 106 columns 77–299, row 107 columns 0–51, row 107 columns
52–57, row 107 columns 58–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_360 : rowsJ2 106 107 77 300 ≤ 568273113131664 := by decide +kernel

theorem rows22325R_361 : rowsJ2 107 108 0 52 ≤ 356346170408396 := by decide +kernel

theorem rows22325R_362 : rowsJ2 107 108 52 58 ≤ 28425630200815 := by decide +kernel

theorem rows22325R_363 : rowsJ2 107 108 58 63 ≤ 10311120429345 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_360
#print axioms SieveCert.rows22325R_363
