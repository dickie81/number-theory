/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 272–275 of 561

File 71 of 142: the parts `rows22325R_272` … `rows22325R_275` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29814 tests: row 93 columns 61–65, row 93 columns 66–70, row 93 columns
71–75, row 93 columns 76–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_272 : rowsJ2 93 94 61 66 ≤ 512825377527 := by decide +kernel

theorem rows22325R_273 : rowsJ2 93 94 66 71 ≤ 502964575607 := by decide +kernel

theorem rows22325R_274 : rowsJ2 93 94 71 76 ≤ 0 := by decide +kernel

theorem rows22325R_275 : rowsJ2 93 94 76 82 ≤ 15060084660352 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_272
#print axioms SieveCert.rows22325R_275
