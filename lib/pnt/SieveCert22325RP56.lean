/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 213–216 of 561

File 56 of 142: the parts `rows22325R_213` … `rows22325R_216` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23635 tests: row 85 columns 75–79, row 85 columns 80–84, row 85 columns
85–299, row 86 columns 0–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_213 : rowsJ2 85 86 75 80 ≤ 6695187765891 := by decide +kernel

theorem rows22325R_214 : rowsJ2 85 86 80 85 ≤ 19176421651530 := by decide +kernel

theorem rows22325R_215 : rowsJ2 85 86 85 300 ≤ 6698721161118 := by decide +kernel

theorem rows22325R_216 : rowsJ2 86 87 0 40 ≤ 662783237374893 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_213
#print axioms SieveCert.rows22325R_216
