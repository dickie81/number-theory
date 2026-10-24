/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 348–351 of 561

File 91 of 142: the parts `rows22325R_348` … `rows22325R_351` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26186 tests: row 104 columns 76–299, row 105 columns 0–51, row 105 columns
52–57, row 105 columns 58–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_348 : rowsJ2 104 105 76 300 ≤ 697339485848962 := by decide +kernel

theorem rows22325R_349 : rowsJ2 105 106 0 52 ≤ 387634304114323 := by decide +kernel

theorem rows22325R_350 : rowsJ2 105 106 52 58 ≤ 20390504741331 := by decide +kernel

theorem rows22325R_351 : rowsJ2 105 106 58 63 ≤ 4553266122508 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_348
#print axioms SieveCert.rows22325R_351
