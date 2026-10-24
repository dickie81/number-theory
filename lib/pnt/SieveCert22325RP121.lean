/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 467–470 of 561

File 121 of 142: the parts `rows22325R_467` … `rows22325R_470` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26177 tests: row 130 columns 53–299, row 131 columns 0–43, row 131 columns
44–51, row 131 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_467 : rowsJ2 130 131 53 300 ≤ 2238987864989197 := by decide +kernel

theorem rows22325R_468 : rowsJ2 131 132 0 44 ≤ 126566499297672 := by decide +kernel

theorem rows22325R_469 : rowsJ2 131 132 44 52 ≤ 111821329405669 := by decide +kernel

theorem rows22325R_470 : rowsJ2 131 132 52 300 ≤ 2395208263865956 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_467
#print axioms SieveCert.rows22325R_470
