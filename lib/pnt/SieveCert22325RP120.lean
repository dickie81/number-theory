/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 463–466 of 561

File 120 of 142: the parts `rows22325R_463` … `rows22325R_466` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29776 tests: row 129 columns 45–52, row 129 columns 53–299, row 130 columns
0–44, row 130 columns 45–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_463 : rowsJ2 129 130 45 53 ≤ 107658195313691 := by decide +kernel

theorem rows22325R_464 : rowsJ2 129 130 53 300 ≤ 2087944881197368 := by decide +kernel

theorem rows22325R_465 : rowsJ2 130 131 0 45 ≤ 138614505404830 := by decide +kernel

theorem rows22325R_466 : rowsJ2 130 131 45 53 ≤ 106413655115049 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_463
#print axioms SieveCert.rows22325R_466
