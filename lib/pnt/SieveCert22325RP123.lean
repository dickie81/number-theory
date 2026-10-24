/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 475–479 of 561

File 123 of 142: the parts `rows22325R_475` … `rows22325R_479` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 29794 tests: row 133 columns 44–52, row 133 columns 53–299, row 134 columns
0–42, row 134 columns 43–51, row 134 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_475 : rowsJ2 133 134 44 53 ≤ 113506817989334 := by decide +kernel

theorem rows22325R_476 : rowsJ2 133 134 53 300 ≤ 2670999677877437 := by decide +kernel

theorem rows22325R_477 : rowsJ2 134 135 0 43 ≤ 122963708673886 := by decide +kernel

theorem rows22325R_478 : rowsJ2 134 135 43 52 ≤ 122117798509225 := by decide +kernel

theorem rows22325R_479 : rowsJ2 134 135 52 300 ≤ 2820325141968972 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_475
#print axioms SieveCert.rows22325R_479
