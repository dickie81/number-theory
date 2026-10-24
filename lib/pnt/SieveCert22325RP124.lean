/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 480–483 of 561

File 124 of 142: the parts `rows22325R_480` … `rows22325R_483` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25696 tests: row 135 columns 0–42, row 135 columns 43–51, row 135 columns
52–299, row 136 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_480 : rowsJ2 135 136 0 43 ≤ 129428858565514 := by decide +kernel

theorem rows22325R_481 : rowsJ2 135 136 43 52 ≤ 118062892713337 := by decide +kernel

theorem rows22325R_482 : rowsJ2 135 136 52 300 ≤ 2805226479565900 := by decide +kernel

theorem rows22325R_483 : rowsJ2 136 137 0 43 ≤ 136628258393281 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_480
#print axioms SieveCert.rows22325R_483
