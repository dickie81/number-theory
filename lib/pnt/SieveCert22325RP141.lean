/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 556–559 of 561

File 141 of 142: the parts `rows22325R_556` … `rows22325R_559` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28925 tests: rows 234–283, rows 284–288, rows 289–292, rows 293–296), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_556 : rows2 234 284 ≤ 42236835023279305 := by decide +kernel

theorem rows22325R_557 : rows2 284 289 ≤ 58606429944370477 := by decide +kernel

theorem rows22325R_558 : rows2 289 293 ≤ 50610858260028722 := by decide +kernel

theorem rows22325R_559 : rows2 293 297 ≤ 54361000493366682 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_556
#print axioms SieveCert.rows22325R_559
