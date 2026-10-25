/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 582–585 of 1732

File 147 of 430: the parts `rows22310R_582` … `rows22310R_585` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27119 tests: row 110 columns 83–86, row 110 columns 87–89, row 110 columns
90–91, row 110 columns 92–93), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_582 : rowsJ2 110 111 83 87 ≤ 539172681637 := by decide +kernel

theorem rows22310R_583 : rowsJ2 110 111 87 90 ≤ 1010538466776 := by decide +kernel

theorem rows22310R_584 : rowsJ2 110 111 90 92 ≤ 1613581691405 := by decide +kernel

theorem rows22310R_585 : rowsJ2 110 111 92 94 ≤ 2672508469481 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_582
#print axioms SieveCert.rows22310R_585
