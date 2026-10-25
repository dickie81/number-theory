/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 663–666 of 1732

File 167 of 430: the parts `rows22310R_663` … `rows22310R_666` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24380 tests: row 114 columns 105–107, row 114 columns 108–110, row 114
columns 111–113, row 114 columns 114–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_663 : rowsJ2 114 115 105 108 ≤ 3259823066245 := by decide +kernel

theorem rows22310R_664 : rowsJ2 114 115 108 111 ≤ 5514328301294 := by decide +kernel

theorem rows22310R_665 : rowsJ2 114 115 111 114 ≤ 8868403790904 := by decide +kernel

theorem rows22310R_666 : rowsJ2 114 115 114 400 ≤ 3892454751428 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_663
#print axioms SieveCert.rows22310R_666
