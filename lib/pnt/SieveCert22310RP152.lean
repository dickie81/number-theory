/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 602–605 of 1732

File 152 of 430: the parts `rows22310R_602` … `rows22310R_605` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25273 tests: row 111 columns 91–92, row 111 columns 93–94, row 111 columns
95–96, row 111 columns 97–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_602 : rowsJ2 111 112 91 93 ≤ 2096105374616 := by decide +kernel

theorem rows22310R_603 : rowsJ2 111 112 93 95 ≤ 3062569982548 := by decide +kernel

theorem rows22310R_604 : rowsJ2 111 112 95 97 ≤ 2884231679832 := by decide +kernel

theorem rows22310R_605 : rowsJ2 111 112 97 99 ≤ 2516757537271 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_602
#print axioms SieveCert.rows22310R_605
