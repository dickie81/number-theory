/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 658–662 of 1732

File 166 of 430: the parts `rows22310R_658` … `rows22310R_662` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 28980 tests: row 114 columns 95–96, row 114 columns 97–98, row 114 columns
99–100, row 114 columns 101–102, row 114 columns 103–104), each a sum of refined costs (`rows2` or `rowsJ2`) at most
its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_658 : rowsJ2 114 115 95 97 ≤ 1757118680677 := by decide +kernel

theorem rows22310R_659 : rowsJ2 114 115 97 99 ≤ 1467245578246 := by decide +kernel

theorem rows22310R_660 : rowsJ2 114 115 99 101 ≤ 1198997256508 := by decide +kernel

theorem rows22310R_661 : rowsJ2 114 115 101 103 ≤ 1159471191032 := by decide +kernel

theorem rows22310R_662 : rowsJ2 114 115 103 105 ≤ 1420590931339 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_658
#print axioms SieveCert.rows22310R_662
