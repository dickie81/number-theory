/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 643–646 of 1732

File 162 of 430: the parts `rows22310R_643` … `rows22310R_646` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26680 tests: row 113 columns 101–102, row 113 columns 103–104, row 113
columns 105–107, row 113 columns 108–110), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_643 : rowsJ2 113 114 101 103 ≤ 1380484997569 := by decide +kernel

theorem rows22310R_644 : rowsJ2 113 114 103 105 ≤ 1565369440949 := by decide +kernel

theorem rows22310R_645 : rowsJ2 113 114 105 108 ≤ 3317572263013 := by decide +kernel

theorem rows22310R_646 : rowsJ2 113 114 108 111 ≤ 5381025619230 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_643
#print axioms SieveCert.rows22310R_646
