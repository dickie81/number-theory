/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 108–111 of 1732

File 27 of 430: the parts `rows22310R_108` … `rows22310R_111` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28500 tests: row 62 columns 44–49, row 62 columns 50–54, row 62 columns
55–58, row 62 columns 59–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_108 : rowsJ2 62 63 44 50 ≤ 165666600296883 := by decide +kernel

theorem rows22310R_109 : rowsJ2 62 63 50 55 ≤ 124960105587516 := by decide +kernel

theorem rows22310R_110 : rowsJ2 62 63 55 59 ≤ 113987579723844 := by decide +kernel

theorem rows22310R_111 : rowsJ2 62 63 59 400 ≤ 143199289443860 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_108
#print axioms SieveCert.rows22310R_111
