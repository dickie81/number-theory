/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 437–440 of 1732

File 110 of 430: the parts `rows22310R_437` … `rows22310R_440` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25145 tests: row 100 columns 90–92, row 100 columns 93–94, row 100 columns
95–96, row 100 columns 97–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_437 : rowsJ2 100 101 90 93 ≤ 5958321580305 := by decide +kernel

theorem rows22310R_438 : rowsJ2 100 101 93 95 ≤ 3935521555234 := by decide +kernel

theorem rows22310R_439 : rowsJ2 100 101 95 97 ≤ 5076987603545 := by decide +kernel

theorem rows22310R_440 : rowsJ2 100 101 97 99 ≤ 6918468654351 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_437
#print axioms SieveCert.rows22310R_440
