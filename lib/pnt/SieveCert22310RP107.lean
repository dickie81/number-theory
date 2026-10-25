/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 425–429 of 1732

File 107 of 430: the parts `rows22310R_425` … `rows22310R_429` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 28136 tests: row 99 columns 90–92, row 99 columns 93–94, row 99 columns
95–96, row 99 columns 97–98, row 99 columns 99–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_425 : rowsJ2 99 100 90 93 ≤ 7192949064439 := by decide +kernel

theorem rows22310R_426 : rowsJ2 99 100 93 95 ≤ 4461534110774 := by decide +kernel

theorem rows22310R_427 : rowsJ2 99 100 95 97 ≤ 5214357988884 := by decide +kernel

theorem rows22310R_428 : rowsJ2 99 100 97 99 ≤ 6963475304517 := by decide +kernel

theorem rows22310R_429 : rowsJ2 99 100 99 400 ≤ 4269700185623 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_425
#print axioms SieveCert.rows22310R_429
