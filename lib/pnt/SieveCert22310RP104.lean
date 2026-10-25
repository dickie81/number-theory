/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 414–417 of 1732

File 104 of 430: the parts `rows22310R_414` … `rows22310R_417` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24105 tests: row 98 columns 90–92, row 98 columns 93–94, row 98 columns
95–96, row 98 columns 97–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_414 : rowsJ2 98 99 90 93 ≤ 8470451098224 := by decide +kernel

theorem rows22310R_415 : rowsJ2 98 99 93 95 ≤ 5173408533984 := by decide +kernel

theorem rows22310R_416 : rowsJ2 98 99 95 97 ≤ 5556503041695 := by decide +kernel

theorem rows22310R_417 : rowsJ2 98 99 97 400 ≤ 7008466725560 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_414
#print axioms SieveCert.rows22310R_417
