/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1468–1471 of 1732

File 369 of 430: the parts `rows22310R_1468` … `rows22310R_1471` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27721 tests: row 175 columns 66–70, row 175 columns 71–76, row 175 columns
77–399, row 176 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1468 : rowsJ2 175 176 66 71 ≤ 26071966356118 := by decide +kernel

theorem rows22310R_1469 : rowsJ2 175 176 71 77 ≤ 14301795816989 := by decide +kernel

theorem rows22310R_1470 : rowsJ2 175 176 77 400 ≤ 1731580936565970 := by decide +kernel

theorem rows22310R_1471 : rowsJ2 176 177 0 52 ≤ 50616727208003 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1468
#print axioms SieveCert.rows22310R_1471
