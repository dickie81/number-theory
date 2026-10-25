/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1417–1420 of 1732

File 356 of 430: the parts `rows22310R_1417` … `rows22310R_1420` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28667 tests: row 168 columns 82–399, row 169 columns 0–53, row 169 columns
54–59, row 169 columns 60–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1417 : rowsJ2 168 169 82 400 ≤ 1115802552396075 := by decide +kernel

theorem rows22310R_1418 : rowsJ2 169 170 0 54 ≤ 72252528325733 := by decide +kernel

theorem rows22310R_1419 : rowsJ2 169 170 54 60 ≤ 27033400041220 := by decide +kernel

theorem rows22310R_1420 : rowsJ2 169 170 60 64 ≤ 29464457576326 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1417
#print axioms SieveCert.rows22310R_1420
