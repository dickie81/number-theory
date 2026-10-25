/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1155–1158 of 1732

File 290 of 430: the parts `rows22310R_1155` … `rows22310R_1158` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29484 tests: row 144 columns 89–92, row 144 columns 93–96, row 144 columns
97–101, row 144 columns 102–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1155 : rowsJ2 144 145 89 93 ≤ 0 := by decide +kernel

theorem rows22310R_1156 : rowsJ2 144 145 93 97 ≤ 0 := by decide +kernel

theorem rows22310R_1157 : rowsJ2 144 145 97 102 ≤ 571630260231 := by decide +kernel

theorem rows22310R_1158 : rowsJ2 144 145 102 400 ≤ 319857020969193 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1155
#print axioms SieveCert.rows22310R_1158
