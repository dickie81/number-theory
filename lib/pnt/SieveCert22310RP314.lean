/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1252–1255 of 1732

File 314 of 430: the parts `rows22310R_1252` … `rows22310R_1255` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27658 tests: row 152 columns 72–74, row 152 columns 75–77, row 152 columns
78–80, row 152 columns 81–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1252 : rowsJ2 152 153 72 75 ≤ 16293418850330 := by decide +kernel

theorem rows22310R_1253 : rowsJ2 152 153 75 78 ≤ 12529336176872 := by decide +kernel

theorem rows22310R_1254 : rowsJ2 152 153 78 81 ≤ 8815960153025 := by decide +kernel

theorem rows22310R_1255 : rowsJ2 152 153 81 85 ≤ 7182610237108 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1252
#print axioms SieveCert.rows22310R_1255
