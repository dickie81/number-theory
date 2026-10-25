/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 76–79 of 1732

File 19 of 430: the parts `rows22310R_76` … `rows22310R_79` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25589 tests: row 56 columns 50–54, row 56 columns 55–399, row 57 columns
0–34, row 57 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_76 : rowsJ2 56 57 50 55 ≤ 159614298268536 := by decide +kernel

theorem rows22310R_77 : rowsJ2 56 57 55 400 ≤ 62471633542725 := by decide +kernel

theorem rows22310R_78 : rowsJ2 57 58 0 35 ≤ 1218152694887108 := by decide +kernel

theorem rows22310R_79 : rowsJ2 57 58 35 44 ≤ 488918803563042 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_76
#print axioms SieveCert.rows22310R_79
