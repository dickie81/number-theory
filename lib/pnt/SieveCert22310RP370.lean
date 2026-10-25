/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1472–1475 of 1732

File 370 of 430: the parts `rows22310R_1472` … `rows22310R_1475` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28898 tests: row 176 columns 52–57, row 176 columns 58–61, row 176 columns
62–65, row 176 columns 66–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1472 : rowsJ2 176 177 52 58 ≤ 35203991742143 := by decide +kernel

theorem rows22310R_1473 : rowsJ2 176 177 58 62 ≤ 36802414648448 := by decide +kernel

theorem rows22310R_1474 : rowsJ2 176 177 62 66 ≤ 32638160913260 := by decide +kernel

theorem rows22310R_1475 : rowsJ2 176 177 66 71 ≤ 24856671864942 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1472
#print axioms SieveCert.rows22310R_1475
