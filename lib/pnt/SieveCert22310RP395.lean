/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1569–1572 of 1732

File 395 of 430: the parts `rows22310R_1569` … `rows22310R_1572` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28790 tests: row 193 columns 46–51, row 193 columns 52–57, row 193 columns
58–399, row 194 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1569 : rowsJ2 193 194 46 52 ≤ 58508276595134 := by decide +kernel

theorem rows22310R_1570 : rowsJ2 193 194 52 58 ≤ 66084305914392 := by decide +kernel

theorem rows22310R_1571 : rowsJ2 193 194 58 400 ≤ 2118000987912927 := by decide +kernel

theorem rows22310R_1572 : rowsJ2 194 195 0 45 ≤ 30699171115959 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1569
#print axioms SieveCert.rows22310R_1572
