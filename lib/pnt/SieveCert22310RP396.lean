/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1573–1576 of 1732

File 396 of 430: the parts `rows22310R_1573` … `rows22310R_1576` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28837 tests: row 194 columns 45–50, row 194 columns 51–56, row 194 columns
57–399, row 195 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1573 : rowsJ2 194 195 45 51 ≤ 56824903871451 := by decide +kernel

theorem rows22310R_1574 : rowsJ2 194 195 51 57 ≤ 69388555415325 := by decide +kernel

theorem rows22310R_1575 : rowsJ2 194 195 57 400 ≤ 2127367429915697 := by decide +kernel

theorem rows22310R_1576 : rowsJ2 195 196 0 45 ≤ 33700097231503 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1573
#print axioms SieveCert.rows22310R_1576
