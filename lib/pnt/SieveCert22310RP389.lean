/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1545–1548 of 1732

File 389 of 430: the parts `rows22310R_1545` … `rows22310R_1548` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27639 tests: row 188 columns 53–57, row 188 columns 58–63, row 188 columns
64–399, row 189 columns 0–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1545 : rowsJ2 188 189 53 58 ≤ 55950852258533 := by decide +kernel

theorem rows22310R_1546 : rowsJ2 188 189 58 64 ≤ 42847105264599 := by decide +kernel

theorem rows22310R_1547 : rowsJ2 188 189 64 400 ≤ 2094919922492683 := by decide +kernel

theorem rows22310R_1548 : rowsJ2 189 190 0 47 ≤ 31491479670337 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1545
#print axioms SieveCert.rows22310R_1548
