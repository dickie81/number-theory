/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1448–1451 of 1732

File 364 of 430: the parts `rows22310R_1448` … `rows22310R_1451` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24982 tests: row 172 columns 76–81, row 172 columns 82–399, row 173 columns
0–52, row 173 columns 53–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1448 : rowsJ2 172 173 76 82 ≤ 6713788133902 := by decide +kernel

theorem rows22310R_1449 : rowsJ2 172 173 82 400 ≤ 1474134050556774 := by decide +kernel

theorem rows22310R_1450 : rowsJ2 173 174 0 53 ≤ 58832705081644 := by decide +kernel

theorem rows22310R_1451 : rowsJ2 173 174 53 59 ≤ 31988648402298 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1448
#print axioms SieveCert.rows22310R_1451
