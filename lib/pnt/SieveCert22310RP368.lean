/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1464–1467 of 1732

File 368 of 430: the parts `rows22310R_1464` … `rows22310R_1467` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28592 tests: row 175 columns 0–51, row 175 columns 52–57, row 175 columns
58–61, row 175 columns 62–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1464 : rowsJ2 175 176 0 52 ≤ 51654065531453 := by decide +kernel

theorem rows22310R_1465 : rowsJ2 175 176 52 58 ≤ 32935220016131 := by decide +kernel

theorem rows22310R_1466 : rowsJ2 175 176 58 62 ≤ 34868832248545 := by decide +kernel

theorem rows22310R_1467 : rowsJ2 175 176 62 66 ≤ 33813172498889 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1464
#print axioms SieveCert.rows22310R_1467
