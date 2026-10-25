/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1549–1552 of 1732

File 390 of 430: the parts `rows22310R_1549` … `rows22310R_1552` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25838 tests: row 189 columns 47–52, row 189 columns 53–57, row 189 columns
58–63, row 189 columns 64–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1549 : rowsJ2 189 190 47 53 ≤ 49990658202912 := by decide +kernel

theorem rows22310R_1550 : rowsJ2 189 190 53 58 ≤ 56175342049684 := by decide +kernel

theorem rows22310R_1551 : rowsJ2 189 190 58 64 ≤ 41116215401467 := by decide +kernel

theorem rows22310R_1552 : rowsJ2 189 190 64 400 ≤ 2087510439212259 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1549
#print axioms SieveCert.rows22310R_1552
