/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1526–1529 of 1732

File 384 of 430: the parts `rows22310R_1526` … `rows22310R_1529` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24131 tests: row 184 columns 65–133, row 184 columns 134–399, row 185 columns
0–48, row 185 columns 49–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1526 : rowsJ2 184 185 65 134 ≤ 118731519437575 := by decide +kernel

theorem rows22310R_1527 : rowsJ2 184 185 134 400 ≤ 1988576078104113 := by decide +kernel

theorem rows22310R_1528 : rowsJ2 185 186 0 49 ≤ 36706020683324 := by decide +kernel

theorem rows22310R_1529 : rowsJ2 185 186 49 55 ≤ 46899638870269 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1526
#print axioms SieveCert.rows22310R_1529
