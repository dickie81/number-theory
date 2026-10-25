/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1617–1620 of 1732

File 407 of 430: the parts `rows22310R_1617` … `rows22310R_1620` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24621 tests: row 207 columns 0–40, row 207 columns 41–47, row 207 columns
48–399, row 208 columns 0–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1617 : rowsJ2 207 208 0 41 ≤ 40132247760933 := by decide +kernel

theorem rows22310R_1618 : rowsJ2 207 208 41 48 ≤ 101119498244560 := by decide +kernel

theorem rows22310R_1619 : rowsJ2 207 208 48 400 ≤ 2248668219189227 := by decide +kernel

theorem rows22310R_1620 : rowsJ2 208 209 0 40 ≤ 34102033968619 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1617
#print axioms SieveCert.rows22310R_1620
