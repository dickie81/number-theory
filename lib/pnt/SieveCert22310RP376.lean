/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1495–1498 of 1732

File 376 of 430: the parts `rows22310R_1495` … `rows22310R_1498` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28962 tests: row 179 columns 61–65, row 179 columns 66–70, row 179 columns
71–399, row 180 columns 0–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1495 : rowsJ2 179 180 61 66 ≤ 38617714546953 := by decide +kernel

theorem rows22310R_1496 : rowsJ2 179 180 66 71 ≤ 21402243018670 := by decide +kernel

theorem rows22310R_1497 : rowsJ2 179 180 71 400 ≤ 2069072099311946 := by decide +kernel

theorem rows22310R_1498 : rowsJ2 180 181 0 50 ≤ 39356378055116 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1495
#print axioms SieveCert.rows22310R_1498
