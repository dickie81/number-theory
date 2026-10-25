/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1515–1518 of 1732

File 381 of 430: the parts `rows22310R_1515` … `rows22310R_1518` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26157 tests: row 182 columns 71–399, row 183 columns 0–48, row 183 columns
49–54, row 183 columns 55–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1515 : rowsJ2 182 183 71 400 ≤ 2096555205676164 := by decide +kernel

theorem rows22310R_1516 : rowsJ2 183 184 0 49 ≤ 34900577132837 := by decide +kernel

theorem rows22310R_1517 : rowsJ2 183 184 49 55 ≤ 41234465582621 := by decide +kernel

theorem rows22310R_1518 : rowsJ2 183 184 55 60 ≤ 51532945738658 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1515
#print axioms SieveCert.rows22310R_1518
