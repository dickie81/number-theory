/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 249–252 of 1732

File 62 of 430: the parts `rows22310R_249` … `rows22310R_252` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24073 tests: row 79 columns 59–63, row 79 columns 64–69, row 79 columns
70–77, row 79 columns 78–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_249 : rowsJ2 79 80 59 64 ≤ 196300643443845 := by decide +kernel

theorem rows22310R_250 : rowsJ2 79 80 64 70 ≤ 207631908747283 := by decide +kernel

theorem rows22310R_251 : rowsJ2 79 80 70 78 ≤ 227892293493894 := by decide +kernel

theorem rows22310R_252 : rowsJ2 79 80 78 400 ≤ 48205209141430 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_249
#print axioms SieveCert.rows22310R_252
