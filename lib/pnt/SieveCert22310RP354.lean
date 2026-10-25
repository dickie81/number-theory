/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1409–1412 of 1732

File 354 of 430: the parts `rows22310R_1409` … `rows22310R_1412` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28034 tests: row 167 columns 83–399, row 168 columns 0–54, row 168 columns
55–59, row 168 columns 60–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1409 : rowsJ2 167 168 83 400 ≤ 1017045662135340 := by decide +kernel

theorem rows22310R_1410 : rowsJ2 168 169 0 55 ≤ 78827862843624 := by decide +kernel

theorem rows22310R_1411 : rowsJ2 168 169 55 60 ≤ 22134150500219 := by decide +kernel

theorem rows22310R_1412 : rowsJ2 168 169 60 64 ≤ 27806608548613 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1409
#print axioms SieveCert.rows22310R_1412
