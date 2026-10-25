/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1390–1393 of 1732

File 349 of 430: the parts `rows22310R_1390` … `rows22310R_1393` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27025 tests: row 165 columns 76–80, row 165 columns 81–86, row 165 columns
87–399, row 166 columns 0–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1390 : rowsJ2 165 166 76 81 ≤ 11238354910240 := by decide +kernel

theorem rows22310R_1391 : rowsJ2 165 166 81 87 ≤ 4130281807661 := by decide +kernel

theorem rows22310R_1392 : rowsJ2 165 166 87 400 ≤ 814350117536560 := by decide +kernel

theorem rows22310R_1393 : rowsJ2 166 167 0 55 ≤ 85989025512736 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1390
#print axioms SieveCert.rows22310R_1393
