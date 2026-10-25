/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1519–1522 of 1732

File 382 of 430: the parts `rows22310R_1519` … `rows22310R_1522` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24697 tests: row 183 columns 60–64, row 183 columns 65–70, row 183 columns
71–399, row 184 columns 0–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1519 : rowsJ2 183 184 60 65 ≤ 36865626378221 := by decide +kernel

theorem rows22310R_1520 : rowsJ2 183 184 65 71 ≤ 22139188047754 := by decide +kernel

theorem rows22310R_1521 : rowsJ2 183 184 71 400 ≤ 2088741042451812 := by decide +kernel

theorem rows22310R_1522 : rowsJ2 184 185 0 49 ≤ 35746176154469 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1519
#print axioms SieveCert.rows22310R_1522
