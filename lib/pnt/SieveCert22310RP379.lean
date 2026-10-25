/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1507–1510 of 1732

File 379 of 430: the parts `rows22310R_1507` … `rows22310R_1510` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28116 tests: row 181 columns 60–64, row 181 columns 65–70, row 181 columns
71–399, row 182 columns 0–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1507 : rowsJ2 181 182 60 65 ≤ 39782965982978 := by decide +kernel

theorem rows22310R_1508 : rowsJ2 181 182 65 71 ≤ 24811970138346 := by decide +kernel

theorem rows22310R_1509 : rowsJ2 181 182 71 400 ≤ 2099361393982868 := by decide +kernel

theorem rows22310R_1510 : rowsJ2 182 183 0 50 ≤ 39585582202884 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1507
#print axioms SieveCert.rows22310R_1510
