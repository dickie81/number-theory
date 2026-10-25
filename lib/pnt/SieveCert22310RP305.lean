/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1215–1218 of 1732

File 305 of 430: the parts `rows22310R_1215` … `rows22310R_1218` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26744 tests: row 149 columns 73–75, row 149 columns 76–78, row 149 columns
79–81, row 149 columns 82–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1215 : rowsJ2 149 150 73 76 ≤ 13664374355223 := by decide +kernel

theorem rows22310R_1216 : rowsJ2 149 150 76 79 ≤ 10613857457394 := by decide +kernel

theorem rows22310R_1217 : rowsJ2 149 150 79 82 ≤ 7145294197643 := by decide +kernel

theorem rows22310R_1218 : rowsJ2 149 150 82 85 ≤ 4370444403953 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1215
#print axioms SieveCert.rows22310R_1218
