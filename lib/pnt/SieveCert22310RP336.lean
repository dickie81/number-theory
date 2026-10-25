/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1339–1342 of 1732

File 336 of 430: the parts `rows22310R_1339` … `rows22310R_1342` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27269 tests: row 160 columns 67–69, row 160 columns 70–72, row 160 columns
73–76, row 160 columns 77–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1339 : rowsJ2 160 161 67 70 ≤ 22023113689940 := by decide +kernel

theorem rows22310R_1340 : rowsJ2 160 161 70 73 ≤ 19485679740642 := by decide +kernel

theorem rows22310R_1341 : rowsJ2 160 161 73 77 ≤ 18284978306688 := by decide +kernel

theorem rows22310R_1342 : rowsJ2 160 161 77 81 ≤ 11189050153954 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1339
#print axioms SieveCert.rows22310R_1342
