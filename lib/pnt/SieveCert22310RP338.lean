/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1347–1350 of 1732

File 338 of 430: the parts `rows22310R_1347` … `rows22310R_1350` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27456 tests: row 161 columns 57–62, row 161 columns 63–66, row 161 columns
67–69, row 161 columns 70–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1347 : rowsJ2 161 162 57 63 ≤ 21501235941960 := by decide +kernel

theorem rows22310R_1348 : rowsJ2 161 162 63 67 ≤ 24143659157599 := by decide +kernel

theorem rows22310R_1349 : rowsJ2 161 162 67 70 ≤ 22704829493593 := by decide +kernel

theorem rows22310R_1350 : rowsJ2 161 162 70 73 ≤ 19117454611023 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1347
#print axioms SieveCert.rows22310R_1350
