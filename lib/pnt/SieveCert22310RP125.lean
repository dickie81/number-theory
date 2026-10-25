/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 495–498 of 1732

File 125 of 430: the parts `rows22310R_495` … `rows22310R_498` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28898 tests: row 104 columns 103–399, row 105 columns 0–34, row 105 columns
35–43, row 105 columns 44–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_495 : rowsJ2 104 105 103 400 ≤ 4608055562630 := by decide +kernel

theorem rows22310R_496 : rowsJ2 105 106 0 35 ≤ 168986204202736 := by decide +kernel

theorem rows22310R_497 : rowsJ2 105 106 35 44 ≤ 139183033204377 := by decide +kernel

theorem rows22310R_498 : rowsJ2 105 106 44 52 ≤ 236052956179325 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_495
#print axioms SieveCert.rows22310R_498
