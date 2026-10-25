/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 476–479 of 1732

File 120 of 430: the parts `rows22310R_476` … `rows22310R_479` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25861 tests: row 103 columns 93–94, row 103 columns 95–96, row 103 columns
97–98, row 103 columns 99–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_476 : rowsJ2 103 104 93 95 ≤ 3454745417484 := by decide +kernel

theorem rows22310R_477 : rowsJ2 103 104 95 97 ≤ 4978856292688 := by decide +kernel

theorem rows22310R_478 : rowsJ2 103 104 97 99 ≤ 6467455486341 := by decide +kernel

theorem rows22310R_479 : rowsJ2 103 104 99 101 ≤ 6219957531338 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_476
#print axioms SieveCert.rows22310R_479
