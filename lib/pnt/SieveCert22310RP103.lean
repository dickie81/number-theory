/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 410–413 of 1732

File 103 of 430: the parts `rows22310R_410` … `rows22310R_413` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29458 tests: row 98 columns 51–58, row 98 columns 59–74, row 98 columns
75–85, row 98 columns 86–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_410 : rowsJ2 98 99 51 59 ≤ 233695311230159 := by decide +kernel

theorem rows22310R_411 : rowsJ2 98 99 59 75 ≤ 297145413695459 := by decide +kernel

theorem rows22310R_412 : rowsJ2 98 99 75 86 ≤ 90396506072768 := by decide +kernel

theorem rows22310R_413 : rowsJ2 98 99 86 90 ≤ 15381826945068 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_410
#print axioms SieveCert.rows22310R_413
