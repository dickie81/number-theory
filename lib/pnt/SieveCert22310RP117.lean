/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 465–468 of 1732

File 117 of 430: the parts `rows22310R_465` … `rows22310R_468` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28271 tests: row 102 columns 97–98, row 102 columns 99–100, row 102 columns
101–399, row 103 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_465 : rowsJ2 102 103 97 99 ≤ 6829824113667 := by decide +kernel

theorem rows22310R_466 : rowsJ2 102 103 99 101 ≤ 6884880817496 := by decide +kernel

theorem rows22310R_467 : rowsJ2 102 103 101 400 ≤ 6320378678133 := by decide +kernel

theorem rows22310R_468 : rowsJ2 103 104 0 35 ≤ 195929355987332 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_465
#print axioms SieveCert.rows22310R_468
