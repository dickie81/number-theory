/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1006–1009 of 1732

File 252 of 430: the parts `rows22310R_1006` … `rows22310R_1009` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29040 tests: row 134 columns 68–72, row 134 columns 73–76, row 134 columns
77–79, row 134 columns 80–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1006 : rowsJ2 134 135 68 73 ≤ 3878844350932 := by decide +kernel

theorem rows22310R_1007 : rowsJ2 134 135 73 77 ≤ 1195607051648 := by decide +kernel

theorem rows22310R_1008 : rowsJ2 134 135 77 80 ≤ 0 := by decide +kernel

theorem rows22310R_1009 : rowsJ2 134 135 80 83 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1006
#print axioms SieveCert.rows22310R_1009
