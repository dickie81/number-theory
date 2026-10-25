/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 650–653 of 1732

File 164 of 430: the parts `rows22310R_650` … `rows22310R_653` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27612 tests: row 114 columns 45–67, row 114 columns 68–78, row 114 columns
79–82, row 114 columns 83–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_650 : rowsJ2 114 115 45 68 ≤ 339549697513659 := by decide +kernel

theorem rows22310R_651 : rowsJ2 114 115 68 79 ≤ 32323272867479 := by decide +kernel

theorem rows22310R_652 : rowsJ2 114 115 79 83 ≤ 416848943731 := by decide +kernel

theorem rows22310R_653 : rowsJ2 114 115 83 86 ≤ 30472768761 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_650
#print axioms SieveCert.rows22310R_653
