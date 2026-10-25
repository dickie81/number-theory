/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1030–1033 of 1732

File 258 of 430: the parts `rows22310R_1030` … `rows22310R_1033` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27520 tests: row 135 columns 96–98, row 135 columns 99–102, row 135 columns
103–106, row 135 columns 107–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1030 : rowsJ2 135 136 96 99 ≤ 0 := by decide +kernel

theorem rows22310R_1031 : rowsJ2 135 136 99 103 ≤ 1129462735515 := by decide +kernel

theorem rows22310R_1032 : rowsJ2 135 136 103 107 ≤ 8167346036516 := by decide +kernel

theorem rows22310R_1033 : rowsJ2 135 136 107 400 ≤ 669455869314482 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1030
#print axioms SieveCert.rows22310R_1033
