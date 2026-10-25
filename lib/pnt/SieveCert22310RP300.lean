/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1195–1198 of 1732

File 300 of 430: the parts `rows22310R_1195` … `rows22310R_1198` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23741 tests: row 147 columns 94–98, row 147 columns 99–106, row 147 columns
107–399, row 148 columns 0–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1195 : rowsJ2 147 148 94 99 ≤ 0 := by decide +kernel

theorem rows22310R_1196 : rowsJ2 147 148 99 107 ≤ 129189976291131 := by decide +kernel

theorem rows22310R_1197 : rowsJ2 147 148 107 400 ≤ 119274984243574 := by decide +kernel

theorem rows22310R_1198 : rowsJ2 148 149 0 60 ≤ 209187950776658 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1195
#print axioms SieveCert.rows22310R_1198
