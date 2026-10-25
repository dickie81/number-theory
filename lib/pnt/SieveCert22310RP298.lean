/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1187–1190 of 1732

File 298 of 430: the parts `rows22310R_1187` … `rows22310R_1190` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27550 tests: row 147 columns 67–70, row 147 columns 71–73, row 147 columns
74–76, row 147 columns 77–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1187 : rowsJ2 147 148 67 71 ≤ 13219884441664 := by decide +kernel

theorem rows22310R_1188 : rowsJ2 147 148 71 74 ≤ 11488641453248 := by decide +kernel

theorem rows22310R_1189 : rowsJ2 147 148 74 77 ≤ 11651541261760 := by decide +kernel

theorem rows22310R_1190 : rowsJ2 147 148 77 80 ≤ 8663330235689 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1187
#print axioms SieveCert.rows22310R_1190
