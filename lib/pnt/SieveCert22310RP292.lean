/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1163–1166 of 1732

File 292 of 430: the parts `rows22310R_1163` … `rows22310R_1166` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28002 tests: row 145 columns 74–76, row 145 columns 77–79, row 145 columns
80–82, row 145 columns 83–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1163 : rowsJ2 145 146 74 77 ≤ 9812994429137 := by decide +kernel

theorem rows22310R_1164 : rowsJ2 145 146 77 80 ≤ 7696593560194 := by decide +kernel

theorem rows22310R_1165 : rowsJ2 145 146 80 83 ≤ 4484864760532 := by decide +kernel

theorem rows22310R_1166 : rowsJ2 145 146 83 86 ≤ 1937871075020 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1163
#print axioms SieveCert.rows22310R_1166
