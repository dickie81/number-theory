/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1319–1322 of 1732

File 331 of 430: the parts `rows22310R_1319` … `rows22310R_1322` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27907 tests: row 158 columns 68–70, row 158 columns 71–73, row 158 columns
74–77, row 158 columns 78–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1319 : rowsJ2 158 159 68 71 ≤ 20838491286275 := by decide +kernel

theorem rows22310R_1320 : rowsJ2 158 159 71 74 ≤ 18303022189878 := by decide +kernel

theorem rows22310R_1321 : rowsJ2 158 159 74 78 ≤ 17141219421365 := by decide +kernel

theorem rows22310R_1322 : rowsJ2 158 159 78 82 ≤ 10494215444483 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1319
#print axioms SieveCert.rows22310R_1322
