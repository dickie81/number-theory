/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 396–399 of 561

File 103 of 142: the parts `rows22325R_396` … `rows22325R_399` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27646 tests: row 113 columns 62–69, row 113 columns 70–299, row 114 columns
0–49, row 114 columns 50–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_396 : rowsJ2 113 114 62 70 ≤ 8755726451467 := by decide +kernel

theorem rows22325R_397 : rowsJ2 113 114 70 300 ≤ 108282300715084 := by decide +kernel

theorem rows22325R_398 : rowsJ2 114 115 0 50 ≤ 255987994244438 := by decide +kernel

theorem rows22325R_399 : rowsJ2 114 115 50 56 ≤ 56808326915196 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_396
#print axioms SieveCert.rows22325R_399
