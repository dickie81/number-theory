/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 229–232 of 561

File 60 of 142: the parts `rows22325R_229` … `rows22325R_232` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25290 tests: row 87 columns 75–79, row 87 columns 80–85, row 87 columns
86–299, row 88 columns 0–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_229 : rowsJ2 87 88 75 80 ≤ 5204880294566 := by decide +kernel

theorem rows22325R_230 : rowsJ2 87 88 80 86 ≤ 28868477180493 := by decide +kernel

theorem rows22325R_231 : rowsJ2 87 88 86 300 ≤ 19740647695694 := by decide +kernel

theorem rows22325R_232 : rowsJ2 88 89 0 48 ≤ 765111152443206 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_229
#print axioms SieveCert.rows22325R_232
