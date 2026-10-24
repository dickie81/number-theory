/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 497–500 of 561

File 128 of 142: the parts `rows22325R_497` … `rows22325R_500` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28551 tests: row 141 columns 41–299, row 142 columns 0–40, row 142 columns
41–299, row 143 columns 0–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_497 : rowsJ2 141 142 41 300 ≤ 2891094098739835 := by decide +kernel

theorem rows22325R_498 : rowsJ2 142 143 0 41 ≤ 157551745013185 := by decide +kernel

theorem rows22325R_499 : rowsJ2 142 143 41 300 ≤ 2884144225212206 := by decide +kernel

theorem rows22325R_500 : rowsJ2 143 144 0 41 ≤ 169229702008743 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_497
#print axioms SieveCert.rows22325R_500
