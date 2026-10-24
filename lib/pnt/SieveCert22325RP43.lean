/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 163–166 of 561

File 43 of 142: the parts `rows22325R_163` … `rows22325R_166` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27188 tests: row 78 columns 61–67, row 78 columns 68–71, row 78 columns
72–75, row 78 columns 76–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_163 : rowsJ2 78 79 61 68 ≤ 13238952325612 := by decide +kernel

theorem rows22325R_164 : rowsJ2 78 79 68 72 ≤ 12707452948760 := by decide +kernel

theorem rows22325R_165 : rowsJ2 78 79 72 76 ≤ 20132323791108 := by decide +kernel

theorem rows22325R_166 : rowsJ2 78 79 76 300 ≤ 12115988382969 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_163
#print axioms SieveCert.rows22325R_166
