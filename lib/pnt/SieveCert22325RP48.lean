/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 183–186 of 561

File 48 of 142: the parts `rows22325R_183` … `rows22325R_186` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24097 tests: row 81 columns 68–71, row 81 columns 72–75, row 81 columns
76–79, row 81 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_183 : rowsJ2 81 82 68 72 ≤ 11785938554952 := by decide +kernel

theorem rows22325R_184 : rowsJ2 81 82 72 76 ≤ 12445976677137 := by decide +kernel

theorem rows22325R_185 : rowsJ2 81 82 76 80 ≤ 10181614538835 := by decide +kernel

theorem rows22325R_186 : rowsJ2 81 82 80 300 ≤ 6057041562794 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_183
#print axioms SieveCert.rows22325R_186
