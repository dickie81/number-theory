/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 404–407 of 561

File 105 of 142: the parts `rows22325R_404` … `rows22325R_407` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26031 tests: row 115 columns 49–54, row 115 columns 55–60, row 115 columns
61–68, row 115 columns 69–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_404 : rowsJ2 115 116 49 55 ≤ 59109063198031 := by decide +kernel

theorem rows22325R_405 : rowsJ2 115 116 55 61 ≤ 39780923819784 := by decide +kernel

theorem rows22325R_406 : rowsJ2 115 116 61 69 ≤ 13492871500486 := by decide +kernel

theorem rows22325R_407 : rowsJ2 115 116 69 300 ≤ 209270025097 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_404
#print axioms SieveCert.rows22325R_407
