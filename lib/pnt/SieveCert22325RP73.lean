/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 280–283 of 561

File 73 of 142: the parts `rows22325R_280` … `rows22325R_283` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26106 tests: row 94 columns 66–70, row 94 columns 71–75, row 94 columns
76–81, row 94 columns 82–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_280 : rowsJ2 94 95 66 71 ≤ 159195715042 := by decide +kernel

theorem rows22325R_281 : rowsJ2 94 95 71 76 ≤ 0 := by decide +kernel

theorem rows22325R_282 : rowsJ2 94 95 76 82 ≤ 16076761016392 := by decide +kernel

theorem rows22325R_283 : rowsJ2 94 95 82 300 ≤ 1198009338512164 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_280
#print axioms SieveCert.rows22325R_283
